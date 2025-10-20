import discord
from discord import app_commands
from discord.ui import Button, View
import psycopg
from psycopg.rows import dict_row
from psycopg_pool import AsyncConnectionPool
import os
from datetime import datetime, timezone
from typing import List, Callable, Any
import asyncio
from contextlib import asynccontextmanager
from enum import Enum
import math
import logging
import signal

# --- Logging Setup ---
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

# --- Configuration ---
BOT_TOKEN = os.getenv('DISCORD_TOKEN')
HUB_SERVER_ID = os.getenv('HUB_SERVER_ID')
HUB_CHANNEL_ID = os.getenv('HUB_CHANNEL_ID')
LOG_CHANNEL_ID = os.getenv('LOG_CHANNEL_ID')
DATABASE_URL = os.getenv('DATABASE_URL')

# --- Constants ---
REMINDER_DELAY_SECONDS = 3600
FORFEIT_DELAY_SECONDS = 1800
DOUBLE_FORFEIT_DELAY_SECONDS = 14400 # 4 hours
SCRIM_REQUEST_TIMEOUT_SECONDS = 3600
MAX_ACTIVE_MATCHES = 5
MATCH_COOLDOWN_SECONDS = 3600 # 1 hour

# --- Elo K-Factor Constants ---
K_FACTOR_NEW = 32
K_FACTOR_ESTABLISHED = 16
NEW_TEAM_MATCH_THRESHOLD = 10

# --- Enums for Statuses ---
class MatchStatus(str, Enum):
    SCHEDULED = 'scheduled'
    COMPLETED = 'completed'
    DISPUTED = 'disputed'

class ScrimStatus(str, Enum):
    OPEN = 'open'
    MATCHED = 'matched'
    EXPIRED = 'expired'
    CANCELLED = 'cancelled'

class ReportStatus(str, Enum):
    PENDING = 'pending'
    CONFIRMED = 'confirmed'
    REJECTED = 'rejected'

# --- Game & Region Definitions ---
GAMES = {
    "valorant": ["Iron", "Bronze", "Silver", "Gold", "Platinum", "Diamond", "Ascendant", "Immortal", "Radiant"],
    "league of legends": ["Iron", "Bronze", "Silver", "Gold", "Platinum", "Emerald", "Diamond", "Master", "Grandmaster", "Challenger"],
    "rocket league": ["Bronze", "Silver", "Gold", "Platinum", "Diamond", "Champion", "Grand Champion", "Supersonic Legend"]
}
REGIONS = ["NAE", "NAW", "EU", "OCE", "ASIA"]

# --- Bot Setup ---
intents = discord.Intents.default()
intents.message_content = True
intents.members = True

client = discord.Client(intents=intents)
tree = app_commands.CommandTree(client)
pool: AsyncConnectionPool = None
match_reminder_tasks = {}
forfeit_check_tasks = {}
double_forfeit_check_tasks = {}

# --- Asynchronous Database Handling ---

@asynccontextmanager
async def get_cursor(commit=False):
    """Async context manager to get a connection and cursor from the async pool."""
    if not pool:
        raise ConnectionError("Database connection pool is not initialized.")
    async with pool.connection() as conn:
        await conn.execute("SET statement_timeout = '5s'")
        async with conn.cursor(row_factory=dict_row) as cur:
            try:
                yield cur
                if commit:
                    await conn.commit()
            except Exception:
                await conn.rollback()
                raise

async def setup_database():
    """Initializes and alters database tables idempotently."""
    async with get_cursor(commit=True) as cur:
        await cur.execute(f'''CREATE TABLE IF NOT EXISTS teams
                     (team_id SERIAL PRIMARY KEY,
                      server_id BIGINT NOT NULL,
                      team_name TEXT NOT NULL,
                      captain_id BIGINT NOT NULL UNIQUE,
                      game TEXT NOT NULL,
                      rank TEXT,
                      region TEXT,
                      wins INTEGER DEFAULT 0,
                      losses INTEGER DEFAULT 0,
                      elo REAL DEFAULT 1000.0,
                      matches_played INTEGER DEFAULT 0,
                      UNIQUE(server_id, team_name))''')

        await cur.execute(f'''CREATE TABLE IF NOT EXISTS scrim_requests
                     (request_id SERIAL PRIMARY KEY,
                      team_id INTEGER REFERENCES teams(team_id) ON DELETE CASCADE,
                      status TEXT DEFAULT '{ScrimStatus.OPEN}',
                      created_at TIMESTAMPTZ DEFAULT NOW(),
                      hub_message_id BIGINT)''')

        await cur.execute(f'''CREATE TABLE IF NOT EXISTS matches
                     (match_id SERIAL PRIMARY KEY,
                      team1_id INTEGER REFERENCES teams(team_id) ON DELETE SET NULL,
                      team2_id INTEGER REFERENCES teams(team_id) ON DELETE SET NULL,
                      game TEXT,
                      status TEXT DEFAULT '{MatchStatus.SCHEDULED}',
                      reported_winner_team1 INTEGER,
                      reported_winner_team2 INTEGER,
                      final_winner_team_id INTEGER,
                      created_at TIMESTAMPTZ DEFAULT NOW())''')

        await cur.execute("ALTER TABLE teams ADD COLUMN IF NOT EXISTS misconduct_count INTEGER DEFAULT 0;")
        await cur.execute("ALTER TABLE teams ADD COLUMN IF NOT EXISTS no_show_count INTEGER DEFAULT 0;")
        await cur.execute("ALTER TABLE teams ADD COLUMN IF NOT EXISTS matches_played INTEGER DEFAULT 0;")
        await cur.execute("ALTER TABLE matches ADD COLUMN IF NOT EXISTS first_report_at TIMESTAMPTZ DEFAULT NULL;")

        await cur.execute(f"""
            CREATE TABLE IF NOT EXISTS misconduct_reports (
                report_id SERIAL PRIMARY KEY,
                match_id INTEGER REFERENCES matches(match_id) ON DELETE SET NULL,
                reporting_team_id INTEGER REFERENCES teams(team_id) ON DELETE SET NULL,
                accused_team_id INTEGER REFERENCES teams(team_id) ON DELETE SET NULL,
                reason TEXT NOT NULL,
                status TEXT DEFAULT '{ReportStatus.PENDING}',
                created_at TIMESTAMPTZ DEFAULT NOW(),
                UNIQUE(match_id, reporting_team_id)
            )
        """)

        await cur.execute("CREATE INDEX IF NOT EXISTS idx_matches_status ON matches(status);")
        await cur.execute("CREATE INDEX IF NOT EXISTS idx_scrim_requests_status ON scrim_requests(status);")
        await cur.execute("CREATE INDEX IF NOT EXISTS idx_teams_captain_id ON teams(captain_id);")
        await cur.execute("CREATE INDEX IF NOT EXISTS idx_misconduct_reports_status ON misconduct_reports(status);")
    logger.info("Database setup/check complete.")

# --- ELO Calculation Logic ---
def get_k_factor(matches_played: int) -> int:
    if matches_played < NEW_TEAM_MATCH_THRESHOLD:
        return K_FACTOR_NEW
    return K_FACTOR_ESTABLISHED

def calculate_elo_score_deltas(team_a_elo: float, team_b_elo: float, team_a_won: bool):
    r_a = math.pow(10, team_a_elo / 400)
    r_b = math.pow(10, team_b_elo / 400)
    e_a = r_a / (r_a + r_b)
    e_b = r_b / (r_a + r_b)
    s_a, s_b = (1, 0) if team_a_won else (0, 1)
    return s_a - e_a, s_b - e_b

async def _apply_elo_and_stats(cur: psycopg.AsyncCursor, winner_id: int, loser_id: int):
    await cur.execute("SELECT elo, matches_played FROM teams WHERE team_id = %s", (winner_id,))
    winner_data = await cur.fetchone()
    await cur.execute("SELECT elo, matches_played FROM teams WHERE team_id = %s", (loser_id,))
    loser_data = await cur.fetchone()

    if winner_data and loser_data:
        winner_elo, winner_matches = winner_data['elo'], winner_data['matches_played']
        loser_elo, loser_matches = loser_data['elo'], loser_data['matches_played']
        elo_change_winner, elo_change_loser = calculate_elo_score_deltas(winner_elo, loser_elo, True)
        k_winner = get_k_factor(winner_matches)
        k_loser = get_k_factor(loser_matches)
        new_winner_elo = winner_elo + k_winner * elo_change_winner
        new_loser_elo = loser_elo + k_loser * elo_change_loser
        await cur.execute("UPDATE teams SET wins = wins + 1, elo = %s, matches_played = matches_played + 1 WHERE team_id = %s", (new_winner_elo, winner_id))
        await cur.execute("UPDATE teams SET losses = losses + 1, elo = %s, matches_played = matches_played + 1 WHERE team_id = %s", (new_loser_elo, loser_id))
    elif winner_id:
        await cur.execute("UPDATE teams SET wins = wins + 1, matches_played = matches_played + 1 WHERE team_id = %s", (winner_id,))
    elif loser_id:
        await cur.execute("UPDATE teams SET losses = losses + 1, matches_played = matches_played + 1 WHERE team_id = %s", (loser_id,))

# --- Utility Functions ---
def _cancel_all_tasks_for_match(match_id: int):
    """Cancels and removes all background tasks associated with a match_id."""
    tasks_cancelled = 0
    for task_dict in [match_reminder_tasks, forfeit_check_tasks, double_forfeit_check_tasks]:
        if match_id in task_dict:
            try:
                task_dict[match_id].cancel()
            except Exception as e:
                logger.warning(f"Failed to cancel task for match {match_id}: {e}")
            del task_dict[match_id]
            tasks_cancelled += 1
    if tasks_cancelled > 0:
        logger.info(f"Cancelled {tasks_cancelled} background tasks for resolved match {match_id}.")

async def send_dm(user_id: int, message: str, log_prefix: str = "") -> bool:
    """Safely sends a DM to a user and logs errors."""
    if not user_id: return False
    try:
        user = await client.fetch_user(user_id)
        await user.send(message)
        return True
    except (discord.Forbidden, discord.NotFound):
        await log_event(f"{log_prefix} Failed to send DM to user {user_id}: User not found or DMs disabled.", "warning")
    except discord.HTTPException as e:
        await log_event(f"{log_prefix} Failed to send DM to user {user_id}: {e}", "error")
    except Exception as e:
        await log_event(f"{log_prefix} An unexpected error occurred sending DM to {user_id}: {e}", "error")
    return False

async def cleanup_tasks():
    logger.info("Cleaning up pending tasks...")
    for task_list in [match_reminder_tasks, forfeit_check_tasks, double_forfeit_check_tasks]:
        for task in list(task_list.values()):
            task.cancel()
    logger.info("All tasks cleaned up.")

async def log_event(message: str, level: str = "info"):
    log_func = getattr(logger, level, logger.info)
    log_func(message)
    if LOG_CHANNEL_ID:
        try:
            log_channel = client.get_channel(int(LOG_CHANNEL_ID))
            if log_channel:
                await log_channel.send(f"`{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}` | {level.upper()} | {message}")
        except (discord.Forbidden, discord.HTTPException) as e:
            logger.error(f"Failed to send to log channel: {e}")

async def remind_after_delay(match_id: int, team1_captain_id: int, team2_captain_id: int):
    try:
        async with get_cursor() as cur:
            await cur.execute("SELECT status, reported_winner_team1, reported_winner_team2 FROM matches WHERE match_id = %s", (match_id,))
            report_data = await cur.fetchone()
        if report_data and report_data['status'] == MatchStatus.SCHEDULED:
            msg = f"🔔 **Reminder:** Don't forget to report the result for Match ID `{match_id}` using `/report`!"
            reminded = False
            if report_data['reported_winner_team1'] is None and team1_captain_id:
                if await send_dm(team1_captain_id, msg, f"[Match {match_id} Reminder]"):
                    reminded = True
            if report_data['reported_winner_team2'] is None and team2_captain_id:
                if await send_dm(team2_captain_id, msg, f"[Match {match_id} Reminder]"):
                    reminded = True
            if reminded: await log_event(f"Sending report reminder for Match ID: `{match_id}`")
    finally:
        match_reminder_tasks.pop(match_id, None)

async def _check_forfeit(match_id: int, reporting_captain_id: int, opponent_captain_id: int):
    await asyncio.sleep(FORFEIT_DELAY_SECONDS)
    async with get_cursor(commit=True) as cur:
        await cur.execute("SELECT status, reported_winner_team1, reported_winner_team2, team1_id, team2_id FROM matches WHERE match_id = %s FOR UPDATE", (match_id,))
        match = await cur.fetchone()
        if not match or match['status'] != MatchStatus.SCHEDULED or (match['reported_winner_team1'] is not None and match['reported_winner_team2'] is not None):
            return
        
        winner_id = match['reported_winner_team1'] if match['reported_winner_team1'] is not None else match['reported_winner_team2']
        loser_id = match['team2_id'] if winner_id == match['team1_id'] else match['team1_id']
        await cur.execute("UPDATE matches SET status = %s, final_winner_team_id = %s WHERE match_id = %s", (MatchStatus.COMPLETED, winner_id, match_id))
        if winner_id: await cur.execute("UPDATE teams SET wins = wins + 1, matches_played = matches_played + 1 WHERE team_id = %s", (winner_id,))
        if loser_id: await cur.execute("UPDATE teams SET losses = losses + 1, no_show_count = no_show_count + 1, matches_played = matches_played + 1 WHERE team_id = %s", (loser_id,))
        
        await log_event(f"Match `{match_id}` auto-forfeited. Team {loser_id} marked as a no-show.", "info")
        _cancel_all_tasks_for_match(match_id)
        
        log_pfx = f"[Match {match_id} Forfeit]"
        await send_dm(reporting_captain_id, f"✅ Your opponent failed to report for Match ID `{match_id}`. You have been granted the win by forfeit.", log_pfx)
        await send_dm(opponent_captain_id, f"❌ You failed to report for Match ID `{match_id}` in time. You have automatically forfeited the match.", log_pfx)
    
    forfeit_check_tasks.pop(match_id, None)

async def _check_double_forfeit(match_id: int, team1_captain_id: int, team2_captain_id: int):
    await asyncio.sleep(DOUBLE_FORFEIT_DELAY_SECONDS)
    async with get_cursor(commit=True) as cur:
        await cur.execute("SELECT status, reported_winner_team1, reported_winner_team2, team1_id, team2_id FROM matches WHERE match_id = %s FOR UPDATE", (match_id,))
        match = await cur.fetchone()
        if not match or match['status'] != MatchStatus.SCHEDULED or (match['reported_winner_team1'] is not None or match['reported_winner_team2'] is not None):
            return
        
        await cur.execute("UPDATE matches SET status = %s WHERE match_id = %s", (MatchStatus.COMPLETED, match_id))
        if match['team1_id']: await cur.execute("UPDATE teams SET matches_played = matches_played + 1, no_show_count = no_show_count + 1 WHERE team_id = %s", (match['team1_id'],))
        if match['team2_id']: await cur.execute("UPDATE teams SET matches_played = matches_played + 1, no_show_count = no_show_count + 1 WHERE team_id = %s", (match['team2_id'],))
        
        await log_event(f"Match `{match_id}` marked as double forfeit. Neither team reported.", "warning")
        _cancel_all_tasks_for_match(match_id)
        msg = f"⌛ Match ID `{match_id}` has been automatically closed as a **double forfeit** because neither team submitted a report. Both teams have received a no-show penalty."
        log_pfx = f"[Match {match_id} Double Forfeit]"
        await send_dm(team1_captain_id, msg, log_pfx)
        await send_dm(team2_captain_id, msg, log_pfx)

    double_forfeit_check_tasks.pop(match_id, None)

# --- Views ---
class ScrimRequestView(View):
    def __init__(self, request_id: int, *, timeout: float = SCRIM_REQUEST_TIMEOUT_SECONDS):
        super().__init__(timeout=timeout)
        self.request_id = request_id
        self.message = None

    async def on_timeout(self):
        async with get_cursor(commit=True) as cur:
            await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s AND status = %s", (ScrimStatus.EXPIRED, self.request_id, ScrimStatus.OPEN))
        if self.message:
            try:
                await self.message.edit(content="*This scrim request has expired.*", view=None)
                await log_event(f"Scrim request `{self.request_id}` expired.")
            except discord.NotFound: pass

    @discord.ui.button(label="Accept Scrim", style=discord.ButtonStyle.green, emoji="⚔️")
    async def accept_button(self, interaction: discord.Interaction, button: Button):
        await interaction.response.defer(ephemeral=True)
        async with get_cursor(commit=True) as cur:
            await cur.execute("SELECT team_id FROM teams WHERE captain_id = %s", (interaction.user.id,))
            accepting_team_row = await cur.fetchone()
            if not accepting_team_row:
                return await interaction.followup.send("❌ You need to be a captain to accept a scrim.", ephemeral=True)
            accepting_team_id = accepting_team_row['team_id']
            
            await cur.execute("SELECT COUNT(*) FROM matches WHERE (team1_id = %s OR team2_id = %s) AND status = %s", (accepting_team_id, accepting_team_id, MatchStatus.SCHEDULED))
            if (await cur.fetchone())['count'] >= MAX_ACTIVE_MATCHES:
                return await interaction.followup.send(f"❌ You cannot accept a scrim while you have {MAX_ACTIVE_MATCHES} or more active matches.", ephemeral=True)
            
            await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s AND status = %s RETURNING team_id", (ScrimStatus.MATCHED, self.request_id, ScrimStatus.OPEN))
            request_row = await cur.fetchone()
            if not request_row:
                return await interaction.followup.send("❌ This scrim was just matched by someone else or has expired!", ephemeral=True)
            requester_team_id = request_row['team_id']
            
            if requester_team_id == accepting_team_id:
                await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s", (ScrimStatus.OPEN, self.request_id))
                return await interaction.followup.send("❌ You cannot accept your own scrim request!", ephemeral=True)
            
            await cur.execute("SELECT COUNT(*) FROM matches WHERE ((team1_id = %s AND team2_id = %s) OR (team1_id = %s AND team2_id = %s)) AND created_at > NOW() - INTERVAL '%s seconds'", (requester_team_id, accepting_team_id, accepting_team_id, requester_team_id, MATCH_COOLDOWN_SECONDS))
            if (await cur.fetchone())['count'] > 0:
                return await interaction.followup.send("❌ You have played against this team too recently. Please wait before matching again.", ephemeral=True)
            
            await cur.execute("SELECT team_name, captain_id, game FROM teams WHERE team_id = %s", (requester_team_id,))
            requester_team = await cur.fetchone()
            await cur.execute("SELECT team_name, captain_id FROM teams WHERE team_id = %s", (accepting_team_id,))
            accepting_team = await cur.fetchone()
            
            await cur.execute("""INSERT INTO matches (team1_id, team2_id, game) VALUES (%s, %s, %s) RETURNING match_id""", (requester_team_id, accepting_team_id, requester_team['game']))
            match_id = (await cur.fetchone())['match_id']
        
        requester_name, requester_captain_id, game = requester_team['team_name'], requester_team['captain_id'], requester_team['game']
        accepting_name, accepting_captain_id = accepting_team['team_name'], accepting_team['captain_id']
        
        await log_event(f"Match `{match_id}` created: **{requester_name}** vs **{accepting_name}**.")
        rem_task = asyncio.create_task(_schedule_reminder(REMINDER_DELAY_SECONDS, match_id, requester_captain_id, accepting_captain_id))
        match_reminder_tasks[match_id] = rem_task
        df_task = asyncio.create_task(_schedule_double_forfeit_check(DOUBLE_FORFEIT_DELAY_SECONDS, match_id, requester_captain_id, accepting_captain_id))
        double_forfeit_check_tasks[match_id] = df_task
        
        self.clear_items()
        await self.message.edit(content=f"**MATCHED!**\n`{requester_name}` vs `{accepting_name}`\n*Match ID: `{match_id}`*", view=self)
        await interaction.channel.send(f"⚔️ **Match Made!** `{requester_name}` vs `{accepting_name}`. Match ID: `{match_id}`\nCaptains will receive a DM.")
        
        log_pfx = f"[Match {match_id} Creation]"
        for user_id, opponent_name in [(requester_captain_id, accepting_name), (accepting_captain_id, requester_name)]:
            if not await send_dm(user_id, f"✅ Your scrim vs **{opponent_name}** is set!\n**Match ID:** `{match_id}`\nUse `/report` after the match.", log_pfx):
                try:
                    await interaction.channel.send(f"🔔 <@{user_id}>, I couldn't DM you! Your match vs **{opponent_name}** (ID: `{match_id}`) is ready. Please check your privacy settings.")
                except Exception: pass

# --- Autocomplete ---
async def game_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    return [app_commands.Choice(name=game.title(), value=game) for game in GAMES if current.lower() in game.lower()]

async def get_team_game(user_id: int):
    async with get_cursor() as cur:
        await cur.execute("SELECT game FROM teams WHERE captain_id = %s", (user_id,))
        result = await cur.fetchone()
        return result['game'] if result else None

async def rank_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    game = interaction.namespace.game
    if not game:
        game = await get_team_game(interaction.user.id)
    return [app_commands.Choice(name=rank, value=rank) for rank in GAMES.get(game, []) if current.lower() in rank.lower()]

async def region_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    return [app_commands.Choice(name=region, value=region) for region in REGIONS if current.lower() in region.lower()]

async def active_matches_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    async with get_cursor() as cur:
        await cur.execute("""SELECT m.match_id, t1.team_name, t2.team_name AS team_name_1 FROM matches m
                             LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                             LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                             WHERE (t1.captain_id = %s OR t2.captain_id = %s) AND m.status = %s""",
                            (interaction.user.id, interaction.user.id, MatchStatus.SCHEDULED))
        matches = await cur.fetchall()
    return [app_commands.Choice(name=f"ID: {row['match_id']} | {row['team_name'] or 'Deleted'} vs {row['team_name_1'] or 'Deleted'}", value=str(row['match_id'])) for row in matches if current.lower() in f"ID: {row['match_id']}".lower()][:25]

async def recent_matches_autocomplete(interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
    async with get_cursor() as cur:
        await cur.execute("""SELECT m.match_id, t1.team_name, t2.team_name AS team_name_1 FROM matches m
                             LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                             LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                             WHERE (t1.captain_id = %s OR t2.captain_id = %s)
                             ORDER BY m.created_at DESC LIMIT 25""",
                            (interaction.user.id, interaction.user.id))
        matches = await cur.fetchall()
    return [app_commands.Choice(name=f"ID: {row['match_id']} | {row['team_name'] or 'Deleted'} vs {row['team_name_1'] or 'Deleted'}", value=str(row['match_id'])) for row in matches if current.lower() in f"ID: {row['match_id']}".lower()]

# --- Error Handler ---
@tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CommandOnCooldown):
        return await interaction.response.send_message(f"⏰ Please wait {error.retry_after:.0f} seconds before using this command again.", ephemeral=True)
    elif isinstance(error, app_commands.MissingPermissions):
        return await interaction.response.send_message("❌ You don't have permission to use this command.", ephemeral=True)
    
    command_name = "Unknown"
    if interaction.command:
        command_name = interaction.command.name
    logger.error(f"Error in command '{command_name}' by {interaction.user}", exc_info=error)
    
    if not interaction.response.is_done():
        await interaction.response.send_message("❌ An unexpected error occurred.", ephemeral=True)
    else:
        await interaction.followup.send("❌ An unexpected error occurred.", ephemeral=True)

# --- Commands ---
@tree.command(name="help", description="Show all available commands")
async def help(interaction: discord.Interaction):
    embed = discord.Embed(title="📖 ScrimHub Commands", color=discord.Color.blue())
    embed.add_field(name="🎮 Team", value="`/team create`\n`/team profile`\n`/team edit`\n`/team rename`\n`/team transfer`\n`/team delete`", inline=True)
    embed.add_field(name="⚔️ Scrim", value="`/scrim post`\n`/scrim cancel`\n`/report`\n`/leaderboard`", inline=True)
    embed.add_field(name="🚩 Report", value="`/report_behaviour`", inline=True)
    if interaction.user.guild_permissions.administrator:
        embed.add_field(name="🛠️ Admin", value="`/admin disputes`\n`/admin resolve`\n`/admin review_reports`\n`/admin confirm_report`", inline=False)
    await interaction.response.send_message(embed=embed, ephemeral=True)

@tree.command(name="leaderboard", description="View the top 10 teams on the network")
async def leaderboard(interaction: discord.Interaction):
    await interaction.response.defer()
    async with get_cursor() as cur:
        await cur.execute("""SELECT team_name, wins, losses, elo, matches_played
                             FROM teams WHERE matches_played >= 5
                             ORDER BY elo DESC, wins DESC, matches_played DESC, team_name ASC LIMIT 10""")
        top_teams = await cur.fetchall()
    embed = discord.Embed(title="🏆 Network Leaderboard", description="Top 10 teams by Elo (min 5 games).", color=discord.Color.gold())
    if not top_teams:
        embed.description = "No teams qualify for the leaderboard yet."
    else:
        medals = ["🥇", "🥈", "🥉"]
        embed.description = "\n".join([f"{medals[i] if i < 3 else f'**#{i+1}**'} **{row['team_name']}** | {int(row['elo'])} Elo ({row['wins']}W-{row['losses']}L)" for i, row in enumerate(top_teams)])
    await interaction.followup.send(embed=embed)

class Team(app_commands.Group):
    """Manage your team"""
    @app_commands.command(name="create", description="Register your team for scrims")
    @app_commands.autocomplete(game=game_autocomplete, rank=rank_autocomplete, region=region_autocomplete)
    async def create(self, interaction: discord.Interaction, team_name: str, game: str, rank: str, region: str):
        if not (1 <= len(team_name) <= 50):
            return await interaction.response.send_message("❌ Team name must be 1-50 characters.", ephemeral=True)
        if game not in GAMES or rank not in GAMES.get(game, []) or region not in REGIONS:
            return await interaction.response.send_message("❌ Invalid game, rank, or region.", ephemeral=True)
        try:
            async with get_cursor(commit=True) as cur:
                await cur.execute("""INSERT INTO teams (server_id, team_name, captain_id, game, rank, region) VALUES (%s, %s, %s, %s, %s, %s)""",
                                (interaction.guild.id, team_name, interaction.user.id, game, rank, region))
            await log_event(f"Team Created: **{team_name}** by `{interaction.user}`.")
            embed = discord.Embed(title="✅ Team Registered!", description=f"**{team_name}** is now ready to find scrims.", color=discord.Color.green())
            await interaction.response.send_message(embed=embed)
        except psycopg.errors.UniqueViolation as e:
            if 'teams_captain_id_key' in str(e):
                await interaction.response.send_message(f"❌ You already own a team.", ephemeral=True)
            elif 'teams_server_id_team_name_key' in str(e):
                await interaction.response.send_message(f"❌ A team named **{team_name}** already exists in this server.", ephemeral=True)
        except Exception as e:
            await log_event(f"Unhandled error in /team create: {e}", "error")
            await interaction.response.send_message(f"❌ An unexpected error occurred.", ephemeral=True)

    @app_commands.command(name="profile", description="View your team's profile and stats")
    async def profile(self, interaction: discord.Interaction):
        async with get_cursor() as cur:
            await cur.execute("SELECT * FROM teams WHERE captain_id = %s", (interaction.user.id,))
            team = await cur.fetchone()
        
        if not team:
            return await interaction.response.send_message("❌ You are not the captain of any team.", ephemeral=True)
        
        total_matches = team['wins'] + team['losses']
        winrate = (team['wins'] / total_matches * 100) if total_matches > 0 else 0

        embed = discord.Embed(title=f"📊 Team Profile: {team['team_name']}", color=discord.Color.blurple())
        embed.add_field(name="Game", value=team['game'].title()).add_field(name="Rank", value=team['rank']).add_field(name="Region", value=team['region'])
        embed.add_field(name="Elo", value=f"**{int(team['elo'])}**")
        embed.add_field(name="Record", value=f"{team['wins']}W - {team['losses']}L").add_field(name="Win Rate", value=f"{winrate:.1f}%")
        embed.add_field(name="Reputation", value=f"No Shows: {team['no_show_count']}\nMisconducts: {team['misconduct_count']}", inline=False)
        await interaction.response.send_message(embed=embed)

    @app_commands.command(name="edit", description="Edit your team's rank or region")
    @app_commands.autocomplete(rank=rank_autocomplete, region=region_autocomplete)
    async def edit(self, interaction: discord.Interaction, rank: str = None, region: str = None):
        if not rank and not region:
            return await interaction.response.send_message("❌ You must specify at least one field to edit.", ephemeral=True)

        async with get_cursor(commit=True) as cur:
            if rank:
                await cur.execute("SELECT game FROM teams WHERE captain_id = %s", (interaction.user.id,))
                team = await cur.fetchone()
                if not team: return await interaction.response.send_message("❌ You don't have a team.", ephemeral=True)
                if rank not in GAMES.get(team['game'], []): return await interaction.response.send_message("❌ Invalid rank for your team's game.", ephemeral=True)
            if region and region not in REGIONS:
                return await interaction.response.send_message("❌ Invalid region.", ephemeral=True)
            
            if rank and region:
                await cur.execute("UPDATE teams SET rank = %s, region = %s WHERE captain_id = %s RETURNING team_name", (rank, region, interaction.user.id))
            elif rank:
                await cur.execute("UPDATE teams SET rank = %s WHERE captain_id = %s RETURNING team_name", (rank, interaction.user.id))
            else:
                await cur.execute("UPDATE teams SET region = %s WHERE captain_id = %s RETURNING team_name", (region, interaction.user.id))
            
            result = await cur.fetchone()
            if not result: return await interaction.response.send_message("❌ You don't have a team.", ephemeral=True)
        
        changes = []
        if rank: changes.append(f"Rank → {rank}")
        if region: changes.append(f"Region → {region}")
        await log_event(f"Team **{result['team_name']}** edited by `{interaction.user}`: {', '.join(changes)}")
        await interaction.response.send_message(f"✅ Team **{result['team_name']}** updated!\n" + "\n".join(changes))

    @app_commands.command(name="rename", description="Rename your team")
    async def rename(self, interaction: discord.Interaction, new_name: str):
        if not (1 <= len(new_name) <= 50):
            return await interaction.response.send_message("❌ New team name must be 1-50 characters.", ephemeral=True)
        
        await interaction.response.defer()
        try:
            async with get_cursor(commit=True) as cur:
                await cur.execute("UPDATE teams SET team_name = %s WHERE captain_id = %s AND server_id = %s RETURNING team_name",
                                  (new_name, interaction.user.id, interaction.guild.id))
                result = await cur.fetchone()
                if not result: return await interaction.followup.send("❌ You do not have a team in this server to rename.", ephemeral=True)
            
            await log_event(f"Team renamed to **{new_name}** by `{interaction.user}`.")
            await interaction.followup.send(f"✅ Your team has been renamed to **{new_name}**.")
        except psycopg.errors.UniqueViolation:
            await interaction.followup.send(f"❌ A team with the name **{new_name}** already exists in this server.", ephemeral=True)

    @app_commands.command(name="transfer", description="Transfer ownership of your team to another member")
    async def transfer(self, interaction: discord.Interaction, new_captain: discord.Member):
        if new_captain.bot or new_captain.id == interaction.user.id:
            return await interaction.response.send_message("❌ Invalid member.", ephemeral=True)
        
        await interaction.response.defer()
        async with get_cursor(commit=True) as cur:
            await cur.execute("SELECT team_id FROM teams WHERE captain_id = %s", (interaction.user.id,))
            if not await cur.fetchone(): return await interaction.followup.send("❌ You are not a captain of a team.", ephemeral=True)
            
            await cur.execute("SELECT team_id FROM teams WHERE captain_id = %s", (new_captain.id,))
            if await cur.fetchone(): return await interaction.followup.send(f"❌ {new_captain.mention} is already a captain of another team.", ephemeral=True)

            await cur.execute("UPDATE teams SET captain_id = %s WHERE captain_id = %s RETURNING team_name",
                              (new_captain.id, interaction.user.id))
            result = await cur.fetchone()
        
        await log_event(f"Team **{result['team_name']}** ownership transferred to `{new_captain}`.")
        await interaction.followup.send(f"✅ You have transferred ownership of **{result['team_name']}** to {new_captain.mention}.")

    @app_commands.command(name="delete", description="Delete your team (WARNING: Cannot be undone!)")
    async def delete(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        async with get_cursor(commit=True) as cur:
            await cur.execute("""SELECT COUNT(*) FROM matches m LEFT JOIN teams t ON (m.team1_id = t.team_id OR m.team2_id = t.team_id)
                                 WHERE t.captain_id = %s AND m.status IN (%s, %s)""", (interaction.user.id, MatchStatus.SCHEDULED, MatchStatus.DISPUTED))
            if (await cur.fetchone())['count'] > 0:
                return await interaction.followup.send("❌ Cannot delete team. You have active/disputed matches.")
            
            await cur.execute("DELETE FROM teams WHERE captain_id = %s RETURNING team_name", (interaction.user.id,))
            result = await cur.fetchone()
            if not result:
                return await interaction.followup.send("❌ You don't have a team to delete.")
        
        await log_event(f"Team **{result['team_name']}** deleted by `{interaction.user}`.", "warning")
        await interaction.followup.send(f"✅ Your team **{result['team_name']}** has been deleted.")

class Scrim(app_commands.Group):
    """Find or manage a scrim"""
    @app_commands.command(name="post", description="Post a request to find a practice match")
    @app_commands.checks.cooldown(1, 60.0, key=lambda i: i.user.id)
    async def post(self, interaction: discord.Interaction):
        if not HUB_SERVER_ID or not HUB_CHANNEL_ID:
            return await interaction.response.send_message("⚠️ Hub Server not configured.", ephemeral=True)
        
        request_id = None
        try:
            async with get_cursor(commit=True) as cur:
                await cur.execute("SELECT team_id, team_name, game, rank, region FROM teams WHERE captain_id = %s", (interaction.user.id,))
                team = await cur.fetchone()
                if not team: return await interaction.response.send_message("❌ You need to be a team captain.", ephemeral=True)
                
                await cur.execute("SELECT request_id FROM scrim_requests sr JOIN teams t ON sr.team_id = t.team_id WHERE t.captain_id = %s AND sr.status = %s", (interaction.user.id, ScrimStatus.OPEN))
                if await cur.fetchone(): return await interaction.response.send_message("❌ You already have an open scrim request. Use `/scrim cancel` first.", ephemeral=True)
                
                await cur.execute("INSERT INTO scrim_requests (team_id) VALUES (%s) RETURNING request_id", (team['team_id'],))
                request_id = (await cur.fetchone())['request_id']
            
            await log_event(f"New scrim request `{request_id}` from **{team['team_name']}**.")
            embed = discord.Embed(title=f"⚔️ Scrim Request [{team['region']}]", description=f"**{team['team_name']}** is looking for a match!", color=discord.Color.blue(), timestamp=datetime.now())
            embed.add_field(name="Game", value=team['game'].title()).add_field(name="Rank", value=team['rank'])
            embed.set_footer(text=f"Request ID: {request_id}")
            
            hub_channel = client.get_channel(int(HUB_CHANNEL_ID))
            if not hub_channel: raise Exception("Hub channel not found.")
            
            view = ScrimRequestView(request_id)
            hub_message = await hub_channel.send(embed=embed, view=view)
            view.message = hub_message
            
            async with get_cursor(commit=True) as cur:
                await cur.execute("UPDATE scrim_requests SET hub_message_id = %s WHERE request_id = %s", (hub_message.id, request_id))
            
            await interaction.response.send_message(f"✅ Your scrim request (`{request_id}`) is live!", ephemeral=True)
        except Exception as e:
            await log_event(f"Failed to post scrim request `{request_id or 'N/A'}` to hub. Rolling back. Error: {e}", "error")
            if request_id:
                async with get_cursor(commit=True) as cur:
                    await cur.execute("DELETE FROM scrim_requests WHERE request_id = %s", (request_id,))
            await interaction.response.send_message(f"❌ Could not post to hub server. The request has been cancelled.", ephemeral=True)

    @app_commands.command(name="cancel", description="Cancel your open scrim request")
    async def cancel(self, interaction: discord.Interaction):
        await interaction.response.defer(ephemeral=True)
        async with get_cursor(commit=True) as cur:
            await cur.execute("""SELECT sr.request_id, sr.hub_message_id FROM scrim_requests sr JOIN teams t ON sr.team_id = t.team_id
                                 WHERE t.captain_id = %s AND sr.status = %s
                                 ORDER BY sr.created_at DESC LIMIT 1""", (interaction.user.id, ScrimStatus.OPEN))
            result = await cur.fetchone()
            if not result: return await interaction.followup.send("❌ You don't have any open scrim requests.")
            request_id, hub_msg_id = result['request_id'], result['hub_message_id']
            await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s", (ScrimStatus.CANCELLED, request_id))
        
        if hub_msg_id and HUB_CHANNEL_ID:
            try:
                hub_channel = client.get_channel(int(HUB_CHANNEL_ID))
                message = await hub_channel.fetch_message(hub_msg_id)
                await message.delete()
            except discord.NotFound: pass
            except Exception as e: logger.warning(f"Failed to delete hub message {hub_msg_id}: {e}")
        
        await log_event(f"Scrim request `{request_id}` cancelled by captain.")
        await interaction.followup.send(f"✅ Your scrim request (ID: `{request_id}`) has been cancelled.")

# --- REPORT COMMANDS ---
@tree.command(name="report", description="Report the result of a completed scrim")
@app_commands.autocomplete(match_id=active_matches_autocomplete)
@app_commands.describe(match_id="Select your active match.", result="Did your team win or lose?")
@app_commands.choices(result=[app_commands.Choice(name="🏆 We Won", value="win"), app_commands.Choice(name="🏳️ We Lost", value="loss")])
async def report(interaction: discord.Interaction, match_id: str, result: app_commands.Choice[str]):
    await interaction.response.defer(ephemeral=True)
    try: match_id_int = int(match_id)
    except ValueError: return await interaction.followup.send("❌ Invalid Match ID.")

    async with get_cursor(commit=True) as cur:
        await cur.execute("""SELECT m.team1_id, m.team2_id, t1.captain_id as c1_id, t2.captain_id as c2_id,
                                m.reported_winner_team1, m.reported_winner_team2,
                                t1.team_name, t2.team_name as team_name_1, m.status
                         FROM matches m 
                         LEFT JOIN teams t1 ON m.team1_id = t1.team_id 
                         LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                         WHERE m.match_id = %s FOR UPDATE""", (match_id_int,))
        match_data = await cur.fetchone()
        
        if not match_data: return await interaction.followup.send("❌ Match not found.")
        if match_data['status'] != MatchStatus.SCHEDULED: return await interaction.followup.send("❌ This match has already been completed or disputed.")

        is_team1 = (interaction.user.id == match_data['c1_id'])
        if not is_team1 and interaction.user.id != match_data['c2_id']: return await interaction.followup.send("❌ You are not a captain in this match.")
        if (is_team1 and match_data['reported_winner_team1'] is not None) or (not is_team1 and match_data['reported_winner_team2'] is not None): return await interaction.followup.send("❌ You already submitted a report for this match.")

        reporting_team_id = match_data['team1_id'] if is_team1 else match_data['team2_id']
        winner_id = reporting_team_id if result.value == 'win' else (match_data['team2_id'] if is_team1 else match_data['team1_id'])
        opponent_captain_id = match_data['c2_id'] if is_team1 else match_data['c1_id']
        
        if is_team1:
            await cur.execute("UPDATE matches SET reported_winner_team1 = %s, first_report_at = COALESCE(first_report_at, NOW()) WHERE match_id = %s", (winner_id, match_id_int))
            opponent_report = match_data['reported_winner_team2']
        else:
            await cur.execute("UPDATE matches SET reported_winner_team2 = %s, first_report_at = COALESCE(first_report_at, NOW()) WHERE match_id = %s", (winner_id, match_id_int))
            opponent_report = match_data['reported_winner_team1']

        status, data = None, None
        if opponent_report is None:
            status = "WAITING_FORFEIT"
            data = opponent_captain_id
        elif opponent_report == winner_id:
            loser_id = match_data['team2_id'] if winner_id == match_data['team1_id'] else match_data['team1_id']
            await _apply_elo_and_stats(cur, winner_id, loser_id)
            await cur.execute("UPDATE matches SET status = %s, final_winner_team_id = %s WHERE match_id = %s", (MatchStatus.COMPLETED, winner_id, match_id_int))
            status = "CONFIRMED"
            data = match_data['team_name'] if winner_id == match_data['team1_id'] else match_data['team_name_1']
        else:
            await cur.execute("UPDATE matches SET status = %s WHERE match_id = %s", (MatchStatus.DISPUTED, match_id_int))
            status = "DISPUTED"

    _cancel_all_tasks_for_match(match_id_int)
        
    if status == "WAITING_FORFEIT":
        task = asyncio.create_task(_check_forfeit(match_id_int, interaction.user.id, data))
        forfeit_check_tasks[match_id_int] = task
        await interaction.followup.send(f"✅ Report received. Your opponent has {int(FORFEIT_DELAY_SECONDS/60)} minutes to submit their report or they will forfeit.")
        await send_dm(data, f"⚠️ **Action Required!** Your opponent has reported a result for Match ID `{match_id_int}`. You have {int(FORFEIT_DELAY_SECONDS/60)} minutes to submit your `/report`, or you will forfeit the match.", f"[Match {match_id_int} Forfeit Warning]")
    elif status == "CONFIRMED":
        await interaction.followup.send(f"✅ Both teams reported the same result. Winner: **{data or 'a deleted team'}**.")
        await log_event(f"Match `{match_id_int}` confirmed. Winner: **{data or 'a deleted team'}**.")
    elif status == "DISPUTED":
        await interaction.followup.send("⚠️ Your report conflicts with your opponent's. Match is now disputed.")
        await log_event(f"Match `{match_id_int}` disputed.", "warning")

@tree.command(name="report_behaviour", description="Report an opponent for toxic behaviour or other misconduct.")
@app_commands.autocomplete(match_id=active_matches_autocomplete)
@app_commands.choices(reason=[
    app_commands.Choice(name="Toxic / Salty Behaviour", value="toxic"),
    app_commands.Choice(name="Suspected Cheating", value="cheating"),
    app_commands.Choice(name="Other (Please explain in support ticket)", value="other")
])
async def report_behaviour(interaction: discord.Interaction, match_id: str, reason: app_commands.Choice[str]):
    await interaction.response.defer(ephemeral=True)
    try: match_id_int = int(match_id)
    except ValueError: return await interaction.followup.send("❌ Invalid Match ID.")

    try:
        async with get_cursor(commit=True) as cur:
            await cur.execute("SELECT team_id FROM teams WHERE captain_id = %s", (interaction.user.id,))
            my_team_row = await cur.fetchone()
            if not my_team_row: return await interaction.followup.send("❌ You do not have a team.", ephemeral=True)
            my_team_id = my_team_row['team_id']

            await cur.execute("SELECT team1_id, team2_id FROM matches WHERE match_id = %s", (match_id_int,))
            match = await cur.fetchone()
            if not match: return await interaction.followup.send("❌ Match not found.", ephemeral=True)
            
            if my_team_id == match['team1_id']: accused_team_id = match['team2_id']
            elif my_team_id == match['team2_id']: accused_team_id = match['team1_id']
            else: return await interaction.followup.send("❌ You were not a participant in this match.", ephemeral=True)

            if not accused_team_id: return await interaction.followup.send("❌ Your opponent in this match has been deleted.", ephemeral=True)

            await cur.execute("""INSERT INTO misconduct_reports (match_id, reporting_team_id, accused_team_id, reason)
                               VALUES (%s, %s, %s, %s) RETURNING report_id""",
                              (match_id_int, my_team_id, accused_team_id, reason.value))
            report_id = (await cur.fetchone())['report_id']
        
        await log_event(f"New Behaviour Report (`{report_id}`) filed by <@{interaction.user.id}> for Match `{match_id}`. Reason: {reason.name}", "warning")
        await interaction.followup.send("✅ Your report has been submitted and is pending admin review.")
    except psycopg.errors.UniqueViolation:
        await interaction.followup.send("❌ You have already submitted a behaviour report for this match.", ephemeral=True)

@app_commands.default_permissions(administrator=True)
class Admin(app_commands.Group):
    """Admin-only commands"""
    async def _get_disputed_matches(self):
        async with get_cursor() as cur:
            await cur.execute("""SELECT m.match_id, t1.team_name, t2.team_name AS team_name_1 FROM matches m
                                 LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                                 LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                                 WHERE m.status = %s""", (MatchStatus.DISPUTED,))
            return await cur.fetchall()

    async def disputed_matches_autocomplete(self, interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
        matches = await self._get_disputed_matches()
        choices = [app_commands.Choice(name=f"ID: {row['match_id']} | {row['team_name'] or 'Deleted'} vs {row['team_name_1'] or 'Deleted'}", value=str(row['match_id'])) for row in matches if current.lower() in str(row['match_id'])]
        return choices[:25]
    
    async def disputed_winner_autocomplete(self, interaction: discord.Interaction, current: str) -> List[app_commands.Choice[str]]:
        match_id = interaction.namespace.match_id
        if not match_id: return []
        try: match_id_int = int(match_id)
        except ValueError: return []

        async with get_cursor() as cur:
            await cur.execute("""SELECT t1.team_name, t2.team_name AS team_name_1 
                                 FROM matches m
                                 LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                                 LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                                 WHERE m.match_id = %s""", (match_id_int,))
            match = await cur.fetchone()

        if not match: return []
        choices = []
        if match['team_name']: choices.append(app_commands.Choice(name=match['team_name'], value=match['team_name']))
        if match['team_name_1']: choices.append(app_commands.Choice(name=match['team_name_1'], value=match['team_name_1']))
        return choices

    @app_commands.command(name="disputes", description="View all disputed matches")
    async def disputes(self, interaction: discord.Interaction):
        disputes = await self._get_disputed_matches()
        if not disputes: return await interaction.response.send_message("✅ No disputed matches.", ephemeral=True)
        embed = discord.Embed(title="⚠️ Disputed Matches", color=discord.Color.orange())
        embed.description = "\n".join([f"- `ID: {row['match_id']}` | **{row['team_name'] or 'Deleted'}** vs **{row['team_name_1'] or 'Deleted'}**" for row in disputes])
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="resolve", description="Manually resolve a disputed match")
    @app_commands.autocomplete(match_id=disputed_matches_autocomplete, winner_name=disputed_winner_autocomplete)
    async def resolve(self, interaction: discord.Interaction, match_id: str, winner_name: str):
        await interaction.response.defer(ephemeral=True)
        try: match_id_int = int(match_id)
        except ValueError: return await interaction.followup.send("❌ Invalid Match ID.")
        
        async with get_cursor(commit=True) as cur:
            await cur.execute("""SELECT t1.team_id, t2.team_id, t1.team_name, t2.team_name AS team_name_1 FROM matches m
                                 LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                                 LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                                 WHERE m.match_id = %s AND m.status = %s""", (match_id_int, MatchStatus.DISPUTED))
            match = await cur.fetchone()
            if not match: return await interaction.followup.send("❌ Match not in dispute.")
            
            if winner_name.lower() == (match['team_name'] or '').lower(): w_id, l_id = match['team1_id'], match['team2_id']
            elif winner_name.lower() == (match['team_name_1'] or '').lower(): w_id, l_id = match['team2_id'], match['team1_id']
            else: return await interaction.followup.send(f"❌ Invalid winner. Must be '{match['team_name'] or 'Deleted'}' or '{match['team_name_1'] or 'Deleted'}'.")

            await _apply_elo_and_stats(cur, w_id, l_id)
            await cur.execute("UPDATE matches SET status = %s, final_winner_team_id = %s WHERE match_id = %s", (MatchStatus.COMPLETED, w_id, match_id_int))

        _cancel_all_tasks_for_match(match_id_int)
        await log_event(f"Admin `{interaction.user}` resolved Match `{match_id_int}`. Winner: **{winner_name}**.", "info")
        await interaction.followup.send(f"✅ Match `{match_id_int}` resolved. Winner: **{winner_name}**.", ephemeral=True)

    @app_commands.command(name="review_reports", description="View all pending misconduct reports")
    async def review_reports(self, interaction: discord.Interaction):
        async with get_cursor() as cur:
            await cur.execute("""SELECT r.report_id, r.match_id, t_rep.team_name, t_acc.team_name AS team_name_1, r.reason
                                   FROM misconduct_reports r
                                   LEFT JOIN teams t_rep ON r.reporting_team_id = t_rep.team_id
                                   LEFT JOIN teams t_acc ON r.accused_team_id = t_acc.team_id
                                   WHERE r.status = %s""", (ReportStatus.PENDING,))
            reports = await cur.fetchall()
        if not reports:
            return await interaction.response.send_message("✅ No pending misconduct reports.", ephemeral=True)
        
        embed = discord.Embed(title="⚠️ Pending Misconduct Reports", color=discord.Color.orange())
        desc = [f"**ID: `{row['report_id']}`** | Match: `{row['match_id']}` | **{row['team_name'] or 'Del'}.** vs **{row['team_name_1'] or 'Del'}.** | Reason: {row['reason']}" for row in reports]
        embed.description = "\n".join(desc)
        await interaction.response.send_message(embed=embed, ephemeral=True)

    @app_commands.command(name="confirm_report", description="Confirm a misconduct report and penalize the team.")
    @app_commands.describe(report_id="The ID of the report to confirm")
    async def confirm_report(self, interaction: discord.Interaction, report_id: int):
        async with get_cursor(commit=True) as cur:
            await cur.execute("SELECT accused_team_id FROM misconduct_reports WHERE report_id = %s AND status = %s", (report_id, ReportStatus.PENDING))
            report = await cur.fetchone()
            if not report: return await interaction.response.send_message(f"❌ Report `{report_id}` not found or already resolved.", ephemeral=True)
            
            if report['accused_team_id']:
                await cur.execute("UPDATE teams SET misconduct_count = misconduct_count + 1 WHERE team_id = %s", (report['accused_team_id'],))
            await cur.execute("UPDATE misconduct_reports SET status = %s WHERE report_id = %s", (ReportStatus.CONFIRMED, report_id))
        
        await log_event(f"Admin `{interaction.user}` confirmed misconduct report `{report_id}`.", "info")
        await interaction.response.send_message(f"✅ Report `{report_id}` confirmed. The team has been penalized.", ephemeral=True)

# --- Register Command Groups ---
tree.add_command(Team())
tree.add_command(Scrim())
tree.add_command(Admin())

async def _schedule_reminder(delay_seconds: float, match_id: int, cap1: int, cap2: int):
    await asyncio.sleep(delay_seconds)
    await remind_after_delay(match_id, cap1, cap2)

async def _schedule_forfeit_check(delay_seconds: float, match_id: int, reporter_id: int, opponent_id: int):
    await asyncio.sleep(delay_seconds)
    await _check_forfeit(match_id, reporter_id, opponent_id)
    
async def _schedule_double_forfeit_check(delay_seconds: float, match_id: int, cap1: int, cap2: int):
    await asyncio.sleep(delay_seconds)
    await _check_double_forfeit(match_id, cap1, cap2)

async def shutdown(sig):
    """Gracefully shutdown the bot."""
    logger.info(f"Received exit signal {sig.name}...")
    await cleanup_tasks()
    if pool:
        await pool.close()
        logger.info("Database connections closed.")
    await client.close()

@client.event
async def on_ready():
    global pool
    try:
        pool = AsyncConnectionPool(min_size=1, max_size=20, conninfo=DATABASE_URL, open=False)
        await pool.open()
        logger.info("Async database connection pool established.")
        await setup_database()
        
        if os.name != 'nt':
            loop = asyncio.get_event_loop()
            for sig in (signal.SIGTERM, signal.SIGINT):
                loop.add_signal_handler(sig, lambda s=sig: asyncio.create_task(shutdown(s)))
        
        # --- State Restoration ---
        async with get_cursor() as cur:
            await cur.execute("""SELECT m.match_id, t1.captain_id, t2.captain_id AS captain_id_1,
                                   EXTRACT(EPOCH FROM (NOW() - m.created_at)) as age_seconds
                             FROM matches m
                             LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                             LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                             WHERE m.status = %s AND m.reported_winner_team1 IS NULL AND m.reported_winner_team2 IS NULL""", (MatchStatus.SCHEDULED,))
            scheduled = await cur.fetchall()
        for match in scheduled:
            age = match['age_seconds']
            if age < REMINDER_DELAY_SECONDS:
                task = asyncio.create_task(_schedule_reminder(REMINDER_DELAY_SECONDS - age, match['match_id'], match['captain_id'], match['captain_id_1']))
                match_reminder_tasks[match['match_id']] = task
            if age < DOUBLE_FORFEIT_DELAY_SECONDS:
                task = asyncio.create_task(_schedule_double_forfeit_check(DOUBLE_FORFEIT_DELAY_SECONDS - age, match['match_id'], match['captain_id'], match['captain_id_1']))
                double_forfeit_check_tasks[match['match_id']] = task
            else:
                 asyncio.create_task(_check_double_forfeit(match['match_id'], match['captain_id'], match['captain_id_1']))

        async with get_cursor() as cur:
            await cur.execute("SELECT request_id, hub_message_id, created_at FROM scrim_requests WHERE status = %s AND hub_message_id IS NOT NULL", (ScrimStatus.OPEN,))
            open_requests = await cur.fetchall()
        hub_channel = client.get_channel(int(HUB_CHANNEL_ID)) if HUB_CHANNEL_ID else None
        
        if hub_channel:
            restored_views = 0
            for req in open_requests:
                try:
                    time_elapsed = (datetime.now(timezone.utc) - req['created_at']).total_seconds()
                    remaining_timeout = SCRIM_REQUEST_TIMEOUT_SECONDS - time_elapsed
                    if remaining_timeout <= 0:
                        async with get_cursor(commit=True) as cur:
                            await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s", (ScrimStatus.EXPIRED, req['request_id']))
                        try:
                            message = await hub_channel.fetch_message(req['hub_message_id'])
                            await message.edit(content="*This scrim request has expired.*", view=None)
                        except discord.NotFound: pass
                        continue
                    message = await hub_channel.fetch_message(req['hub_message_id'])
                    view = ScrimRequestView(req['request_id'], timeout=remaining_timeout)
                    view.message = message
                    client.add_view(view, message_id=req['hub_message_id'])
                    restored_views += 1
                except discord.NotFound:
                    async with get_cursor(commit=True) as cur:
                        await cur.execute("UPDATE scrim_requests SET status = %s WHERE request_id = %s", (ScrimStatus.EXPIRED, req['request_id']))
            if restored_views > 0: logger.info(f"Restored {restored_views} active ScrimRequest views.")

        async with get_cursor() as cur:
            await cur.execute(f"""
                SELECT m.match_id, 
                       m.first_report_at,
                       CASE WHEN m.reported_winner_team1 IS NOT NULL THEN t1.captain_id ELSE t2.captain_id END as reporter_id,
                       CASE WHEN m.reported_winner_team1 IS NOT NULL THEN t2.captain_id ELSE t1.captain_id END as opponent_id
                FROM matches m
                LEFT JOIN teams t1 ON m.team1_id = t1.team_id
                LEFT JOIN teams t2 ON m.team2_id = t2.team_id
                WHERE m.status = %s 
                  AND m.first_report_at IS NOT NULL
                    AND (
                        (m.reported_winner_team1 IS NOT NULL AND m.reported_winner_team2 IS NULL)
                    OR
                        (m.reported_winner_team1 IS NULL AND m.reported_winner_team2 IS NOT NULL)
                    )
                """, (MatchStatus.SCHEDULED,))
            pending_forfeits = await cur.fetchall()

        restored_forfeits = 0
        for forfeit in pending_forfeits:
            time_elapsed = (datetime.now(timezone.utc) - forfeit['first_report_at']).total_seconds()
            remaining = FORFEIT_DELAY_SECONDS - time_elapsed
            if remaining > 0:
                task = asyncio.create_task(_schedule_forfeit_check(remaining, forfeit['match_id'], forfeit['reporter_id'], forfeit['opponent_id']))
                forfeit_check_tasks[forfeit['match_id']] = task
                restored_forfeits += 1
            else:
                asyncio.create_task(_check_forfeit(forfeit['match_id'], forfeit['reporter_id'], forfeit['opponent_id']))

        if restored_forfeits > 0: logger.info(f"Restored {restored_forfeits} pending forfeit checks.")
        logger.info("State restored from database.")
        await tree.sync()
        logger.info(f'Bot ready! Logged in as {client.user}')
    except Exception as e:
        logger.critical(f"Could not connect to database or sync commands: {e}", exc_info=True)
        await cleanup_tasks()
        if pool: await pool.close()
        await client.close()

if __name__ == "__main__":
    if not DATABASE_URL or not BOT_TOKEN:
        logger.critical("DATABASE_URL and DISCORD_TOKEN environment variables must be set.")
    else:
        try:
            client.run(BOT_TOKEN)
        except KeyboardInterrupt:
            logger.info("Bot shutdown requested by user.")
        except Exception as e:
            logger.critical(f"Fatal error running bot: {e}", exc_info=True)
