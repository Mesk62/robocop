# 🚔 RoboCop

A Discord bot for a *Police Chief* mobile-game community. It welcomes newcomers, sorts people into alliances and ranks, translates messages, runs a few light games, and gives the moderators tools to keep the peace.

**This is the real code the bot runs** — one file, `main.py`. It's published so anyone can check exactly what RoboCop does, and what it doesn't.

## What it does

- **Onboarding** — new members answer a few questions in a private `#gateway` channel (language, in-game name, alliance tag, game server) and get the matching roles and nickname.
- **Alliances and ranks** — alliance roles and channels, R4/R5 rank requests with staff approval.
- **Translation** — react 🌐 to any message for a private translation.
- **Games** — Rock-Paper-Scissors, Cops & Robbers (everyone registered is drafted in rotation — up to 12 per round, recent chatters first, *Not for me* opts out; roles are revealed in private threads, with a DM only as a fallback), Rogue RoboCop, the Daily Case File (a riddle a day), with leaderboards. Rules are auto-posted in `#🎮-how-to-play`.
- **Quiet by design** — it only DMs you about things you asked for or that concern you (your registration, a rank request, a warning, a game you joined). No "welcome back" DMs, no daily digests when nothing happened. The first time a registered member shows up each day it posts one short, silent, no-@mention line in the main chat reminding them the monthly prize is up for grabs (at most one per person per day, never more than one every 10 minutes server-wide).
- **Buttons everywhere** — nobody has to remember a slash command. Members have pinned buttons in `#⚙️-settings` and on the main chat's pinned post (games); each alliance's R5 has buttons pinned in their leadership chat; staff have `#🛠️-precinct-desk` (staff-only) with every moderation control. Every button calls exactly the same code as the matching slash command and asks for confirmation before changing anything.
- **Moderation** — warnings, timeouts, a "prison" channel, bans and kicks, every one logged with an undo button.
- **Fresh start** — staff can wipe everything the bot stores about one person (and lift their ban) with one click, so they can register again from scratch — optionally with a one-use invite sent to them.
- **Self-checks** — on every startup it checks the server's roles and channels and reports problems to the staff-only `#logs` channel.

## It will never ask you for

Passwords, login codes, account emails, or payment — ever. If anything claiming to be RoboCop asks for those, it's a scam: report it to a moderator. Type `/safety` in the server to see this, and the list below, any time.

## What it stores about you — everything

- **What you tell it:** your in-game name (one per game server, if they differ), alliance tag, game server number(s), language, and a rough time zone only if you choose to share it.
- **Your Discord ID and username**, so it recognises you if you leave and come back.
- **Your place in the server:** rank (R4/R5), rank requests, badges like Innovator, and which registration steps you've finished.
- **Game scores:** Rock-Paper-Scissors, Cops & Robbers, Rogue RoboCop, Daily Case File solves and monthly standings, plus guesses used in the current round (`chase_participants.guesses_used`, `rogue_guesses`), and two rotation counters per player (`chase_stats.last_drafted_round`, `chase_stats.no_show_streak`) so quiet members get their turn and no-shows go to the back of the queue.
- **The date you last posted** (`users.last_active_at`, day-level, no message content) — only used to put recent chatters at the front of the Cops & Robbers draft.
- **The date you last made a game move** (`users.last_played_at`) — only people who played in the last 3 days get a heads-up ping when a new Case File or Rogue round opens (at most one every 6 hours). A 🔕 button on that ping opts out for good (stored as a flag in `capability_notifications`). New members get one friendly pointer to the live game ~25 seconds after their welcome, and nothing at all once they've left the server.
- **Moderation history, if any:** warnings, time-outs, kicks or bans and the reason given, and, if you're ever jailed, the roles you had so they can be handed back.

**Where it's kept:** in a database on the owner's own machine — PostgreSQL, or a local SQLite file if no Postgres is configured. Nothing is sent to any outside database service.

**It never collects** a real name, address, phone number, email, location or payment details, and it **doesn't save chat messages.** You can check all of this in `init_db()` in `main.py`, which creates every database table the bot has.

## What leaves the server

- **Google Translate** — only when someone asks for a translation (🌐 or a non-English onboarding), the text being translated is sent to Google's official Cloud Translation API. Nothing is saved.
- **Datamuse** (a free rhyming-dictionary service, api.datamuse.com) — once, when you finish registering, your in-game name is sent to it to find rhyming words for your welcome rhyme in the everyone-chat. Only the name goes out; nothing is saved. The rhymes are the bot's own lines, not song lyrics.
- **An AI service — optional, off unless configured.** If the owner sets `AI_PROVIDER` and `AI_API_KEY` in `.env` (Google Gemini, Groq, OpenRouter, Anthropic, any OpenAI-compatible API, or Ollama running on the owner's own machine), a question typed into `/help question:…` or asked as `@RoboCop …` that the bot's built-in guide can't answer is sent to that service together with the bot's own command list, to write a short answer. Only the question text and the asker's rank tier go out — no names, IDs or other messages. Without it, the bot simply says it doesn't know that one yet. The same service also writes a one-line congratulation when someone receives a custom role (only the role name is sent), and the Daily Case File riddle each morning (the only thing sent is the list of recent riddle answers, so it doesn't repeat itself); without it, riddles come from a built-in bank of 100+.
- Posts in `#🐛-bugs` and `#💡-suggestions` are copied into the staff `#logs` channel so staff see them.
- The bot notices when you come online so it can send the odd stats reminder, but it doesn't record it.

## What it can't see or do

- It can't read your DMs with other people, your password, or anything outside this Discord server.
- Its secrets (the Discord bot token and Google API key) live in a private `.env` file that is **never** published. See `.gitignore`.

## Discord access it needs, and why

- **Server Members, Message Content and Presence intents** — to welcome new members, read answers typed in `#gateway`, and greet top-10 players / staff when they come online.
- **Manage Roles, Nicknames and Channels** — to set up alliances, ranks and nicknames.
- **Create Private Threads, Send Messages in Threads, Manage Threads** — each Cops & Robbers round gets two private threads — one for the cops (clues) and one for the robbers — instead of DMs. Without these it falls back to DMs.
- **Kick, Ban, Moderate Members, Manage Messages** — moderation tools, used by staff commands (and a few automatic safety rules, all logged). Manage Messages also lets staff pin the `/safety` notice.
- **View Audit Log** — so the `#visitors` log can tell "left" apart from "kicked" or "banned".
- **Create Invite** — only for the staff "fresh start + invite back" button, which makes a one-use, 7-day invite for one person.

## One file not published

`main.py` will load an optional `personal_extras.py` if it's sitting next to it. That's a small personal add-on the owner keeps for himself; it's deliberately left out of this repository, and RoboCop runs exactly the same without it.

## Running it yourself

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
# create a .env file containing:  DISCORD_TOKEN=...   (and optionally GOOGLE_API_KEY=...)
# optional: DATABASE_URL=postgresql://user:password@localhost/robocop  to use PostgreSQL instead of SQLite
#           (the first start copies an existing SQLite database across automatically)
python main.py
```

Game messages include a running gag at the server owner's expense — the name is read from the server's owner at runtime, nothing is stored.

Questions? Ask **Mesk** in the server.
