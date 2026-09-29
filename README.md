# 🚔 RoboCop

A Discord bot for a *Police Chief* mobile-game community. It welcomes newcomers, sorts people into alliances and ranks, translates messages, runs a few light games, and gives the moderators tools to keep the peace.

**This is the real code the bot runs** — one file, `main.py`. It's published so anyone can check exactly what RoboCop does, and what it doesn't.

## What it does

- **Onboarding** — new members answer a few questions in a private `#gateway` channel (language, in-game name, alliance tag, game server) and get the matching roles and nickname.
- **Alliances and ranks** — alliance roles and channels, R4/R5 rank requests with staff approval.
- **Translation** — react 🌐 to any message for a private translation.
- **Games** — Rock-Paper-Scissors, Cops & Robbers, Rogue RoboCop, with leaderboards.
- **Moderation** — warnings, timeouts, a "prison" channel, bans and kicks, every one logged with an undo button.
- **Self-checks** — on every startup it checks the server's roles and channels and reports problems to the staff-only `#logs` channel.

## What it stores about you — everything

- **What you tell it:** your in-game name (one per game server, if they differ), alliance tag, game server number(s), language, and a rough time zone only if you choose to share it.
- **Your Discord ID and username**, so it recognises you if you leave and come back.
- **Your place in the server:** rank (R4/R5), rank requests, badges like Innovator, and which registration steps you've finished.
- **Game scores:** Rock-Paper-Scissors, Cops & Robbers, Rogue RoboCop and monthly standings.
- **Moderation history, if any:** warnings, time-outs, kicks or bans and the reason given, and, if you're ever jailed, the roles you had so they can be handed back.

**It never collects** a real name, address, phone number, email, location or payment details, and it **doesn't save chat messages.** You can check all of this in `init_db()` in `main.py`, which creates every database table the bot has.

## What leaves the server

- **Google Translate** — only when someone asks for a translation (🌐 or a non-English onboarding), the text being translated is sent to Google's official Cloud Translation API. Nothing is saved.
- Posts in `#🐛-bugs` and `#💡-suggestions` are copied into the staff `#logs` channel so staff see them.
- The bot notices when you come online so it can send the odd stats reminder, but it doesn't record it.

## What it can't see or do

- It can't read your DMs with other people, your password, or anything outside this Discord server.
- Its secrets (the Discord bot token and Google API key) live in a private `.env` file that is **never** published. See `.gitignore`.

## Discord access it needs, and why

- **Server Members, Message Content and Presence intents** — to welcome new members, read answers typed in `#gateway`, and send online reminders.
- **Manage Roles, Nicknames and Channels** — to set up alliances, ranks and nicknames.
- **Kick, Ban, Moderate Members, Manage Messages** — moderation tools, used by staff commands (and a few automatic safety rules, all logged).
- **View Audit Log** — so the `#visitors` log can tell "left" apart from "kicked" or "banned".

## One file not published

`main.py` will load an optional `personal_extras.py` if it's sitting next to it. That's a small personal add-on the owner keeps for himself; it's deliberately left out of this repository, and RoboCop runs exactly the same without it.

## Running it yourself

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
# create a .env file containing:  DISCORD_TOKEN=...   (and optionally GOOGLE_API_KEY=...)
python main.py
```

Questions? Ask **Mesk** in the server.
