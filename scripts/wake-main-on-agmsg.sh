#!/usr/bin/env bash
# Wake the main Codex session for unread agmsg without consuming the inbox.
set -euo pipefail

if [[ "${HERDR_ENV:-}" != 1 ]]; then
  echo "This watcher must run inside Herdr" >&2
  exit 1
fi

target_session="${1:?usage: wake-main-on-agmsg.sh CODEX_SESSION_ID}"
db="${AGMSG_DB_PATH:-/home/zksecurity/.agents/skills/agmsg/db/messages.db}"
poll_seconds="${AGMSG_WAKE_POLL_SECONDS:-3}"
team="flapjack-port"
recipient="flapjack-main"

command -v herdr >/dev/null
command -v jq >/dev/null
command -v sqlite3 >/dev/null
command -v flock >/dev/null
[[ -f "$db" ]] || { echo "agmsg database missing: $db" >&2; exit 1; }

exec 9>/tmp/flapjack-main-agmsg-sql-waker.lock
flock -n 9 || { echo "main agmsg watcher already running"; exit 0; }

# Keep only a process-local notification watermark. The SQL connection is
# read-only; in particular, this watcher never sets messages.read_at.
last_notified=0
echo "read-only agmsg watcher active for Codex session $target_session"
while true; do
  if ! newest_unread="$(sqlite3 -readonly -batch -noheader "$db" \
    "SELECT COALESCE(MAX(id),0) FROM messages WHERE team='$team' AND to_agent='$recipient' AND read_at IS NULL;")"; then
    sleep "$poll_seconds"
    continue
  fi
  if [[ "$newest_unread" =~ ^[0-9]+$ ]] && (( newest_unread > last_notified )); then
    # Session identity survives a pane move. Never send to an idle shell,
    # a Codex resume picker, a different session, or an approval dialog.
    if agent_json="$(herdr agent list 2>/dev/null)"; then
      agent_row="$(jq -r --arg sid "$target_session" \
        'first(.result.agents[] | select(.agent_session.value == $sid and .agent == "codex" and .interactive_ready == true and (.agent_status == "idle" or .agent_status == "done")) | [.pane_id, .agent_status] | @tsv) // empty' \
        <<<"$agent_json")"
      if [[ -n "$agent_row" ]]; then
        IFS=$'\t' read -r pane _status <<<"$agent_row"
        if foreground="$(herdr pane process-info --pane "$pane" 2>/dev/null)" &&
          jq -e '.result.process_info.foreground_processes | any(.name == "codex")' \
            <<<"$foreground" >/dev/null; then
          # The main agent reads its own inbox. Do not put message contents
          # into a terminal or mark anything read on its behalf.
          if herdr agent prompt "$pane" \
            "Unread agmsg for flapjack-main is waiting. Check the inbox and assess it before acting." \
            >/dev/null 2>&1; then
            last_notified="$newest_unread"
            echo "notified $pane about unread agmsg through id $last_notified"
          fi
        fi
      fi
    fi
  fi
  sleep "$poll_seconds"
done
