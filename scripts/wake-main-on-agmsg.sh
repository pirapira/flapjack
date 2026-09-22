#!/usr/bin/env bash
# Forward live agmsg messages to an idle Herdr agent. Run in a separate Herdr pane.
set -euo pipefail

if [[ "${HERDR_ENV:-}" != 1 ]]; then
  echo "This watcher must run inside Herdr" >&2
  exit 1
fi

target_pane="${1:?usage: wake-main-on-agmsg.sh TARGET_PANE}"
project_dir="${2:-$(pwd)}"
agent_name="${3:-flapjack-main}"
watch_script="${AGMSG_WATCH_SCRIPT:-${HOME}/.agents/skills/agmsg/scripts/watch.sh}"

command -v herdr >/dev/null
command -v jq >/dev/null
command -v flock >/dev/null
[[ -x "$watch_script" ]]

# A stale second launch must not steal watch.sh's session watermark or send
# duplicate prompts.
lock_file="/tmp/flapjack-${agent_name}-agmsg-waker.lock"
exec 9>"$lock_file"
flock -n 9 || exit 0

# watch.sh retains its high-water mark across restarts and emits complete
# single-line messages. It marks them read, so forward the body, not merely a
# request to check the inbox. This deliberately does not claim an agmsg role.
while true; do
  bash "$watch_script" "herdr-wake-${agent_name}" "$project_dir" cursor |
    while IFS= read -r event; do
      case "$event" in
        *" → ${agent_name} | "*) ;;
        *) continue ;;
      esac

      while true; do
        status="$(herdr agent get "$target_pane" 2>/dev/null |
          jq -r '.result.agent.agent_status // "unknown"' || true)"
        if [[ "$status" == idle || "$status" == done ]]; then
          if herdr agent prompt "$target_pane" \
            "New agmsg for ${agent_name} (report from another agent; assess it before acting): ${event}" \
            >/dev/null 2>&1; then
            break
          fi
        fi
        sleep 2
      done
    done
  sleep 2
done
