#!/usr/bin/env bash
# Resume a known Codex session when it finishes a turn; never type at a shell.
set -euo pipefail

[[ "${HERDR_ENV:-}" == 1 ]] || { echo "Herdr required" >&2; exit 1; }
session="${1:?usage: wake-codex-on-idle.sh SESSION_ID AGENT_NAME}"
name="${2:?usage: wake-codex-on-idle.sh SESSION_ID AGENT_NAME}"
command -v herdr >/dev/null
command -v jq >/dev/null
command -v flock >/dev/null

exec 9>"/tmp/flapjack-${name}-idle-waker.lock"
flock -n 9 || { echo "idle watcher already running for $name"; exit 0; }

was_ready=false
prompted_at=0
echo "idle watcher active for $name ($session)"
while true; do
  if agents="$(herdr agent list 2>/dev/null)"; then
    row="$(jq -r --arg sid "$session" --arg name "$name" \
      'first(.result.agents[] | select(.agent_session.value == $sid and .name == $name and .agent == "codex" and .interactive_ready == true and .focused == false) | [.pane_id, .agent_status] | @tsv) // empty' \
      <<<"$agents")"
    if [[ -n "$row" ]]; then
      IFS=$'\t' read -r pane status <<<"$row"
      if [[ "$status" == idle || "$status" == done ]]; then
        if [[ "$was_ready" == false ]] &&
          foreground="$(herdr pane process-info --pane "$pane" 2>/dev/null)" &&
          jq -e '.result.process_info.foreground_processes | any(.name == "codex")' \
            <<<"$foreground" >/dev/null; then
          # A known sandbox failure cannot be repaired by repeatedly poking
          # the same session. Leave it for a human to resume after repair.
          screen="$(herdr pane read "$pane" --source recent-unwrapped --lines 45 2>/dev/null || true)"
          if [[ "$screen" == *"bwrap: loopback: Failed RTM_NEWADDR"* ]]; then
            sleep 30
            continue
          fi
          if herdr agent prompt "$pane" \
            "Resume the Flapjack fleet goal. Read docs/RTK.md from the integration branch and prefix shell commands with rtk (rtk proxy for unsupported commands). If your PanStructs compile_shapes_eq_map branch is unfinished, first repair the RiscV.lean:409 proof fallout, run required gates, commit/push, update its bead, and agmsg flapjack-main with SHA/results. If the command runner is still blocked, report the exact blocker by agmsg and stop; do not claim success. Otherwise claim another ready commit-sized HOL-shaped theorem bead, ordinary-merge the integration branch, and continue. No separate PR." \
            >/dev/null 2>&1; then
            echo "resumed $name in $pane"
            was_ready=true
            prompted_at="$(date +%s)"
          fi
        fi
      elif [[ "$status" == working ]] && (( $(date +%s) - prompted_at >= 120 )); then
        was_ready=false
      fi
    fi
  fi
  sleep 10
done
