#!/usr/bin/env zsh

set -euo pipefail

# Get project root relative to script
script_dir="${0:A:h}"
cd "$script_dir"

# Set port for slides
PORT=8891

# Print usage and exit when asked for help.
if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  echo "Usage: $0 [deck ...]"
  echo "  deck: lecture1, lecture2, ..., verso-ex"
  echo "  With no args, compiles all slide decks; otherwise only the named ones."
  exit 0
fi

# Stop existing $PORT processes
# (e.g. Ctrl+C didn't stop a previous run,
# or the terminal was closed).
if pid=$(lsof -tiTCP:"$PORT" -sTCP:LISTEN 2>/dev/null); then
  echo "Killing stale process on port $PORT (pid $pid)"
  kill "$pid"
fi

# Compile slides ("$@" forwards deck names, if any, to only build those).
lake exe qic891 "$@"

# Serve slides on a local server.
# Presently serves to port $PORT suggestive of
# the QIC 891 code for lectures.
lake exe verso-serve _slides/ --port "$PORT" --strict-port # &
