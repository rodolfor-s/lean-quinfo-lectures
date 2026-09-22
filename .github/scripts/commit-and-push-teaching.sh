#!/usr/bin/env bash
#
# Tracked by git as 100755 (executable; see git lsfiles -s)
#
# Commits and pushes `_pages/teaching.md` if `sync-readme-to-teaching.py`
# changed it
#
# Run with the website repo (rodolfor-s/rodolfor-s.github.io) as the
# working directory
#
# This script is used in `.github/workflows/qic891-README-to-teaching.yml`

set -euo pipefail

git config user.name "github-actions[bot]"
git config user.email "github-actions[bot]@users.noreply.github.com"
git add _pages/teaching.md
if git diff --cached --quiet; then
  echo "No changes to sync"
  exit 0
fi
git commit -m "Sync teaching page from QIC891 README"
git push
