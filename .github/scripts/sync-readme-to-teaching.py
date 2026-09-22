#!/usr/bin/env python3
# Tracked by git as 100755 (executable; see git lsfiles -s)
#
"""Sync the QIC891-README-marked block from
`README.md` into `_pages/teaching.md`.

Run from the repository root, with the website repo checked out at
`website/`.

This script is used in `.github/workflows/qic891-README-to-teaching.yml`
"""
import re

START = "<!-- QIC891-README:START -->"
END = "<!-- QIC891-README:END -->"

with open("README.md", encoding="utf-8") as f:
    readme = f.read()

source_match = re.search(
    re.escape(START) + r"(.*?)" + re.escape(END),
    readme,
    re.DOTALL,
)
if not source_match:
    raise SystemExit("Sync markers not found in README.md")

body = source_match.group(1).strip()
target_path = "website/_pages/teaching.md"

with open(target_path, encoding="utf-8") as f:
    target = f.read()

target_pattern = re.compile(
    re.escape(START) + r".*?" + re.escape(END),
    re.DOTALL,
)

if not target_pattern.search(target):
    raise SystemExit(
        f"Sync markers not found in {target_path}; "
        "add the QIC891-README markers to the website page"
    )

updated = target_pattern.sub(
    lambda _: f"{START}\n{body}\n{END}",
    target,
)

with open(target_path, "w", encoding="utf-8") as f:
    f.write(updated)
