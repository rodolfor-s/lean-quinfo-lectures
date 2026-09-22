#!/usr/bin/env bash
#
# Tracked by git as 100755 (executable; see git lsfiles -s)
#
# Generates `_slides/index.html`: a page listing compiled slides.
#
# Copies `listing.css` next to it and fills the `__LECTURE_LIST__`
# placeholder in `index-template.html` with one `<li>` per directory in
# `_slides/` that has an `index.html`.
#
# Run from the repository root, after `lake exe qic891` has populated
# `_slides/*/index.html`. This script is used in `deploy-slides.yml`

set -euo pipefail

assets_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/assets" && pwd)"

# `_slides/` is the Pages upload root (see deploy-slides.yml), so the
# stylesheet must live inside it to be servable as a sibling of index.html.
cp "${assets_dir}/listing.css" _slides/listing.css

list=""
# Build one `<li>` element per lecture directory that has rendered slides.
for dir in _slides/*/; do
  name="$(basename "$dir")"
  if [ -f "${dir}index.html" ]; then
    label="$(echo "$name" | sed -E 's/^lecture([0-9]+)$/Lecture \1/; s/-/ /g' \
      | awk '{for (i = 1; i <= NF; i++) $i = toupper(substr($i, 1, 1)) substr($i, 2)}1')"
    list="${list}<li class=\"dir\"><a href=\"${name}/\">${label}</a></li>"$'\n'
  fi
done

# Fill the static template's `__LECTURE_LIST__` placeholder with the list
# generated above. `${var//search/replace}` is a literal (non-regex) bash
# substitution, so special characters in `list` (quotes, slashes, etc.)
# can't be misinterpreted the way they would be with `sed`.
template="$(cat "${assets_dir}/index-template.html")"
template="${template//__LECTURE_LIST__/$list}"
printf '%s\n' "$template" > _slides/index.html
