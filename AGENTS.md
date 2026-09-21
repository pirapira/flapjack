# Agent Notes

## Lean/Lake cache artifacts

OLean files under `.lake/` are local build outputs, not source artifacts. If
Lake reports that an expected `.olean` is missing or a hardlink is stale,
remove only that module's local generated `.olean`/`.ilean` file (and, when the
OLean is absent, its matching generated trace/hash metadata), then rebuild the
required target from source. Do not use a broad `lake clean` for this routine
repair.

Do not copy `.olean` files between worktrees or overwrite one with a copied
artifact: a copied OLean can be newer than its source and hide subsequent
source changes. Cache cleanup is local-only; do not stage `.lake` outputs.
