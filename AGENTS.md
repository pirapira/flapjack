# Agent Notes

## Lean/Lake cache artifacts

Prefer a targeted repair over a global cache reset. When a build is blocked by
one bad or hardlinked cache artifact, remove that individual local `.olean`
(and its matching generated `.ilean`, `.ilean.hash`, or `.trace` metadata when
present) and rebuild the affected target. Do not use `lake clean` for this
class of problem: it discards unrelated, reusable cache state.

OLean files under `.lake/` are local build outputs, not source artifacts. If
Lake reports that an expected `.olean` is missing or a hardlink is stale,
identify the exact module path and remove only that module's local generated
`.olean`/`.ilean` file (and, when the OLean is absent, its matching generated
trace/hash metadata), then rebuild the required target from source. The
recommended repair is to remove the individual problematic OLean, not to run
`lake clean`; a broad clean throws away unrelated useful cache state and is
unnecessary for this failure mode.

In particular, when a hardlink is the immediate cause, resolve the exact
`.olean` path first and remove that individual generated file; do not replace it
with a copied OLean from another worktree. This keeps the rebuilt artifact
source-derived and ensures later source changes are observed.

Do not copy `.olean` files between worktrees or overwrite one with a copied
artifact: a copied OLean can be newer than its source and hide subsequent
source changes. Cache cleanup is local-only; do not stage `.lake` outputs.
