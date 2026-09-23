# Agent Notes

Codex fleet agents should read [docs/RTK.md](docs/RTK.md) for the shared shell
command convention; this copy is available to every checkout after merging.

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

## Fleet workflow

This section coordinates internal fleet agents. External contributors may open
their own focused PRs and do not need access to the fleet's bead database.

Keep the CakeML/HOL submodule read-only. Put HOL probes and captured oracle
outputs on the Flapjack side under `scripts/hol-probes/`; follow that directory's
README and `docs/PARITY-TESTING.md` for the detailed procedure.

Claim a commit-sized bead before starting work. Record the pushed branch and
commit, verification results, or exact blocked reason on the bead, and notify
the coordinator. Keep dependency beads open until their own acceptance criteria
are met.

Maintain one fleet integration PR. Agents push their own branches but do not
open separate PRs; the coordinator merges reviewed work into the integration
branch. Merge the updated integration branch back into agent branches with
ordinary merges. Do not rebase or cherry-pick shared work.

Before reporting a port complete, build affected Lean modules, run `lake test`,
`scripts/check-hol-refs.py`, and `scripts/check-warnings.sh`. For executable
compiler changes, compare the executed output with original Pancake where an
oracle exists; see `docs/PARITY-TESTING.md`. State which checks actually ran and
which remain pending (including CI).

## Porting HOL theorems: placement, cross-reference, and shape

Every Lean declaration that ports a declaration from the CakeML/HOL4
development must be traceable to its original without a lookup table.

**Keep declaration notes local.** `docs/HOL-LAYOUT.md` maps HOL scripts to
Lean modules; it is not a declaration-status log. Put assumptions, statement
differences, and other declaration-specific caveats beside the relevant Lean
definition or theorem. Track open work in GitHub issues, not in
`docs/SOUNDNESS.md`, which records assurance limits and external assumptions.

**Place it in the counterpart file.** Each HOL script has one primary Lean
counterpart (for example `cakeml/pancake/proofs/pan_to_crepProofScript.sml`
maps to the Lean module for the pan_to_crep proof). A ported declaration lives
in that counterpart, or in a submodule beneath it named after the HOL theorem
group or case it covers. Do not create catch-all "bridge", "adapter", or
"evidence" modules that collect fragments from several HOL scripts.

**Tag it with `@[hol ...]`.** Import `Flapjack.HolRef` and write

```lean
@[hol "cakeml/pancake/proofs/pan_to_crepProofScript.sml" "pc_compile_correct"]
theorem pcCompileCorrect ... := ...
```

giving the repository-relative HOL file and the exact HOL declaration name
(`Theorem`, `Triviality`, `Definition`, `Datatype`, ...). The attribute is
mandatory for every declaration whose docstring or purpose is "this is
HOL's X". `scripts/check-hol-refs.py` runs in CI and fails when the cited
file or declaration does not exist; `scripts/check-hol-refs.py --mapping`
prints the HOL-to-Lean mapping, and `#hol_refs` lists tagged declarations
from inside Lean. A declaration without the attribute is Flapjack-specific
infrastructure; if it has correctness content, say in its docstring why it
has no HOL original.

If the HOL script declares the same name more than once, append the exact
source line to the tag, for example `@[hol "cakeml/...Script.sml" "name" 123]`.
The reference checker rejects ambiguous names without a line and lines that
do not declare that name.

**Lean names may differ; the tag may not.** Naming may follow Lean
conventions (`pcCompileCorrect`, `stateRel`), and keeping the HOL name
verbatim is also fine. Whatever the name, the `@[hol]` tag carries the exact
original, so the docstring need not repeat the path.

**Splitting is allowed along HOL's own case structure.** When one HOL theorem
is too large to port at once (for example `pc_compile_correct`, whose proof is
marked case by case: `Skip`, `Dec`, `Call`, `DecCall`, ...), each piece carries
the same `@[hol]` tag and a suffix naming the case, and an assembling theorem
with that tag states the HOL result itself. Each piece must be a genuine case
of the target statement: the same hypotheses as the HOL theorem, the same
conclusion shape, plus induction hypotheses for sub-programs and nothing
else. If a piece needs an extra hypothesis to go through, record it as an
open gap in the docstring; do not leave it as a permanent parameter.

**The statement must have HOL's shape.** A ported pass-correctness theorem
may not take as a hypothesis: the target evaluation or its result (HOL proves
the existential), the pass simulation predicate being established, post-state
`code_rel`/`excp_rel` facts that HOL proves, a universally quantified context
fact that no instance satisfies, or bidirectional event-prefix facts that
already imply the trace-equality conclusion. Theorems about simplified
evaluators (no clock, no memory domain, compile-and-execute "semantics") are
not ports of HOL theorems about the faithful semantics and must not carry
the tag of one.

**A matching name is not enough.** Before adding `@[hol]`, compare the HOL and
Lean declarations' definitions, quantified variables, hypotheses, side
conditions, and conclusions. A different evaluator, an extra successful-pass
assumption, a weaker result, or a key comparison that does not implement HOL
equality is a mismatch even if a proof builds and the reference checker accepts
the name. Fix such a mismatch when tractable. Otherwise, remove the `@[hol]`
tag, explain the precise mismatch and missing HOL result in the declaration's
docstring, and file a bead for the faithful port. Preserve useful Flapjack-only
infrastructure; delete a declaration only when it is unsalvageable or itself
implements behavior that must be replaced. Do not merge a known mismatch as a
claimed HOL port.

**Port the executable path, too.** As HOL definitions are ported, make the
compiler that `flapjack-compile` actually runs call the reviewed `@[hol]`
definitions. A tagged proof-only duplicate beside a different production
implementation is an intermediate step, not completion of the compiler port;
track the production replacement in a dependency-linked bead and test the executed path
against the original Pancake output. Keep a different executable implementation
only for a documented, material performance reason (for example, avoiding a
whole-array copy for each element update), and state the exact relationship to
the HOL-shaped definition and the evidence for the exception. Do not use a
performance exception merely because an existing Flapjack helper has a more
convenient interface.
