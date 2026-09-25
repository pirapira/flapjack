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

For an executable HOL definition, landing a tagged proof-side duplicate is
partial progress: keep its inventory bead open until the executed compiler
uses the reviewed definition, or a documented, measured performance exception
is in place. Record the remaining production-path work on a linked bead.

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

**Reviewed statements are pinned.** `docs/HOL-TYPE-HASHES.json` records the
elaborated Lean type of each `reviewed_exact` entry in
`docs/HOL-THEOREM-MAP.json`; for tagged definitions and `opaque` declarations it
also records the elaborated body. CI runs `scripts/check_hol_type_hashes.py` and
rejects statement or definition-body drift. After comparing a changed Lean
statement (or definition body) with its HOL source, run
`python3 scripts/check_hol_type_hashes.py --update` and review the
lock-file diff. The hash gate detects Lean declaration changes only: it does not
hash untagged dependencies, theorem proof terms, or the HOL declarations, and it
does not prove HOL-to-Lean equivalence or replace source-level review.
After rebuilding a tagged declaration, run `lake build Flapjack` before the
type-hash check: it refreshes `.lake/build/ir/Flapjack.setup.json`, which can
otherwise still point at an older cached OLean even when `lake test` passes.

**A matching name is not enough.** Before adding `@[hol]`, compare the HOL and
Lean declarations' definitions, quantified variables, hypotheses, side
conditions, and conclusions. A different evaluator, an extra successful-pass
assumption, a weaker result, or a key comparison that does not implement HOL
equality is a mismatch even if a proof builds and the reference checker accepts
the name. Also compare the imported datatype carriers: constructor arity, field
types, and fixed word widths must match before a definition or theorem using
them is tagged as an exact HOL port. A generic parameter in place of a fixed
HOL width is a mismatch, even when the function ignores that field. Fix such a
mismatch when tractable. Otherwise, remove the `@[hol]` tag, explain the precise
mismatch and missing HOL result in the declaration's
docstring, and file a bead for the faithful port. Preserve useful Flapjack-only
infrastructure; delete a declaration only when it is unsalvageable or itself
implements behavior that must be replaced. Do not merge a known mismatch as a
claimed HOL port.

**Qualify only named list-to-array state fields.** An unqualified tag records a
statement reviewed as exact and has manifest status `reviewed_exact`. The
standard translation of a HOL data structure must be explicit in the `@[hol]`
tag of every declaration that relies on it, using a specific supported
qualifier. Do not treat acceptance of a translation for one declaration as a
blanket exception for other declarations or leave a representation difference
implicit under an unqualified tag. Add a new qualifier and its checker/review
rules before using a further standard translation; a qualifier records only
that translation, not unrelated differences in the statement or behavior.
The `(list_as_array := [field, ...])` qualifier is only for specific HOL list
fields represented by Lean arrays; it does not allow any other difference in
the theorem statement or semantics. Review the fields against the surrounding
HOL state relation, list lengths, index bounds, and update behavior. The
manifest must list the same fields and use `reviewed_list_as_array` after that
comparison; never call a qualified theorem `reviewed_exact`.

The `(list_as_list := [xs, ...])` qualifier identifies HOL list variables
represented by Lean `List` binders. The reference checker requires every name
to be a declaration binder of Lean `List` type. The manifest uses
`reviewed_list_as_list`; source review must still compare each operation,
length/index bounds, and full theorem shape. For example, a bounded Lean
`get?` fact may represent HOL `EL` only when the existing HOL bound is
preserved and the option equality is proved equivalent to the selected
element. The qualifier itself authorizes no changed premises or conclusion.
Combinations with other qualifiers need their own explicit reviewed manifest
status before use.

Each qualified field must be a field of a structure in the same Lean module
and have a kernel-checked theorem named `holListArrayWitness_<field>`. Its
result type must establish `RepresentsHOLNodeList` for that field and a HOL
list, without assuming `RepresentsHOLNodeList` in its premises. The reference
checker enforces this shape and Lake checks the theorem proof, but those gates
do not independently establish the cross-language correspondence. Review the
witness and HOL/Lean theorem statements manually; the qualifier does not
authorize changed evaluators, errors, quantified types, side conditions, or
conclusions. If bounds or out-of-range behavior differ, leave the theorem
untagged and document the mismatch beside it.

Representation witnesses alone do not establish transition equivalence.
Review successful updates, invalid representations, and out-of-range errors
separately before tagging any transition theorem.

**Qualify String-backed HOL `mlstring` names.** Use
`(names_as_string := [name, ...])` when a Lean `String` identifier models HOL
`mlstring`; identifiers can be parameters or uses, not just structure fields.
Use manifest status `reviewed_names_as_string` only after comparing the cited
HOL declaration. Classify each identifier in the reviewer note as
`equality/map-key-only` or `byte-observable`; the latter must also appear in
`(names_as_string_boundary := [...])`. For each byte-observable declaration,
provide a same-module `holMlStringWitness_<LeanDeclaration>` whose conclusion
is `NameRanged` on that declaration's output. Input premises such as
`NameRanged name` are allowed; source review must verify that the executed path
supplies them. The reference checker verifies the witness name/result shape and
manifest classification, while Lake checks the proof. Neither check establishes
HOL correspondence or premise discharge; record those in source review. The
theorem map and type-hash lock record both qualifier lists. Do not add this
qualifier to production declarations until checker tests and source review pass.

**Qualify canonical finite-map carriers.** Use
`(fmap_as_finite_support := [field, ...])` when a HOL `|->` finite-map field is
represented by the reviewed canonical Lean translation `HolFiniteMapExact`
(a `lookup` function plus a `finiteSupport` proposition). Every named field must
be declared by ONE owning carrier structure in the same module, whose field
types use `HolFiniteMapExact`; a raw function-backed `α → Option β` map is
ineligible, and fields split across several structures are rejected. When a
module declares several structures with the same field names (for example a
broad state and its finite-support counterpart), the tagged declaration's own
carrier disambiguates: the owner must be named in that declaration's signature.
The module must contain the checked canonical witness
`holFmapAsFiniteSupportWitness`,
whose statement names that owning structure and states a real `toX`/`ofX`
roundtrip between it and its broad counterpart (a bare `State -> Broad -> State`
arrow, or an unrelated counterpart mention, is rejected; the broad counterpart
need not be declared in the same module). The
reference checker verifies field/owner/carrier/witness shape and Lake checks the
proof; neither establishes HOL correspondence. The qualifier is a representation
statement only: it does not authorize changed quantifiers, hypotheses,
conclusions, `BEq` side conditions, or word-model differences, and every tagged
declaration still needs its own statement/side-condition review.

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
