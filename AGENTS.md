# Agent Notes

## Lean/Lake cache artifacts

Mathlib is a pinned proof dependency. Run `lake exe cache get` after dependency
updates to fetch its compiled cache; CI explicitly enables the same command via
Lean Action's `use-mathlib-cache` input. Keep the real-sqrt agreement module
reachable from the umbrella build. The compiler executable does not depend on
Mathlib's real-analysis modules.

For a one-off check of a Lean source file, prefer `lake lean path/to/File.lean`
over `lake env lean path/to/File.lean`. `lake lean` builds the file's imports
through Lake first, so it can reuse and restore cached build artifacts, and
passes the root package's configured Lean arguments. `lake env lean` sets up
the environment but does not build missing or stale imports. For a module's
normal build, continue to use `lake build Module.Name`.

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

When the local `.olean` files of a target are absent but the Lake artifact cache
has them, `scripts/lake-restore-oleans.sh [TARGET ...]` (which runs
`LAKE_RESTORE_ARTIFACTS=true lake build`) is the sanctioned restore route: Lake
re-checks each cached output against the current sources and re-materializes the
missing `.olean` files, rebuilding anything whose inputs changed. A restored
`.olean` is a hardlink into the content-addressed cache, so never edit a
restored hardlinked `.olean` in place: that mutates the shared cache entry.
Treat restored outputs as read-only and rebuild the affected module from source
instead.

## Fleet workflow

This section coordinates internal fleet agents. External contributors may open
their own focused PRs and do not need access to the fleet's bead database.

Initialize both reference submodules in your own checkout with
`git submodule update --init -- cakeml HOL`; use their committed revisions,
not an unrelated local HOL installation. Keep both submodules read-only.
Put HOL probes and captured oracle
outputs on the Flapjack side under `scripts/hol-probes/`; follow that directory's
README and `docs/PARITY-TESTING.md` for the detailed procedure.

Before closing a porting bead backed by a HOL probe, regenerate its captured
outputs from the original CakeML/HOL source. Probes provide regression evidence,
not a HOL-to-Lean equivalence proof.

Prefer a whole HOL script or a large coherent section as an agent work area,
with different agents owning distant areas. Keep declaration-level beads and
real dependency edges underneath it for traceability; they are not necessarily
separate reporting events. Split an oversized script along its own theorem
groups. Agree on ownership before crossing into another agent's area, and
change areas only between tasks, without interrupting ongoing work.

Claim a ready bead before starting work. Record the pushed branch and
commit, verification results, or exact blocked reason on the bead. Keep
dependency beads open until their own acceptance criteria are met.

Report a completed file or substantial coherent section as soon as its checks
are finished, even if it took fewer than ten commits. For smaller scattered
work, roughly ten meaningful content commits is a useful reporting interval,
not a quota. Keep pushing your own branch and
updating individual beads throughout the batch; do not wait to publish work.
Send one summary with the branch/head, covered beads, and actual checks instead
of a message for every commit or small task. Report urgent blockers, conflicts,
coordination needs, or a requested delivery sooner. Do not interrupt ongoing
work merely to report; use a clean between-task boundary.

Before creating or claiming a child bead, read the fleet inbox and list the
parent's children in the shared bead database. Do not duplicate a constructor
or case already assigned to another agent, even if its bead is still open.
Use your fleet agent name as the assignee (not a generic tool name). If an
assignment conflicts with a new message, stop and ask the coordinator which
case to keep before editing.

Use `bd ready` to choose the next unblocked task within your assigned area. The shared bead
database is the source of truth for current priorities; do not hard-code a
temporary strategic focus here or claim a blocked parent merely because it is
high priority. The coordinator keeps bead priorities aligned with the current
goal.

Do not wait for a coordinator assignment to continue. Claim ready work in your
area and coordinate directly with peers about sharing or taking over a
prerequisite, especially one blocking your own work. Check existing claims and
pending deliveries first; agree on ownership before taking over active work.
If blocked, record the genuine dependency, release the blocked parent, and pick
an available prerequisite or another ready task. Work awaiting integration may
be consumed by an ordinary peer merge; its acceptance status stays unchanged.

Persistent agent goals describe the overall fleet mission, not a particular
bead or temporary assignment. Send individual assignments as ordinary messages
and use the shared database to choose subsequent work. Completing a bead is a
checkpoint, not completion of the persistent goal; continue with the next ready
task. Keep wake-up prompts generic for the same reason.

Keep one explicit correctness critical path in the shared bead dependency
graph, from faithful source semantics through each required compiler pass to
the RISC-V result. Give every missing HOL declaration a bead; split a large
declaration into commit-sized children along its HOL cases or prerequisites.
Before adding a blocking edge, check the HOL proof or definition to confirm it
really needs that prerequisite. Do not serialize independent ports merely to
make a tidy-looking chain. Assign P1 work only from unblocked
leaves; leave blocked parents unassigned and record the exact frontier there.

Agents leave completed slices open, record readiness on their beads, and include
them in the next batched report with branch, commit, and checks. The coordinator reviews the source and Lean
statement, merges the commit into the single integration PR, then closes the
bead only if its acceptance criteria are met. A pushed agent branch alone is
not completion.

Close a theorem-port bead only after the theorem itself is source-reviewed and
kernel-checked in Lean, with a justified `@[hol]` qualifier when needed. A
mismatch classification or other disposition is not a completed port. If an
unqualified port is specifically required, track it on a bead that explicitly
says so in its title and acceptance criteria.

If a claimed porting bead needs an unported prerequisite, create a commit-sized
bead for that prerequisite, add a blocking dependency from the original bead,
record the exact blocker, then unassign yourself from the original bead. Claim
the prerequisite or another ready bead rather than holding the blocked bead;
notify the coordinator of the new dependency and assignment change.

For an executable HOL definition, landing a tagged proof-side duplicate is
partial progress: keep its inventory bead open until the executed compiler
uses the reviewed definition, or a documented, measured performance exception
is in place. Record the remaining production-path work on a linked bead.

Maintain one fleet integration PR. Agents push their own branches but do not
open separate PRs; the coordinator merges reviewed work into the integration
branch. Merge the updated integration branch back into agent branches with
ordinary merges. Do not rebase or cherry-pick shared work.

Ordinary-merge a peer's pushed branch when it supplies a dependency needed for
your work; do not wait for coordinator integration just to consume that
dependency. Coordinate overlapping file ownership, inspect the peer's reported
verification scope, and run affected checks after merging. Record the peer
branch and commit on your bead and in your next batch report. A peer merge does
not close its beads or certify its ports: coordinator acceptance and the usual
source-comparison requirements still apply.

Before reporting a port complete, build affected Lean modules, run `lake test`,
`scripts/check-hol-refs.py`, and `scripts/check-warnings.sh`. The warning gate
excludes diagnostics from `Flapjack/Test/`, as requested by the maintainer;
warnings from other modules and all build errors still fail the gate. Tests
remain default build targets and must pass `lake test`. For executable
compiler changes, compare the executed output with original Pancake where an
oracle exists; see `docs/PARITY-TESTING.md`. State which checks actually ran and
which remain pending (including CI).

Keep the edit-check loop short without weakening that completion gate. While
working, build the affected module with `lake build Module.Name` (or use
`lake lean path/to/File.lean` for a one-off source check), preserve reusable
Lake artifacts, and run focused tests first. Independent reference, mapping,
and probe checks may run concurrently. `check-warnings.sh` invokes Lake, so
run it sequentially with other Lake commands; do not run multiple Lake builds
against the same worktree at once.
Treat `check_hol_ref_export.py` as a Lake user: its export can build modules.
Run it sequentially with builds, `lake test`, and the warning check to avoid
artifact-write races. The HOL checker unit suite mocks the exporter and does
not invoke Lake; it may run concurrently with these commands. Keep actual
elaborated-export coverage in the separate export gate.
Run the full required suite before reporting a branch ready and again on the
coordinator's merged tree before integration. Profile a persistently slow
theorem or checker and fix the bottleneck; never shorten default build targets
or skip a required gate merely to obtain a faster green result.

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

**Reviewed rows must match the elaborated attributes.** CI runs
`scripts/check_hol_ref_export.py`, which exports every `@[hol]`-tagged
declaration through `scripts/HolRefExport.lean` and requires each `reviewed_*`
row of `docs/HOL-THEOREM-MAP.json` to match exactly one tagged declaration
(by HOL reference and Lean leaf name) whose elaborated qualifiers equal the
manifest's. Declaration statements and bodies are not pinned: a change to a
reviewed Lean statement or definition body must be compared with its HOL source
again before merging, and the gate does not prove HOL-to-Lean equivalence or
replace source-level review. After rebuilding a tagged declaration, run
`lake build Flapjack` before this check: it refreshes
`.lake/build/ir/Flapjack.setup.json`, which can otherwise still point at an
older cached OLean even when `lake test` passes.

Entries marked `pending_statement_review` or
`no_hol_reference_pending_classification` must not be described as exact HOL
ports. A reference tag or a successful build does not substitute for the
required source review and manifest classification.

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

Capture the original declaration with inferred types (`show_types` or `type_of`)
when adding reviewed rows. Check independent type variables inside each conjunct
and recursive premise, not just the outer state carrier. Do not identify generic
result widths, input/output payload types, or unrelated instruction widths.
For local declarations that cannot be exported, record the exact source typing
and a typed replay where available; untyped printed statements are insufficient
evidence for claims about inferred carriers.

**Qualify only named list-to-array state fields.** An unqualified tag records a
statement reviewed as exact and has manifest status `reviewed_exact`. When a
HOL data structure uses a reviewed *different Lean representation* (for
example, HOL list as Lean `Array`), name that standard translation in the
`@[hol]` tag of every declaration that relies on it, using a supported
qualifier. Ordinary constructor-for-constructor ports such as HOL list to
Lean `List` need no qualifier. Do not treat acceptance of a representation
difference for one declaration as a blanket exception for others or leave it
implicit under an unqualified tag. Add a new qualifier and its checker/review
rules before using another non-identity representation; a qualifier records
only that translation, not unrelated statement or behavior differences.
The `(list_as_array := [field, ...])` qualifier is only for specific HOL list
fields represented by Lean arrays; it does not allow any other difference in
the theorem statement or semantics. Review the fields against the surrounding
HOL state relation, list lengths, index bounds, and update behavior. The
manifest must list the same fields and use `reviewed_list_as_array` after that
comparison; never call a qualified theorem `reviewed_exact`.

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
theorem map records both qualifier lists, and `check_hol_ref_export.py` compares
them with the elaborated attribute. Do not add this
qualifier to production declarations until checker tests and source review pass.

**Qualify canonical finite-map carriers.** Use
`(fmap_as_finite_support := [field, ...])` when a HOL `|->` finite-map field is
represented by the reviewed canonical Lean translation `HolFiniteMapExact`
(a `lookup` function plus a `finiteSupport` proposition). Every named field must
be declared by ONE owning carrier structure whose field types use
`HolFiniteMapExact`; a raw function-backed `α → Option β` map is ineligible, and
fields split across several structures are rejected. Only HOL `|->` fields are
eligible: an `sptree$num_map` (for example `loopSem$state`'s `locals`/`code`) is
a tree map, not a `|->` finite map, so it must not be named here even when the
Lean field uses `HolFiniteMapExact`. Represent such fields with their own
reviewed carrier (for example `Flapjack/Misc/Sptree.lean`'s `Spt`) or wait for a
dedicated qualifier, and leave the affected declaration untagged until then.
The owning carrier may be
declared in the tagged module or reached through its transitive imports (for
example a tagged evaluator whose state carrier lives in a dedicated `HOLState`
module). Do not declare a local duplicate of an imported state carrier just to
satisfy placement; a same-named local copy that shadows the imported owner is
rejected as ambiguous. When several in-scope structures declare the same field
names, the tagged declaration's own signature disambiguates: the owner must be
named there as a whole identifier. The tagged module must contain the checked
canonical witness `holFmapAsFiniteSupportWitness`, whose statement names that
owning structure and states a real `toX`/`ofX` roundtrip between it and its broad
counterpart (a bare `State -> Broad -> State` arrow, or an unrelated counterpart
mention, is rejected; the broad counterpart need not be declared in the same
module). A witness declared under a fresh local namespace (to avoid clashing with
an imported witness of the same name) is acceptable, and an imported witness may
be re-exported as a local one. The reference checker verifies
field/owner/carrier/witness shape and Lake checks the proof; neither establishes
HOL correspondence. Source review must additionally confirm the imported owner is
the reviewed carrier the evaluator actually uses, that no local duplicate carrier
shadows it, and that the witness is non-vacuous. The qualifier is a
representation statement only: it does not authorize changed quantifiers,
hypotheses, conclusions, `BEq` side conditions, or word-model differences, and
every tagged declaration still needs its own statement/side-condition review.

**Qualify finite maps nested in a function type.** For a HOL type abbreviation
whose function argument and optional result are products containing `|->` maps,
use `(fmap_as_finite_support_function := [argument_N, result_M])` with one-based
product positions. The Lean abbreviation must use `HolFiniteMapExact` at both
named positions with the same map type, and account for every such map in the
abbreviation. Keep the same-module `holFmapAsFiniteSupportWitness` and record
the two positions and the source comparison in the manifest; use status
`reviewed_fmap_as_finite_support_function` (or its combined
`_words_as_type_indexed_bitvec` status). This qualifier is mutually exclusive
with the other finite-map qualifiers. Its syntactic checker and Lean witness
do not prove HOL-to-Lean equivalence; review the entire function domain,
codomain, and surrounding word/set carriers against HOL before tagging.

**Qualify a heterogeneous finite-map function.** Use
`(fmap_as_finite_support_heterogeneous_function := [argument_N, result_M])`
only for a direct function definition with a typed result whose named explicit
input binder and `Option`-wrapped product result slot are each exactly one
`HolFiniteMapExact` carrier. `argument_N` counts explicit input binders;
`result_M` counts one-based top-level tuple components. The two map types may
be distinct, but every `HolFiniteMapExact` occurrence in the declaration
signature must be one of those two slots. Raw maps and products/functions that
merely contain a map are ineligible. The same module must provide
`holFmapAsFiniteSupportHeterogeneousFunctionWitness_<declaration>` over exactly
the same explicit inputs and exactly the same implicit/typeclass binders as
the operation; extra proof premises or instances are rejected.
The qualifier requires self-contained declaration and witness binders in a
module without ambient `variable`/`variables`/`include`/`omit` commands, since
Lean can insert inherited proof premises absent from the written header.
Bind width/type parameters and `NeZero` instances in each declaration header.
This conservative syntax restriction does not independently prove absence of
elaborated assumptions for arbitrary Lean syntax or replace source review.
Its unconditional equality must compare the tagged
operation's `Option.map` result projection (using the returned map's `.lookup`)
with an independent raw lookup operation applied through the canonical input
map's `.lookup`. Each complete equality side must have that application shape:
embedded mentions, discarded arguments, inert wrappers, and trailing terms do
not qualify. This narrowly permits different input/result map types; it
does not authorize changes to the HOL function's clauses or any other carriers.
Use manifest status `reviewed_fmap_as_finite_support_heterogeneous_function`
(or its `_words_as_type_indexed_bitvec` combination) only after source review
compares the complete HOL declaration and projection witness. The checker and
Lean theorem establish syntax/kernel validity, not HOL correspondence.

**Qualify standalone finite-map carriers.** Use
`(fmap_as_finite_support_result)` when a tagged declaration is not a structure
field but whose own input or result carrier is the reviewed canonical
`HolFiniteMapExact` translation (for example a HOL definition that returns a
finite map directly, such as `get_eids_from_decls_def`). This is distinct from
`fmap_as_finite_support`, which names the fields of an owning carrier; the two
qualifiers are mutually exclusive. When the same declaration also translates
HOL words to positive-width BitVecs, include `words_as_type_indexed_bitvec`
and use manifest status
`reviewed_fmap_as_finite_support_result_words_as_type_indexed_bitvec`.
Both qualifiers and the existing lookup witness remain mandatory; their
combination permits no additional statement or semantic difference.
The tagged declaration's own signature must
mention `HolFiniteMapExact`; a raw function-backed `α → Option β` map is
ineligible. The module must contain a checked canonical witness named
`holFmapAsFiniteSupportResultWitness_<declaration>`, whose final equality/iff
conclusion mentions the tagged declaration on exactly one side, applies a lookup
operation to that side, and states an unconditional or premise-independent
lookup-level correspondence to an independent HOL-shaped raw map operation or
codec on the other side. A witness is rejected when it is missing, vacuous,
type-name-only, wrongly-named, unrelated, a self-equality (both sides
syntactically identical), mentions the tagged declaration on both sides or
neither side, does not apply a lookup to the tagged declaration's side, or
assumes the target relation in a premise. The reference checker verifies
carrier/witness shape and Lake checks the proof; neither establishes HOL
correspondence. The qualifier is a representation statement only: it does not
authorize changed quantifiers, hypotheses, conclusions, `BEq` side conditions,
or word-model differences, and the manifest must use status
`reviewed_fmap_as_finite_support_result` after source comparison.

**Qualify standalone finite-map input parameters.** Use
`(fmap_as_finite_support_parameters := [binder, ...])` for explicitly named
HOL `|->` inputs represented directly by `HolFiniteMapExact`, when the result
is not a finite map. Each binder must have that explicit carrier and a
same-module kernel-checked
`holFmapAsFiniteSupportParamWitness_<declaration>_<binder>` establishing its
lookup/finite-support codec roundtrip. This is distinct from qualifiers for
structure fields and map-valued results. Source review must preserve binder
order, hypotheses, and conclusions; the representation witness and checker
do not prove HOL-to-Lean correspondence or permit other statement differences.
Record the named parameters in the reviewed manifest, with the matching
`reviewed_fmap_as_finite_support_parameters` status (or its supported combined
status).

**Qualify observations of computed finite-map results.** Use
`(fmap_as_finite_support_result_observations := [Producer, ...])` only
for explicitly named imported map producers used in the tagged observer's
type. Each producer must resolve uniquely to an imported tagged declaration,
return `HolFiniteMapExact` directly, carry `fmap_as_finite_support_result`,
and have its checked same-module canonical lookup witness and a
`reviewed_fmap_as_finite_support_result` manifest row with source review.
Local declarations or observer binders must not shadow the producer; short
names ambiguous among imported declarations are rejected. The producer list
must be nonempty, distinct, used in the observer signature, and identical in
the attribute and observer manifest row. Use status
`reviewed_fmap_as_finite_support_result_observations` after separately
comparing the observer's complete HOL statement and carriers.

This qualifier records only the canonical representation of those computed
map results. It does not qualify an observer's own map parameters, authorize
raw function maps, change any quantifier or hypothesis, or establish the
observer from producer acceptance. It cannot combine with any other
representation qualifier. The reference checker validates producer resolution,
usage, result carrier, witness and manifest evidence syntactically; the
elaborated-attribute export checks manifest agreement and Lean checks the
witness. None establishes cross-language correspondence. Complete source
review of both the producer and observer remains required.

**Qualify multi-carrier finite-map relations.** Use
`(fmap_as_finite_support_relation := [Carrier.field, ...])` when a HOL relation
mentions multiple carrier structures and needs explicit ownership for the
finite-map fields it actually traverses (for example HOL `state_rel_def`,
whose only translated finite-map field is `PanSemStateFiniteExact.globals`). Each
entry names one field of one carrier; the carrier must be declared in the module
or reachable through its imports and that field's type must be the reviewed
canonical `HolFiniteMapExact` translation (a raw `α → Option β` map is
ineligible). The tagged declaration must name every entry carrier. The qualifier
covers only the listed maps (and their HOL vs Lean representation); a bare
entry (a name without a dot) records a standalone finite-map binder of the
tagged declaration, including a universally quantified binder inside an induction
hypothesis. The declaration must bind that name at the reviewed canonical
`HolFiniteMapExact` translation and needs no carrier witness, while a
`Carrier.field` entry must name one field of one carrier that is declared in the
module or reachable through its imports with a `HolFiniteMapExact` field. The
qualifier does not authorize changed quantifiers, hypotheses, conclusions, `BEq`
side conditions, or word-model differences. Each distinct entry carrier needs a
same-module checked canonical witness
`holFmapAsFiniteSupportRelationWitness_<Carrier>` naming the carrier and stating a
genuine `toX`/`ofX` roundtrip with its broad counterpart (a carrier named in the
statement that contributes no translated finite-map field needs no witness). This
qualifier is mutually exclusive with `fmap_as_finite_support` and
`fmap_as_finite_support_result`, cannot use `reviewed_exact`, and requires
manifest status `reviewed_fmap_as_finite_support_relation` with a
source-comparison note after the reviewer compares each HOL conjunct.

Unused HOL binders may be retained or omitted only when source review confirms
that they are vacuous for the particular statement or case. Document any omission
beside the declaration; never drop a guard, hypothesis, or conclusion dependency.

**Combine multi-carrier relation and word translation.** When a HOL relation
must be represented both through the canonical finite-support map translation
and through the type-indexed `'a word`/`'ffi` translation, tag the declaration
with `(fmap_as_finite_support_relation := [...])` and
`(words_as_type_indexed_bitvec)` together. The manifest status is
`reviewed_fmap_as_finite_support_relation_words_as_type_indexed_bitvec`, both
qualifiers are required together, and neither single status is accepted. The
word-carrier and positivity obligations are checked on the tagged signature as
for the field-based combination, and the same-module per-carrier relation
witnesses remain required. This combination is limited to the relation
qualifier: it cannot be combined with `fmap_as_finite_support`,
`fmap_as_finite_support_result`, or `fmap_as_finite_support_equalities`.

**Qualify theorem-level finite-map equalities.** Use
`(fmap_as_finite_support_equalities)` when the tagged declaration is a theorem
whose conclusion is a conjunction of `HolFiniteMapExact` map *equalities* (for
example HOL `slc_tlc_rw`), rather than a declaration whose own result/input
carrier is a finite map. This is a conjunction-specific qualifier, so at least
two top-level equality conjuncts are required. The checker counts the top-level
conjuncts `N` of the theorem's conclusion and requires, in the same module, one
checked witness `holFmapAsFiniteSupportEqualityWitness_<declaration>_<i>` for
each `i = 1..N`.
Every witness must state an unconditional equality with each side shaped
precisely as `<map expression>.lookup <key>` (only safe outer parentheses may
wrap a side), where the key is a universally bound identifier in the statement
(no fixed keys, no wrapping `let`, prefix lookup, or nested term), must apply
both lookups at the same key, must be syntactically associated with its numbered
conjunct (each side of the `i`-th witness must be exactly the corresponding side
of the `i`-th conjunct), must not be an `↔`, a self-equality, or have a premise
that already assumes the relation, and must NOT mention the tagged theorem at all
(this rejects the ignored-proof / threaded-argument pattern that passes a theorem
application as a term, and the inert-`let` bypass that hides a reference to the
tagged theorem behind a discarded binder). The qualifier is mutually exclusive
with `fmap_as_finite_support`, `fmap_as_finite_support_result`, and
`fmap_as_finite_support_relation`, cannot use `reviewed_exact`, and requires
manifest status `reviewed_fmap_as_finite_support_equalities` with a
source-comparison note in the reviewer field. The checker's checks are syntactic:
it validates witness count, naming, exact equality shape, same-key application, a
universally bound key, and per-conjunct association, but it does not prove that
the Lean witnesses and conjuncts correspond to the HOL map equalities, so source
review must still compare each numbered witness against the
HOL equality and record that comparison in the reviewer note.

**Qualify a single theorem-level finite-map equality.** Use
`(fmap_as_finite_support_equality)` when the tagged declaration is a theorem
whose entire conclusion is exactly one `HolFiniteMapExact` map *equality* (for
example HOL `res_var_FEMPTY` or numeric `fperm_code` empty), rather than a
conjunction of equalities. The checker requires the conclusion to contain
exactly one top-level conjunct, splits the stripped conclusion on `=`, and
requires, in the same module, one checked witness
`holFmapAsFiniteSupportEqualityWitness_<declaration>` whose two sides are shaped
precisely as `<map expression>.lookup <key>` (only safe outer parentheses),
applied at the same universally bound key, unconditional, not a self-equality,
not mentioning the tagged theorem, and with no premise assuming the relation.
A conjunction must use the plural `(fmap_as_finite_support_equalities)` instead,
and a raw `alpha -> Option beta` map is rejected (the canonical carrier is
`HolFiniteMapExact`). The qualifier is mutually exclusive with
`fmap_as_finite_support`, `fmap_as_finite_support_result`,
`fmap_as_finite_support_relation`, `fmap_as_finite_support_equalities`, and the
function/heterogeneous-function qualifiers, cannot use `reviewed_exact`, and
requires manifest status `reviewed_fmap_as_finite_support_equality` with a
reviewer note containing both `source` and `fmap_as_finite_support_equality`.
The checker is syntactic and does not prove the Lean witness equals the HOL
equality, so source review must compare the single witness against the HOL
equality and record the comparison in the reviewer note.

**Qualify the HOL word-dimension and FFI-universe translation.** Use
`(words_as_type_indexed_bitvec)` when the only carrier difference from the HOL
declaration is the standard translation of HOL's type-indexed `'a word`
(dimension `dimindex (:α)`) to Lean's positive-width `BitVec width` and of HOL's
`'ffi ffi_state` to a universe-0 Lean host type `σ : Type`. The tagged
declaration must name `BitVec`, or name a reviewed width-indexed carrier
structure or inductive family (declared locally or reached through imports)
whose own header carries `[NeZero <width>]` for its width parameter and some
field or constructor payload of that SAME owner mentions `BitVec <width>`
(directly, or through the single reviewed word abbrev
`RiscV.Word <width>` at `Flapjack/RiscV/Model.lean:17` (`abbrev Word (width :
Nat) := BitVec width`), which counts as the same `BitVec` carrier at that same
width identifier) with that same width identifier; the carrier is
resolved from its declaration, never accepted by name alone, and the
`[NeZero <width>]` discharge and the word-carrier field must come from the
SAME owning declaration and the same width identifier (a header with
`[NeZero other]` or a field such as `BitVec 5 × HolWordLab width` does not
qualify); the check is syntactic and resolves only the known reviewed abbrev
`RiscV.Word`, not arbitrary abbrev unfolding, so any other word alias does not
qualify until it is added to the reviewed abbrev list; a name with several owners (a
local duplicate shadowing an imported owner) is rejected as ambiguous unless the
signature uniquely resolves it. Every word dimension occurring in the tagged
signature (not only the first) must be bound at its own `Nat` width with its own
`[NeZero <id>]` discharge; a literal `BitVec 0` dimension and a `[NeZero 0]`
discharge are rejected as non-positive. The
declaration must retain `[NeZero width]` as the
discharge of HOL's `dimindex (:α) ≥ 1`, and must not restate word-dimension
positivity as an extra hypothesis (`width ≠ 0`, `0 < width`, `Nat.pos`,
`NeZero.out`); when it mentions the FFI carrier `HolFfiState`, the host type must
be bound as `{σ : Type}` (or `Type 0`) without a universe-level variable or a
`Sort`, and `Type n` for `n ≥ 1` is rejected. This is a
conventional data-structure translation only: it authorizes no change to
quantifiers, hypotheses, side conditions, or conclusions, and no cross-assistant
agreement theorem is required. It cannot use `reviewed_exact`; use manifest
status `reviewed_words_as_type_indexed_bitvec` after comparing the HOL and Lean
declarations. When the same declaration also carries
`fmap_as_finite_support`, use the combined status
`reviewed_fmap_as_finite_support_words_as_type_indexed_bitvec` (both qualifiers
required together; the checker rejects either one missing). The reference
checker reads the tagged declaration's signature, not its proof or body, when
verifying the `BitVec`/`NeZero`/`Type` obligations; it remains syntactic and
does not prove HOL-to-Lean correspondence, so source review must compare the
declaration itself.

**Qualify a word-free HOL dimension used numerically.** Use
`(word_dimension_as_width := width)` only when the HOL declaration takes a
type dimension `(:'a)` but has no word-valued carrier, and uses that dimension
only through its numeric size (`dimindex`/`dimword`). Lean must bind the named
`(width : Nat)` explicitly with `[NeZero width]`; `dimword` becomes `2 ^ width`.
The qualifier is mutually exclusive with `words_as_type_indexed_bitvec` and
requires manifest status `reviewed_word_dimension_as_width`. The reference
checker verifies the Lean binder, positivity discharge, word-free signature,
and exclusivity, but cannot verify that HOL actually has the dimension argument
or uses it only numerically. Source review must check both points, compare the
entire equation and its operator associativity, and record the comparison in
the manifest. The qualifier permits no changed hypotheses or behavior and does
not itself prove cross-language equivalence.

**Qualify two independent word-free dimensions.** Use
`(word_dimensions_as_widths := [t, w])` for a dimension-only real definition
such as original binary_ieee `largest_def` or `threshold_def`. The declaration
must bind exactly two distinct explicit `(t : Nat)` / `(w : Nat)` parameters,
each with its own `[NeZero ...]`, and return Mathlib `ℝ`/`Real` without
word-valued arguments, extra binders, or positivity premises. Keep HOL's two
independent dimensions and compare the entire formula: dimindex is the named
width, dimword is `2 ^ width`, and all UINT_MAX/INT_MAX uses retain the original
dimension. The qualifier permits no fixed-width specialization, real-domain
restriction, changed equation, or cross-language equivalence claim. It is
mutually exclusive with all other representation qualifiers except the
separately reviewed `reals_as_rational_cuts` family marker. Use manifest status
`reviewed_word_dimensions_as_widths`, the identical ordered pair and a local
source-comparison note naming both dimensions. The singular
`word_dimension_as_width` route remains separate and unchanged. Parser,
source/manifest checkers and native attribute export validate this scope and
agreement; none independently proves HOL-to-Lean correspondence.

**Qualify the reviewed binary64 real rendering.** Use
`(reals_as_rational_cuts)` on a tagged declaration whose own source uses a
declaration of the reviewed HOL-standard-library IEEE renderings
(`Flapjack/Misc/MachineIeee.lean`, `Flapjack/Misc/BinaryIeee*.lean`). Those
renderings represent each HOL `real` inside `binary_ieee`/`machine_ieee`
rounding by a Lean `Rat` when the real is rational, and the square root of
`fp64_sqrt` by its rational cut. This is admissible only because HOL's rounding
specification (`float_round_with_flags`, `float_round`, `round`,
`closest_such`, `is_closest`, `threshold`) inspects its real argument only
through order, equality and absolute-difference comparisons with rationals,
which the cut decides exactly, and because the rounded value does not depend
on HOL's choice operator. Agreement with HOL's real-number specification
remains the external assumption of `docs/SOUNDNESS.md` item 8. The qualifier
records that representation only: it authorizes no change to clauses,
hypotheses, conclusions, NaN or flag behavior. `check-hol-refs.py` requires
the qualifier exactly on the tagged declarations whose own source (signature
and body, comments excluded) names a rendering declaration, and rejects it
elsewhere, except for the reviewed bit-only forms `HolFloat`,
`holFloatIsNormal`, `holFloatIsSubnormal`, `holFloatNegate`, `holFloatAbs`,
`holFp64ToFloat`, `holFloatToFp64`, `holFp64Abs`, `holFp64Negate`,
`holFp32ToFloat`, and `holFloatToFp32`.
The checker exempts these forms only while their canonical bodies, namespace,
and unique declaration ownership pass its fail-closed checks; real-dependent
operations still require the qualifier. These checks do not establish
HOL-to-Lean equivalence or replace source review.
A declaration that merely calls a qualified declaration (for
example the wordSem `evaluate` calling `inst`) is a dependent: it does not
carry the qualifier but must record `"inherits_reals_as_rational_cuts": true`
and a note naming the inherited assumption in the theorem map.
`check_hol_ref_export.py` compares that field, in both directions, with the
constant closure computed by `scripts/HolRefExport.lean` (types, and bodies
of definitions, through Flapjack definitions and datatypes; theorem proofs are
not followed). The inherited marker propagates the assumption only; it is
not a review of the untagged definitions on the path. NaN results
(`float_some_qnan`, HOL choice rendered by `Classical.epsilon`) are outside
the qualifier. The status is `reviewed_reals_as_rational_cuts` when no other qualifier
applies; otherwise the status the other qualifiers require is kept and the
manifest records `"reals_as_rational_cuts": true`. The manifest note must
name the qualifier and SOUNDNESS item 8, and it can never be `reviewed_exact`.

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
