# Dependency inventory: `evaluateDecls` (source declaration evaluator)

Bead: `flapjack-pxn.18.3.6.1` (child of the `flapjack-pxn.18.3.6` audit).
Scope: the **direct** production calls and datatypes reachable from the tagged
`evaluateDecls`, paired with their HOL definitions, plus the HOL-defined calls
traced one layer deep. This is a review-frontier triage, not a proof: it records
what is tagged `reviewed_exact`, what is unreviewed (and thus a *possible*
mismatch until clause-by-clause evidence exists), a representation refinement,
or a confirmed mismatch, and links a child bead for every remaining node. A
classification of "unreviewed" does **not** assert exactness — it only means no
review has been done yet.

## Root

| Lean | HOL | Status |
| --- | --- | --- |
| `Flapjack.evaluateDecls` (`Flapjack/Pancake/Semantics/PanSem.lean:1447`) | `evaluate_decls_def` (`cakeml/pancake/semantics/panSemScript.sml:813`) | exact / tagged `@[hol ... "evaluate_decls_def"]`, `reviewed_exact` |

The definition's four declaration branches (`Name`, `Decl`, `Function`,
`ExnDecl`) and the `[]` base case match HOL clause-for-clause. The `Name` case is
a no-op, the `Decl` case evaluates with empty locals and checks the declared
shape, the `Function` case checks parameter/return shapes and updates `code`,
and the `ExnDecl` case rejects a duplicate exception and checks the shape.

## Direct dependencies

| Dependency | Lean (file:line) | HOL counterpart | Classification | Bead |
| --- | --- | --- | --- | --- |
| `evalPanValueExp` | `Flapjack/PanValues.lean:1242` | `eval_def` (`panSemScript.sml:209`) | **unreviewed / possible mismatch** (no clause-by-clause evidence for the `NStruct`, memory/domain, or word-operation cases) | `.18.3.6.2` |
| `isWfShape` | `Flapjack/Pancake/PanStatic.lean:142` | `is_wf_shape_def` (`panLangScript.sml:139`) | **reviewed, not exact** (clauses align: `One`/`Comb`=EVERY/`Named`=presence; but `StructInfo` has an extra `shapedFields` field vs HOL `struct_info`, and `Named` uses `lookupInfo`'s canonical String `==` rather than HOL `ALOOKUP` with `=`). Direct HOL oracle: `pan_lang_wf_shape_probe` | `.18.3.6.7` (+ carrier `.18.3.5.5`) |
| `panValueShape` | `Flapjack/PanValues.lean:491` | `shape_of_def` (`panSemScript.sml:80`) | **mismatch**: unused `context` parameter; duplicate of the tagged `panSemShapeOf` (`PanSem.lean:36`) | `.18.3.6.4` |
| `panShapeMatches` | `Flapjack/PanValues.lean:1039` | HOL `=` on `Shape` (`sh = shape_of res`) | **representation**: structural `Bool` using `==` for `Named` | `.18.3.6.4` |
| `lookupInfo` | `Flapjack/Pancake/PanStatic.lean:64` | `alist$ALOOKUP` / `FLOOKUP` | **unreviewed** (key-polymorphic `[BEq κ]`; needs review to establish `==` reflects HOL `=`) | `.18.3.6.5` |
| `panSemDeclUpdateGlobal` | `Flapjack/Pancake/Semantics/PanSem.lean:1428` | `globals |+ (v,res)` (`FUPDATE` on a finite map) | **representation**: total function vs finite map | `.18.3.6.5` |
| `panSemDeclUpdateInfo` | `Flapjack/Pancake/Semantics/PanSem.lean:1421` | `code |+ ...` / `eshapes |+ ...` (sptree update) | **representation**: association list vs `num_map` | `.18.3.6.5` |
| `Decl` | `Flapjack/Pancake/PanLang.lean:220` | `panLang$decl` datatype | datatype | existing `.18.3.5.5` |
| `Shape` | `Flapjack/Pancake/PanLang.lean:21` | `panLang$shape` datatype | datatype | existing `.18.3.5.2` |
| `Exp` (inside `.decl`) | `Flapjack/Pancake/PanLang.lean:135` | `panLang$exp` datatype | datatype | existing `.18.3.5.3` |
| `Prog` (inside `.function`) | `Flapjack/Pancake/PanLang.lean` | `panLang$prog` datatype | datatype | existing `.18.3.5.4` |
| `PanValue` | `Flapjack/PanValues.lean:29` | `word_lab` datatype | datatype | `.18.3.6.6` |
| `PanSemDeclarationState` | `Flapjack/Pancake/Semantics/PanSem.lean:86` | `panSem$state` record | representation: production record split (runtime/base, `code`/`eshapes` maps) | note (below) |
| `PanSemFunctionEntry` | `Flapjack/Pancake/Semantics/PanSem.lean:74` | `(params,(body,return))` tuple in the `code` map | representation: named record vs tuple | note (below) |

## One-layer frontier of HOL-defined calls

- `eval_def` (`panSemScript.sml:209`) — untagged in Lean (`.18.3.6.2`). It calls:
  `OPT_MMAP` (Lean carrier `List.mapM`; tagged `optMmapEqSome` in
  `Flapjack/Pancake/Semantics/PanCommonProps.lean`), `shape_of` (tagged
  `panSemShapeOf`), `ALOOKUP` (`lookupInfo`, `.18.3.6.5`), `UNZIP`, `EVERY`,
  `LENGTH`, `EL`, and itself recursively on subexpressions. Its `NStruct` case
  additionally checks `field_names' = field_names` and
  `EVERY (\(s,v). s = shape_of v) (ZIP ...)`.
- `is_wf_shape_def` (`panLangScript.sml:139`) — reviewed in `.18.3.6.3`:
  production `isWfShape` clauses align, but it is not statement-exact (carrier
  plus `lookupInfo` equality); the exact HOL-shaped Shape-level port is tracked
  by `.18.3.6.7`. It calls `EVERY` and `ALOOKUP` (`lookupInfo`).
- `shape_of_def` (`panSemScript.sml:80`) — tagged exact as `panSemShapeOf`; the
  behavior used by `evaluateDecls` also flows through the untagged
  `panValueShape`/`panShapeMatches` pair (`.18.3.6.4`).
- `FLOOKUP`/`FUPDATE` on `code`, `eshapes`, `globals` — represented by
  association lists and total functions (`.18.3.6.5`); the sibling
  finite-map/key-equality gap is tracked by `flapjack-pxn.18.5.5.19`.

## Representation notes (terminal unless a child bead is listed)

- `PanSemDeclarationState` splits HOL `panSem$state` into a `runtime`
  (`structs`/`globals`/`memory`/…) plus `code`, `eshapes`, `memoryAccess`,
  `contracts`, `memoryHandler`. This is the production state shape used by the
  tracer/runtime; the source-field projections are reviewed as part of the
  `evaluateDecls` port but the record layout itself is a documented refinement,
  not an exact HOL datatype.
- `PanSemFunctionEntry` names the tuple stored in HOL's `code` map; the
  `code`/`eshapes` maps are association lists (`InfoMap`) rather than HOL
  `num_map`/finite maps.
- External primitives reachable through `eval` (word ops, `PanCmp`, shifts,
  `AndOp`/`OrOp`/`HXor`) are the assumed typeclass operations; they are leaves
  of this review and are not re-audited here.

## Child beads (parent `flapjack-pxn.18.3.6`)

- `.18.3.6.2` — review the production expression evaluator against HOL `eval_def`; tag only if review establishes exactness.
- `.18.3.6.3` — reviewed the production `Shape` predicate against HOL `is_wf_shape_def`: clauses align, but not statement-exact (carrier/equality); exact port tracked by `.18.3.6.7`.
- `.18.3.6.7` — port the exact HOL-shaped `is_wf_shape_def` Shape-level predicate over `StructContextHOL`.
- `.18.3.6.4` — align `evaluateDecls` shape comparison with tagged `panSemShapeOf` / HOL shape equality.
- `.18.3.6.5` — review finite-map lookup/update helpers (`lookupInfo`, `panSemDeclUpdateGlobal`, `panSemDeclUpdateInfo`).
- `.18.3.6.6` — review/tag the `word_lab` value datatype (`PanValue`).

Datatype reviews for `Decl`, `Shape`, `Exp`, `prog` are owned by the existing
`flapjack-pxn.18.3.5.2`–`.18.3.5.5` beads.