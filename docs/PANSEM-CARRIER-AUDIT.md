# panSem HOL tag carrier audit (P0 String/MlString holds)

Status: working document for the open P0 carrier holds
(`flapjack-0lj` HolValue `v`, `flapjack-9x4` `panMemLoadHOL`, `flapjack-4w9`
`lookup_code`). It records, for every tag over
`cakeml/pancake/semantics/panSemScript.sml`, whether the Lean declaration is
carrier-safe or transitively uses a String-backed carrier while HOL uses
`mlstring`.

Carrier mismatch: HOL `stcname`/`fldname`/`varname`/`funname`/`eid` are
`mlstring`; the Lean production counterparts (`StructName`, `FieldName`,
`VarName`, `FunName`, `ExceptionId`) are `String`. Consequently any tag whose
declaration mentions `HolValue` (`nStruct`/`NStruct` name/field are `String`),
`StructContextHOL`, `Shape` (`named` carries `StructName = String`),
`PanSemHolState`, `PanSemState`, or a `VarName`/`FunName`/`ExceptionId`-keyed
map is **held** until the exact MlString carriers land (see
`Flapjack/Pancake/PanLang/Shape.lean` `ShapeHOL`, and the MlString state
carrier work under `flapjack-pxn.18.3.5.8`).

This document records the review frontier. Two sets of false tags have been
withdrawn so far:

* the four `PanSem.lean` tags for `v`, `shape_of_def` (`panSemShapeOf`),
  `empty_locals_def`, and `evaluate_decls_def`, withdrawn in commit `7dd5e7f7b`
  (`flapjack-0lj.1`);
* the four `HolValue`/`String`-dependent tags `holShapeOf`, `holValueIsWord`,
  `evalHOL`, and `panSemLookupCodeHOL`, withdrawn under `flapjack-0lj.2`
  (untagged with local caveats, manifest/type-lock updated).

Their definitions remain as documented Flapjack-specific infrastructure until
exact MlString carriers are ported; the rows below record their pre-withdrawal
locations.

## Carrier-safe tags (word payload / `OpSize` only)

| Lean module:line | HOL name | Lean declaration | carrier |
|---|---|---|---|
| `Pancake/Semantics/PanSem.lean:67` | `word_lab` | `HolWordLab` | `BitVec width` (word payload) |
| `Pancake/Semantics/PanSemStateEval.lean:164` | `mem_load_byte_def` | `panMemLoadByteHOL` | `HolWordLab`/`RiscV.Word` |
| `Pancake/Semantics/PanSemStateEval.lean:183` | `mem_load_32_def` | `panMemLoad32HOL` | `HolWordLab`/`RiscV.Word` |
| `Pancake/Semantics/PanSemStateEval.lean:228` | `mem_store_byte_def` | `memStoreByteAuxHOL` | `HolWordLab`/`RiscV.Word` |
| `Pancake/Semantics/PanSemStateEval.lean:251` | `write_bytearray_def` | `writeBytearrayHOL` | `HolWordLab`/`RiscV.Word` |
| `Pancake/Semantics/PanSemStateEval.lean:292` | `mem_store_def` | `panMemStoreHOL` | `HolWordLab` |
| `Pancake/Semantics/PanSemStateEval.lean:301` | `mem_stores_def` | `panMemStoresHOL` | `HolWordLab` |
| `Pancake/Semantics/PanSemStateEval.lean:1219` | `isWord_def` | `isWordHOL` | `HolWordLab` |
| `Pancake/Semantics/PanSemStateEval.lean:1228` | `theWord_def` | `theWordHOL` | `HolWordLab` |
| `Pancake/Semantics/PanSemStateEval.lean:1339` | `pan_op_def` | `panOpHOL` | `RiscV.Word` |
| `Pancake/Semantics/PanSemStateEval.lean:2626` | `nb_op_def` | `nbOpHOL` | `OpSize` |

Note: `panMemLoadByteHOL`/`panMemLoad32HOL` are also inside the separate
`flapjack-9x4` positive-width audit; their carrier is word-only and unaffected
by the name mismatch.

## Tags held by the String/MlString carrier holds

| Lean module:line | HOL name | offending carrier(s) | tracking |
|---|---|---|---|
| `Pancake/Semantics/PanSem.lean:95` | `v` | `HolValue.nStruct name : StructName`, `fields : List (FieldName × …)` | withdrawn (`flapjack-0lj.1`, `7dd5e7f7b`) |
| `Pancake/Semantics/PanSemStateEval.lean:1369` | `eval_def` | returns `HolValue`; `PanSemHolState` (structs, code, eshapes) | withdrawn (`flapjack-0lj.2`) |
| `Pancake/Semantics/PanSemStateEval.lean:361` | `mem_load_def` | `StructContextHOL`, `HolValue.nStruct` | `flapjack-9x4` |
| `Pancake/Semantics/PanSem.lean:36` | `shape_of_def` | returns `Shape` (`named` = `StructName`) | withdrawn (`flapjack-0lj.1`, `7dd5e7f7b`) |
| `Pancake/Semantics/PanSemStateEval.lean:1201` | `shape_of_def` | returns `Shape` (`named` = `StructName`) | withdrawn (`flapjack-0lj.2`) |
| `Pancake/Semantics/PanSemStateEval.lean:1211` | `isValWord_def` | `HolValue` | withdrawn (`flapjack-0lj.2`) |
| `Pancake/Semantics/PanSem/LookupCode.lean:37` | `lookup_code_def` | `FunName`-keyed code map | withdrawn (`flapjack-0lj.2`; retarget `flapjack-4w9`) |
| `Pancake/Semantics/PanSem.lean:24` | `empty_locals_def` | `PanSemState` (`StructContext`, `VarName`) | withdrawn (`flapjack-0lj.1`, `7dd5e7f7b`) |
| `Pancake/Semantics/PanSem.lean:2421` | `evaluate_decls_def` | `PanSemState` | withdrawn (`flapjack-0lj.1`, `7dd5e7f7b`) |
| `Pancake/Semantics/PanSem/TotalSteps.lean:1058` | `dec_clock_def` | `PanSemHolState` | review (clock-only body) |
| `Pancake/Semantics/PanSem/TotalSteps.lean:1067` | `fix_clock_def` | `PanSemHolState` | review (clock-only body) |
| `Pancake/Semantics/PanSem/Primop.lean:16` | `flatten_def` | `PanValue` (`nStruct` names `String`) | review (name-ignoring body) |
| `Pancake/Semantics/PanSem/Primop.lean:48` | `pan_primop_def` | `PanValue` (`nStruct` names `String`) | review (name-ignoring body) |

## Resolution order

1. Land the exact MlString syntax/state carriers (`ShapeHOL` done by
   `flapjack-deepseek-three`; MlString-keyed context/state pending
   `flapjack-pxn.18.3.5.8`).
2. Withdraw or retarget the `v`, `eval_def`, `mem_load_def`, `shape_of_def`,
   `isValWord_def` tags once a `HolValue`-equivalent over `MlString` exists
   (`flapjack-0lj`).
3. Retarget `lookup_code_def` (`flapjack-4w9`).
4. Re-review the clock-only and name-ignoring tags (`dec_clock_def`,
   `fix_clock_def`, `flatten_def`, `pan_primop_def`, `empty_locals_def`,
   `evaluate_decls_def`) against the landed exact carriers; do not assume the
   strict transitive reading without a decision from the reviewer.
