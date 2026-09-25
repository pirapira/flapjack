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

Eleven false tags have been withdrawn: four in `PanSem.lean` (`flapjack-0lj.1`),
four `HolValue`-dependent declarations (`flapjack-0lj.2`), `panMemLoadHOL`
(`flapjack-9x4`), and `decClockHOL`/`fixClockHOL`
(`flapjack-pxn.18.4.3.77.11.1`). Their definitions remain documented
Flapjack-specific infrastructure pending exact MlString carriers. The rows
below are the conservative review frontier, not claims of completed ports.

## Carrier-safe tags (word payload / `OpSize` only)

| Lean module:line | HOL name | Lean declaration | carrier |
|---|---|---|---|
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

## Withdrawn (String/MlString carrier review)

| Lean module:line | HOL name | offending carrier(s) | tracking |
|---|---|---|---|
| `Pancake/Semantics/PanSem.lean:76` | `word_lab` | `HolWordLab width` admits `width = 0`; HOL `'a word` requires positive `dimindex`. Constructor arity/field type otherwise match | withdrawn (`flapjack-0lj.5`; positive-width `[NeZero width]` inductive pending, blocked by the `PanSemStateEval.lean` edit freeze and the `CrepLocalsExact`/`HolValue` propagation) |
| `Pancake/Semantics/PanSem/Primop.lean` | `flatten_def` | `PanValue` (`nStruct` names `FieldName`/`StructName` `String`; `.word` payload `α` vs `'a word_lab`) | withdrawn (`flapjack-0lj.3`); exact MlString port landed as `flattenHOL` (`PanSem/ValueHOL.lean`) |
| `Pancake/Semantics/PanSem/Primop.lean` | `pan_primop_def` | `PanValue` (same carrier mismatch; body ignores names but the quantifier is not exact) | withdrawn (`flapjack-0lj.3`); exact MlString port landed as `panPrimopHOLExact` (`PanSem/ValueHOL.lean`) |

`PanSem/ValueHOL.lean` adds the positive-width exact `ValueHOL`
(`[NeZero width]` on the inductive, mirroring `CrepProgHOL`), with `flattenHOL`
and `panPrimopHOLExact` tagged and their direct-HOL oracle rows reproduced by
`Flapjack/Test/PanSemValueHOLParity.lean`. `ValueHOL.val` still wraps the
generic `HolWordLab`, whose Datatype tag remains withheld (`flapjack-0lj.5`).

## Resolution order

1. Land the exact MlString syntax/state carriers (`ShapeHOL` done by
   `flapjack-deepseek-three`; MlString-keyed context/state pending
   `flapjack-pxn.18.3.5.8`).
2. Retarget the withdrawn `HolValue`-dependent definitions once their exact
   MlString-backed carriers exist (`flapjack-0lj`, `flapjack-9x4`).
3. Retarget `lookup_code_def` (`flapjack-4w9`).
4. Re-add the withdrawn name-ignoring tags (`flatten_def`, `pan_primop_def`)
   only once stated over the exact MlString/HolWordLab carriers
   (`flapjack-0lj.3`); name-ignoring behavior is not carrier equivalence.
