import Flapjack.Pancake.Proofs.CrepArith.HOLStateMapc

namespace Flapjack.Test.CrepHolStateParity

open Flapjack.Basis.Pure.MlString

private def codeName : MlString := .implode []

private def sampleCode : HolFiniteMapExact MlString
    (List Nat × CrepProgHOL 8) where
  lookup name := if name = codeName then some ([], .skip) else none
  finiteSupport := by
    refine ⟨[codeName], ?_⟩
    intro name hlookup
    by_cases h : name = codeName
    · simp [h]
    · simp [h] at hlookup

private def sampleMapc
    (entry : MlString × (List Nat × CrepProgHOL 8)) :
    List Nat × CrepProgHOL 8 := (entry.2.1, .tick)

theorem mapc_lookup_fixture :
    (sampleCode.map2 sampleMapc).lookup codeName = some ([], .tick) := by
  simp [HolFiniteMapExact.map2, sampleCode, sampleMapc, codeName]

def parityGuard : Bool :=
  match (sampleCode.map2 sampleMapc).lookup codeName with
  | some (parameters, .tick) => parameters.isEmpty
  | _ => false

#eval parityGuard

example : parityGuard = true := by rfl

/-- The source evaluator sees identical observable states across HOL `mapc`.
The direct HOL evidence is in `crep_state_mapc_probe.out`. -/
example {width : Nat} [NeZero width] {ffiState : Type}
    (f : MlString × (List Nat × CrepProgHOL width) →
      List Nat × CrepProgHOL width)
    (state : CrepSemHOLState width ffiState)
    (expression : CrepExp (Fin width → Bool)) :
    evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        (state.mapc f).toExpressionEvaluatorState expression =
      evalCrepHolFiniteWordSourceExp (instFinHolFiniteDimension (width := width))
        state.toExpressionEvaluatorState expression :=
  evalCrepHolFiniteWordSourceExp_mapc_projection f state expression

/-! ## Finite-support map operation rows

Direct rows for `FEMPTY` (`empty`), `FUPDATE` (`update`), `FUPDATE_LIST`
(`updateList`), domain subtraction (`erase`), and `res_var` (`resVar`) on the
finite-support carrier. These pin the observable lookup behavior required by
`crepSemScript.sml:55,61,66,71,163`. -/

private def sampleLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.updateList [(3, .word 7), (5, .word 9)]

example : sampleLocals.lookup 3 = some (.word 7) := by decide

example : sampleLocals.lookup 5 = some (.word 9) := by decide

example : sampleLocals.lookup 4 = none := by decide

example : (sampleLocals.update (3, .word 11)).lookup 3 = some (.word 11) := by decide

example : (sampleLocals.update (3, .word 11)).lookup 5 = some (.word 9) := by decide

example : (sampleLocals.resVar (5, none)).lookup 5 = none := by decide

example : (sampleLocals.resVar (5, some (.word 13))).lookup 5 = some (.word 13) := by
  decide

example :
    (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab 8)).lookup 3 = none := rfl

/-! ### HOL-equality (`=`) forms for the polymorphic `res_var_def` port

The tagged `resVarEq`/`updateEq`/`eraseEq` use `DecidableEq` (HOL `=`) rather
than Boolean `BEq`; the rows below mirror the direct HOL rows
`res_var_delete_hit`/`res_var_update_hit` in `crep_res_var_probe.out`. -/

example : (sampleLocals.resVarEq (5, none)).lookup 5 = none := by decide

example : (sampleLocals.resVarEq (5, none)).lookup 3 = some (.word 7) := by decide

example : (sampleLocals.resVarEq (5, some (.word 13))).lookup 5 = some (.word 13) := by
  decide

example : (sampleLocals.updateEq (4, .word 21)).lookup 4 = some (.word 21) := by decide

example : (sampleLocals.eraseEq 3).lookup 3 = none := by decide

example : (sampleLocals.eraseEq 3).lookup 5 = some (.word 9) := by decide

/-! ## Kernel-checked projection bridges

Each finite-support state update projects into the executable `CrepHolState`
helper (`CrepSem.lean`) under `toBitVecEvaluatorState`. The statement-level
examples below apply the bridges; the bridge proofs themselves live beside the
helpers in `CrepSem/HOLState.lean`. -/

example {width : Nat} [NeZero width] {ffiState : Type} (name : Nat)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.setVar name value state).toBitVecEvaluatorState =
      setCrepHolVarW name value.toPanWordLab state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_setVar name value state

example {width : Nat} [NeZero width] {ffiState : Type} (key : BitVec 5)
    (value : HolWordLab width) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.setGlobals key value state).toBitVecEvaluatorState =
      setCrepHolGlobalsW key value.toPanWordLab state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_setGlobals key value state

example {width : Nat} [NeZero width] {ffiState : Type}
    (varargs : List (Nat × HolWordLab width)) (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.updLocals varargs state).toBitVecEvaluatorState =
      updCrepHolLocalsW (varargs.map (fun entry => (entry.1, entry.2.toPanWordLab)))
        state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_updLocals varargs state

example {width : Nat} [NeZero width] {ffiState : Type} (state : CrepSemHOLState width ffiState) :
    (CrepSemHOLState.emptyLocals state).toBitVecEvaluatorState =
      emptyCrepHolLocalsW state.toBitVecEvaluatorState :=
  CrepSemHOLState.toBitVecEvaluatorState_emptyLocals state

example {width : Nat} [NeZero width]
    (map : HolFiniteMapExact Nat (HolWordLab width)) (key : Nat)
    (value : Option (HolWordLab width)) :
    (fun k => ((CrepSemHOLState.resVar map (key, value)).lookup k).map
        HolWordLab.toPanWordLab) =
      resVarW (fun k => (map.lookup k).map HolWordLab.toPanWordLab)
        (key, value.map HolWordLab.toPanWordLab) :=
  CrepSemHOLState.lookup_resVarW map key value

end Flapjack.Test.CrepHolStateParity
