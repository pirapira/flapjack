import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepProps

/-!
Direct runtime checks against `scripts/hol-probes/crep_eval_probe.out` and
`crep_store_global_probe.out`. Cake's `crepSem` globals are indexed by `5 word`
and store `word_lab` cells; these checks cover a nonempty read, a missing key,
an insert that preserves a sibling, and a read after `StoreGlob`.
-/

namespace Flapjack.Test.CrepGlobalShapeParity

open Flapjack

def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0
def noNatDomain : Nat → Bool := fun _ => false

def globalState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := updateCrepRuntimeGlobal
      (updateCrepRuntimeGlobal (fun _ => none) (4 : BitVec 5) (.word 11))
      (8 : BitVec 5) (.word 9)
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

def runtimeHandler : CrepRuntimeFfiHandler Nat Unit Unit :=
  fun _ state => CrepRuntimeFfiResponse.returned state []

def noPrimitive : CrepPrimitiveHandler Nat := fun _ _ => none

/- HOL crep_store_global_probe: set_globals_direct has a hit at global 4,
   preserves the local 3, and leaves local 9 absent. This checks the observable
   update behavior; it does not claim the whole Lean runtime-state type is a
   port of HOL crepSem$state. -/
def directUpdateState : CrepRuntimeState Nat Unit :=
  { globalState with locals := fun name => if name == 3 then some (.word 7) else none }

#guard let state := setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState
       state.globals (4 : BitVec 5) == some (.word 22) &&
       state.locals 3 == some (.word 7) &&
       (state.locals 9).isNone

/- HOL crep_eval_probe: eval_global_hit=SOME (Word 11w). -/
#guard evalCrepRuntimeExp globalState (.loadGlob (4 : BitVec 5)) == some 11
#guard evalCrepRuntimeExp globalState (.loadGlob (36 : BitVec 5)) == some 11

/- HOL crep_eval_probe: eval_global_miss=NONE. -/
#guard (evalCrepRuntimeExp globalState (.loadGlob (12 : BitVec 5))).isNone

/- HOL crep_store_global_probe: StoreGlob inserts the wrapped cell and leaves
   the unrelated global at address eight unchanged. -/
#guard match evalCrepRuntimeProg runtimeHandler noPrimitive 2 globalState
    (.storeGlob (4 : BitVec 5) (.const 22)) with
  | some (.normal, state) =>
      state.globals (4 : BitVec 5) == some (.word 22) &&
      state.globals (8 : BitVec 5) == some (.word 9)
  | _ => false

/- HOL crep_store_global_probe: storing then evaluating LoadGlob returns the
   word_lab value as a Crep expression word. -/
#guard match evalCrepRuntimeProg runtimeHandler noPrimitive 3 globalState
    (.seq (.storeGlob (4 : BitVec 5) (.const 11)) .skip) with
  | some (.normal, state) =>
      evalCrepRuntimeExp state (.loadGlob (4 : BitVec 5)) == some 11
  | _ => false

/- HOL `crepSem$set_globals_def` (crepSemScript.sml:61) is the record update
   `s with globals := s.globals |+ (gv,w)`; the tagged `setCrepRuntimeGlobals`
   has exactly that body written through the HOL finite-map `FUPDATE`. -/
example :
    setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState =
      { directUpdateState with
        globals := FUPDATE directUpdateState.globals ((4 : BitVec 5), .word 22) } :=
  setCrepRuntimeGlobals_eq_FUPDATE (4 : BitVec 5) (.word 22) directUpdateState

/- HOL `crepProps$FLOOKUP_set_globals` (crepPropsScript.sml:297): writing a
   global cell leaves every local lookup unchanged. -/
example :
    FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 3 =
      FLOOKUP directUpdateState.locals 3 :=
  flookup_setCrepRuntimeGlobals_locals (4 : BitVec 5) (.word 22) directUpdateState 3

#guard FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 3 ==
    some (.word 7) &&
  FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 9 == none

end Flapjack.Test.CrepGlobalShapeParity
