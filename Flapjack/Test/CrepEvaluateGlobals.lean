import Flapjack.CrepEvaluate

/-! Regression tests for the `crepEvaluate` global/memory boundary
    (`crepSemScript.sml:111,288-291`).  Globals are a separate finmap:
    `Store` never reaches `LoadGlob`, `StoreGlob` never reaches `Load`, and a
    call entry carries the caller's globals into the callee.  The legacy
    compact evaluator that aliased the two maps is internal to the proof
    suite and is not exposed by `crepEvaluate`. -/

namespace Flapjack.Test.CrepEvaluateGlobals

open Flapjack

def noPrim : CrepPrimitiveHandler Nat := fun _ _ => none

def shm : CrepSharedMemHandler Nat := defaultCrepSharedMemHandler

def state5 : CrepState Nat :=
  { locals := fun _ => none
    memory := fun address => if address = 5 then some 9 else none
    globals := fun address => if address = 5 then some 3 else none }

/-- Projected observation: returned values, the global at 5, and the memory
    word at 5 after the run. -/
def observe (result : Option (CrepControlResult Nat)) :
    Option (List Nat × Option Nat × Option Nat) :=
  result.bind fun result =>
    match result with
    | .returned state values => some (values, state.globals 5, state.memory 5)
    | _ => none

/-- `Store` writes main memory only: `LoadGlob` still reads the old global. -/
example :
    observe (crepEvaluate [] noPrim (noCrepFfi Nat) shm 0 0 10 state5
      (.seq (.store (.const 5) (.const 7))
        (.return [.loadGlob 5]))) = some ([3], some 3, some 7) := by
  decide +kernel

/-- `StoreGlob` writes the globals map only: `Load` still reads old memory. -/
example :
    observe (crepEvaluate [] noPrim (noCrepFfi Nat) shm 0 0 10 state5
      (.seq (.storeGlob 5 (.const 7))
        (.return [.load (.const 5)]))) = some ([9], some 7, some 9) := by
  decide +kernel

/-- A global written by `StoreGlob` is read back by `LoadGlob`. -/
example :
    observe (crepEvaluate [] noPrim (noCrepFfi Nat) shm 0 0 10 state5
      (.seq (.storeGlob 5 (.const 7))
        (.return [.loadGlob 5]))) = some ([7], some 7, some 9) := by
  decide +kernel

/-- Call entry carries the caller's globals into the callee and back. -/
def keepGlobalsFunctions : List (CompiledFunction Nat) :=
  [{ name := "f", params := [], body := .skip, returnShape := .one }]

example :
    observe (crepEvaluate keepGlobalsFunctions noPrim (noCrepFfi Nat) shm
      0 0 10 state5
      (.seq (.storeGlob 5 (.const 7))
        (.seq (.call none "f" [])
          (.return [.loadGlob 5])))) = some ([7], some 7, some 9) := by
  decide +kernel

end Flapjack.Test.CrepEvaluateGlobals
