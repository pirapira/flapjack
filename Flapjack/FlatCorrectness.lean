import Flapjack.Semantics
import Flapjack.PanMemory

/-!
Small correctness bridges for the CakeML-faithful flat source memory model.

The first bridge deliberately targets the structured store/load fragment.  It
connects the existing `pan_to_crep` lowering and Crepe memory evaluator to
the flat Pancake evaluator, whose memory cells contain words rather than
whole structured values.
-/

namespace Flapjack

def flatContractDomain : PanMemoryDomain Nat :=
  fun _ => true

def flatContractMemory : PanFlatMemory Nat :=
  fun _ => none

def flatContractNoFfi : PanFlatFfiHandler Nat :=
  fun _ _ _ _ _ locals => some locals

def flatContractReturnShapes : InfoMap Shape :=
  [("badReturn", .one), ("main", .one)]

def flatContractExceptionShapes : InfoMap Shape :=
  [("E", .comb [.one, .one])]

def flatContractEnvironment : Option PanValueCallContracts :=
  some (PanValueCallContracts.mk flatContractReturnShapes flatContractExceptionShapes [])

example :
    (evalPanFlatProgWithCallsAndFfi []
      [("badReturn", [], .return (.rStruct [.const 1, .const 2])),
       ("main", [], .seq (.call none "badReturn" []) (.return (.const 0)))]
      flatContractNoFfi 0 100 1 30 (fun _ => none) (fun _ => none)
      flatContractDomain flatContractMemory
      (.seq (.call none "badReturn" []) (.return (.const 0)))
      (contracts := flatContractEnvironment)).isNone = true := by
  decide +kernel

example :
    (evalPanFlatProgWithCallsAndFfi []
      [("badRaise", [], .raise "E" (.const 1)),
       ("main", [], .seq (.call none "badRaise" []) (.return (.const 0)))]
      flatContractNoFfi 0 100 1 30 (fun _ => none) (fun _ => none)
      flatContractDomain flatContractMemory
      (.seq (.call none "badRaise" []) (.return (.const 0)))
      (contracts := some (PanValueCallContracts.mk
        [("main", .one)] flatContractExceptionShapes []))).isNone = true := by
  native_decide

example :
    (evalPanFlatProgWithCallsAndFfi []
      [("raiseGood", [], .raise "E" (.const 1)),
       ("main", [], .skip)]
      flatContractNoFfi 0 100 1 30 (fun _ => none) (fun _ => none)
      flatContractDomain flatContractMemory
      (.call (some (none, some ("E", "missing", .skip)))
        "raiseGood" [])
      (contracts := some (PanValueCallContracts.mk
        [("main", .one), ("raiseGood", .one)]
        [("E", .one)] []))).isNone = true := by
  decide +kernel

end Flapjack
