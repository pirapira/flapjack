import Flapjack.RiscV.CorrectnessWordToStack

/-! Regression for state-threaded FFI lowering. -/

namespace Flapjack.RiscV

def statefulFfiConfig : WordStackConfig :=
  { locations := [(0, .register 4), (1, .register 5),
      (2, .register 6), (3, .register 7)]
    scratch := 31
    stackBase := 10 }

def statefulFfiBitmaps : WordStackBitmapState :=
  { data := [4, 12]
    length := 2 }

/-! Source-shaped Cake FFI uses stack ABI registers 1--4.  The Lab boundary
    maps those once to hardware x10--x13; using the historical 10--13 names
    here would instead map the suffix onto Cake's scratch registers. -/
def cakeFfiAbiShape : Bool :=
  match wordStackFfiCake (α := Nat)
      { locations := [(0, .register 1), (1, .register 2),
          (2, .register 3), (3, .register 4)]
        scratch := 31
        stackBase := 0
        abiBase := 1
        abiStride := 1 }
      "halt" 0 1 2 3 with
  | some (.ffi "halt" 1 2 3 4 0) => true
  | _ => false

#guard cakeFfiAbiShape

example :
    wordToStackProgNatWithBitmapBuilder statefulFfiConfig (fun live => live)
      2 26 4 64 none statefulFfiBitmaps
      (.ffi "echo" 0 1 2 3 ([], [4]) : WordProg Nat) =
      some (.seq (.arith .or 10 4 4)
        (.seq (.arith .or 11 5 5)
          (.seq (.arith .or 12 6 6)
            (.seq (.arith .or 13 7 7)
              (.ffi "echo" 10 11 12 13 0)))), statefulFfiBitmaps) := by
  apply wordToStackProgNatWithBitmapBuilder_ffi
    (config := statefulFfiConfig) (bitmapBuilder := fun live => live)
    (registerCount := 2) (bitmapRegister := 26) (frameSlots := 4)
    (wordBits := 64) (storeConstsStub := none)
    (state := statefulFfiBitmaps) (function := "echo")
    (configuration := 0) (configurationLength := 1) (array := 2)
    (arrayLength := 3) (live := ([], [4]))
    (configurationMove := .arith .or 10 4 4)
    (configurationLengthMove := .arith .or 11 5 5)
    (arrayMove := .arith .or 12 6 6)
    (arrayLengthMove := .arith .or 13 7 7)
  all_goals simp [statefulFfiConfig,
    wordStackFfiSourcesSafe, wordStackFfiSourceSafe,
    wordStackFfiRegisterSafe, wordStackFfiMove, wordStackLocation,
    lookupNatInfo]

end Flapjack.RiscV
