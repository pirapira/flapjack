import Flapjack.Compiler.Backend.StackRemove

/-!
Kernel-checked parity for the stackLang instruction overloads and `halt_inst`
against the direct HOL EVAL oracle `stack_lang_inst_overloads_probe`.  HOL prints
the overloads back with overload notation, so the probe rows compare each
application to the explicit constructor term (all `T`); the `example`s below are
the corresponding definitional equalities.

The implementations are stated over the exact width-indexed carrier
`StackLang.HolProg 8` (faithful `MlString` FFI field and exact `HolInst`/
`HolRegImm`/`HolAddr` payload mirrors), so they carry exact `@[hol]` tags.
-/

namespace Flapjack.Test.StackLangInstOverloadsParity

open Flapjack
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

private abbrev W := BitVec 8

/-- Structural tag for the `const_inst` shape (`Inst (Const r w)`). -/
private def isConstInst {width : Nat} [NeZero width] : HolProg width → Bool
  | .inst (.const _ _) => true
  | _ => false

/-- Structural tag for the `halt_inst` shape (`Seq (Inst (Const 1 w)) (Halt 1)`). -/
private def isHaltInst {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq (.inst (.const 1 _)) (.halt 1) => true
  | _ => false

example : (leftShiftInst (width := 8) 2 3 : HolProg 8) =
    (.inst (.arith (.shift .lsl 2 2 (.imm (BitVec.ofNat 8 3)))) :
      HolProg 8) := rfl

example : (rightShiftInst (width := 8) 2 3 : HolProg 8) =
    (.inst (.arith (.shift .lsr 2 2 (.imm (BitVec.ofNat 8 3)))) :
      HolProg 8) := rfl

example : (constInst (width := 8) 1 (BitVec.ofNat 8 0) : HolProg 8) =
    (.inst (.const 1 (BitVec.ofNat 8 0)) : HolProg 8) := rfl

example : (loadInst (width := 8) 2 3 : HolProg 8) =
    (.inst (.mem .load 2 (.addr 3 0)) : HolProg 8) := rfl

example : (storeInst (width := 8) 2 3 : HolProg 8) =
    (.inst (.mem .store 2 (.addr 3 0)) : HolProg 8) := rfl

example : (haltInst (width := 8) (BitVec.ofNat 8 0) : HolProg 8) =
    (.seq (.inst (.const 1 (BitVec.ofNat 8 0))) (.halt 1) : HolProg 8) :=
  rfl

private def guard : Bool :=
  isConstInst (constInst (width := 8) 1 (BitVec.ofNat 8 0)) &&
    isHaltInst (haltInst (width := 8) (BitVec.ofNat 8 0))

#guard guard

def runChecks : IO Bool := do
  IO.println "PASS stackLang instruction overloads and halt_inst match the HOL oracle"
  pure guard

end Flapjack.Test.StackLangInstOverloadsParity