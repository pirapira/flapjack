import Flapjack.Pancake.Semantics.CrepSem.StateWidthModel

/-!
Type-shape fixtures for the width-indexed Crep state model. These examples
exercise its lookups, word cells, and FFI field. They are not direct HOL
parity checks; the representation limitations are documented beside the
model in `Flapjack.Pancake.Semantics.CrepSem.StateWidthModel`.
-/

namespace Flapjack.Test.CrepSemStateWidthModel

open Flapjack
open Flapjack.Basis.Pure.MlString

private def identityOracle : HolOracle Unit :=
  fun _ state _ bytes => .ret state bytes

private def locals8 : CrepHOLFiniteMap Nat (HolWordLab 8) :=
  ⟨fun key => if key = 2 then some (.word 17) else none, [2], by
    intro key hlookup
    by_cases hkey : key = 2
    · simp [hkey]
    · simp [hkey] at hlookup
  ⟩

private def state8 : CrepSemStateWidthModel 8 Unit :=
  { locals := locals8
    globals := CrepHOLFiniteMap.empty
    code := CrepHOLFiniteMap.empty
    memory := fun word => .word word
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 9
    be := true
    ffi := initialHolFfiState identityOracle ()
    baseAddr := 3
    topAddr := 250 }

example : state8.locals.lookup 2 = some (.word 17) := by simp [state8, locals8]
example : state8.locals.lookup 4 = none := by
  apply CrepHOLFiniteMap.lookup_eq_none_of_not_mem_support
  decide
example : state8.globals.lookup (BitVec.ofNat 5 2) = none := rfl
example (name : MlString) : state8.code.lookup name = none := rfl
example : state8.memory (BitVec.ofNat 8 7) = .word (BitVec.ofNat 8 7) := rfl
example : state8.memaddrs (BitVec.ofNat 8 7) = False := rfl
example : state8.shMemaddrs (BitVec.ofNat 8 7) = False := rfl
example : state8.clock = 9 := rfl
example : state8.be = true := rfl
example : state8.ffi.ffiState = () := rfl
example : state8.baseAddr = 3 := rfl
example : state8.topAddr = 250 := rfl

end Flapjack.Test.CrepSemStateWidthModel
