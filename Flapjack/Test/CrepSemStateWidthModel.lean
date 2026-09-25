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

private def state8 : CrepSemStateWidthModel 8 Unit :=
  { locals := fun _ => none
    globals := fun _ => none
    code := fun _ => none
    memory := fun word => .word word
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 9
    be := true
    ffi := initialHolFfiState identityOracle ()
    baseAddr := 3
    topAddr := 250 }

example : state8.locals 4 = none := rfl
example : state8.globals (BitVec.ofNat 5 2) = none := rfl
example : state8.code = fun _ => none := rfl
example : state8.memory (BitVec.ofNat 8 7) = .word (BitVec.ofNat 8 7) := rfl
example : state8.memaddrs (BitVec.ofNat 8 7) = False := rfl
example : state8.shMemaddrs (BitVec.ofNat 8 7) = False := rfl
example : state8.clock = 9 := rfl
example : state8.be = true := rfl
example : state8.ffi.ffiState = () := rfl
example : state8.baseAddr = 3 := rfl
example : state8.topAddr = 250 := rfl

end Flapjack.Test.CrepSemStateWidthModel
