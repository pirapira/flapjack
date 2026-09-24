import Flapjack.Compiler.Backend.MlStringBridge

/-!
# `String` <-> `mlstring` bridge parity checks

Kernel-checked examples for the bridge in
`Flapjack.Compiler.Backend.MlStringBridge`, tying the exact `HolProg` carrier
(faithful `MlString` FFI) to the executable `StackCarrier.ProgW` (`String` FFI).
-/

namespace Flapjack.Test.MlStringBridgeParity

open Flapjack.Compiler.Backend
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.StackLang (HolProg)
open Flapjack.Compiler.Encoders.Asm

/-- Byte-valued character helper. -/
private def c8 (n : Nat) : HolChar := BitVec.ofNat 8 n

/-- The FFI name round-trips through the executable `String` carrier. -/
example : ofString (toStringOfBytes (MlString.implode [c8 65, c8 66])) =
    MlString.implode [c8 65, c8 66] :=
  ofString_toStringOfBytes _

/-- A concrete FFI program round-trips between the exact and executable
carriers. -/
example {width : Nat} [NeZero width] :
    progWToHolProg (width := width)
        (holProgToProgW (width := width)
          ((.ffi (MlString.implode [c8 65, c8 66]) 1 2 3 4 5) : HolProg width)) =
      ((.ffi (MlString.implode [c8 65, c8 66]) 1 2 3 4 5) : HolProg width) :=
  progWToHolProg_holProgToProgW _

/-- The bridge is the identity on an FFI-free program as well. -/
example {width : Nat} [NeZero width] :
    progWToHolProg (width := width)
        (holProgToProgW (width := width) (.stackAlloc 3 : HolProg width)) =
      (.stackAlloc 3 : HolProg width) :=
  progWToHolProg_holProgToProgW _

end Flapjack.Test.MlStringBridgeParity