import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Backend.StackLang.Prog
import Flapjack.Compiler.Backend.StackCarrier
import Flapjack.Compiler.Encoders.Asm

/-!
# `String` <-> `mlstring` bridge for the stack program carrier

HOL `stackLang$prog` stores an `mlstring` in its `FFI` constructor, while the
executed `Flapjack.Compiler.Backend.StackCarrier.ProgW` stores a Lean `String`.
The exact width-indexed carrier `Flapjack.Compiler.Backend.StackLang.HolProg` uses the
faithful `Flapjack.Basis.Pure.MlString.MlString` carrier instead.  This
module records the kernel-checked bridge between the two: `holProgToProgW`
decodes the exact program into the executable carrier and `progWToHolProg`
encodes it back, and the round trip `progWToHolProg (holProgToProgW p) = p`
shows the exact carrier embeds into the executable one.

The bridge is only a structural relation: the executed compiler does not
textually route through `HolProg`, so this does NOT by itself satisfy the
AGENTS.md production-path rule.  It shows that the `String` FFI field of `ProgW`
is the image of the faithful `mlstring` field under
`Flapjack.Basis.Pure.MlString.toStringOfBytes`, so the exact `MlString`
theorems can be transported onto programs whose FFI names are byte strings.
-/

namespace Flapjack.Compiler.Backend

open Flapjack.Basis.Pure
open Flapjack.Compiler.Backend.StackLang (Prog HolProg)
open Flapjack.Compiler.Backend.StackCarrier (ProgW)
open Flapjack.Compiler.Encoders.Asm

/-- Decode an exact `HolProg` (faithful `MlString` FFI) into the executable
`ProgW` (`String` FFI) carrier, using the checked `HolInst`/`HolRegImm`/
`HolAddr` isomorphisms and `MlString.toStringOfBytes`. -/
def holProgToProgW {width : Nat} [NeZero width] (program : HolProg width) :
    ProgW (BitVec width) :=
  Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
    HolAddr.toWordLangAddr MlString.toStringOfBytes program

/-- Encode an executable `ProgW` (`String` FFI) back into the exact `HolProg`
(faithful `MlString` FFI) carrier. -/
def progWToHolProg {width : Nat} [NeZero width] (program : ProgW (BitVec width)) :
    HolProg width :=
  Prog.map HolInst.ofWordLangInst id HolRegImm.ofWordRegImm id id
    HolAddr.ofWordLangAddr MlString.ofString program

/-- The exact `HolProg` carrier embeds into the executable `ProgW` carrier: the
encoding of the decoding of any exact program is the program itself.  This is
the kernel-checked `String`<->`mlstring` bridge for the stack program
carrier. -/
theorem progWToHolProg_holProgToProgW {width : Nat} [NeZero width]
    (program : HolProg width) :
    progWToHolProg (holProgToProgW program) = program := by
  unfold progWToHolProg holProgToProgW
  fun_induction Prog.map HolInst.toWordLangInst id HolRegImm.toWordRegImm id id
      HolAddr.toWordLangAddr MlString.toStringOfBytes program <;>
    repeat rw [Prog.map.eq_def] <;>
    simp_all [MlString.ofString_toStringOfBytes, HolInst.of_to, HolRegImm.of_to,
      HolAddr.of_to]
  case case6 => rename_i rh t h ih2 ih1; cases rh <;> cases h <;> simp_all
  all_goals (try rfl)

end Flapjack.Compiler.Backend