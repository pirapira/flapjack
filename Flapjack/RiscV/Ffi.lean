import Flapjack.RiscV.Calls

/-!
RISC-V environment-call boundary for Word FFI operations.

CakeML lowers foreign calls through a target-side environment-call primitive.
The native instruction model therefore keeps ECALL distinct from host
effects; executeWithFfi supplies the explicit environment transition used by
the compiler-correctness boundary.

The ABI used here is deliberately small and explicit:

* x10--x13 carry configuration pointer, configuration length, array pointer,
  and array length;
* x14 carries the numeric FFI service identifier; and
* the host receives the post-marshalling machine state and may reject the
  operation by returning none.
-/

namespace Flapjack.RiscV

structure WordFfiContext where
  services : List (FunName × Nat)

def lookupWordFfiService (function : FunName) :
    List (FunName × Nat) → Option Nat
  | [] => none
  | (candidate, service) :: services =>
      if function == candidate then some service
      else lookupWordFfiService function services

def wordFfiToRiscV [NeZero width] (context : WordFfiContext)
    (function : FunName)
    (configuration configurationLength array arrayLength : Nat) :
    Option (List (Instruction width)) := do
  let service ← lookupWordFfiService function context.services
  let moves ← wordRegisterMoves
    [(10, configuration), (11, configurationLength),
     (12, array), (13, arrayLength)]
  pure (moves ++
    [.addi 14 0 (BitVec.ofNat width service), .ecall])

abbrev WordFfiHost (width : Nat) :=
  Nat → Word width → Word width → Word width → Word width →
    State width → Option (State width)

def executeWithFfi [NeZero width] (host : WordFfiHost width)
    (state : State width) : Instruction width → Option (State width)
  | .ecall =>
      host (readRegister state 14).toNat
        (readRegister state 10) (readRegister state 11)
        (readRegister state 12) (readRegister state 13) state
  | instruction => some (execute state instruction)

def executeInstructionsWithFfi [NeZero width] (host : WordFfiHost width)
    (state : State width) : List (Instruction width) → Option (State width)
  | [] => some state
  | instruction :: instructions => do
      let state ← executeWithFfi host state instruction
      executeInstructionsWithFfi host state instructions

theorem lookupWordFfiService_shape :
    lookupWordFfiService "sum" [("sum", 7), ("other", 8)] = some 7 := by
  rfl

theorem wordFfiToRiscV_shape [NeZero width] :
    wordFfiToRiscV
      { services := [("sum", 7)] } "sum" 2 3 4 5 =
      some [.addi 10 2 0, .addi 11 3 0, .addi 12 4 0, .addi 13 5 0,
        .addi 14 0 (BitVec.ofNat width 7), .ecall] := by
  simp [wordFfiToRiscV, lookupWordFfiService, wordRegisterMoves,
    registerOfNat]

theorem executeWithFfi_ecall [NeZero width] (host : WordFfiHost width)
    (state : State width) :
    executeWithFfi host state .ecall =
      host (readRegister state 14).toNat
        (readRegister state 10) (readRegister state 11)
        (readRegister state 12) (readRegister state 13) state := by
  rfl

end Flapjack.RiscV
