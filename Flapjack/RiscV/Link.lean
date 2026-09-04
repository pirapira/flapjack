import Flapjack.RiscV.Calls

/-!
The first RISC-V linker layer for Flapjack function artifacts. Function labels
are assigned byte addresses from the emitted instruction lengths; unresolved
artifacts fail explicitly. The resulting entry table feeds
`wordCallToRiscVLabel`, which resolves a Word call target before selecting its
RISC-V sequence.
-/

namespace Flapjack.RiscV

def linkRiscVFunctionsAt [NeZero width] (start : Word width) (offset : Nat) :
    List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) →
      Option (List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)))
  | [] => some []
  | (label, parameters, some (code, returns)) :: functions => do
      let rest ← linkRiscVFunctionsAt start (offset + 4 * code.length) functions
      pure ((label, start + BitVec.ofNat width offset, parameters, code, returns) :: rest)
  | _ => none

def linkRiscVFunctions [NeZero width]
    (start : Word width)
    (functions : List (Nat × List Nat × Option (List (Instruction width) × List (Fin 32)))) :=
  linkRiscVFunctionsAt start 0 functions

def lookupLinkedEntry [NeZero width]
    (label : Nat)
    (functions : List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32))) :
    Option (Word width) :=
  match functions with
  | [] => none
  | (candidate, entry, _, _, _) :: functions =>
      if label == candidate then some entry else lookupLinkedEntry label functions

def wordCallToRiscVLabel [NeZero width]
    (functions : List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)))
    (label : Nat) (parameters returns arguments destinations : List Nat) :
    Option (List (Instruction width)) := do
  let entry ← lookupLinkedEntry label functions
  wordCallToRiscV entry parameters returns arguments destinations

theorem linkRiscVFunctions_empty [NeZero width] (start : Word width) :
    linkRiscVFunctions start [] = some [] := by
  rfl

end Flapjack.RiscV
