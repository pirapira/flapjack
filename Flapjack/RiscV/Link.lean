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

def wordFunctionReturnNames [NeZero width] :
    WordProg (Word width) → Option (List Nat)
  | .return _ values => some values
  | .seq first second =>
      match wordFunctionReturnNames first with
      | some values => some values
      | none => wordFunctionReturnNames second
  | .ite _ _ _ thenBranch elseBranch =>
      match wordFunctionReturnNames thenBranch, wordFunctionReturnNames elseBranch with
      | some thenReturns, some elseReturns =>
          if thenReturns == elseReturns then some thenReturns else none
      | _, _ => none
  | _ => none
  termination_by program => sizeOf program

def lookupWordFunctionBody [NeZero width] (label : Nat) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (WordProg (Word width))
  | [] => none
  | (candidate, _, body) :: functions =>
      if label == candidate then some body
      else lookupWordFunctionBody label functions

def wordFunctionReturnNamesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
    WordProg (Word width) → Option (List Nat)
  | .call (some ([], _)) (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .call none (some label) _ none => do
      let body ← lookupWordFunctionBody label functions
      wordFunctionReturnNames body
  | .seq first second =>
      match wordFunctionReturnNamesWithCalls functions first with
      | some values => some values
      | none => wordFunctionReturnNamesWithCalls functions second
  | .ite _ _ _ thenBranch elseBranch => do
      let thenReturns ← wordFunctionReturnNamesWithCalls functions thenBranch
      let elseReturns ← wordFunctionReturnNamesWithCalls functions elseBranch
      if thenReturns == elseReturns then some thenReturns else none
  | .return _ values => some values
  | _ => none
termination_by program => sizeOf program

def compileLinkedWordFunction [NeZero width]
    (context : WordCallContext width)
    (function : Nat × List Nat × WordProg (Word width)) :
    Option (Nat × List Nat × Option (List (Instruction width) × List (Fin 32))) := do
  let (label, parameters, body) := function
  let (code, returns) ← wordFunctionToRiscVWithCalls context body
  pure (label, parameters, some (code ++ [.jalr 0 1 0], returns))

def wordFunctionTargetSignaturesAux [NeZero width]
    (allFunctions : List (Nat × List Nat × WordProg (Word width))) :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNamesWithCalls allFunctions body
      let rest ← wordFunctionTargetSignaturesAux allFunctions functions
      pure ((label, 0, parameters, returns) :: rest)

def wordFunctionTargetSignaturesWithCalls [NeZero width]
    (functions : List (Nat × List Nat × WordProg (Word width))) :
      Option (List (Nat × Word width × List Nat × List Nat)) :=
  wordFunctionTargetSignaturesAux functions functions

def wordFunctionTargetSignatures [NeZero width] :
    List (Nat × List Nat × WordProg (Word width)) →
      Option (List (Nat × Word width × List Nat × List Nat))
  | [] => some []
  | (label, parameters, body) :: functions => do
      let returns ← wordFunctionReturnNames body
      let rest ← wordFunctionTargetSignatures functions
      pure ((label, 0, parameters, returns) :: rest)

def linkWordFunctions [NeZero width]
    (start : Word width)
    (functions : List (Nat × List Nat × WordProg (Word width))) := do
  let signatures ← wordFunctionTargetSignaturesWithCalls functions
  let provisionalContext : WordCallContext width := { targets := signatures }
  let provisional ← functions.mapM (compileLinkedWordFunction provisionalContext)
  let linked :
      List (Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) ←
    linkRiscVFunctions start provisional
  let targets : List (Nat × Word width × List Nat × List Nat) :=
    linked.map (fun (item :
        Nat × Word width × List Nat × List (Instruction width) × List (Fin 32)) =>
      let (label, entry, parameters, _code, returns) := item
      (label, entry, parameters, List.map (fun register : Fin 32 => register.val) returns))
  let context : WordCallContext width := { targets := targets }
  let actual ← functions.mapM (compileLinkedWordFunction context)
  linkRiscVFunctions start actual

theorem wordFunctionReturnNames_return [NeZero width] (values : List Nat) :
    wordFunctionReturnNames (.return 0 values : WordProg (Word width)) = some values := by
  simp [wordFunctionReturnNames]

theorem linkWordFunctions_empty [NeZero width] (start : Word width) :
    linkWordFunctions start [] = some [] := by
  rfl

theorem linkRiscVFunctions_empty [NeZero width] (start : Word width) :
    linkRiscVFunctions start [] = some [] := by
  rfl

end Flapjack.RiscV
