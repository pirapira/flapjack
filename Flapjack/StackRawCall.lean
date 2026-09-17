import Flapjack.StackRemove

namespace Flapjack

def stackFrameWords : StackProg α → Option Nat
  | .stackAlloc words => some words
  | .seq (.stackAlloc words) _ => some words
  | _ => none

def stackRawCallFrameLookup : Nat → List (Nat × Nat) → Option Nat
  | _, [] => none
  | label, (candidate, words) :: entries =>
      if label = candidate then some words
      else stackRawCallFrameLookup label entries

def stackRawCallFrames : List (Nat × StackProg Nat) → List (Nat × Nat)
  | [] => []
  | (label, program) :: programs =>
      match stackFrameWords program with
      | some words => (label, words) :: stackRawCallFrames programs
      | none => stackRawCallFrames programs

def stackRawCallSeq (frames : List (Nat × Nat))
    (first second : StackProg Nat) : Option (StackProg Nat) :=
  match first, second with
  | .stackFree words, .call none (.label target) none =>
      match stackRawCallFrameLookup target frames with
      | none => none
      | some calleeWords =>
          if calleeWords = words then
            some (.rawCall target)
          else if calleeWords < words then
            some (.seq (.stackFree (words - calleeWords)) (.rawCall target))
          else
            some (.seq .tick
              (.seq (.stackAlloc (calleeWords - words)) (.rawCall target)))
  | _, _ => none

def stackRawCallFuel : Nat → List (Nat × Nat) → StackProg Nat → StackProg Nat
  | 0, _, program => program
  | fuel + 1, frames, .seq first second =>
      match stackRawCallSeq frames first second with
      | some replacement => replacement
      | none =>
          .seq (stackRawCallFuel fuel frames first)
            (stackRawCallFuel fuel frames second)
  | fuel + 1, frames, .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (stackRawCallFuel fuel frames thenBranch)
        (stackRawCallFuel fuel frames elseBranch)
  | fuel + 1, frames, .loop body => .loop (stackRawCallFuel fuel frames body)
  | _fuel + 1, _, .call none target none => .call none target none
  | fuel + 1, frames, .call none target (some (handler, exceptionLabel, handlerLabel)) =>
      .call none target
        (some (stackRawCallFuel fuel frames handler, exceptionLabel, handlerLabel))
  | fuel + 1, frames,
      .call (some (continuation, link, returnLabel, entryLabel)) target handler =>
      .call
        (some (stackRawCallFuel fuel frames continuation, link, returnLabel, entryLabel))
        target
        (handler.map (fun (body, exceptionLabel, handlerLabel) =>
          (stackRawCallFuel fuel frames body, exceptionLabel, handlerLabel)))
  | _fuel + 1, _, program => program

def stackRawCall (frames : List (Nat × Nat)) (program : StackProg Nat) : StackProg Nat :=
  stackRawCallFuel (stackProgDepth program + 1) frames program

def stackRawCallPrograms : List (Nat × StackProg Nat) → List (Nat × StackProg Nat)
  | programs =>
      let frames := stackRawCallFrames programs
      programs.map (fun (label, program) => (label, stackRawCall frames program))

end Flapjack
