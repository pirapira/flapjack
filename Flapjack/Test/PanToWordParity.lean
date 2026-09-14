import Flapjack.Pipeline

namespace Flapjack.Test.PanToWordParity

def skipMain : List (Decl Nat) :=
  [.function
    { name := "main", inline := false, exported := false, params := [],
      body := .skip, returnShape := .one }]

def originalSkipMain : List (Nat × Nat × WordProg Nat) :=
  [(64, 1, .seq .skip (.seq (.call none (some 65) [0] none) .skip)),
   (65, 1, .skip)]

def normalizeSourceBody : WordProg Nat → WordProg Nat
  | .seq first second =>
      .seq (normalizeSourceBody first) (normalizeSourceBody second)
  | .call returns (some 65) arguments handler =>
      .call returns (some 2) arguments handler
  | body => body

def normalizedSourceSkipMain : List (Nat × Nat × WordProg Nat) :=
  originalSkipMain.map (fun (label, arity, body) =>
    (if label = 64 then 1 else if label = 65 then 2 else label,
      arity, normalizeSourceBody body))

def leanSkipMain : List (Nat × Nat × WordProg Nat) :=
  compilePanToWord (α := Nat) .rv64i 1 id skipMain

#eval leanSkipMain

def parityGuard : Bool :=
  match leanSkipMain, normalizedSourceSkipMain with
  | [(1, 1, .seq .skip (.seq (.call none (some leanTarget) leanArguments none) .skip)),
      (2, 1, .skip)],
    [(1, 1, .seq .skip (.seq (.call none (some sourceTarget) sourceArguments none) .skip)),
      (2, 1, .skip)] =>
      leanTarget == sourceTarget && leanArguments == sourceArguments
  | _, _ => false

#eval parityGuard

#guard parityGuard

end Flapjack.Test.PanToWordParity
