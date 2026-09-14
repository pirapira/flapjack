import Flapjack.Language

/-! Parity guard for `panLang$free_var_ids` from
    `cakeml/pancake/panLangScript.sml:347-389`. -/

namespace Flapjack.Test.PanLangFreeVarIdsParity

open Flapjack

def declaration : Prog Nat :=
  .dec "x" .one (.var .local "e")
    (.assign .local "x" (.var .local "x"))

def conditional : Prog Nat :=
  .ite (.var .local "g")
    (.return (.var .local "p"))
    (.return (.var .local "q"))

def handledCall : Prog Nat :=
  .call (some (none, some ("E", "h",
    .assign .local "z" (.var .local "q")))) "f"
    [.var .local "a"]

def declarationCall : Prog Nat :=
  .decCall "x" .one "d" [.var .local "a"]
    (.return (.var .local "r"))

def parityGuard : Bool :=
  freeVarIds (.skip : Prog Nat) == [] &&
  freeVarIds (.assign .local "v" (.var .local "x") : Prog Nat) == ["v", "x"] &&
  freeVarIds (.assign .global "v" (.var .local "x") : Prog Nat) == ["x"] &&
  freeVarIds declaration == ["e"] &&
  freeVarIds conditional == ["g", "p", "q"] &&
  freeVarIds (.call none "f" [.var .local "a"] : Prog Nat) == ["a"] &&
  freeVarIds handledCall == ["h", "z", "q", "a"] &&
  freeVarIds declarationCall == ["x", "r", "a"]

#guard parityGuard
#eval parityGuard

end Flapjack.Test.PanLangFreeVarIdsParity
