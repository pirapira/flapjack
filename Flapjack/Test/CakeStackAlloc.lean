import Flapjack.Compiler.Backend.StackAlloc

namespace Flapjack.Test.StackAlloc

open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackAlloc

abbrev ProbeProg := Prog Nat Nat Nat Nat Nat Nat String

def handlerOnly (label : Nat) : ProbeProg :=
  .call none (.inl 0) (some (.skip, 0, label))

def nextLabPairedGuards : Bool :=
  -- HOL stack_alloc_next_lab_probeScript: default case and simple labels.
  nextLab (.skip : ProbeProg) 3 == 3 &&
  nextLab (.seq (handlerOnly 5) .skip : ProbeProg) 1 == 7 &&
  nextLab (.call none (.inl 0) none : ProbeProg) 3 == 3 &&
  -- if/loop recurse into both branches and preserve the returned seed.
  nextLab (.loop (.ite 0 1 2 (handlerOnly 4) (handlerOnly 8)) : ProbeProg) 0 == 10 &&
  -- A handler with no return continuation updates from its label only; its
  -- program is intentionally not recursively visited by the HOL clause.
  nextLab (handlerOnly 6) 2 == 8 &&
  nextLab (.call none (.inl 7) (some (handlerOnly 40, 0, 6)) : ProbeProg) 2 == 8 &&
  -- A return continuation is traversed after reserving its two labels.
  nextLab (.call (some (handlerOnly 5, 0, 3, 4)) (.inl 0) none : ProbeProg) 1 == 7 &&
  nextLab (.call (some (handlerOnly 12, 0, 3, 4)) (.inl 0) none : ProbeProg) 1 == 14 &&
  -- With both continuations, seed is max(l2,l3)+2, then return then handler.
  nextLab (.call (some (handlerOnly 12, 0, 3, 4)) (.inl 0)
    (some (handlerOnly 15, 1, 7)) : ProbeProg) 1 == 17 &&
  nextLab (.raise 99 : ProbeProg) 5 == 5

#guard nextLabPairedGuards

end Flapjack.Test.StackAlloc
