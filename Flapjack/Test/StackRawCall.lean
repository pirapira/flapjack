import Flapjack.StackRawCall

namespace Flapjack.Test.StackRawCall

def equalFrameTailCall : Bool :=
  match stackRawCallSeq [(7, 6)] (.stackFree 6)
      (.call none (.label 7) none) with
  | some (.rawCall 7) => true
  | _ => false

def residualFrameTailCall : Bool :=
  match stackRawCallSeq [(7, 5)] (.stackFree 6)
      (.call none (.label 7) none) with
  | some (.seq (.stackFree 1) (.rawCall 7)) => true
  | _ => false

def largerFrameTailCall : Bool :=
  match stackRawCallSeq [(7, 7)] (.stackFree 6)
      (.call none (.label 7) none) with
  | some (.seq .tick (.seq (.stackAlloc 1) (.rawCall 7))) => true
  | _ => false

def nonTailCallUnchanged : Bool :=
  match stackRawCallSeq [(7, 6)] (.stackFree 6)
      (.call (some (.skip, 0, 1, 2)) (.label 7) none) with
  | none => true
  | _ => false

#guard equalFrameTailCall
#guard residualFrameTailCall
#guard largerFrameTailCall
#guard nonTailCallUnchanged

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("equal tail-call frames become RawCall", equalFrameTailCall),
      ("smaller tail-call frames retain residual StackFree", residualFrameTailCall),
      ("larger tail-call frames allocate the residual frame", largerFrameTailCall),
      ("non-tail calls are not rewritten", nonTailCallUnchanged) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.StackRawCall
