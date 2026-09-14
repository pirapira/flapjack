import Flapjack.PanHProg

/-!
# Parity checks for Pancake `h_prog_def`

The direct HOL fixture in
`scripts/hol-probes/pan_itree_h_prog_probe.out` comes from
`pan_itreeSemScript.sml:555-577`.  The Lean checks exercise each terminal
dispatcher case and a delegated branch, preserving the source state token.
-/

namespace Flapjack.Test.PanHProgParity

open Flapjack

def defaultHandlers : PanHProgHandlers Nat Nat := panHProgDefaultHandlers Nat Nat

def delegatedHandlers : PanHProgHandlers Nat Nat :=
  { panHProgDefaultHandlers Nat Nat with
    seq := fun _ _ sourceState => .ret (.normal sourceState) }

def observeSkip : Bool :=
  match panHProg defaultHandlers .skip 7 with
  | .ret (.normal state) => state == 7
  | _ => false

def observeAnnot : Bool :=
  match panHProg defaultHandlers (.annot "tag" "text") 7 with
  | .ret (.normal state) => state == 7
  | _ => false

def observeBreak : Bool :=
  match panHProg defaultHandlers .break 7 with
  | .ret (.break state) => state == 7
  | _ => false

def observeContinue : Bool :=
  match panHProg defaultHandlers .continue 7 with
  | .ret (.continue state) => state == 7
  | _ => false

def observeTick : Bool :=
  match panHProg defaultHandlers .tick 7 with
  | .ret (.normal state) => state == 7
  | _ => false

def observeDelegated : Bool :=
  match panHProg delegatedHandlers (.seq .skip .skip) 7 with
  | .ret (.normal state) => state == 7
  | _ => false

#guard observeSkip
#guard observeAnnot
#guard observeBreak
#guard observeContinue
#guard observeTick
#guard observeDelegated

def runChecks : IO Bool := do
  if observeSkip then IO.println "PASS h_prog Skip" else IO.println "FAIL h_prog Skip"
  if observeAnnot then IO.println "PASS h_prog Annot" else IO.println "FAIL h_prog Annot"
  if observeBreak then IO.println "PASS h_prog Break" else IO.println "FAIL h_prog Break"
  if observeContinue then IO.println "PASS h_prog Continue" else IO.println "FAIL h_prog Continue"
  if observeTick then IO.println "PASS h_prog Tick" else IO.println "FAIL h_prog Tick"
  if observeDelegated then IO.println "PASS h_prog delegated Seq" else IO.println "FAIL h_prog delegated Seq"
  pure (observeSkip && observeAnnot && observeBreak && observeContinue &&
    observeTick && observeDelegated)

end Flapjack.Test.PanHProgParity
