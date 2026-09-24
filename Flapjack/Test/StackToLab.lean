import Flapjack.Compiler.Backend.StackToLab

namespace Flapjack.Test.StackToLab

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab

abbrev ProbeProg := Prog Nat Nat Nat Nat Nat Nat String
abbrev ProbeAsmWithLab := AsmWithLab Nat Nat String
abbrev ProbeAsmOrCbw := AsmOrCbw Nat Nat Nat
abbrev ProbeLine := Line ProbeAsmOrCbw ProbeAsmWithLab (BitVec 64)

def probeOps : FlattenOps Nat Nat Nat Nat :=
  { skip := 90
    embedInst := id
    jumpReg := id
    reg := id
    lower := 7
    negate := fun cmp => cmp + 10 }

def flattenAt (tail : Bool) (program : ProbeProg) (next : Nat := 2)
    (conts breaks : List Nat := []) : List ProbeLine × Bool × Nat :=
  flatten probeOps (BitVec.ofNat 64 0) tail program 3 next conts breaks

def flattenSummary (tail : Bool) (program : ProbeProg) (next : Nat := 2)
    (conts breaks : List Nat := []) : Nat × Bool × Nat :=
  let (lines, terminates, finalNext) := flattenAt tail program next conts breaks
  (lines.length, terminates, finalNext)

def handlerOnly (label : Nat) : ProbeProg :=
  .call none (.inl 0) (some (.skip, 0, label))

def allClauseSummaries : List (Nat × Bool × Nat) :=
  [ flattenSummary false .skip
  , flattenSummary false .tick
  , flattenSummary false (.inst 4)
  , flattenSummary false (.halt 0)
  , flattenSummary true (.seq .tick (.inst 4))
  , flattenSummary false (.seq .tick (.inst 4))
  , flattenSummary false (.ite 1 2 3 .skip .skip)
  , flattenSummary false (.ite 1 2 3 .skip .tick)
  , flattenSummary false (.ite 1 2 3 .tick .skip)
  , flattenSummary false (.ite 1 2 3 (.halt 0) .tick)
  , flattenSummary false (.ite 1 2 3 .tick (.halt 0))
  , flattenSummary false (.ite 1 2 3 .tick (.inst 4))
  , flattenSummary false (.loop (.ite 1 2 3 .tick .tick))
  , flattenSummary false (.raise 4)
  , flattenSummary false (.ret 5)
  , flattenSummary false (.break 1) 2 [] [4, 9]
  , flattenSummary false (.continue 0) 2 [6] []
  , flattenSummary false (.rawCall 11)
  , flattenSummary false (.call none (.inl 11) none)
  , flattenSummary false (.call none (.inr 4) none)
  , flattenSummary false (.call (some (.tick, 4, 5, 6)) (.inr 7) none)
  , flattenSummary false (.call (some (.tick, 4, 5, 6)) (.inr 7)
      (some (.halt 0, 8, 9)))
  , flattenSummary false (.jumpLower 1 2 12)
  , flattenSummary false (.ffi "ffi" 0 0 0 0 4)
  , flattenSummary false (.locValue 1 2 3)
  , flattenSummary false (.install 0 0 0 0 4)
  , flattenSummary false (.shMemOp 1 2 3)
  , flattenSummary false (.codeBufferWrite 1 2)
  , flattenSummary false (.dataBufferWrite 1 2) ]

-- Row order mirrors the direct EVAL fixture in stack_to_lab_flatten_probe.out.
#guard allClauseSummaries ==
  [ (0, false, 2), (1, false, 2), (1, false, 2), (1, true, 2)
  , (3, false, 2), (2, false, 2), (0, false, 2), (3, false, 3)
  , (3, false, 3), (4, false, 3), (4, false, 3), (6, false, 4)
  , (9, false, 6), (1, true, 2), (1, true, 2), (1, true, 2)
  , (1, true, 2), (1, true, 2), (1, true, 2), (1, true, 2)
  , (4, false, 2), (8, false, 3), (1, false, 2), (3, false, 3)
  , (1, false, 2), (3, false, 3), (1, false, 2), (1, false, 2)
  , (0, false, 2) ]

-- These samples pin exact output constructors as well as the summary table.
example : flattenAt false (.ite 1 2 3 .skip .tick) ==
  ([.labAsm (.jumpCmp 1 2 3 (.lab 3 2)) (BitVec.ofNat 64 0) [] 0,
    .asm (.asmi 90) [] 0, .label 3 2 0], false, 3) := by native_decide

example : flattenAt false (.call none (.inl 11) none) ==
  ([.labAsm (.jump (.lab 11 0)) (BitVec.ofNat 64 0) [] 0], true, 2) := by native_decide

example : flattenAt false (.break 1) 2 [] [4, 9] ==
  ([.labAsm (.jump (.lab 3 9)) (BitVec.ofNat 64 0) [] 0], true, 2) := by native_decide

-- `prog_to_section` chooses label 1 for a non-Seq root and the final `next`
-- label for a Seq root, after `next_lab` seeds flattening.
example : progToSection probeOps (BitVec.ofNat 64 0) 3 (.skip : ProbeProg) ==
    { sectionId := 3, lines := [.label 3 1 0] } := by native_decide

example : progToSection probeOps (BitVec.ofNat 64 0) 3
    (.seq .tick (.inst 4) : ProbeProg) ==
    { sectionId := 3, lines := [.asm (.asmi 90) [] 0, .label 3 1 0,
      .asm (.asmi 4) [] 0, .label 3 2 0] } := by native_decide

example : progToSection probeOps (BitVec.ofNat 64 0) 3
    (.ite 1 1 2 .tick .tick : ProbeProg) ==
    { sectionId := 3, lines :=
      [.labAsm (.jumpCmp 1 1 2 (.lab 3 2)) (BitVec.ofNat 64 0) [] 0,
       .asm (.asmi 90) [] 0, .labAsm (.jump (.lab 3 3)) (BitVec.ofNat 64 0) [] 0,
       .label 3 2 0, .asm (.asmi 90) [] 0, .label 3 3 0, .label 3 1 0] } := by native_decide

end Flapjack.Test.StackToLab
