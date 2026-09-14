import Flapjack.RiscV.CakeRegAlloc

/-!
# Cake register-allocation parity

Mirrors of the `word_alloc$get_stack_only` probe fixtures in
`scripts/hol-probes/get_stack_only_probeScript.sml` (oracle outputs in
`get_stack_only_probe.out`, from
`cakeml/compiler/backend/word_allocScript.sml:1741-1789`) and of the
`word_alloc$get_forced` probe fixtures in
`scripts/hol-probes/get_forced_probeScript.sml` (oracle outputs in
`get_forced_probe.out`, from
`cakeml/compiler/backend/word_allocScript.sml:1466-1512`).

Bead `flapjack-pxn.8.5.14.1.3` (frame occupancy and allocator temporary
slots), driver slices 1 and 2.
-/

namespace Flapjack.Test.CakeRegAlloc

open Flapjack.RiscV.CakeRegAlloc

/-- Move chain whose second element writes the allocatable variable 9
    from the stack variable 7: 9 becomes forced-stack (`{9}`). -/
def moveChainGuard : Bool :=
  cakeGetStackOnly (.move 1 [(9, 9), (7, 9)] : WordProg Nat) = [9]

/-- The same move shape but sourced from physical register 2: the target
    stays allocatable (`∅`). -/
def moveFromRegGuard : Bool :=
  cakeGetStackOnly (.move 1 [(9, 9), (2, 9)] : WordProg Nat) = []

/-- Sequences thread the state right-to-left; the second move's
    forced-stack target stays visible, and the first move's plain
    delete leaves it intact (`{9}`). -/
def seqMovesGuard : Bool :=
  cakeGetStackOnly
    (.seq (.move 1 [(13, 13), (2, 13)] : WordProg Nat)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)) = [9]

/-- Branches merge the two arms; 19 is a stack variable (4n+3), so the
    right arm contributes nothing (`{9}`). -/
def ifMergeGuard : Bool :=
  cakeGetStackOnly
    (.ite .notEqual 2 (.reg 3)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)
      (.move 1 [(19, 19), (7, 19)] : WordProg Nat)) = [9]

/-- Both arms contribute allocatable targets 9 and 21 (`{9, 21}`). -/
def ifMergeAllocGuard : Bool :=
  cakeGetStackOnly
    (.ite .notEqual 2 (.reg 3)
      (.move 1 [(9, 9), (7, 9)] : WordProg Nat)
      (.move 1 [(21, 21), (7, 21)] : WordProg Nat)) = [9, 21]

/-- Calls analyse and merge the return continuation and exception
    handler; 19 is a stack variable so only the continuation
    contributes (`{9}`). -/
def callMergeGuard : Bool :=
  cakeGetStackOnly
    (.call (some ([9], ([], []),
        (.move 1 [(9, 9), (7, 9)] : WordProg Nat), 0, 1))
      (some 5) [2]
      (some (11, (.move 1 [(19, 19), (7, 19)] : WordProg Nat), 0, 2))) = [9]

/-- Tail calls (no return tuple) leave the state untouched (`∅`). -/
def callTailGuard : Bool :=
  cakeGetStackOnly (.call none (some 5) [0, 2] none : WordProg Nat) = []

/-- A plain assignment is a clash-tree leaf: its written name is removed
    from the temporaries set (`∅`). -/
def assignLeafGuard : Bool :=
  cakeGetStackOnly (.assign 9 (.const 7 : WordExp Nat) : WordProg Nat) = []

def parityGuard : Bool :=
  moveChainGuard && moveFromRegGuard && seqMovesGuard && ifMergeGuard &&
    ifMergeAllocGuard && callMergeGuard && callTailGuard && assignLeafGuard

/-- LongMul on the RISC-V configuration forces the destination against both
    sources, in source order (`[(9,13); (9,17)]`). -/
def gfLongMulGuard : Bool :=
  cakeGetForced
    (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat) [] =
    [(9, 13), (9, 17)]

/-- A destination that equals its first source suppresses that pair
    (`[(9,17)]`). -/
def gfLongMulEqGuard : Bool :=
  cakeGetForced
    (.inst (.arith (.longMul 9 11 9 17)) : WordProg Nat) [] = [(9, 17)]

/-- AddCarry forces the same pairs as LongMul on RISC-V. -/
def gfAddCarryGuard : Bool :=
  cakeGetForced
    (.inst (.arith (.cakeAddCarry 9 11 13 17)) : WordProg Nat) [] =
    [(9, 13), (9, 17)]

/-- A destination that equals the carry input suppresses that pair
    (`[(9,13)]`). -/
def gfAddCarryEq4Guard : Bool :=
  cakeGetForced
    (.inst (.arith (.cakeAddCarry 9 11 13 9)) : WordProg Nat) [] =
    [(9, 13)]

/-- Sequences fold right-to-left: the first statement's pairs precede the
    second's. -/
def gfSeqGuard : Bool :=
  cakeGetForced
    (.seq (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat)
      (.inst (.arith (.cakeAddCarry 21 2 25 29)) : WordProg Nat)) [] =
    [(9, 13), (9, 17), (21, 25), (21, 29)]

/-- Branches analyse the then-arm first. -/
def gfIfGuard : Bool :=
  cakeGetForced
    (.ite .notEqual 2 (.reg 3)
      (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat)
      (.inst (.arith (.cakeAddCarry 21 2 25 29)) : WordProg Nat)) [] =
    [(9, 13), (9, 17), (21, 25), (21, 29)]

/-- Handler-less calls analyse the return continuation only. -/
def gfCallGuard : Bool :=
  cakeGetForced
    (.call (some ([], ([], []),
        (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat), 0, 1))
      (some 5) [2] none) [] = [(9, 13), (9, 17)]

/-- Calls with handlers fold the handler before the return continuation. -/
def gfCallHandlerGuard : Bool :=
  cakeGetForced
    (.call (some ([], ([], []),
        (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat), 0, 1))
      (some 5) [2]
      (some (11, (.inst (.arith (.cakeAddCarry 21 2 25 29)) : WordProg Nat),
        0, 2))) [] =
    [(21, 25), (21, 29), (9, 13), (9, 17)]

/-- Loops analyse the loop body. -/
def gfLoopGuard : Bool :=
  cakeGetForced
    (.loop [] (.inst (.arith (.longMul 9 11 13 17)) : WordProg Nat) []) [] =
    [(9, 13), (9, 17)]

def forcedParityGuard : Bool :=
  gfLongMulGuard && gfLongMulEqGuard && gfAddCarryGuard && gfAddCarryEq4Guard &&
    gfSeqGuard && gfIfGuard && gfCallGuard && gfCallHandlerGuard && gfLoopGuard

#eval parityGuard
#guard parityGuard
#eval forcedParityGuard
#guard forcedParityGuard

def runChecks : IO Bool := do
  let results := [
    moveChainGuard, moveFromRegGuard, seqMovesGuard, ifMergeGuard,
    ifMergeAllocGuard, callMergeGuard, callTailGuard, assignLeafGuard,
    gfLongMulGuard, gfLongMulEqGuard, gfAddCarryGuard, gfAddCarryEq4Guard,
    gfSeqGuard, gfIfGuard, gfCallGuard, gfCallHandlerGuard, gfLoopGuard]
  let names := [
    "get_stack_only move chain", "get_stack_only move from reg",
    "get_stack_only seq moves", "get_stack_only if merge",
    "get_stack_only if merge alloc", "get_stack_only call merge",
    "get_stack_only call tail", "get_stack_only assign leaf",
    "get_forced longmul", "get_forced longmul eq",
    "get_forced addcarry", "get_forced addcarry eq4",
    "get_forced seq", "get_forced if",
    "get_forced call", "get_forced call handler", "get_forced loop"]
  let mut all := true
  for (name, result) in names.zip results do
    if result then IO.println s!"PASS {name}" else IO.println s!"FAIL {name}"
    all := all && result
  pure all

end Flapjack.Test.CakeRegAlloc
