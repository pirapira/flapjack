import Flapjack.RiscV.CakeRegAlloc
import Flapjack.RiscV.LinearScan
import Flapjack.RiscV.LinearScanSource

/-!
# Direct Cake `word_alloc` output parity

The post-SSA two-register add below is copied from
`scripts/hol-probes/word_alloc_add1_probeScript.sml`.  The expected shape is
the checked `word_alloc_add1_probe.out` result from Cake's
`word_allocScript.sml`: the entry move is coloured to `(0,0),(2,2),(4,4)`,
the two source moves retain colours 4 and 2, and the add/return use those
colours.  This exercises the production CakeRegAlloc driver directly rather
than a hand-built allocator state.
-/

namespace Flapjack.Test.CakeWordAllocParity

open Flapjack
open Flapjack.RiscV
open Flapjack.RiscV.CakeRegAlloc

def add1Program : WordProg Nat :=
  .seq
    (.move 1 [(13, 0), (17, 2), (21, 4)])
    (.seq
      (.seq
        (.move 0 [(25, 21)])
        (.seq
          (.move 0 [(29, 17)])
          (.inst (.arith (.binOp .add 33 25 (.reg 29))))))
      (.seq (.move 0 [(2, 33)]) (.return 13 [2])))

/-! This mirrors Cake's `word_alloc 5 riscv_config 3 22` after the source
    has already passed `full_ssa_cc_trans`; the direct allocator result is
    then compared structurally with the checked HOL output above. -/
def cakeWordAllocAdd1 : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 3 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .irc scost 22 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def add1AllocatorGuard : Bool :=
  match cakeWordAllocAdd1 with
  | some
      (.seq (.move 1 [(0, 0), (2, 2), (4, 4)])
        (.seq
          (.seq (.move 0 [(4, 4)])
            (.seq (.move 0 [(2, 2)])
              (.inst (.arith (.binOp .add 2 4 (.reg 2))))))
          (.seq (.move 0 [(2, 2)]) (.return 0 [2])))) => true
  | _ => false

#guard add1AllocatorGuard

/-! Cake's algorithm 0 is the unweighted simple allocator: unlike algorithm 1,
    it carries no spill-cost table into `reg_alloc`.  The same post-SSA add
    fixture is an independent guard for that driver boundary. -/
def cakeWordAllocSimple : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 0 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .simple scost 22 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def simpleAllocatorGuard : Bool :=
  match cakeWordAllocSimple with
  | some
      (.seq (.move 1 [(0, 0), (4, 2), (2, 4)])
        (.seq
          (.seq (.move 0 [(2, 2)])
            (.seq (.move 0 [(4, 4)])
              (.inst (.arith (.binOp .add 2 2 (.reg 4))))))
          (.seq (.move 0 [(2, 2)]) (.return 0 [2])))) => true
  | _ => false

#guard simpleAllocatorGuard

/-! Cake algorithms 4 and above select `linear_scan_reg_alloc`.  Its source
    bijection and retained pass-1 colours are exercised here, then converted
    from compressed colours to the even Word RISC-V names at the boundary. -/
def cakeWordAllocLinearScanSourceFor (registerColours : Nat) : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forced := cakeGetForced add1Program
  let moves := (wordGetHeuristics 4 5 add1Program).1
  match wordLinearScanAllocateSource registerColours forced moves tree with
  | none => none
  | some allocation =>
      some (wordApplyColour
        (fun name => match lookupNatInfo name
            (wordLinearScanToWordColouring allocation.colouring) with
          | some colour => colour
          | none => 0)
        add1Program)

def cakeWordAllocLinearScanSource : Option (WordProg Nat) :=
  cakeWordAllocLinearScanSourceFor 22

def linearScanSourceAllocatorGuard : Bool :=
  match cakeWordAllocLinearScanSource with
  | some
      (.seq (.move 1 [(0, 0), (4, 2), (6, 4)])
        (.seq
          (.seq (.move 0 [(6, 6)])
            (.seq (.move 0 [(4, 4)])
              (.inst (.arith (.binOp .add 6 6 (.reg 4))))))
          (.seq (.move 0 [(2, 6)]) (.return 0 [2])))) => true
  | _ => false

#guard linearScanSourceAllocatorGuard

def linearScanSourceK1AllocatorGuard : Bool :=
  match cakeWordAllocLinearScanSourceFor 1 with
  | some
      (.seq (.move 1 [(4, 0), (6, 2), (0, 4)])
        (.seq
          (.seq (.move 0 [(0, 0)])
            (.seq (.move 0 [(6, 6)])
              (.inst (.arith (.binOp .add 0 0 (.reg 6))))))
          (.seq (.move 0 [(2, 0)]) (.return 4 [2])))) => true
  | _ => false

#guard linearScanSourceK1AllocatorGuard


/-! Cake's `word_alloc 5 riscv_config 1 22` takes the simple allocator with
    spill heuristics.  This is a separate driver branch from the IRC add
    case above; its exact result is checked in
    `scripts/hol-probes/word_alloc_spill_probe.out`. -/
def cakeWordAllocSimpleSpill : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 1 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .simple scost 22 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def simpleSpillAllocatorGuard : Bool :=
  match cakeWordAllocSimpleSpill with
  | some
      (.seq (.move 1 [(0, 0), (4, 2), (2, 4)])
        (.seq
          (.seq (.move 0 [(2, 2)])
            (.seq (.move 0 [(4, 4)])
              (.inst (.arith (.binOp .add 2 2 (.reg 4))))))
          (.seq (.move 0 [(2, 2)]) (.return 0 [2])))) => true
  | _ => false

#guard simpleSpillAllocatorGuard

/-! The same source through Cake's default IRC allocator with `k=1` crosses
    the register/frame boundary.  This pins the colour choice and return ABI
    after the spill worklist has run, rather than only checking the 22-register
    driver path above. -/
def cakeWordAllocIrcK1 : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 3 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .irc scost 1 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def ircK1AllocatorGuard : Bool :=
  match cakeWordAllocIrcK1 with
  | some
      (.seq (.move 1 [(4, 0), (0, 2), (2, 4)])
        (.seq
          (.seq (.move 0 [(2, 2)])
            (.seq (.move 0 [(0, 0)])
              (.inst (.arith (.binOp .add 0 2 (.reg 0))))))
          (.seq (.move 0 [(2, 0)]) (.return 4 [2])))) => true
  | _ => false

#guard ircK1AllocatorGuard

/-! Cake algorithm 2 is the unweighted IRC path.  At the same `k=1` frame
    boundary it deliberately chooses a different colour ordering from the
    heuristic path, so this is an independent guard for the optional spill
    cost table rather than a duplicate output assertion. -/
def cakeWordAllocIrcK1Unweighted : Option (WordProg Nat) :=
  let tree := wordClashTree add1Program []
  let forcedStack := cakeGetStackOnly add1Program
  let forced := cakeGetForced add1Program
  let (wordMoves, spillCosts) := wordGetHeuristics 2 5 add1Program
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .irc scost 1 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) add1Program)

def ircK1UnweightedAllocatorGuard : Bool :=
  match cakeWordAllocIrcK1Unweighted with
  | some
      (.seq (.move 1 [(4, 0), (2, 2), (0, 4)])
        (.seq
          (.seq (.move 0 [(0, 0)])
            (.seq (.move 0 [(2, 2)])
              (.inst (.arith (.binOp .add 0 0 (.reg 2))))))
          (.seq (.move 0 [(2, 0)]) (.return 4 [2])))) => true
  | _ => false

#guard ircK1UnweightedAllocatorGuard

/-! This post-SSA Cake `AddCarry` fixture exercises `get_forced` and its
    carry interference edges through the complete word_alloc driver. -/
def addCarryProgram : WordProg Nat :=
  .seq
    (.move 1 [(13, 0), (17, 2), (21, 4), (25, 6)])
    (.seq
      (.inst (.arith (.cakeAddCarry 29 25 21 17)))
      (.return 13 [29, 17]))

def cakeWordAllocAddCarry : Option (WordProg Nat) :=
  let tree := wordClashTree addCarryProgram []
  let forcedStack := cakeGetStackOnly addCarryProgram
  let forced := cakeGetForced addCarryProgram
  let (wordMoves, spillCosts) := wordGetHeuristics 3 5 addCarryProgram
  let moves := wordMoves.map (fun move => (move.priority, (move.left, move.right)))
  let bij := cakeMkBij tree
  let scost := spillCosts.map (cakeSpillCostMap bij.nextNode)
  let initialState := cakeInitRaStateFromBij bij tree forced forcedStack
  match cakeDoRegAllocFromState .irc scost 22 moves bij initialState with
  | none => none
  | some colouring =>
      some (wordApplyColour (CakeAlloc.totalColour colouring) addCarryProgram)

def addCarryAllocatorGuard : Bool :=
  match cakeWordAllocAddCarry with
  | some
      (.seq (.move 1 [(0, 0), (2, 2), (4, 4), (6, 6)])
        (.seq (.inst (.arith (.cakeAddCarry 6 6 4 2)))
          (.return 0 [6, 2]))) => true
  | _ => false

#guard addCarryAllocatorGuard

def runChecks : IO Bool := do
  if add1AllocatorGuard then
    IO.println "PASS Cake word_alloc add1 output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc add1 output matches the checked HOL oracle"
  if simpleAllocatorGuard then
    IO.println "PASS Cake word_alloc simple unweighted output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc simple unweighted output matches the checked HOL oracle"
  if linearScanSourceAllocatorGuard then
    IO.println "PASS Cake word_alloc linear-scan output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc linear-scan output matches the checked HOL oracle"
  if simpleSpillAllocatorGuard then
    IO.println "PASS Cake word_alloc simple+spill output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc simple+spill output matches the checked HOL oracle"
  if ircK1AllocatorGuard then
    IO.println "PASS Cake word_alloc IRC k=1 output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc IRC k=1 output matches the checked HOL oracle"
  if ircK1UnweightedAllocatorGuard then
    IO.println "PASS Cake word_alloc IRC k=1 unweighted output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc IRC k=1 unweighted output matches the checked HOL oracle"
  if addCarryAllocatorGuard then
    IO.println "PASS Cake word_alloc AddCarry output matches the checked HOL oracle"
  else
    IO.println "FAIL Cake word_alloc AddCarry output matches the checked HOL oracle"
  pure (add1AllocatorGuard && simpleAllocatorGuard && linearScanSourceAllocatorGuard && simpleSpillAllocatorGuard && ircK1AllocatorGuard &&
    ircK1UnweightedAllocatorGuard && addCarryAllocatorGuard)

end Flapjack.Test.CakeWordAllocParity
