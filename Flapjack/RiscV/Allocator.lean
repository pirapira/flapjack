import Flapjack.Word

/-!
The first explicit register-allocation boundary for the Word backend.

CakeML's full `word_alloc` pass uses SSA renaming, clash colouring, and
spill-aware allocation.  Flapjack currently represents Word variables by
natural-number register names directly, so this module ports the part of the
target contract that must hold before that larger pass is introduced:

* x0 is the architectural zero register;
* x1 is the call link register;
* x30 is the stack pointer used by ordinary calls; and
* x31 is the backend scratch register.

The allocator preserves the historical `name + 2` assignment whenever it is
safe.  Out-of-range names are assigned the first free register that is not a
preferred register of another slot.  Exhaustion is reported as `none`; it is
never converted into an aliased or reserved register.
-/

namespace Flapjack

def wordAllocatableRegisters : List Nat :=
  (List.range 28).map (fun index => index + 2)

def wordPreferredRegister (name : Nat) : Option Nat :=
  let register := name + 2
  if register < 30 then some register else none

def wordPreferredRegisters : List Nat → List Nat
  | [] => []
  | name :: names =>
      match wordPreferredRegister name with
      | some register => register :: wordPreferredRegisters names
      | none => wordPreferredRegisters names

def wordRemoveRegisters (removed registers : List Nat) : List Nat :=
  match registers with
  | [] => []
  | register :: registers =>
      if register ∈ removed then
        wordRemoveRegisters removed registers
      else
        register :: wordRemoveRegisters removed registers

def wordAllocateVars : List Nat → List Nat → Option (NatInfoMap Nat)
  | [], _ => some []
  | name :: names, fallback =>
      match wordPreferredRegister name with
      | some register =>
          (wordAllocateVars names fallback).map
            (fun result => (name, register) :: result)
      | none =>
          match fallback with
          | [] => none
          | register :: fallback =>
              (wordAllocateVars names fallback).map
                (fun result => (name, register) :: result)

def wordAllocateVarsFromSlots (slots : List Nat) : Option (NatInfoMap Nat) :=
  wordAllocateVars slots
    (wordRemoveRegisters (wordPreferredRegisters slots)
      wordAllocatableRegisters)

def wordAllocateContext (slots : List Nat) : Option WordContext :=
  (wordAllocateVarsFromSlots slots).map (fun vars => { vars := vars })

def wordRegisterIsReserved (register : Nat) : Bool :=
  register == 0 || register == 1 || register == 30 || register == 31

def wordRegisterIsAllocatable (register : Nat) : Bool :=
  register ≥ 2 && register < 30

/-! A compact executable clash-colouring interface.  CakeML builds a clash
tree from the SSA program and then colours its graph.  The current Word IR
does not yet carry the full spill metadata, but this layer already consumes
the resulting undirected clash edges instead of ignoring them. -/

def wordNeighbours (name : Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (left, right) :: edges =>
      if left == name then right :: wordNeighbours name edges
      else if right == name then left :: wordNeighbours name edges
      else wordNeighbours name edges

def wordUsedRegisters (names : List Nat) (colouring : NatInfoMap Nat) : List Nat :=
  match names with
  | [] => []
  | name :: names =>
      match lookupNatInfo name colouring with
      | some register => register :: wordUsedRegisters names colouring
      | none => wordUsedRegisters names colouring

def wordFirstAvailable : List Nat → List Nat → Option Nat
  | [], _ => none
  | register :: registers, forbidden =>
      if register ∈ forbidden then
        wordFirstAvailable registers forbidden
      else some register

def wordColourCandidates (name : Nat) : List Nat :=
  match wordPreferredRegister name with
  | some register =>
      register :: wordRemoveRegisters [register] wordAllocatableRegisters
  | none => wordAllocatableRegisters

def wordGreedyColour (names : List Nat) (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : Option (NatInfoMap Nat) :=
  match names with
  | [] => some colouring
  | name :: names =>
      let neighbours := wordNeighbours name edges
      let forbidden := wordUsedRegisters neighbours colouring
      match wordFirstAvailable (wordColourCandidates name) forbidden with
      | none => none
      | some register =>
          wordGreedyColour names edges ((name, register) :: colouring)

def wordColouringUsesAllocatable (names : List Nat)
    (colouring : NatInfoMap Nat) : Bool :=
  match names with
  | [] => true
  | name :: names =>
      match lookupNatInfo name colouring with
      | some register =>
          wordRegisterIsAllocatable register &&
            wordColouringUsesAllocatable names colouring
      | none => false

def wordColouringRespectsClashes (edges : List (Nat × Nat))
    (colouring : NatInfoMap Nat) : Bool :=
  match edges with
  | [] => true
  | (left, right) :: edges =>
      match lookupNatInfo left colouring, lookupNatInfo right colouring with
      | some leftRegister, some rightRegister =>
          leftRegister != rightRegister &&
            wordColouringRespectsClashes edges colouring
      | _, _ => false

def wordAllocateVarsWithClashes (slots : List Nat)
    (edges : List (Nat × Nat)) : Option (NatInfoMap Nat) :=
  let names := slots.eraseDups
  match wordGreedyColour names edges [] with
  | none => none
  | some colouring =>
      if wordColouringUsesAllocatable names colouring &&
          wordColouringRespectsClashes edges colouring then
        some colouring
      else none

def wordAllocateContextWithClashes (slots : List Nat)
    (edges : List (Nat × Nat)) : Option WordContext :=
  (wordAllocateVarsWithClashes slots edges).map (fun vars => { vars := vars })

/-! Straight-line liveness and clash construction for the current Word
instruction fragment.  The analysis walks backwards, keeping values live
after each instruction and adding an edge from every written variable to the
values that remain live. -/

def wordInstReadVars : WordInst → List Nat
  | .arith operation =>
      match operation with
      | .longMul _ _ sourceLeft sourceRight => [sourceLeft, sourceRight]
      | .longDiv _ _ sourceLeft sourceRight quotient =>
          [sourceLeft, sourceRight, quotient]
      | .addCarry _ _ sourceLeft sourceRight carryIn =>
          [sourceLeft, sourceRight, carryIn]
      | .div _ dividend divisor => [dividend, divisor]
  | .mem operator destination address =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [address]
      | .store | .store8 | .store16 | .store32 => [destination, address]

def wordInstWriteVars : WordInst → List Nat
  | .arith operation =>
      match operation with
      | .longMul destinationLeft destinationRight _ _ =>
          [destinationLeft, destinationRight]
      | .longDiv destinationLeft destinationRight _ _ _ =>
          [destinationLeft, destinationRight]
      | .addCarry destination resultCarry _ _ _ =>
          [destination, resultCarry]
      | .div destination _ _ => [destination]
  | .mem operator destination _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [destination]
      | .store | .store8 | .store16 | .store32 => []

def wordInstVars (instruction : WordInst) : List Nat :=
  wordInstReadVars instruction ++ wordInstWriteVars instruction

def wordClashPairs (writes live : List Nat) : List (Nat × Nat) :=
  writes.flatMap (fun write =>
    (live.filter (fun name => name != write)).map (fun name => (write, name)))

def wordPairwiseClashes : List Nat → List (Nat × Nat)
  | [] => []
  | name :: names =>
      (names.map (fun other => (name, other))) ++
        wordPairwiseClashes names

def wordInstLiveBefore (instruction : WordInst) (liveAfter : List Nat) : List Nat :=
  wordInstReadVars instruction ++
    liveAfter.filter (fun name => name ∉ wordInstWriteVars instruction)

def wordInstClashes (instruction : WordInst) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  wordPairwiseClashes (wordInstWriteVars instruction) ++
    wordClashPairs (wordInstWriteVars instruction) liveAfter

def wordLinearClashAnalysis : List WordInst → List Nat →
    List Nat × List (Nat × Nat)
  | [], liveOut => (liveOut, [])
  | instruction :: instructions, liveOut =>
      let (liveAfter, edges) := wordLinearClashAnalysis instructions liveOut
      (wordInstLiveBefore instruction liveAfter,
        wordInstClashes instruction liveAfter ++ edges)

def wordLinearVariables (instructions : List WordInst) : List Nat :=
  instructions.flatMap wordInstVars

def wordAllocateLinearInstructions (instructions : List WordInst) :
    Option WordContext :=
  let (liveIn, edges) := wordLinearClashAnalysis instructions []
  wordAllocateContextWithClashes
    (wordLinearVariables instructions ++ liveIn) edges

/-! Word SSA renaming.  Each write receives a fresh virtual name; reads use the
latest name for their source variable.  The implementation mirrors the
single-block part of CakeML's `ssa_cc_trans_inst`, extends it with branch
reconciliation, and carries loop entry/exit frames for back-edge moves. -/

structure WordSsaState where
  current : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordSsaRead (state : WordSsaState) (name : Nat) : Nat :=
  match lookupNatInfo name state.current with
  | some value => value
  | none => name

def wordSsaFresh (state : WordSsaState) (name : Nat) : WordSsaState × Nat :=
  ({ current := (name, state.next) ::
        state.current.filter (fun entry => entry.1 != name),
      next := state.next + 1 },
    state.next)

def wordSsaFreshList (state : WordSsaState) : List Nat →
    WordSsaState × List Nat
  | [] => (state, [])
  | name :: names =>
      let (state, freshName) := wordSsaFresh state name
      let (state, freshNames) := wordSsaFreshList state names
      (state, freshName :: freshNames)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaRenameReturns (state : WordSsaState) :
    Option (List Nat × List Nat) →
      WordSsaState × Option (List Nat × List Nat)
  | none => (state, none)
  | some (destinations, live) =>
      let live := live.map (wordSsaRead state)
      let (state, destinations) := wordSsaFreshList state destinations
      (state, some (destinations, live))


def wordSsaRenameInst (state : WordSsaState) : WordInst → WordSsaState × WordInst
  | .arith operation =>
      match operation with
      | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let (state, freshLeft) := wordSsaFresh state destinationLeft
          let (state, freshRight) := wordSsaFresh state destinationRight
          (state, .arith (.longMul freshLeft freshRight
            sourceLeft sourceRight))
      | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let quotient := wordSsaRead state quotient
          let (state, freshLeft) := wordSsaFresh state destinationLeft
          let (state, freshRight) := wordSsaFresh state destinationRight
          (state, .arith (.longDiv freshLeft freshRight
            sourceLeft sourceRight quotient))
      | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
          let sourceLeft := wordSsaRead state sourceLeft
          let sourceRight := wordSsaRead state sourceRight
          let carryIn := wordSsaRead state carryIn
          let (state, freshDestination) := wordSsaFresh state destination
          let (state, freshCarry) := wordSsaFresh state resultCarry
          (state, .arith (.addCarry freshDestination freshCarry
            sourceLeft sourceRight carryIn))
      | .div destination dividend divisor =>
          let dividend := wordSsaRead state dividend
          let divisor := wordSsaRead state divisor
          let (state, freshDestination) := wordSsaFresh state destination
          (state, .arith (.div freshDestination dividend divisor))
  | .mem operator destination address =>
      let address := wordSsaRead state address
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          let (state, freshDestination) := wordSsaFresh state destination
          (state, .mem operator freshDestination address)
      | .store | .store8 | .store16 | .store32 =>
          (state, .mem operator (wordSsaRead state destination) address)

def wordSsaRenameLinear (state : WordSsaState) : List WordInst →
    WordSsaState × List WordInst
  | [] => (state, [])
  | instruction :: instructions =>
      let (state, instruction) := wordSsaRenameInst state instruction
      let (state, instructions) := wordSsaRenameLinear state instructions
      (state, instruction :: instructions)

def wordAllocateSsaLinear (state : WordSsaState) (instructions : List WordInst) :
    Option (WordSsaState × List WordInst × WordContext) :=
  let (state, instructions) := wordSsaRenameLinear state instructions
  (wordAllocateLinearInstructions instructions).map
    (fun context => (state, instructions, context))

/-! Branch-aware SSA renaming for the Word program fragment.  A conditional
    starts both branches from the same incoming map, but gives the second
    branch the first branch's fresh-name counter.  Variables whose branch
    versions differ are reconciled with explicit copy assignments after each
    branch.  Those copies are ordinary Word assignments, so the result stays
    inside the existing IR and can be analysed by the allocator. -/

def wordSsaRenameExp (state : WordSsaState) : WordExp α → WordExp α
  | .const value => .const value
  | .var name => .var (wordSsaRead state name)
  | .lookup store => .lookup store
  | .load address => .load (wordSsaRenameExp state address)
  | .op operator arguments =>
      .op operator (arguments.map (wordSsaRenameExp state))
  | .shift operator left right =>
      .shift operator (wordSsaRenameExp state left) (wordSsaRenameExp state right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordSsaRenameRegImm (state : WordSsaState) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (wordSsaRead state name)

def wordSsaSeq (first second : WordProg α) : WordProg α :=
  match first, second with
  | .skip, second => second
  | first, .skip => first
  | first, second => .seq first second

def wordSsaKeys (state : WordSsaState) : List Nat :=
  state.current.map (fun entry => entry.1)

def wordSsaBranchNames (base left right : WordSsaState) : List Nat :=
  (wordSsaKeys base ++ wordSsaKeys left ++ wordSsaKeys right).eraseDups

def wordSsaReconcile : List Nat → WordSsaState → WordSsaState → Nat →
    WordSsaState × WordProg α × WordProg α
  | [], _left, _right, next => ({ current := [], next := next }, .skip, .skip)
  | name :: names, left, right, next =>
      let leftName := wordSsaRead left name
      let rightName := wordSsaRead right name
      if leftName = rightName then
        let (merged, leftMoves, rightMoves) :=
          wordSsaReconcile names left right next
        ({ current := (name, leftName) :: merged.current, next := merged.next },
          leftMoves, rightMoves)
      else
        let leftMove := .assign next (.var leftName)
        let rightMove := .assign next (.var rightName)
        let (merged, leftMoves, rightMoves) :=
          wordSsaReconcile names left right (next + 1)
        ({ current := (name, next) :: merged.current, next := merged.next },
          wordSsaSeq leftMove leftMoves, wordSsaSeq rightMove rightMoves)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

structure WordSsaLoopFrame where
  entry : WordSsaState
  exit : WordSsaState
  entryNames : List Nat
  exitNames : List Nat

def wordSsaRestrict (state : WordSsaState) (names : List Nat) : WordSsaState :=
  { state with current := state.current.filter (fun entry => entry.1 ∈ names) }

def wordSsaReconcileTo (source target : WordSsaState) : List Nat →
    WordProg α
  | [] => .skip
  | name :: names =>
      let move := if wordSsaRead source name = wordSsaRead target name then
        (.skip : WordProg α)
      else
        .assign (wordSsaRead target name) (.var (wordSsaRead source name))
      wordSsaSeq move (wordSsaReconcileTo source target names)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaRefreshList (state : WordSsaState) : List Nat →
    WordSsaState × WordProg α
  | [] => (state, .skip)
  | name :: names =>
      let oldName := wordSsaRead state name
      let hadName := (lookupNatInfo name state.current).isSome
      let (state, freshName) := wordSsaFresh state name
      let (state, moves) := wordSsaRefreshList state names
      let move := if hadName then
        (.assign freshName (.var oldName) : WordProg α)
      else
        .skip
      (state, wordSsaSeq move moves)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

def wordSsaFindLoopFrame : Nat → List WordSsaLoopFrame →
    Option WordSsaLoopFrame
  | _, [] => none
  | 0, frame :: _ => some frame
  | label, _ :: frames => wordSsaFindLoopFrame (label - 1) frames

def wordSsaRenameProgramWithLoops (frames : List WordSsaLoopFrame)
    (state : WordSsaState) : WordProg α → WordSsaState × WordProg α
  | .skip => (state, .skip)
  | .assign name value =>
      let value := wordSsaRenameExp state value
      let (state, freshName) := wordSsaFresh state name
      (state, .assign freshName value)
  | .inst instruction =>
      let (state, instruction) := wordSsaRenameInst state instruction
      (state, .inst instruction)
  | .seq first second =>
      let (state, first) := wordSsaRenameProgramWithLoops frames state first
      let (state, second) := wordSsaRenameProgramWithLoops frames state second
      (state, .seq first second)
  | .store address value =>
      (state, .store (wordSsaRenameExp state address) (wordSsaRead state value))
  | .set store value =>
      (state, .set store (wordSsaRenameExp state value))
  | .raise exception =>
      (state, .raise (wordSsaRead state exception))
  | .return label values =>
      (state, .return label (values.map (wordSsaRead state)))
  | .tick => (state, .tick)
  | .break label =>
      match wordSsaFindLoopFrame label frames with
      | none => (state, .break label)
      | some frame =>
          (state, wordSsaSeq
            (wordSsaReconcileTo state frame.exit frame.exitNames)
            (.break label))
  | .continue label =>
      match wordSsaFindLoopFrame label frames with
      | none => (state, .continue label)
      | some frame =>
          (state, wordSsaSeq
            (wordSsaReconcileTo state frame.entry frame.entryNames)
            (.continue label))
  | .locValue destination source =>
      let source := wordSsaRead state source
      let (state, destination) := wordSsaFresh state destination
      (state, .locValue destination source)
  | .ffi function configuration configurationLength array arrayLength live =>
      (state, .ffi function (wordSsaRead state configuration)
        (wordSsaRead state configurationLength) (wordSsaRead state array)
        (wordSsaRead state arrayLength) (live.map (wordSsaRead state)))
  | .shareInst operator name address =>
      let address := wordSsaRenameExp state address
      match operator with
      | .load | .load8 | .load16 | .load32 =>
          let (state, name) := wordSsaFresh state name
          (state, .shareInst operator name address)
      | .store | .store8 | .store16 | .store32 =>
          (state, .shareInst operator (wordSsaRead state name) address)
  | .call returns target arguments none =>
      let arguments := arguments.map (wordSsaRead state)
      let (state, returns) := wordSsaRenameReturns state returns
      (state, .call returns target arguments none)
  | .loop liveIn body liveOut =>
      let names := (liveIn ++ liveOut).eraseDups
      let (setupState, setup) := wordSsaRefreshList state names
      let entryState := wordSsaRestrict setupState liveIn
      let exitState := wordSsaRestrict setupState liveOut
      let frame := WordSsaLoopFrame.mk entryState exitState
        liveIn.eraseDups liveOut.eraseDups
      let (bodyState, body) :=
        wordSsaRenameProgramWithLoops (frame :: frames) entryState body
      let backMoves := wordSsaReconcileTo bodyState setupState liveIn.eraseDups
      let body := wordSsaSeq body backMoves
      let program := .loop (liveIn.map (wordSsaRead setupState)) body
        (liveOut.map (wordSsaRead setupState))
      (exitState, wordSsaSeq setup program)
  | .ite operator condition right thenBranch elseBranch =>
      let right := wordSsaRenameRegImm state right
      let (thenState, thenBranch) :=
        wordSsaRenameProgramWithLoops frames state thenBranch
      let elseInput := { state with next := thenState.next }
      let (elseState, elseBranch) :=
        wordSsaRenameProgramWithLoops frames elseInput elseBranch
      let names := wordSsaBranchNames state thenState elseState
      let (merged, thenMoves, elseMoves) :=
        wordSsaReconcile names thenState elseState elseState.next
      ({ current := merged.current, next := merged.next },
        .ite operator (wordSsaRead state condition) right
          (wordSsaSeq thenBranch thenMoves)
          (wordSsaSeq elseBranch elseMoves))
  | program => (state, program)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial
def wordSsaRenameProgram (state : WordSsaState) (program : WordProg α) :
    WordSsaState × WordProg α :=
  wordSsaRenameProgramWithLoops [] state program

theorem wordSsaRenameProgram_ite :
    wordSsaRenameProgram ({ current := [], next := 10 } : WordSsaState)
        (.ite .equal 0 (.reg 0)
          (.assign 1 (.var 0)) (.assign 1 (.var 0)) : WordProg α) =
      ({ current := [(1, 12)], next := 13 },
        .ite .equal 0 (.reg 0)
          (.seq (.assign 10 (.var 0)) (.assign 12 (.var 10)))
          (.seq (.assign 11 (.var 0)) (.assign 12 (.var 11)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp, wordSsaRenameRegImm,
    wordSsaRead, wordSsaFresh, wordSsaBranchNames, wordSsaKeys,
    wordSsaReconcile, wordSsaSeq, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop, lookupNatInfo]

/-! Program-level variable collection and liveness.  Sequencing and branch
    paths use backwards transfers; loop entry/exit sets remain conservative
    until the loop SSA reconciliation and spill contracts are ported. -/

def wordExpReadVars : WordExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => wordExpReadVars address
  | .op _ arguments => arguments.flatMap wordExpReadVars
  | .shift _ left right => wordExpReadVars left ++ wordExpReadVars right

def wordProgReadVars : WordProg α → List Nat
  | .skip => []
  | .assign _ value => wordExpReadVars value
  | .inst instruction => wordInstReadVars instruction
  | .store address value => wordExpReadVars address ++ [value]
  | .set _ value => wordExpReadVars value
  | .seq first second => wordProgReadVars first ++ wordProgReadVars second
  | .ite _ condition right thenBranch elseBranch =>
      [condition] ++ (match right with | .reg name => [name] | .imm _ => []) ++
        wordProgReadVars thenBranch ++ wordProgReadVars elseBranch
  | .loop liveIn body liveOut =>
      liveIn ++ wordProgReadVars body ++ liveOut
  | .break _ | .continue _ => []
  | .raise exception => [exception]
  | .return _ values => values
  | .tick => []
  | .locValue _ source => [source]
  | .call returns _ arguments handler =>
      arguments ++ (match returns with
        | none => []
        | some (_, live) => live) ++
        (match handler with
        | none => []
        | some (_, body) => wordProgReadVars body)
  | .ffi _ configuration configurationLength array arrayLength live =>
      [configuration, configurationLength, array, arrayLength] ++ live
  | .shareInst operator name address =>
      (match operator with
      | .load | .load8 | .load16 | .load32 => []
      | .store | .store8 | .store16 | .store32 => [name]) ++
        wordExpReadVars address

def wordProgWriteVars : WordProg α → List Nat
  | .skip | .store _ _ | .set _ _ | .break _ | .continue _ | .raise _
  | .return _ _ | .tick => []
  | .assign name _ => [name]
  | .inst instruction => wordInstWriteVars instruction
  | .seq first second => wordProgWriteVars first ++ wordProgWriteVars second
  | .ite _ _ _ thenBranch elseBranch =>
      wordProgWriteVars thenBranch ++ wordProgWriteVars elseBranch
  | .loop _ body _ => wordProgWriteVars body
  | .locValue destination _ => [destination]
  | .call returns _ _ handler =>
      (match returns with
      | none => []
      | some (values, _) => values) ++
      (match handler with
      | none => []
      | some (exception, body) => exception :: wordProgWriteVars body)
  | .ffi _ _ _ _ _ _ => []
  | .shareInst operator name _ =>
      match operator with
      | .load | .load8 | .load16 | .load32 => [name]
      | .store | .store8 | .store16 | .store32 => []

def wordProgVariables (program : WordProg α) : List Nat :=
  wordProgReadVars program ++ wordProgWriteVars program

def wordProgLiveBefore (program : WordProg α) (liveAfter : List Nat) : List Nat :=
  wordProgReadVars program ++
    liveAfter.filter (fun name => name ∉ wordProgWriteVars program)

def wordListUnion (left right : List Nat) : List Nat :=
  (left ++ right).eraseDups

def wordProgAtomicClashes (program : WordProg α) (liveAfter : List Nat) :
    List (Nat × Nat) :=
  wordClashPairs (wordProgWriteVars program) liveAfter

def wordProgClashAnalysis : WordProg α → List Nat →
    List Nat × List (Nat × Nat)
  | .seq first second, liveOut =>
      let (liveMiddle, secondEdges) := wordProgClashAnalysis second liveOut
      let (liveIn, firstEdges) := wordProgClashAnalysis first liveMiddle
      (liveIn, firstEdges ++ secondEdges)
  | .ite _ condition right thenBranch elseBranch, liveOut =>
      let (thenLive, thenEdges) := wordProgClashAnalysis thenBranch liveOut
      let (elseLive, elseEdges) := wordProgClashAnalysis elseBranch liveOut
      let conditionLive := condition :: match right with
        | .reg name => [name]
        | .imm _ => []
      (wordListUnion conditionLive (wordListUnion thenLive elseLive),
        thenEdges ++ elseEdges)
  | .loop liveIn body liveOut, liveAfter =>
      let (bodyLive, bodyEdges) :=
        wordProgClashAnalysis body (wordListUnion liveIn (liveOut ++ liveAfter))
      (wordListUnion liveIn bodyLive, bodyEdges)
  | program, liveOut =>
      (wordProgLiveBefore program liveOut, wordProgAtomicClashes program liveOut)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateProgramWithSlots (slots : List Nat) (program : WordProg α) :
    Option WordContext :=
  let (liveIn, edges) := wordProgClashAnalysis program []
  wordAllocateContextWithClashes
    (slots ++ wordProgVariables program ++ liveIn) edges

def wordAllocateProgram (program : WordProg α) : Option WordContext :=
  wordAllocateProgramWithSlots [] program

def wordAllocateSsaProgram (state : WordSsaState) (program : WordProg α) :
    Option (WordSsaState × WordProg α × WordContext) :=
  let (state, program) := wordSsaRenameProgram state program
  let (liveIn, edges) := wordProgClashAnalysis program []
  (wordAllocateContextWithClashes
      (wordProgVariables program ++ liveIn) edges).map
    (fun context => (state, program, context))

/-! Apply a completed colouring to the full current Word syntax.  Control
    labels and function labels are not virtual registers; every data-register
    position, including nested handlers and loop live sets, is transformed. -/

def wordApplyColourExp (colour : Nat → Nat) : WordExp α → WordExp α
  | .const value => .const value
  | .var name => .var (colour name)
  | .lookup store => .lookup store
  | .load address => .load (wordApplyColourExp colour address)
  | .op operator arguments =>
      .op operator (arguments.map (wordApplyColourExp colour))
  | .shift operator left right =>
      .shift operator (wordApplyColourExp colour left)
        (wordApplyColourExp colour right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

def wordApplyColourRegImm (colour : Nat → Nat) : WordRegImm α → WordRegImm α
  | .imm value => .imm value
  | .reg name => .reg (colour name)

def wordApplyColourArith (colour : Nat → Nat) : WordArith → WordArith
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      .longMul (colour destinationLeft) (colour destinationRight)
        (colour sourceLeft) (colour sourceRight)
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      .longDiv (colour destinationLeft) (colour destinationRight)
        (colour sourceLeft) (colour sourceRight) (colour quotient)
  | .addCarry destination resultCarry sourceLeft sourceRight carryIn =>
      .addCarry (colour destination) (colour resultCarry)
        (colour sourceLeft) (colour sourceRight) (colour carryIn)
  | .div destination dividend divisor =>
      .div (colour destination) (colour dividend) (colour divisor)

def wordApplyColourInst (colour : Nat → Nat) : WordInst → WordInst
  | .arith operation => .arith (wordApplyColourArith colour operation)
  | .mem operator destination address =>
      .mem operator (colour destination) (colour address)

def wordApplyColour (colour : Nat → Nat) : WordProg α → WordProg α
  | .skip => .skip
  | .assign name value =>
      .assign (colour name) (wordApplyColourExp colour value)
  | .inst instruction => .inst (wordApplyColourInst colour instruction)
  | .store address value =>
      .store (wordApplyColourExp colour address) (colour value)
  | .set store value => .set store (wordApplyColourExp colour value)
  | .seq first second =>
      .seq (wordApplyColour colour first) (wordApplyColour colour second)
  | .ite operator condition right thenBranch elseBranch =>
      .ite operator (colour condition) (wordApplyColourRegImm colour right)
        (wordApplyColour colour thenBranch) (wordApplyColour colour elseBranch)
  | .loop liveIn body liveOut =>
      .loop (liveIn.map colour) (wordApplyColour colour body) (liveOut.map colour)
  | .break label => .break label
  | .continue label => .continue label
  | .raise exception => .raise (colour exception)
  | .return label values => .return label (values.map colour)
  | .tick => .tick
  | .locValue destination source =>
      .locValue (colour destination) (colour source)
  | .call returns target arguments none =>
      .call (returns.map (fun (values, live) =>
        (values.map colour, live.map colour))) target (arguments.map colour)
        none
  | .call returns target arguments (some (exception, body)) =>
      .call (returns.map (fun (values, live) =>
        (values.map colour, live.map colour))) target (arguments.map colour)
        (some (colour exception, wordApplyColour colour body))
  | .ffi function configuration configurationLength array arrayLength live =>
      .ffi function (colour configuration) (colour configurationLength)
        (colour array) (colour arrayLength) (live.map colour)
  | .shareInst operator name address =>
      .shareInst operator (colour name) (wordApplyColourExp colour address)
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def wordAllocateProgramWithSlotsAndColour (slots : List Nat)
    (program : WordProg α) : Option (WordContext × WordProg α) :=
  let (liveIn, edges) := wordProgClashAnalysis program []
  (wordAllocateContextWithClashes
      (slots ++ wordProgVariables program ++ liveIn) edges).map
    (fun context => (context, wordApplyColour (wordFindVar context) program))

theorem wordApplyColour_assign (colour : Nat → Nat) (name source : Nat) :
    wordApplyColour colour (.assign name (.var source) : WordProg α) =
      .assign (colour name) (.var (colour source)) := by
  simp [wordApplyColour, wordApplyColourExp]

theorem wordApplyColour_preserves_control_labels (colour : Nat → Nat) (label : Nat) :
    wordApplyColour colour (.break label : WordProg α) = .break label := by
  simp [wordApplyColour]

theorem wordProgClashAnalysis_skip :
    wordProgClashAnalysis (.skip : WordProg α) [] = ([], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs]

theorem wordProgClashAnalysis_seq :
    wordProgClashAnalysis
        ((.seq (.assign 0 (.var 1)) (.assign 2 (.var 0))) : WordProg α) [] =
      ([1], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars,
    wordProgWriteVars, wordProgLiveBefore, wordProgAtomicClashes,
    wordClashPairs, wordExpReadVars]

theorem wordProgClashAnalysis_ite :
    wordProgClashAnalysis
        ((.ite .equal 0 (.reg 1)
          (.assign 2 (.var 0)) (.assign 3 (.var 0))) : WordProg α) [] =
      ([0, 1], []) := by
  simp [wordProgClashAnalysis, wordProgReadVars, wordProgWriteVars,
    wordProgLiveBefore, wordProgAtomicClashes, wordClashPairs,
    wordListUnion, wordExpReadVars, List.eraseDups, List.eraseDupsBy,
    List.eraseDupsBy.loop]

theorem wordLinearClashAnalysis_empty (liveOut : List Nat) :
    wordLinearClashAnalysis [] liveOut = (liveOut, []) := by
  rfl

theorem wordInstVars_addCarry :
    wordInstVars (.arith (.addCarry 1 2 3 4 5)) = [3, 4, 5, 1, 2] := by
  rfl

theorem wordSsaRenameLinear_addCarry :
    wordSsaRenameLinear
        { current := [(2, 100), (3, 101), (4, 102)], next := 200 }
        [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      ({ current := [(6, 203), (5, 202), (1, 201), (0, 200),
          (2, 100), (3, 101), (4, 102)], next := 204 },
        [.arith (.addCarry 200 201 100 101 102),
          .arith (.addCarry 202 203 200 201 100)]) := by
  rfl

theorem wordAllocateLinearInstructions_example :
    wordAllocateLinearInstructions
      [.arith (.addCarry 0 1 2 3 4), .arith (.addCarry 5 6 0 1 2)] =
      some { vars := [(6, 8), (5, 7), (1, 3), (0, 2), (4, 6), (3, 5), (2, 4)] } := by
  rfl

theorem wordAllocateVarsWithClashes_sound (slots : List Nat)
    (edges : List (Nat × Nat)) (colouring : NatInfoMap Nat)
    (hcolouring : wordAllocateVarsWithClashes slots edges = some colouring) :
    wordColouringUsesAllocatable slots.eraseDups colouring = true ∧
      wordColouringRespectsClashes edges colouring = true := by
  simp [wordAllocateVarsWithClashes] at hcolouring
  split at hcolouring <;> try simp_all
  all_goals
    rcases hcolouring with ⟨hcheck, heq⟩
    simpa [heq] using hcheck

/-! Spill-aware allocation boundary.  CakeML's `word_to_stack` pass consumes
    the spill information produced by `word_alloc`; keeping that information
    explicit here prevents register exhaustion from being confused with a
    failed compilation.  Stack rewriting is intentionally a following pass:
    this result records a fresh stack slot for every value that cannot use a
    target register, while preserving the same clash check for values that do
    receive registers. -/

inductive WordLocation where
  | register (register : Nat)
  | stack (slot : Nat)
  deriving DecidableEq, Repr

structure WordSpillState where
  locations : NatInfoMap WordLocation
  nextSpill : Nat
  deriving Repr

def wordUsedLocationRegisters (names : List Nat)
    (locations : NatInfoMap WordLocation) : List Nat :=
  match names with
  | [] => []
  | name :: names =>
      let registers := match lookupNatInfo name locations with
        | some (.register register) => [register]
        | some (.stack _) | none => []
      registers ++ wordUsedLocationRegisters names locations

def wordGreedyAllocateWithSpills : List Nat → List (Nat × Nat) →
    WordSpillState → WordSpillState
  | [], _, state => state
  | name :: names, edges, state =>
      let forbidden :=
        wordUsedLocationRegisters (wordNeighbours name edges) state.locations
      let state := match wordFirstAvailable (wordColourCandidates name) forbidden with
        | some register =>
            { state with locations := (name, .register register) :: state.locations }
        | none =>
            { locations := (name, .stack state.nextSpill) :: state.locations,
              nextSpill := state.nextSpill + 1 }
      wordGreedyAllocateWithSpills names edges state

def wordSpillAllocationRespectsClashes (edges : List (Nat × Nat))
    (locations : NatInfoMap WordLocation) : Bool :=
  match edges with
  | [] => true
  | (left, right) :: edges =>
      match lookupNatInfo left locations, lookupNatInfo right locations with
      | some (.register leftRegister), some (.register rightRegister) =>
          leftRegister != rightRegister &&
            wordSpillAllocationRespectsClashes edges locations
      | some _, some _ => wordSpillAllocationRespectsClashes edges locations
      | _, _ => false

def wordAllocateVarsWithSpills (slots : List Nat)
    (edges : List (Nat × Nat)) : Option WordSpillState :=
  let state := wordGreedyAllocateWithSpills slots.eraseDups edges
    { locations := [], nextSpill := 0 }
  if wordSpillAllocationRespectsClashes edges state.locations then some state
  else none

theorem wordAllocateVarsWithSpills_sound (slots : List Nat)
    (edges : List (Nat × Nat)) (state : WordSpillState)
    (hstate : wordAllocateVarsWithSpills slots edges = some state) :
    wordSpillAllocationRespectsClashes edges state.locations = true := by
  simp [wordAllocateVarsWithSpills] at hstate
  rcases hstate with ⟨hcheck, heq⟩
  simpa [heq] using hcheck

theorem wordAllocateVarsWithSpills_example :
    wordAllocateVarsWithSpills [0, 1] [(0, 1)] =
      some { locations := [(1, .register 3), (0, .register 2)], nextSpill := 0 } := by
  rfl

theorem wordAllocateVarsWithSpills_spills_example :
    (wordAllocateVarsWithSpills (List.range 29)
      (wordPairwiseClashes (List.range 29))).map
        (fun state => state.nextSpill != 0) = some true := by
  native_decide

theorem wordAllocatableRegisters_safe :
    ∀ register ∈ wordAllocatableRegisters,
      wordRegisterIsAllocatable register = true := by
  intro register hregister
  simp [wordAllocatableRegisters, wordRegisterIsAllocatable] at hregister ⊢
  omega

theorem wordAllocatableRegisters_not_reserved :
    ∀ register ∈ wordAllocatableRegisters,
      wordRegisterIsReserved register = false := by
  intro register hregister
  simp [wordAllocatableRegisters, wordRegisterIsReserved] at hregister ⊢
  omega

theorem wordPreferredRegister_safe (name register : Nat)
    (hregister : wordPreferredRegister name = some register) :
    wordRegisterIsAllocatable register = true := by
  simp [wordPreferredRegister] at hregister
  rcases hregister with ⟨hbound, rfl⟩
  simp [wordRegisterIsAllocatable]
  omega

theorem wordAllocateContext_examples :
    wordAllocateContext [0, 1, 29, 30] =
      some { vars := [(0, 2), (1, 3), (29, 4), (30, 5)] } := by
  rfl

theorem wordAllocateContext_preserves_small_names :
    wordAllocateContext [0, 1, 2, 3] =
      some { vars := [(0, 2), (1, 3), (2, 4), (3, 5)] } := by
  rfl

theorem wordAllocateContext_add_slots :
    wordAllocateContext [2, 0, 1] =
      some { vars := [(2, 4), (0, 2), (1, 3)] } := by
  rfl

theorem wordAllocateContextWithClashes_examples :
    wordAllocateContextWithClashes [0, 1, 28]
        [(0, 1), (1, 28)] =
      some { vars := [(28, 2), (1, 3), (0, 2)] } := by
  rfl

theorem wordAllocateVarsWithClashes_safe_example :
    wordAllocateVarsWithClashes [0, 1]
        [(0, 1)] = some [(1, 3), (0, 2)] := by
  rfl

end Flapjack
