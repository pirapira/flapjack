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

/-! Straight-line SSA renaming.  Each write receives a fresh virtual name;
reads use the latest name for their source variable.  This mirrors the
single-block part of CakeML's `ssa_cc_trans_inst` and keeps the renaming state
explicit so branch reconciliation can be added without changing the API. -/

structure WordSsaState where
  current : NatInfoMap Nat
  next : Nat
  deriving Repr

def wordSsaRead (state : WordSsaState) (name : Nat) : Nat :=
  match lookupNatInfo name state.current with
  | some value => value
  | none => name

def wordSsaFresh (state : WordSsaState) (name : Nat) : WordSsaState × Nat :=
  ({ current := (name, state.next) :: state.current, next := state.next + 1 },
    state.next)

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
