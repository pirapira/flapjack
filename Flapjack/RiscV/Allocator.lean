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
