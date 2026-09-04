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

end Flapjack
