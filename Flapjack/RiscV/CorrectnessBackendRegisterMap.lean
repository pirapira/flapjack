import Flapjack.RiscV.CorrectnessBackend
import Flapjack.RiscV.InstructionDataCommutation

/-!
# Backend correctness through the CakeML `riscv_names` map

This is the first green, additive slice of the CakeML ABI rebase
(bead `flapjack-pxn.8.5.10.4.2.2.3`).  It keeps the raw Backend selector and
evaluators unchanged and instead routes their results through the one-time
stack-to-hardware register map now available in `Flapjack.RiscV.RegisterMap`.

Two facts are established:

* an internal read on a transferred hardware state resolves the internal name
  through `labRegisterOfNat` exactly once and returns the raw internal value;
* running the relabeled image of a straight-line Backend compilation on the
  transferred state transfers the raw execution result.

Neither statement changes emission or abstract semantics; they are the boundary
lemmas the later atomic rebase consumes.
-/

namespace Flapjack.RiscV

variable {width : Nat}

/-- Reading an internal Cake register from a transferred hardware state agrees
with the raw internal read: the name is resolved through `labRegisterOfNat`
once, and the hardware read lands on the same place the raw read does. -/
theorem readRegisterInternal_transfer (state : State width) {name : Nat}
    {register : Fin 32} (h : registerOfNat name = some register) :
    readRegisterInternal (transferState state) name = readRegister state register := by
  have hmap : labRegisterOfNat name = some (riscvForward register) := by
    rw [labRegisterOfNat_eq_registerOfNat_map_forward, h]
    simp
  unfold readRegisterInternal
  rw [hmap]
  simp

/-- Writing an internal Cake register into a transferred hardware state agrees
with the raw internal write: the name is resolved through `labRegisterOfNat`
once, and the hardware write lands on the same place the raw write does.  This
is the write counterpart of `readRegisterInternal_transfer` and completes the
register-boundary accessor pair the rebase consumes. -/
theorem writeRegisterInternalNat_transfer (state : State width) {name : Nat}
    {register : Fin 32} (h : registerOfNat name = some register) (value : Word width) :
    writeRegisterInternalNat (transferState state) name value =
      transferState (writeRegisterInternal riscvForward state register value) := by
  have hmap : labRegisterOfNat name = some (riscvForward register) := by
    rw [labRegisterOfNat_eq_registerOfNat_map_forward, h]
    simp
  rw [writeRegisterInternalNat_of_some (state := transferState state) hmap]
  exact writeRegister_transfer_forward state register value

/-- Above the architectural range the one-time Cake map is the identity, so the
internal register accessors reduce to the raw `registerOfNat` selection.  This
confines the later emission rebase to registers `0`-`31`. -/
theorem readRegisterInternal_eq_registerOfNat_map_of_ge_32 (state : State width)
    {name : Nat} (h : 32 ≤ name) :
    readRegisterInternal state name = (registerOfNat name).map (readRegister state) := by
  unfold readRegisterInternal
  rw [labRegisterOfNat_eq_registerOfNat_of_ge_32 h]

/-- Write-side counterpart of `readRegisterInternal_eq_registerOfNat_map_of_ge_32`. -/
theorem writeRegisterInternalNat_eq_registerOfNat_of_ge_32 (state : State width)
    {name : Nat} (h : 32 ≤ name) (value : Word width) :
    writeRegisterInternalNat state name value =
      (registerOfNat name).elim state (fun register => writeRegister state register value) := by
  unfold writeRegisterInternalNat
  rw [labRegisterOfNat_eq_registerOfNat_of_ge_32 h]

/-- Backend correctness through the Cake register map: for a straight-line
program, the relabeled image of the Backend-selected code executes on the
transferred state exactly as transferring the raw selected execution. -/
theorem wordProgToRiscV_transfer_relabel_sound_of_straightLine [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV program = some code)
    (hzero : ∀ instruction ∈ code,
      ∀ register ∈ instructionWrites instruction, riscvForward register ≠ 0)
    (hname : ∀ instruction ∈ code,
      ∀ register ∈ instructionWrites instruction, register ≠ 0) :
    evalWordProg state program = some (executeInstructions state code) ∧
      executeInstructions (transferState state) (relabelInstructions code) =
        transferState (executeInstructions state code) :=
  ⟨wordProgToRiscV_sound_of_straightLine state program hstraight code hcompile,
   executeInstructions_transfer_relabel state code hzero hname⟩

/-- The Cake map sends a hardware register to the architectural zero register
exactly when that register is the internal zero role `27`.  This is the
`Fin`-level form of `riscvForward_eq_zero_iff` used to discharge the write-set
side conditions of the transfer/relabel soundness theorem. -/
theorem riscvForward_ne_zero_iff {register : Fin 32} :
    riscvForward register ≠ 0 ↔ register.val ≠ 27 :=
  not_congr riscvForward_eq_zero_iff

/-- The transfer/relabel soundness theorem with its side conditions discharged
from a single write-set invariant: no instruction writes the architectural zero
register or the internal zero role.  The Cake map's only preimage of `0` is
`27`, so excluding both names from every write set yields the `hzero` and
`hname` premises without any extra semantic assumption on the abstract state. -/
theorem wordProgToRiscV_transfer_relabel_sound_of_writes [NeZero width]
    (state : State width) (program : WordProg (Word width))
    (hstraight : WordRiscVStraightLine program)
    (code : List (Instruction width))
    (hcompile : wordProgToRiscV program = some code)
    (hwrites : ∀ instruction ∈ code,
      ∀ register ∈ instructionWrites instruction,
        register.val ≠ 0 ∧ register.val ≠ 27) :
    evalWordProg state program = some (executeInstructions state code) ∧
      executeInstructions (transferState state) (relabelInstructions code) =
        transferState (executeInstructions state code) :=
  wordProgToRiscV_transfer_relabel_sound_of_straightLine state program hstraight
    code hcompile
    (fun instruction hinst register hreg =>
      riscvForward_ne_zero_iff.mpr (hwrites instruction hinst register hreg).2)
    (fun instruction hinst register hreg hz =>
      (hwrites instruction hinst register hreg).1 (by simp [hz]))

example {register : Fin 32} :
    (riscvForward register ≠ 0) ↔ register.val ≠ 27 :=
  riscvForward_ne_zero_iff

example : riscvForward (27 : Fin 32) = 0 := by decide

example : riscvForward (0 : Fin 32) ≠ 0 := by decide

end Flapjack.RiscV