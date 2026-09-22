import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.Proofs.PanSimp.Evaluate

namespace Flapjack

/-! Counterpart of Cake's `compile_Others_tac` simple cases
    (`cakeml/pancake/proofs/pan_simpProofScript.sml:667-1015`): `pan_simp`
    leaves a fixed family of program constructs syntactically unchanged, so
    the compiled program evaluates exactly as the source program. -/

theorem panSimpProg_assign (kind : VarKind) (name : VarName) (value : Exp α) :
    panSimpProg (.assign kind name value : Prog α) = .assign kind name value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_primitive (name : VarName) (operator : PrimOp) (args : List (Exp α)) :
    panSimpProg (.primitive name operator args : Prog α) =
      .primitive name operator args := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_store (address value : Exp α) :
    panSimpProg (.store address value : Prog α) = .store address value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_store32 (address value : Exp α) :
    panSimpProg (.store32 address value : Prog α) = .store32 address value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_storeByte (address value : Exp α) :
    panSimpProg (.storeByte address value : Prog α) = .storeByte address value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_break : panSimpProg (.break : Prog α) = .break := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_continue : panSimpProg (.continue : Prog α) = .continue := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_raise (exception : ExceptionId) (value : Exp α) :
    panSimpProg (.raise exception value : Prog α) = .raise exception value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_return (value : Exp α) :
    panSimpProg (.return value : Prog α) = .return value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_extCall (function : FunName)
    (configuration configurationLength array arrayLength : Exp α) :
    panSimpProg (.extCall function configuration configurationLength array arrayLength :
      Prog α) =
      .extCall function configuration configurationLength array arrayLength := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_shMemLoad (size : OpSize) (kind : VarKind) (name : VarName)
    (address : Exp α) :
    panSimpProg (.shMemLoad size kind name address : Prog α) =
      .shMemLoad size kind name address := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_shMemStore (size : OpSize) (address value : Exp α) :
    panSimpProg (.shMemStore size address value : Prog α) =
      .shMemStore size address value := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem panSimpProg_tick : panSimpProg (.tick : Prog α) = .tick := by
  simp [panSimpProg, seqAssoc, retToTail]

/-- `compile_Others` evaluation preservation: whenever `panSimpProg` leaves a
    program unchanged, the compiled program evaluates exactly as the source
    program. -/
theorem evalPanValueFfiClockProg_eq_of_panSimpProg_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog α))
    (baseAddress topAddress bytesInWord : α) (fuel : Nat)
    (locals globals : VarName → Option (PanValue α))
    (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat)
    (program : Prog α) (h : panSimpProg program = program) :
    evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        (panSimpProg program) =
      evalPanValueFfiClockProg context primitive handler structs functions
        baseAddress topAddress bytesInWord fuel locals globals memory ffi clock
        program := by
  rw [h]

end Flapjack
