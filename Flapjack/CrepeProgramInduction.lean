import Flapjack.CrepeProgramRelation

/-!
The induction assembly for the Pancake-to-Crep program relation.

The source evaluator has a recursive `Prog` syntax, while the `call` case
contains a handler program inside an option-valued metadata field.  Lean's
structural induction therefore supplies hypotheses for declaration bodies,
sequence branches, conditionals, loops, and declaration-call bodies, but not
for a call handler hidden in that metadata.  The handler-aware call case is
kept as an explicit premise here; the ordinary call correctness module can
instantiate it once its callee/handler relation is available.

This theorem is the Lean counterpart of the case-assembly layer surrounding
CakeML's `pc_compile_correct`: individual constructor proofs remain separate,
and this result performs only the final syntax induction.
-/

namespace Flapjack

theorem panValueCrepProgramCorrect_induction
    [BEq α] [LawfulBEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (hskip : PanValueCrepProgramCorrect (.skip : Prog α))
    (hdec : ∀ (name : VarName) (shape : Shape) (value : Exp α)
      (body : Prog α),
      PanValueCrepProgramCorrect body →
      PanValueCrepProgramCorrect (.dec name shape value body))
    (hassign : ∀ (kind : VarKind) (name : VarName) (value : Exp α),
      PanValueCrepProgramCorrect (.assign kind name value))
    (hprimitive : ∀ (name : VarName) (operator : PrimOp)
      (args : List (Exp α)),
      PanValueCrepProgramCorrect (.primitive name operator args))
    (hstore : ∀ (address value : Exp α),
      PanValueCrepProgramCorrect (.store address value))
    (hstore32 : ∀ (address value : Exp α),
      PanValueCrepProgramCorrect (.store32 address value))
    (hstoreByte : ∀ (address value : Exp α),
      PanValueCrepProgramCorrect (.storeByte address value))
    (hseq : ∀ (first second : Prog α),
      PanValueCrepProgramCorrect first →
      PanValueCrepProgramCorrect second →
      PanValueCrepProgramCorrect (.seq first second))
    (hite : ∀ (condition : Exp α) (thenBranch elseBranch : Prog α),
      PanValueCrepProgramCorrect thenBranch →
      PanValueCrepProgramCorrect elseBranch →
      PanValueCrepProgramCorrect (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : Exp α) (body : Prog α),
      PanValueCrepProgramCorrect body →
      PanValueCrepProgramCorrect (.while condition body))
    (hbreak : PanValueCrepProgramCorrect (.break : Prog α))
    (hcontinue : PanValueCrepProgramCorrect (.continue : Prog α))
    (hcall : ∀
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (name : FunName) (args : List (Exp α)),
      PanValueCrepProgramCorrect (.call info name args))
    (hdecCall : ∀ (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α),
      PanValueCrepProgramCorrect body →
      PanValueCrepProgramCorrect (.decCall name shape function args body))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Exp α),
      PanValueCrepProgramCorrect
        (.extCall function configuration configurationLength array arrayLength))
    (hraise : ∀ (exception : ExceptionId) (value : Exp α),
      PanValueCrepProgramCorrect (.raise exception value))
    (hreturn : ∀ (value : Exp α),
      PanValueCrepProgramCorrect (.return value))
    (hshMemLoad : ∀ (size : OpSize) (kind : VarKind) (name : VarName)
      (address : Exp α),
      PanValueCrepProgramCorrect (.shMemLoad size kind name address))
    (hshMemStore : ∀ (size : OpSize) (address value : Exp α),
      PanValueCrepProgramCorrect (.shMemStore size address value))
    (htick : PanValueCrepProgramCorrect (.tick : Prog α))
    (hannot : ∀ (tag text : String),
      PanValueCrepProgramCorrect (@Prog.annot α tag text)) :
    ∀ program : Prog α, PanValueCrepProgramCorrect program := by
  let rec go : (program : Prog α) → PanValueCrepProgramCorrect program
    | .skip => hskip
    | .dec name shape value body => hdec name shape value body (go body)
    | .assign kind name value => hassign kind name value
    | .primitive name operator args => hprimitive name operator args
    | .store address value => hstore address value
    | .store32 address value => hstore32 address value
    | .storeByte address value => hstoreByte address value
    | .seq first second => hseq first second (go first) (go second)
    | .ite condition thenBranch elseBranch =>
        hite condition thenBranch elseBranch (go thenBranch) (go elseBranch)
    | .while condition body => hwhile condition body (go body)
    | .break => hbreak
    | .continue => hcontinue
    | .call info name args => hcall info name args
    | .decCall name shape function args body =>
        hdecCall name shape function args body (go body)
    | .extCall function configuration configurationLength array arrayLength =>
        hextCall function configuration configurationLength array arrayLength
    | .raise exception value => hraise exception value
    | .return value => hreturn value
    | .shMemLoad size kind name address => hshMemLoad size kind name address
    | .shMemStore size address value => hshMemStore size address value
    | .tick => htick
    | .annot tag text => hannot tag text
    termination_by program => sizeOf program
  exact fun program => go program

end Flapjack
