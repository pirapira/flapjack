import Flapjack.PanToCrepCorrectnessBoundary

namespace Flapjack

/-! Structural induction for properties used by the Lean analogue of Cake's
    `pc_compile_correct`.  The Call handler is stored inside an option rather
    than as a direct `Prog` field, so it is exposed explicitly here; this is
    the same recursive shape used by the source-state correctness induction.
    Instantiating `P` with `PanValuePcCompileCorrect` lets the constructor
    branch theorems compose into a program-level correctness result. -/
theorem panValueProg_compile_correct_induction
    (P : Prog α → Prop)
    (hskip : P (.skip : Prog α))
    (hdec : ∀ (name : VarName) (shape : Shape) (value : Exp α)
      (body : Prog α), P body → P (.dec name shape value body))
    (hassign : ∀ (kind : VarKind) (name : VarName) (value : Exp α),
      P (.assign kind name value))
    (hprimitive : ∀ (name : VarName) (operator : PrimOp)
      (args : List (Exp α)), P (.primitive name operator args))
    (hstore : ∀ (address value : Exp α), P (.store address value))
    (hstore32 : ∀ (address value : Exp α), P (.store32 address value))
    (hstoreByte : ∀ (address value : Exp α), P (.storeByte address value))
    (hseq : ∀ (first second : Prog α), P first → P second → P (.seq first second))
    (hite : ∀ (condition : Exp α) (thenBranch elseBranch : Prog α),
      P thenBranch → P elseBranch → P (.ite condition thenBranch elseBranch))
    (hwhile : ∀ (condition : Exp α) (body : Prog α),
      P body → P (.while condition body))
    (hbreak : P (.break : Prog α))
    (hcontinue : P (.continue : Prog α))
    (hcall : ∀
      (info : Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)))
      (name : FunName) (args : List (Exp α)),
      (match info with
       | some (_, some (_, _, handler)) => P handler
       | _ => True) →
      P (.call info name args))
    (hdecCall : ∀ (name : VarName) (shape : Shape) (function : FunName)
      (args : List (Exp α)) (body : Prog α),
      P body → P (.decCall name shape function args body))
    (hextCall : ∀ (function : FunName)
      (configuration configurationLength array arrayLength : Exp α),
      P (.extCall function configuration configurationLength array arrayLength))
    (hraise : ∀ (exception : ExceptionId) (value : Exp α),
      P (.raise exception value))
    (hreturn : ∀ (value : Exp α), P (.return value))
    (hshMemLoad : ∀ (size : OpSize) (kind : VarKind) (name : VarName)
      (address : Exp α),
      P (.shMemLoad size kind name address))
    (hshMemStore : ∀ (size : OpSize) (address value : Exp α),
      P (.shMemStore size address value))
    (htick : P (.tick : Prog α))
    (hannot : ∀ (tag text : String),
      P (@Prog.annot α tag text)) :
    ∀ program : Prog α, P program := by
  let rec go : (program : Prog α) → P program
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
    | .call info name args =>
        hcall info name args (by
          cases info with
          | none => exact True.intro
          | some info =>
              cases info with
              | mk destination handlerInfo =>
                  cases handlerInfo with
                  | none => exact True.intro
                  | some handler =>
                      cases handler with
                      | mk exception handlerInfo =>
                          cases handlerInfo with
                          | mk handlerVar handlerProgram =>
                              exact go handlerProgram)
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
