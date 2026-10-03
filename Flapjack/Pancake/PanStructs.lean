import Flapjack.HolRef
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanStatic
import Flapjack.Pancake.PanStructs.CompileShapeExact

/-!
The named-structure elimination pass from CakeML's `pan_structs` theory.

Named structures are converted to raw `Comb` shapes and `RStruct` values. The
context records the structure declarations and the source-level local/global
shapes needed to resolve field projections. Malformed names deliberately use
the same defensive defaults as the HOL pass (`One`, index zero, or an empty
field list); the static checker is responsible for rejecting such programs.

The generic production carriers in this module remain distinct from the native
MlString/ShapeHOL compiler in the `PanStructs` submodules. The latter has the
full program/declaration correctness proofs and observational/top-level
semantics results in `Pancake/Proofs/PanStructs/{CompileCorrectExact,
CompileDeclsCorrectExact,SemanticsEq,CompileTopSemanticsDeclsExact}.lean`.
Those source results do not certify every generic production helper or the
executed pipeline; their local carrier notes and routing obligations remain.
-/

namespace Flapjack

/-! Faithful executable port of `pan_structs$afindi` from
    `cakeml/pancake/pan_structsScript.sml:25-32`; it compares keys by equality
    and returns the first zero-based matching position. -/
@[hol "cakeml/pancake/pan_structsScript.sml" "afindi_def"]
def afindi [DecidableEq α] (key : α) : List (α × β) → Option Nat
  | [] => none
  | (candidate, _) :: entries =>
      if key = candidate then some 0
      else match afindi key entries with
        | none => none
        | some index => some (index + 1)
termination_by entries => sizeOf entries
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

theorem afindi_cons [DecidableEq α] (key : α) (entry : α × β) (rest : List (α × β)) :
    afindi key (entry :: rest) =
      if key = entry.1 then some 0
      else match afindi key rest with
        | none => none
        | some index => some (index + 1) := by
  obtain ⟨candidate, value⟩ := entry
  simp [afindi]

structure StructPassContext where
  structs : StructContext
  locals : InfoMap Shape
  globals : InfoMap Shape
  deriving Repr

@[simp] theorem lookupInfoWithRest_self (name : String) (info : StructInfo)
    (context : StructContext) :
    lookupInfoWithRest name ((name, info) :: context) = some (info, context) := by
  simp [lookupInfoWithRest]

def structFindFieldIndex [BEq String] (field : FieldName) :
    List (FieldName × Shape) → Option Nat
  | [] => none
  | (candidate, _) :: fields =>
      if candidate == field then some 0
      else (structFindFieldIndex field fields).map (· + 1)

def structCompileShapeDepth : Shape → Nat
  | .one => 1
  | .comb shapes => 1 + structCompileShapeDepths shapes
  | .named _ => 1
where
  structCompileShapeDepths : List Shape → Nat
    | [] => 0
    | shape :: shapes => structCompileShapeDepth shape + structCompileShapeDepths shapes

def structCompileContextFuel : StructContext → Nat
  | [] => 0
  | (_, info) :: context =>
      1 + structCompileFieldFuel info.fields + structCompileContextFuel context
where
  structCompileFieldFuel : List (FieldName × Shape) → Nat
    | [] => 0
    | (_, shape) :: fields => structCompileShapeDepth shape + structCompileFieldFuel fields

/-! Fuel-indexed auxiliary analogue of Cake's `compile_shape`, retained for the
    explicit fuel-indexed map lemma and its regression fixture. Production
    `structCompileShape` below now uses the no-fuel well-founded definition that
    mirrors HOL's mutual recursion and suffix-context termination measure. -/
def structCompileShapeFuel : Nat → StructContext → Shape → Shape
  | 0, _, _ => .one
  | _fuel + 1, _context, .one => .one
  | fuel + 1, context, .comb shapes =>
      .comb (structCompileShapesFuel fuel context shapes)
  | fuel + 1, context, .named name =>
      match lookupInfoWithRest name context with
      | some (info, suffix) =>
          .comb (structCompileShapesFuel fuel suffix (info.fields.map Prod.snd))
      | none => .one
  termination_by fuel _context shape => (fuel, sizeOf shape)
where
  structCompileShapesFuel (fuel : Nat) (context : StructContext) :
      List Shape → List Shape
    | [] => []
    | shape :: shapes =>
        structCompileShapeFuel fuel context shape ::
          structCompileShapesFuel fuel context shapes
  termination_by shapes => (fuel, sizeOf shapes)
  decreasing_by all_goals simp_wf <;> omega

/-- Looking up a declaration and returning its suffix always strictly shortens
    the context, matching the first component of Cake's `compile_shape`
    termination measure. -/
theorem lookupInfoWithRest_suffix_length_lt [BEq String] (name : String)
    (context : StructContext) (info : StructInfo) (suffix : StructContext)
    (hlookup : lookupInfoWithRest name context = some (info, suffix)) :
    suffix.length < context.length := by
  induction context with
  | nil => simp [lookupInfoWithRest] at hlookup
  | cons entry context ih =>
      by_cases hmatch : entry.1 == name
      · simp [lookupInfoWithRest, hmatch] at hlookup
        rcases hlookup with ⟨_, rfl⟩
        simp
      · simp only [lookupInfoWithRest, hmatch] at hlookup
        have htail := ih hlookup
        simp
        omega

/-! The production compiler uses a well-founded, no-fuel version of Cake's
    mutually recursive `compile_shape` and `compile_shapes`. Its lexicographic
    measure mirrors the HOL definition: a named declaration recurses only on
    the strictly shorter context suffix, while Comb children and list tails
    decrease their syntax size. -/
def structCompileShapeWF : StructContext → Shape → Shape
  | _context, .one => .one
  | context, .comb shapes => .comb (structCompileShapesWF context shapes)
  | context, .named name =>
      match _hlookup : lookupInfoWithRest name context with
      | some (info, suffix) =>
          .comb (structCompileShapesWF suffix (info.fields.map Prod.snd))
      | none => .one
termination_by context shape => (context.length, sizeOf shape)
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | apply Prod.Lex.left
      exact lookupInfoWithRest_suffix_length_lt name context info suffix _hlookup
    | omega
where
  structCompileShapesWF : StructContext → List Shape → List Shape
    | _context, [] => []
    | context, shape :: shapes =>
        structCompileShapeWF context shape :: structCompileShapesWF context shapes
  termination_by context shapes => (context.length, sizeOf shapes)
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals exact lookupInfoWithRest_suffix_length_lt name context info suffix hlookup

def structCompileShape (context : StructContext) (shape : Shape) : Shape :=
  structCompileShapeWF context shape

def structOldExpShape (context : StructPassContext) : Exp α → Shape
  | .var kind name =>
      match kind with
      | .local => (lookupInfo name context.locals).getD .one
      | .global => (lookupInfo name context.globals).getD .one
  | .rStruct fields => .comb (structOldExpShapes context fields)
  | .rField index value =>
      match structOldExpShape context value with
      | .comb shapes => shapes.getD index .one
      | _ => .one
  | .nStruct name _ => .named name
  | .nField field value =>
      match structOldExpShape context value with
      | .named name =>
          match lookupInfo name context.structs with
          | some info =>
              match lookupInfo field info.fields with
              | some shape => shape
              | none => .one
          | none => .one
      | _ => .one
  | .load shape _ => shape
  | _ => .one
termination_by expression => sizeOf expression
where
  structOldExpShapes (context : StructPassContext) : List (Exp α) → List Shape
    | [] => []
    | expression :: expressions =>
        structOldExpShape context expression :: structOldExpShapes context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structSelectFields [BEq String] (fields : List (FieldName × Shape))
    (compiled : InfoMap (Exp α)) : List (Exp α) :=
  match fields with
  | [] => []
  | (field, _) :: fields =>
      match lookupInfo field compiled with
      | some expression => expression :: structSelectFields fields compiled
      | none => structSelectFields fields compiled

def structCompileExp [BEq String] (context : StructPassContext) :
    Exp α → (compileShape : StructContext → Shape → Shape := structCompileShape) →
      (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) → Exp α
  | .rStruct fields, compileShape, oldExpShape =>
      .rStruct (structCompileExps context fields compileShape oldExpShape)
  | .rField index value, compileShape, oldExpShape =>
      .rField index (structCompileExp context value compileShape oldExpShape)
  | .nStruct name fields, compileShape, oldExpShape =>
      let compiledFields := structCompileFields context fields compileShape oldExpShape
      match lookupInfo name context.structs with
      | some info => .rStruct (structSelectFields info.fields compiledFields)
      | none => .rStruct []
  | .nField field value, compileShape, oldExpShape =>
      let compiledValue := structCompileExp context value compileShape oldExpShape
      let index :=
        match oldExpShape context value with
        | .named name =>
            match lookupInfo name context.structs with
            | some info => (structFindFieldIndex field info.fields).getD 0
            | none => 0
        | _ => 0
      .rField index compiledValue
  | .load shape address, compileShape, oldExpShape =>
      .load (compileShape context.structs shape)
        (structCompileExp context address compileShape oldExpShape)
  | .load32 address, compileShape, oldExpShape =>
      .load32 (structCompileExp context address compileShape oldExpShape)
  | .loadByte address, compileShape, oldExpShape =>
      .loadByte (structCompileExp context address compileShape oldExpShape)
  | .op operator arguments, compileShape, oldExpShape =>
      .op operator (structCompileExps context arguments compileShape oldExpShape)
  | .panOp operator arguments, compileShape, oldExpShape =>
      .panOp operator (structCompileExps context arguments compileShape oldExpShape)
  | .cmp operator left right, compileShape, oldExpShape =>
      .cmp operator (structCompileExp context left compileShape oldExpShape)
        (structCompileExp context right compileShape oldExpShape)
  | .shift operator left right, compileShape, oldExpShape =>
      .shift operator (structCompileExp context left compileShape oldExpShape)
        (structCompileExp context right compileShape oldExpShape)
  | expression, _, _ => expression
termination_by expression => sizeOf expression
where
  structCompileExps [BEq String] (context : StructPassContext) :
      List (Exp α) → (compileShape : StructContext → Shape → Shape := structCompileShape) →
        (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) →
        List (Exp α)
    | [], _, _ => []
    | expression :: expressions, compileShape, oldExpShape =>
        structCompileExp context expression compileShape oldExpShape ::
          structCompileExps context expressions compileShape oldExpShape
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  structCompileFields [BEq String] (context : StructPassContext) :
      List (FieldName × Exp α) → (compileShape : StructContext → Shape → Shape := structCompileShape) →
        (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) →
        InfoMap (Exp α)
    | [], _, _ => []
    | (field, expression) :: fields, compileShape, oldExpShape =>
        (field, structCompileExp context expression compileShape oldExpShape) ::
          structCompileFields context fields compileShape oldExpShape
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structCompileProg [BEq String] (context : StructPassContext) :
    Prog α → (compileShape : StructContext → Shape → Shape := structCompileShape) →
      (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) → Prog α
  | .dec name shape value body, compileShape, oldExpShape =>
      .dec name (compileShape context.structs shape)
        (structCompileExp context value compileShape oldExpShape)
        (structCompileProg { context with locals := (name, shape) :: context.locals }
          body compileShape oldExpShape)
  | .assign kind name value, compileShape, oldExpShape =>
      .assign kind name (structCompileExp context value compileShape oldExpShape)
  | .primitive name operator arguments, compileShape, oldExpShape =>
      .primitive name operator (structCompileExps context arguments compileShape oldExpShape)
  | .store address value, compileShape, oldExpShape =>
      .store (structCompileExp context address compileShape oldExpShape)
        (structCompileExp context value compileShape oldExpShape)
  | .store32 address value, compileShape, oldExpShape =>
      .store32 (structCompileExp context address compileShape oldExpShape)
        (structCompileExp context value compileShape oldExpShape)
  | .storeByte address value, compileShape, oldExpShape =>
      .storeByte (structCompileExp context address compileShape oldExpShape)
        (structCompileExp context value compileShape oldExpShape)
  | .seq first second, compileShape, oldExpShape =>
      .seq (structCompileProg context first compileShape oldExpShape)
        (structCompileProg context second compileShape oldExpShape)
  | .ite condition thenBranch elseBranch, compileShape, oldExpShape =>
      .ite (structCompileExp context condition compileShape oldExpShape)
        (structCompileProg context thenBranch compileShape oldExpShape)
        (structCompileProg context elseBranch compileShape oldExpShape)
  | .while condition body, compileShape, oldExpShape =>
      .while (structCompileExp context condition compileShape oldExpShape)
        (structCompileProg context body compileShape oldExpShape)
  | .call info function arguments, compileShape, oldExpShape =>
      let compiledInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar,
              structCompileProg context handler compileShape oldExpShape))
      .call compiledInfo function (structCompileExps context arguments compileShape oldExpShape)
  | .decCall name shape function arguments body, compileShape, oldExpShape =>
      .decCall name (compileShape context.structs shape) function
        (structCompileExps context arguments compileShape oldExpShape)
        (structCompileProg { context with locals := (name, shape) :: context.locals }
          body compileShape oldExpShape)
  | .extCall function configuration configurationLength array arrayLength, compileShape, oldExpShape =>
      .extCall function (structCompileExp context configuration compileShape oldExpShape)
        (structCompileExp context configurationLength compileShape oldExpShape)
        (structCompileExp context array compileShape oldExpShape)
        (structCompileExp context arrayLength compileShape oldExpShape)
  | .raise exception value, compileShape, oldExpShape =>
      .raise exception (structCompileExp context value compileShape oldExpShape)
  | .return value, compileShape, oldExpShape =>
      .return (structCompileExp context value compileShape oldExpShape)
  | .shMemLoad size kind name address, compileShape, oldExpShape =>
      .shMemLoad size kind name (structCompileExp context address compileShape oldExpShape)
  | .shMemStore size address value, compileShape, oldExpShape =>
      .shMemStore size (structCompileExp context address compileShape oldExpShape)
        (structCompileExp context value compileShape oldExpShape)
  | program, _, _ => program
termination_by program => sizeOf program
where
  structCompileExps [BEq String] (context : StructPassContext) :
      List (Exp α) → (compileShape : StructContext → Shape → Shape := structCompileShape) →
        (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) →
        List (Exp α)
    | [], _, _ => []
    | expression :: expressions, compileShape, oldExpShape =>
        structCompileExp context expression compileShape oldExpShape ::
          structCompileExps context expressions compileShape oldExpShape
termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def structGetNames (context : StructPassContext) (declarations : List (Decl α)) :
    StructPassContext :=
  declarations.foldl (fun context declaration =>
    match declaration with
    | .name name fields =>
        { context with structs := (name, { fields := fields, size := 0 }) :: context.structs }
    | _ => context) context

def structCompileDecls [BEq String] :
    List (Decl α) → StructPassContext →
      (compileShape : StructContext → Shape → Shape := structCompileShape) →
        (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) →
        List (Decl α) × StructPassContext
  | [], context, _, _ => ([], context)
  | .decl shape name value :: declarations, context, compileShape, oldExpShape =>
      let nextContext := { context with globals := (name, shape) :: context.globals }
      let (compiled, finalContext) := structCompileDecls declarations nextContext compileShape oldExpShape
      (.decl (compileShape context.structs shape) name
        (structCompileExp context value compileShape oldExpShape) :: compiled,
        finalContext)
  | .function declaration :: declarations, context, compileShape, oldExpShape =>
      let (compiled, finalContext) := structCompileDecls declarations context compileShape oldExpShape
      let parameters := declaration.params.map
        (fun (name, shape) => (name, compileShape context.structs shape))
      let functionContext := { finalContext with locals := declaration.params }
      let compiledDeclaration := { declaration with
        params := parameters
        body := structCompileProg functionContext declaration.body compileShape oldExpShape
        returnShape := compileShape context.structs declaration.returnShape }
      (.function compiledDeclaration :: compiled, finalContext)
  | .exnDecl exception shape :: declarations, context, compileShape, oldExpShape =>
      let (compiled, finalContext) := structCompileDecls declarations context compileShape oldExpShape
      (.exnDecl exception (compileShape context.structs shape) :: compiled, finalContext)
  | .name _ _ :: declarations, context, compileShape, oldExpShape =>
      structCompileDecls declarations context compileShape oldExpShape

def structCompileTop (declarations : List (Decl α))
    (compileShape : StructContext → Shape → Shape := structCompileShape)
    (oldExpShape : StructPassContext → Exp α → Shape := structOldExpShape) : List (Decl α) :=
  let initial : StructPassContext :=
    { structs := [], locals := [], globals := [] }
  (structCompileDecls declarations (structGetNames initial declarations) compileShape oldExpShape).1

@[simp] theorem structCompileShape_one (context : StructContext) :
    structCompileShape context .one = .one := by
  simp [structCompileShape, structCompileShapeWF]

@[simp] theorem structCompileExp_const [BEq String]
    (context : StructPassContext) (value : α) :
    structCompileExp context (.const value) = .const value := by
  simp [structCompileExp]

theorem structCompileProg_seq [BEq String] (context : StructPassContext)
    (first second : Prog α) :
    structCompileProg context (.seq first second) =
      .seq (structCompileProg context first) (structCompileProg context second) := by
  simp [structCompileProg]

/-- Cake's `function_names_structs_compile_decs`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml`): the struct pass keeps
    the function-name table. -/
theorem functions_names_structCompileDecls [BEq String]
    (declarations : List (Decl α)) (context : StructPassContext) :
    (functions (structCompileDecls declarations context).1).map Prod.fst =
      (functions declarations).map Prod.fst := by
  induction declarations generalizing context with
  | nil => simp [structCompileDecls]
  | cons declaration declarations ih =>
      cases declaration <;> simp [structCompileDecls, functions, functionEntries, ih]

/-- Cake's `function_names_structs_compile_top`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:313`): the struct pass at
    the declaration list level keeps the function-name table. -/
theorem functions_names_structCompileTop (declarations : List (Decl α)) :
    (functions (structCompileTop declarations)).map Prod.fst =
      (functions declarations).map Prod.fst := by
  unfold structCompileTop
  dsimp only
  exact functions_names_structCompileDecls declarations
    (structGetNames { structs := [], locals := [], globals := [] } declarations)

end Flapjack
