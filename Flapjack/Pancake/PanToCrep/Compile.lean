import Flapjack.HolRef
import Flapjack.Pancake.PanToCrep
import Flapjack.Pancake.PanGlobals

/-!
Core statement lowering from Flapjack to Crepe.

This is the structured-local/control-flow portion of `pan_to_crep`. The
function is intentionally extraction-friendly: malformed shape lengths and
front-end constructs whose runtime environments are not ported yet lower to
`Skip`, matching the reference pass's defensive fallback style.
-/

namespace Flapjack

def compileArgs [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (expressions : List (Exp α)) : List (CrepExp α) :=
  match expressions with
  | [] => []
  | expression :: expressions =>
      (compileExp context expression).1 ++ compileArgs context expressions
termination_by structural expressions

/-! Finite-map expression lowering for the HOL `context` record. The lookup is
    directly `FLOOKUP context.vars`; this path does not enumerate or project a
    finite map into `InfoMap`. `compileProgHOL` uses this expression compiler
    throughout its recursive program lowering.

    NOT TAGGED `@[hol]`.  The equations match Cake's
    `pan_to_crep$compile_exp` (`cakeml/pancake/pan_to_crepScript.sml:39-101`)
    clause by clause, with `compileExpListHOL` standing for HOL's
    `MAP (compile_exp ctxt)` and the `CrepBytesInWord` stride for HOL's implicit
    `bytes_in_word`.  The declaration is however generic in the element type `α`
    carrying `[BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]`, whereas HOL's
    `compile_exp` and `context` are indexed by the word type `'a word`
    (`pan_to_crepScript.sml:10-16`) with HOL equality and no typeclass side
    conditions.  As with the generic `loadShapeBytes` versus the exact
    width-indexed `loadShapeBytesW` (`Flapjack/Pancake/CrepLang.lean:210-228`),
    the exact Lean tag is on the width-indexed `compileExpHOLW` below; this
    generic form is retained as Flapjack support.  The fallback branches return
    `([Const 0w], One)`, matching HOL.  Direct oracle:
    `scripts/hol-probes/compile_exp_probe.out`. -/
def compileExpHOL [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) : Exp α → List (CrepExp α) × Shape
  | .const value => ([.const value], .one)
  | .var .local name =>
      match FLOOKUP context.vars name with
      | some (shape, names) => (names.map .var, shape)
      | none => ([.const 0], .one)
  | .var .global _ => ([.const 0], .one)
  | .rStruct expressions =>
      let compiled := compileExpListHOL context expressions
      (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
  | .rField index expression =>
      let compiled := compileExpHOL context expression
      match compiled.2 with
      | .comb shapes => compileField index shapes compiled.1
      | _ => ([.const 0], .one)
  | .nStruct _ _ => ([.const 0], .one)
  | .nField _ _ => ([.const 0], .one)
  | .load shape expression =>
      match compileExpHOL context expression with
      | (expression :: _, _) =>
          (loadShape 0 CrepBytesInWord.bytesInWord (Shape.shapeSize shape) expression, shape)
      | _ => ([.const 0], .one)
  | .load32 expression =>
      match compileExpHOL context expression with
      | (expression :: _, .one) => ([.load32 expression], .one)
      | _ => ([.const 0], .one)
  | .loadByte expression =>
      match compileExpHOL context expression with
      | (expression :: _, .one) => ([.loadByte expression], .one)
      | _ => ([.const 0], .one)
  | .op operator expressions =>
      match cexpHeads (compileExpListHOL context expressions |>.map Prod.fst) with
      | some expressions => ([.op operator expressions], .one)
      | none => ([.const 0], .one)
  | .panOp operator expressions =>
      match cexpHeads (compileExpListHOL context expressions |>.map Prod.fst) with
      | some expressions => ([.crepOp (compilePanOp operator) expressions], .one)
      | none => ([.const 0], .one)
  | .cmp operator left right =>
      match compileExpHOL context left, compileExpHOL context right with
      | (left :: _, _), (right :: _, _) => ([.cmp operator left right], .one)
      | _, _ => ([.const 0], .one)
  | .shift operator left right =>
      match compileExpHOL context left, compileExpHOL context right with
      | (left :: _, _), (right :: _, _) => ([.shift operator left right], .one)
      | _, _ => ([.const 0], .one)
  | .baseAddr => ([.baseAddr], .one)
  | .topAddr => ([.topAddr], .one)
  | .bytesInWord => ([.const CrepBytesInWord.bytesInWord], .one)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  compileExpListHOL (context : PanToCrepHOLContext α) (expressions : List (Exp α)) :
      List (List (CrepExp α) × Shape) :=
    match expressions with
    | [] => []
    | expression :: expressions =>
        compileExpHOL context expression :: compileExpListHOL context expressions
  termination_by sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-- WITHDRAWN HOL TAG, source-reviewed documented mismatch: this width-indexed
    counterpart of `pan_to_crep$compile_exp_def`
    (`cakeml/pancake/pan_to_crepScript.sml:39-101`) is NOT an exact port. Its
    clause structure matches HOL one-for-one, but the following carrier/typing
    differences remain:
    (1) HOL `compile_exp` and its `context` are indexed by the word type
        `'a word` (`pan_to_crepScript.sml:10-16`) with HOL equality and no
        typeclass side conditions, whereas the underlying `compileExpHOL` is
        generic in `α` carrying `[BEq α] [OfNat α 0] [Add α]
        [CrepBytesInWord α]`; the tag was on this delegation, whose body is that
        generic compiler and whose `bytesInWord` case returns
        `Const CrepBytesInWord.bytesInWord` rather than HOL's `bytes_in_word`
        theory constant;
    (2) the context `PanToCrepHOLContext α` keys `vars`/`funcs`/`eids` by
        `VarName`/`FunName`/`ExceptionId` = `String` (HOL keys them by
        `varname`/`funname`/`eid` = `mlstring`);
    (3) `Exp α`/`Shape` are the production carriers with `Named : String`
        (HOL uses `'a panLang$exp`/`shape` with `Named : mlstring`);
    (4) the compiled output is the production `CrepExp α`/`CrepProg α` family.
    `names_as_string` cannot authorize the added typeclass side conditions, the
    `CrepBytesInWord` stride abstraction, or the `Exp`/`Shape` production
    carriers (the identifier keys themselves are map-key-only equality uses),
    and no `NameRanged` byte witness applies: the output is a compiled
    expression list paired with a shape. Direct HOL-EVAL rows are recorded in
    `scripts/hol-probes/compile_exp_probe.out` and reproduced by
    `Flapjack/Test/CompileExpParity.lean` (including through this
    `compileExpHOLW` at the `BitVec 64` carrier). A faithful exact-carrier port
    over `ExpHOL`/`ShapeHOL`/`CrepExpHOL width` is tracked by
    `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`; the exact
    `compile_def` dependency path is `flapjack-pxn.18.3.5.8.13`). -/
def compileExpHOLW {width : Nat} [NeZero width]
    (context : PanToCrepHOLContext (BitVec width)) :
    Exp (BitVec width) → List (CrepExp (BitVec width)) × Shape :=
  compileExpHOL context

/-- Kernel-checked definitional-equality bridge for `flapjack-pxn.18.3.1.3.2`:
    at the RISC-V word carrier, the generic expression compiler `compileExpHOL`
    is definitionally equal to the width-indexed `compileExpHOLW` specialization.
    Neither String-context definition is tagged as HOL `compile_exp_def`.
    This is a BRIDGE ONLY, not textual routing: the shipped
    `compileProgRiscV`/`compileProgHOL` path still calls the generic
    `compileExpHOL`, so the executed compiler does not textually call that
    specialization and the AGENTS.md production-path rule is NOT met here. A
    textual width specialization of the enclosing `compileProg` chain would
    duplicate the large `compileProgHOL` equation/codeRel proof surface and is
    tracked by `flapjack-pxn.18.3.5.3.1.2`. -/
theorem compileExpHOLW_eq_compileExpHOL {width : Nat} [NeZero width]
    (context : PanToCrepHOLContext (BitVec width)) (expression : Exp (BitVec width)) :
    compileExpHOLW context expression = compileExpHOL context expression := rfl

def compileArgsHOL [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (expressions : List (Exp α)) : List (CrepExp α) :=
  match expressions with
  | [] => []
  | expression :: expressions =>
      (compileExpHOL context expression).1 ++ compileArgsHOL context expressions
termination_by structural expressions

def allocatedNamesHOL (context : PanToCrepHOLContext α) (shape : Shape) : List Nat :=
  (List.range (Shape.shapeSize shape)).map (fun offset => context.vmax + 1 + offset)

def freshNamesHOL (context : PanToCrepHOLContext α) (count start : Nat) : List Nat :=
  (List.range count).map (fun offset => context.vmax + start + offset)

def functionReturnNamesHOL (context : PanToCrepHOLContext α) (function : FunName) : List Nat :=
  match FLOOKUP context.funcs function with
  | some (_, shape) => allocatedNamesHOL context shape
  | none => []

def callDestinationNamesHOL (context : PanToCrepHOLContext α) (_kind : VarKind)
    (name : VarName) : Option (List Nat) :=
  (wrapRt (FLOOKUP context.vars name)).map Prod.snd

def firstCompiledExpHOL [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExpHOL context expression with
  | (compiled :: _, .one) => some compiled
  | _ => none

def firstCompiledExpAnyShapeHOL [BEq α] [OfNat α 0] [Add α] [CrepBytesInWord α]
    (context : PanToCrepHOLContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExpHOL context expression with
  | (compiled :: _, _) => some compiled
  | _ => none

/-- Maximum variable index mentioned by the given compiled expressions.  Calls
    the generic `crepExpVars`; the tagged width-indexed `crepExpVarsW` is a
    definitional delegation of it, so this executed use computes the identical
    function (`flapjack-pxn.18.4.3.82`). -/
def maxCrepExpVarHOL (expressions : List (CrepExp α)) : Nat :=
  (expressions.flatMap crepExpVars).foldl max 0

/-! Freshness bounds for the temporaries that `compileProgHOL` allocates from
    the finite-map `PanToCrepHOLContext`. These are the exact-context
    counterparts of `allocatedNames_gt`/`freshNames_gt`, used by Cake's
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`) to
    rule out collisions between fresh temporaries and live variables. -/
theorem allocatedNamesHOL_gt (context : PanToCrepHOLContext α) (shape : Shape)
    {slot : Nat} (hmem : slot ∈ allocatedNamesHOL context shape) :
    context.vmax < slot := by
  obtain ⟨offset, _hoffset, rfl⟩ := List.mem_map.mp hmem
  omega

theorem freshNamesHOL_gt (context : PanToCrepHOLContext α) (count start : Nat)
    (hstart : 0 < start) {slot : Nat}
    (hmem : slot ∈ freshNamesHOL context count start) :
    context.vmax < slot := by
  obtain ⟨offset, _hoffset, rfl⟩ := List.mem_map.mp hmem
  omega

theorem not_mem_allocatedNamesHOL (context : PanToCrepHOLContext α) (shape : Shape)
    {x : Nat} (hx : x ≤ context.vmax) : x ∉ allocatedNamesHOL context shape := by
  intro hmem
  have := allocatedNamesHOL_gt context shape hmem
  omega

theorem not_mem_freshNamesHOL (context : PanToCrepHOLContext α) (count start : Nat)
    (hstart : 0 < start) {x : Nat} (hx : x ≤ context.vmax) :
    x ∉ freshNamesHOL context count start := by
  intro hmem
  have := freshNamesHOL_gt context count start hstart hmem
  omega

/-- HOL-context counterpart of `mem_crepExpVars_le_maxCrepExpVar`: every
    variable of a compiled expression list is bounded by `maxCrepExpVarHOL`,
    the `foldl max 0` used for Cake's `ExtCall`/`ShMemStore` temporaries. -/
theorem mem_crepExpVars_le_maxCrepExpVarHOL
    (expressions : List (CrepExp α)) {name : Nat}
    (hmem : name ∈ expressions.flatMap crepExpVars) :
    name ≤ maxCrepExpVarHOL expressions := by
  have hacc : ∀ (xs : List Nat) (acc : Nat), acc ≤ xs.foldl max acc := by
    intro xs
    induction xs with
    | nil => intro acc; exact Nat.le_refl acc
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih (max acc x))
  have hbound : ∀ (xs : List Nat) (acc : Nat), name ∈ xs →
      name ≤ xs.foldl max acc := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro acc h
        simp only [List.mem_cons] at h
        simp only [List.foldl_cons]
        rcases h with rfl | h
        · exact Nat.le_trans (Nat.le_max_right _ _) (hacc xs (max acc name))
        · exact ih (max acc x) h
  exact hbound (expressions.flatMap crepExpVars) 0 hmem

theorem allocatedNamesHOL_length (context : PanToCrepHOLContext α) (shape : Shape) :
    (allocatedNamesHOL context shape).length = Shape.shapeSize shape := by
  simp [allocatedNamesHOL]

theorem freshNamesHOL_length (context : PanToCrepHOLContext α) (count start : Nat) :
    (freshNamesHOL context count start).length = count := by
  simp [freshNamesHOL]

theorem not_mem_functionReturnNamesHOL (context : PanToCrepHOLContext α)
    (function : FunName) {x : Nat} (hx : x ≤ context.vmax) :
    x ∉ functionReturnNamesHOL context function := by
  unfold functionReturnNamesHOL
  split
  · exact not_mem_allocatedNamesHOL context _ hx
  · simp

/-- A call-destination slot list is exactly the slot list recorded for the
    destination variable in the finite-map context (the `wrap_rt` normalization
    only drops the empty one-word return slot).  This is the finite-map
    counterpart of the `locals_rel` slot link used by Cake's
    `not_mem_context_assigned_mem_gt` (`pan_to_crepProofScript.sml:1252`). -/
theorem callDestinationNamesHOL_mem (context : PanToCrepHOLContext α) (kind : VarKind)
    (name : VarName) {slots : List Nat}
    (h : callDestinationNamesHOL context kind name = some slots) :
    ∃ sh ns, FLOOKUP context.vars name = some (sh, ns) ∧ slots = ns := by
  unfold callDestinationNamesHOL at h
  cases hlookup : FLOOKUP context.vars name with
  | none => simp [wrapRt, hlookup] at h
  | some pair =>
      obtain ⟨sh, ns⟩ := pair
      simp only [hlookup] at h
      cases sh with
      | one =>
          cases ns with
          | nil => simp [wrapRt] at h
          | cons slot slots =>
              simp only [wrapRt, Option.map_some] at h
              exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
      | comb fields =>
          simp only [wrapRt, Option.map_some] at h
          exact ⟨_, _, rfl, (Option.some.inj h).symm⟩
      | named structName =>
          simp only [wrapRt, Option.map_some] at h
          exact ⟨_, _, rfl, (Option.some.inj h).symm⟩

/-- Extending the compiler context with the slots freshly allocated for a
    variable preserves the freshness hypothesis used by Cake's
    `not_mem_context_assigned_mem_gt`
    (`pan_to_crepProofScript.sml:1252`): a slot that is neither in the new
    variable's slot list nor in the old context remains unused.  This is the
    `FUPDATE` step for the `dec`/`decCall` cases. -/
theorem hfresh_update [BEq String] [LawfulBEq String]
    (context : PanToCrepHOLContext α) (name : VarName) (shape : Shape)
    (names : List Nat) (x : Nat)
    (hfresh : ∀ v sh ns', FLOOKUP context.vars v = some (sh, ns') → x ∉ ns')
    (hnames : x ∉ names) :
    ∀ v sh ns', FLOOKUP (FUPDATE context.vars (name, (shape, names))) v = some (sh, ns') →
      x ∉ ns' := by
  intro v sh ns' hlk
  rw [FLOOKUP_update] at hlk
  by_cases hv : name == v
  · rw [if_pos hv] at hlk
    have hpair : (shape, names) = (sh, ns') := Option.some.inj hlk
    have hns : names = ns' := congrArg Prod.snd hpair
    exact hns ▸ hnames
  · rw [if_neg hv] at hlk
    exact hfresh v sh ns' hlk

/-- HOL `panLang$load_op` (`panLangScript.sml:300-305`): `Op8 ↦ Load8`,
    `Op16 ↦ Load16`, `OpW ↦ Load`, `Op32 ↦ Load32`. `OpSize` is the tagged
    exact `opsize` port; `CrepMemOp`'s eight nullary constructors mirror
    `asm$memop`, the representation accepted for `shMem` in the reviewed
    `HolLoopProg` entry. The executable `compileProg` below calls this
    definition directly. -/
@[hol "cakeml/pancake/panLangScript.sml" "load_op_def"]
def loadMemOpHOL : OpSize → CrepMemOp
  | .op8 => .load8
  | .opW => .load
  | .op32 => .load32
  | .op16 => .load16

/-- HOL `panLang$store_op` (`panLangScript.sml:307-312`): `Op8 ↦ Store8`,
    `Op16 ↦ Store16`, `OpW ↦ Store`, `Op32 ↦ Store32`. See `loadMemOpHOL`
    for the carrier comparison. -/
@[hol "cakeml/pancake/panLangScript.sml" "store_op_def"]
def storeMemOpHOL : OpSize → CrepMemOp
  | .op8 => .store8
  | .opW => .store
  | .op32 => .store32
  | .op16 => .store16

/-! Generic finite-map implementation used to share the compile equations
    with non-word fixtures. This helper takes the target word's byte stride as
    an instance parameter, so the HOL reference belongs to the RISC-V
    specialization below rather than this generic adapter.  Its expression
    compilation runs the generic `compileExpHOL`; the kernel-checked bridge
    `compileExpHOLW_eq_compileExpHOL` shows this is definitionally equal to the
    width-indexed `compileExpHOLW` at the RISC-V carrier, but the path is
    NOT textually routed to that specialization (see
    `flapjack-pxn.18.3.5.3.1.2`). -/
def compileProgHOL [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    [CrepBytesInWord α] (context : PanToCrepHOLContext α)
    (program : Prog α) : CrepProg α :=
  match program with
  | .skip => .skip
  | .dec name _shape value body =>
      let compiled := compileExpHOL context value
      let names := allocatedNamesHOL context compiled.2
      let nextContext := { context with
        vars := FUPDATE context.vars (name, (compiled.2, names))
        vmax := context.vmax + Shape.shapeSize compiled.2 }
      if Shape.shapeSize compiled.2 = compiled.1.length then
        nestedDecs names compiled.1 (compileProgHOL nextContext body)
      else .skip
  | .assign .local name value =>
      match FLOOKUP context.vars name, compileExpHOL context value with
      | some (_, names), (expressions, _) =>
          if names.length = expressions.length then
            if distinctLists names (expressions.flatMap crepExpVars) then
              crepNestedSeq
                (names.zipWith (fun name expression => .assign name expression) expressions)
            else
              let temporaries := freshNamesHOL context names.length 1
              nestedDecs temporaries expressions
                (crepNestedSeq
                  (names.zipWith (fun name temporary => .assign name (.var temporary))
                    temporaries))
          else .skip
      | _, _ => .skip
  | .assign .global _ _ => .skip
  | .primitive name operator arguments =>
      match FLOOKUP context.vars name with
      | some (_, names) =>
          let compiledArgs := compileArgsHOL context arguments
          let temporaries := freshNamesHOL context compiledArgs.length 1
          nestedDecs temporaries compiledArgs (.primitive names operator temporaries)
      | none => .skip
  | .store address value =>
      match compileExpHOL context address, compileExpHOL context value with
      | (address :: _, _), (values, shape) =>
          let addressTemporary := context.vmax + 1
          let temporaries := freshNamesHOL context values.length 2
          if values.length = Shape.shapeSize shape then
            nestedDecs (addressTemporary :: temporaries) (address :: values)
              (crepNestedSeq (stores (.var addressTemporary) (temporaries.map .var)
                0 CrepBytesInWord.bytesInWord))
          else .skip
      | _, _ => .skip
  | .store32 address value =>
      match compileExpHOL context address, compileExpHOL context value with
      | (address :: _, _), (value :: _, _) => .store32 address value
      | _, _ => .skip
  | .storeByte address value =>
      match compileExpHOL context address, compileExpHOL context value with
      | (address :: _, _), (value :: _, _) => .storeByte address value
      | _, _ => .skip
  | .seq first second => .seq (compileProgHOL context first) (compileProgHOL context second)
  | .ite condition thenBranch elseBranch =>
      match compileExpHOL context condition with
      | (condition :: _, _) =>
          .ite condition (compileProgHOL context thenBranch) (compileProgHOL context elseBranch)
      | _ => .skip
  | .while condition body =>
      match compileExpHOL context condition with
      | (condition :: _, _) => .while condition (compileProgHOL context body)
      | _ => .skip
  | .break => .break 0
  | .continue => .continue 0
  | .call info function arguments =>
      let args := compileArgsHOL context arguments
      match info with
      | none => .call none function args
      | some (destination, handler) =>
          let compiledHandler :=
            match handler with
            | none => none
            | some (exception, handlerVar, handlerProgram) =>
                match FLOOKUP context.eids exception with
                | none => none
                | some code =>
                    let handlerSetup := expHdlFiniteMap context.vars handlerVar
                    some (code, .seq handlerSetup (compileProgHOL context handlerProgram))
          match destination with
          | none =>
              let returnNames := functionReturnNamesHOL context function
              nestedDecs returnNames (returnNames.map (fun _ => .const 0))
                (.call (some (returnNames, compiledHandler)) function args)
          | some (kind, name) =>
              match callDestinationNamesHOL context kind name with
              | none =>
                  compiledHandler.elim (.call none function args)
                    (fun handler => .call (some ([], some handler)) function args)
              | some names => .call (some (names, compiledHandler)) function args
  | .decCall name shape function arguments body =>
      let names := allocatedNamesHOL context shape
      let nextContext := { context with
        vars := FUPDATE context.vars (name, (shape, names))
        vmax := context.vmax + Shape.shapeSize shape }
      let call := .call (some (names, none)) function (compileArgsHOL context arguments)
      nestedDecs names (names.map (fun _ => .const 0))
        (.seq call (compileProgHOL nextContext body))
  | .extCall function configuration configurationLength array arrayLength =>
      let compiledConfiguration := compileExpHOL context configuration
      let compiledConfigurationLength := compileExpHOL context configurationLength
      let compiledArray := compileExpHOL context array
      let compiledArrayLength := compileExpHOL context arrayLength
      match compiledConfiguration, compiledConfigurationLength,
          compiledArray, compiledArrayLength with
      | (configuration :: _, .one), (configurationLength :: _, .one),
          (array :: _, .one), (arrayLength :: _, .one) =>
          /- HOL computes this bound from every compiled expression element,
             before selecting each One-shaped expression's head for Dec. -/
          let base := maxCrepExpVarHOL
            (compiledConfiguration.1 ++ compiledConfigurationLength.1 ++
              compiledArray.1 ++ compiledArrayLength.1) + 1
          let configurationName := base
          let configurationLengthName := base + 1
          let arrayName := base + 2
          let arrayLengthName := base + 3
          let names := [configurationName, configurationLengthName, arrayName, arrayLengthName]
          nestedDecs names [configuration, configurationLength, array, arrayLength]
            (.extCall function configurationName configurationLengthName arrayName arrayLengthName)
      | _, _, _, _ => .skip
  | .raise exception value =>
      match FLOOKUP context.eids exception with
      | some code =>
          let compiled := compileExpHOL context value
          let temporaries := freshNamesHOL context compiled.1.length 1
          if compiled.1.length = Shape.shapeSize compiled.2 then
            .seq
              (nestedDecs temporaries compiled.1
                (crepNestedSeq (storeGlobals 0 (temporaries.map .var))))
              (.raise code)
          else .skip
      | none => .skip
  | .return value =>
      let compiled := compileExpHOL context value
      if Shape.shapeSize compiled.2 = 0 then .return [] else .return compiled.1
  | .shMemLoad size .local name address =>
      match FLOOKUP context.vars name, firstCompiledExpAnyShapeHOL context address with
      | some (_, destination :: _), some address => .shMem (loadMemOpHOL size) destination address
      | _, _ => .skip
  | .shMemLoad _ .global _ _ => .skip
  | .shMemStore size address value =>
      match firstCompiledExpAnyShapeHOL context address,
          firstCompiledExpAnyShapeHOL context value with
      | some address, some value =>
          let temporary := maxCrepExpVarHOL [address] + 1
          nestedDecs [temporary] [value] (.shMem (storeMemOpHOL size) temporary address)
      | _, _ => .skip
  | .tick => .tick
  | .annot _ _ => .skip
termination_by structural program

/-! FLAPJACK-SPECIFIC (not an exact HOL port). Source-reviewed decision
    (`flapjack-dlc.18`): the `@[hol]` tag stays withdrawn as a documented
    carrier mismatch. HOL `compile_def`
    (`cakeml/pancake/pan_to_crepScript.sml:139-307`) is a structural recursion
    over positive-width `ProgHOL width` / `ExpHOL width` / `ShapeHOL`, with
    context vars/functions/eids keyed by `mlstring`, returning
    `CrepProgHOL width`. Both `compileProgHOL` and this RISC-V specialization
    `compileProgRiscV` instead take production `Prog (BitVec width)` / `Exp` /
    `Shape`, String identifiers and context keys, and admit `width = 0` (no
    `[NeZero width]`); `compileProgRiscV` only fixes `α := BitVec width` before
    delegating to generic `compileProgHOL`. The `names_as_string` qualifier
    cannot authorize the `Shape`/`Exp`/`Prog`/`CrepProg` carriers or the missing
    positive-width side condition, and a `NameRanged` byte witness does not
    apply because the output is a compiled program, not a name. Direct HOL-EVAL
    rows for the `compile_def` equations are recorded in
    `scripts/hol-probes/compile_def_probe.out` and reproduced by
    `Flapjack/Test/CompileDefParity.lean`. Exact-carrier replacement is tracked
    by `flapjack-pxn.18.3.5.8.13` (under `flapjack-pxn.18.3.5.8`). -/
def compileProgRiscV (context : PanToCrepHOLContext (BitVec width))
    (program : Prog (BitVec width)) : CrepProg (BitVec width) :=
  compileProgHOL context program

def allocatedNames (context : CompileContext α) (shape : Shape) : List Nat :=
  (List.range (Shape.shapeSize shape)).map (fun offset => context.maxVar + 1 + offset)

def freshNames (context : CompileContext α) (count start : Nat) : List Nat :=
  (List.range count).map (fun offset => context.maxVar + start + offset)

/-- Every slot allocated by `allocatedNames` lies strictly above the context's
    current `maxVar`.  This is the bound Cake's `not_mem_context_assigned_mem_gt`
    uses to rule out collisions between fresh temporaries and live variables. -/
theorem allocatedNames_gt (context : CompileContext α) (shape : Shape) {slot : Nat}
    (hmem : slot ∈ allocatedNames context shape) : context.maxVar < slot := by
  obtain ⟨offset, _hoffset, rfl⟩ := List.mem_map.mp hmem
  omega

/-- Every slot allocated by `freshNames` lies strictly above the context's
    current `maxVar`, provided the fresh window starts above zero (Cake always
    calls it with `start ≥ 1`). -/
theorem freshNames_gt (context : CompileContext α) (count start : Nat) (hstart : 0 < start)
    {slot : Nat} (hmem : slot ∈ freshNames context count start) : context.maxVar < slot := by
  obtain ⟨offset, _hoffset, rfl⟩ := List.mem_map.mp hmem
  omega

theorem not_mem_allocatedNames (context : CompileContext α) (shape : Shape) {x : Nat}
    (hx : x ≤ context.maxVar) : x ∉ allocatedNames context shape := by
  intro hmem
  have := allocatedNames_gt context shape hmem
  omega

theorem not_mem_freshNames (context : CompileContext α) (count start : Nat)
    (hstart : 0 < start) {x : Nat} (hx : x ≤ context.maxVar) :
    x ∉ freshNames context count start := by
  intro hmem
  have := freshNames_gt context count start hstart hmem
  omega

/-- `x` occurs in no slot list stored in the variable context.  This is the
    second hypothesis of Cake's `not_mem_context_assigned_mem_gt`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:1252`). -/
def panValueSlotBound [BEq String] (x : Nat) (vars : InfoMap (Shape × List Nat)) : Prop :=
  ∀ name shape slots, lookupInfo name vars = some (shape, slots) → x ∉ slots

/-- Extending the variable context with an entry whose slots avoid `x` preserves
    the `panValueSlotBound` invariant. -/
theorem panValueSlotBound_cons_of [BEq String] (x : Nat) (name : String)
    (shape : Shape) (slots : List Nat) (vars : InfoMap (Shape × List Nat))
    (h : panValueSlotBound x vars) (hslots : x ∉ slots) :
    panValueSlotBound x ((name, (shape, slots)) :: vars) := by
  intro name' shape' slots' hlookup
  cases hb : (name == name') with
  | false =>
      simp only [lookupInfo, hb] at hlookup
      exact h name' shape' slots' hlookup
  | true =>
      simp only [lookupInfo, hb] at hlookup
      have hpair : (shape, slots) = (shape', slots') := by simpa using hlookup
      have hslotsEq : slots = slots' := congrArg Prod.snd hpair
      rw [← hslotsEq]
      exact hslots

/-! Cake's ExtCall lowering chooses its temporary base from the largest
    variable occurring in all four compiled expressions, rather than from the
    context's cached `vmax`.  `ShMemStore` chooses its temporary from the
    compiled address expression (`pan_to_crepScript.sml:291-299`); using the
    value expression here can shadow the address variable and changes emitted
    register allocation. -/
def maxCrepExpVar (expressions : List (CrepExp α)) : Nat :=
  (expressions.flatMap crepExpVars).foldl max 0

/-! Every variable occurring in the compiled expression list is bounded by
    the `FOLDR MAX 0 (FLAT (MAP var_cexp ...))` value used by Cake's
    `compile` for `ExtCall` and `ShMemStore` temporaries
    (`pan_to_crepScript.sml:291-305`).  This is the freshness bridge needed
    by the assigned-memory proof: adding a positive offset produces a slot
    strictly above every expression variable. -/
theorem mem_crepExpVars_le_maxCrepExpVar
    (expressions : List (CrepExp α)) {name : Nat}
    (hmem : name ∈ expressions.flatMap crepExpVars) :
    name ≤ maxCrepExpVar expressions := by
  have hacc : ∀ (xs : List Nat) (acc : Nat),
      acc ≤ xs.foldl max acc := by
    intro xs
    induction xs with
    | nil => intro acc; exact Nat.le_refl acc
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_left _ _) (ih (max acc x))
  have hbound : ∀ (xs : List Nat) (acc : Nat), name ∈ xs →
      name ≤ xs.foldl max acc := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
        intro acc h
        simp only [List.mem_cons] at h
        simp only [List.foldl_cons]
        rcases h with rfl | h
        · exact Nat.le_trans (Nat.le_max_right _ _) (hacc xs (max acc name))
        · exact ih (max acc x) h
  exact hbound (expressions.flatMap crepExpVars) 0 hmem

def functionReturnNames (context : CompileContext α) (function : FunName) : List Nat :=
  match lookupInfo function context.functions with
  | some (_, shape) => allocatedNames context shape
  | none => []

/- `wrap_rt`-based call-destination resolution (`pan_to_crepScript.sml:247`).
    Cake ignores the source `rk` tag at this post-`pan_globals` boundary and
    looks up the destination name in `ctxt.vars`. -/
def callDestinationNames (context : CompileContext α) (_kind : VarKind)
    (name : VarName) : Option (List Nat) :=
  (wrapRt (lookupInfo name context.vars)).map Prod.snd

def firstCompiledExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExp context expression with
  | (compiled :: _, .one) => some compiled
  | _ => none

/-- CakeML's shared-memory compilation only requires the compiled
    address/value list to be nonempty and proceeds with the head word, for
    any shape (`pan_to_crepScript.sml:291-305`). -/
def firstCompiledExpAnyShape [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExp context expression with
  | (compiled :: _, _) => some compiled
  | _ => none

theorem firstCompiledExpAnyShape_of_firstCompiledExp [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    {context : CompileContext α} {expression : Exp α} {compiled : CrepExp α}
    (h : firstCompiledExp context expression = some compiled) :
    firstCompiledExpAnyShape context expression = some compiled := by
  unfold firstCompiledExp at h
  unfold firstCompiledExpAnyShape
  split at h <;> split <;> simp_all

structure CompiledFunction (α : Type u) where
  name : FunName
  params : List Nat
  body : CrepProg α
  returnShape : Shape
  deriving Repr

def compileParamVars : List (VarName × Shape) → Nat →
    InfoMap (Shape × List Nat) × List Nat × Nat
  | [], offset => ([], [], offset)
  | (name, shape) :: params, offset =>
      let names := (List.range (Shape.shapeSize shape)).map (fun index => offset + index)
      let (restVars, restNames, nextOffset) := compileParamVars params
        (offset + Shape.shapeSize shape)
      ((name, (shape, names)) :: restVars, names ++ restNames, nextOffset)
termination_by params => sizeOf params

/-! Source-named port of CakeML Pancake's active `make_vmap_def`
    (`pan_to_crepScript.sml:327`).  The first component of the parameter
    allocation is the finite map from source names to shaped flattened slots;
    `compileParamVars` supplies the same `with_shape` numbering used by Cake.

    Cake builds this map with `FEMPTY |++ ZIP`, so a later duplicate name
    replaces an earlier one.  `InfoMap` is a first-entry lookup list; reversing
    the update order is the list-backed representation of that finite-map
    semantics. -/
abbrev panToCrepMakeVmap (params : List (VarName × Shape)) :
    InfoMap (Shape × List Nat) :=
  (compileParamVars params 0).1.reverse
/-! Source-named port of CakeML Pancake's `make_funcs_def`
    (`pan_to_crepScript.sml:366`).  Cake's function table keeps each function
    name paired with its original parameter list and return shape; non-function
    declarations are absent from the table. -/
def panToCrepMakeFuncs : List (Decl α) → InfoMap (List (VarName × Shape) × Shape)
  | [] => []
  | .function declaration :: declarations =>
      (declaration.name, (declaration.params, declaration.returnShape)) ::
        panToCrepMakeFuncs declarations
  | _ :: declarations => panToCrepMakeFuncs declarations

def functionInfos : List (Decl α) → InfoMap (List (VarName × Shape) × Shape) :=
  panToCrepMakeFuncs

/-! HOL `make_funcs_def` (`cakeml/pancake/pan_to_crepScript.sml:366-373`) over
    the extracted function table:
    `make_funcs prog = alist_to_fmap (MAP3 (λx y z. (x,y,z)) (MAP FST prog)
    (MAP (FST o SND) prog) (MAP (SND o SND o SND) prog))`, keyed by
    `funname = mlstring` and valued by `(varname # shape) list # shape`;
    `alist_to_fmap` is a right fold of `FUPDATE`, so the first duplicate name
    wins. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): `makeFuncsHOL` keys the table by
-- `FunName` = `String` and stores values in the production `VarName` = `String`
-- and `Shape` (`named : StructName` = `String`) carriers, not HOL's
-- `funname`/`varname` = `mlstring` and `shape` (`named : mlstring`); its input
-- also mentions the production `Prog α` body carrier even though `make_funcs`
-- ignores bodies; and the result is a `FiniteMap` function rather than HOL's
-- `fmap` (rendered by `FUPDATE_LIST FEMPTY` over the reversed association list,
-- a left fold).  The `names_as_string` qualifier cannot authorize the `Shape`
-- and `Prog` carriers, and no `NameRanged` byte witness applies because the
-- output is a finite map of function signatures, not a name.  (The theorem
-- map's `make_funcs_def` -> `crepToLoopMakeFuncsHOL` entry is the exact port of
-- the *different* `crep_to_loopScript.sml` declaration, not this one.)  Direct
-- HOL-EVAL rows `make_funcs_empty_params`/`make_funcs_param_entry`/
-- `make_funcs_absent`/`make_funcs_duplicate_first_wins` are recorded in
-- `scripts/hol-probes/crep_make_funcs_probe.out` and exercised by
-- `makeFuncsGuard` (`Flapjack/Test/PanToCrepCodeRelParity.lean`) and
-- `makeFuncsOracle` (`Flapjack/Test/CompileToCrepeParity.lean`).  The faithful
-- exact-carrier port is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`); this analogue remains deliberately untagged.
def makeFuncsHOL
    (functions : List (FunName × List (VarName × Shape) × Prog α × Shape)) :
    FiniteMap FunName (List (VarName × Shape) × Shape) :=
  FUPDATE_LIST FEMPTY
    ((functions.map fun entry => (entry.1, (entry.2.1, entry.2.2.2))).reverse)

/-- `panToCrepMakeFuncs` maps exactly the extracted function entries through the
    HOL `make_funcs` projection. -/
theorem panToCrepMakeFuncs_eq_map (declarations : List (Decl α)) :
    panToCrepMakeFuncs declarations =
      (functionEntries declarations).map
        (fun entry => (entry.1, (entry.2.1, entry.2.2.2))) := by
  induction declarations with
  | nil => simp [panToCrepMakeFuncs, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panToCrepMakeFuncs, functionEntries, ih]

/-! Exact port of HOL `pan_to_crep$crep_vars`
    (`cakeml/pancake/pan_to_crepScript.sml:376-380`):

```
crep_vars params =
  let shapes = MAP SND params;
      len    = size_of_shape (Comb shapes) in
      GENLIST I len
```

HOL infers the polymorphic type `('a # shape) list -> num list`: the first
component of each parameter pair is never inspected, and `shape` carries no
word width.  The Lean statement is therefore polymorphic in `α`, and the shape
carrier is the exact `ShapeHOL` (names are discarded, so no `names_as_string`
qualifier is needed).  `GENLIST I len` is `List.range len` and
`size_of_shape (Comb shapes)` is the tagged
`sizeOfShapeHOL (.comb shapes)` (`@[hol ... "size_of_shape_def"]`,
`PanLang/Shape.lean`). -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "crep_vars_def"]
def crepVarsHOL {α : Type}
    (params : List (α × Flapjack.Pancake.PanLang.ShapeHOL)) : List Nat :=
  List.range
    (Flapjack.Pancake.PanLang.sizeOfShapeHOL
      (.comb (params.map Prod.snd)))

/-! Production `crep_vars` for the executed compiler, routed through the
    reviewed exact port `crepVarsHOL`: the `String`/`Shape` parameter carrier is
    encoded by the `shapeToHOL` codec before the slot list is computed.  Direct
    HOL-oracle-derived rows are exercised by `Test/CompileToCrepeParity.lean`
    (`crepVarsOracle`). -/
def panToCrepVars (params : List (VarName × Shape)) : List Nat :=
  crepVarsHOL
    (params.map fun parameter =>
      (parameter.1, Flapjack.Pancake.PanLang.shapeToHOL parameter.2))

/-- The routed production definition computes the same consecutive slot list as
    HOL's `GENLIST I (size_of_shape (Comb (MAP SND params)))` formula.  Names
    are inert on both sides, so no byte-rangedness hypothesis is needed. -/
@[simp] theorem panToCrepVars_eq (params : List (VarName × Shape)) :
    panToCrepVars params =
      List.range (Shape.shapeSize (.comb (params.map Prod.snd))) := by
  have hmap :
      (params.map fun parameter =>
        (parameter.1, Flapjack.Pancake.PanLang.shapeToHOL parameter.2)).map Prod.snd
        = (params.map Prod.snd).map Flapjack.Pancake.PanLang.shapeToHOL := by
    simp [List.map_map, Function.comp_def]
  simp only [panToCrepVars, crepVarsHOL, hmap,
    Flapjack.Pancake.PanLang.sizeOfShapeHOL_comb,
    sizeOfShapesHOL_shapeToHOL, Shape.shapeSize]

/-! Legacy list-backed `pan_to_crep$compile` implementation. It is retained
    for list-context analyses, but is not the exact HOL `compile_def` port:
    `CompileContext` admits a caller-supplied width and its maps are `InfoMap`
    lists. The finite-map compiler used by the RISC-V specialization is `compileProgHOL` below.

    The recursive compiler below keeps CakeML's fallback behavior for
    malformed compiled expressions and preserves the source control-flow
    constructors. -/
def compileProg [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (program : Prog α) : CrepProg α :=
  match program with
  | .skip => .skip
  | .dec name _shape value body =>
      /- CakeML derives the slot count, vmap entry, and `vmax` bump from the
         compiled expression's shape; the declared shape is ignored
         (`pan_to_crepScript.sml:141-149`). -/
      let compiled := compileExp context value
      let names := allocatedNames context compiled.2
      let nextContext := { context with
        vars := (name, (compiled.2, names)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize compiled.2 }
      if names.length = compiled.1.length then
        nestedDecs names compiled.1 (compileProg nextContext body)
      else .skip
  | .assign .local name value =>
      match lookupInfo name context.vars, compileExp context value with
      | some (_, names), (expressions, _) =>
          if names.length = expressions.length then
            if distinctLists names (expressions.flatMap crepExpVars) then
              crepNestedSeq
                (names.zipWith (fun name expression => .assign name expression) expressions)
            else
              let temporaries := freshNames context names.length 1
              nestedDecs temporaries expressions
                (crepNestedSeq
                  (names.zipWith (fun name temporary => .assign name (.var temporary))
                    temporaries))
          else .skip
      | _, _ => .skip
  | .assign .global _ _ => .skip
  | .primitive name operator arguments =>
      match lookupInfo name context.vars with
      | some (_, names) =>
          let compiledArgs := compileArgs context arguments
          let temporaries := freshNames context compiledArgs.length 1
          nestedDecs temporaries compiledArgs (.primitive names operator temporaries)
      | none => .skip
  | .store address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (values, shape) =>
          let addressTemporary := context.maxVar + 1
          let temporaries := freshNames context values.length 2
          if values.length = Shape.shapeSize shape then
            nestedDecs (addressTemporary :: temporaries) (address :: values)
              (crepNestedSeq (stores (.var addressTemporary) (temporaries.map .var)
                0 context.bytesInWord))
          else .skip
      | _, _ => .skip
  | .store32 address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .store32 address value
      | _, _ => .skip
  | .storeByte address value =>
      match compileExp context address, compileExp context value with
      | (address :: _, _), (value :: _, _) => .storeByte address value
      | _, _ => .skip
  | .seq first second => .seq (compileProg context first) (compileProg context second)
  | .ite condition thenBranch elseBranch =>
      match compileExp context condition with
      | (condition :: _, _) => .ite condition (compileProg context thenBranch)
          (compileProg context elseBranch)
      | _ => .skip
  | .while condition body =>
      match compileExp context condition with
      | (condition :: _, _) => .while condition (compileProg context body)
      | _ => .skip
  | .break => .break 0
  | .continue => .continue 0
  | .call info function arguments =>
      let args := compileArgs context arguments
      match info with
      | none => .call none function args
      | some (destination, handler) =>
          let compiledHandler :=
            match handler with
            | none => none
            | some (exception, handlerVar, handlerProgram) =>
                match lookupInfo exception context.exceptions with
                | none => none
                | some code =>
                    /- HOL's handled-call branch builds the handler body with
                       `exp_hdl` (`pan_to_crepScript.sml:238`) and never calls
                       `ret_hdl`/`ret_var`; see bead `flapjack-pxn.18.2.4.1`. -/
                    let handlerSetup :=
                      expHdlFiniteMap (infoMapToFiniteMap context.vars) handlerVar
                    some (code, .seq handlerSetup (compileProg context handlerProgram))
          match destination with
          | none =>
              /- A standalone value-returning call declares its return
                 temporaries up front (`pan_to_crepScript.sml:226-246`):
                 `nested_decs rts (REPLICATE (LENGTH rts) (Const 0w))`
                 around the call, with `rts` drawn from the callee's return
                 shape and empty for an unknown callee. -/
              let returnNames := functionReturnNames context function
              nestedDecs returnNames (returnNames.map (fun _ => .const 0))
                (.call (some (returnNames, compiledHandler)) function args)
          | some (kind, name) =>
              /- An assigned call keeps its destination only when `wrap_rt`
                  preserves the variable's shape; otherwise the call degrades
                  to a tail call, or to a handler-only call when the handler's
                  exception is known (`pan_to_crepScript.sml:247-260`). -/
              match callDestinationNames context kind name with
              | none =>
                  compiledHandler.elim (.call none function args)
                    (fun handler => .call (some ([], some handler)) function args)
              | some names => .call (some (names, compiledHandler)) function args
  | .decCall name shape function arguments body =>
      let names := allocatedNames context shape
      let nextContext := { context with
        vars := (name, (shape, names)) :: context.vars
        maxVar := context.maxVar + Shape.shapeSize shape }
      let call := .call (some (names, none)) function (compileArgs context arguments)
      nestedDecs names (names.map (fun _ => .const 0))
        (.seq call (compileProg nextContext body))
  | .extCall function configuration configurationLength array arrayLength =>
      match firstCompiledExp context configuration,
          firstCompiledExp context configurationLength,
          firstCompiledExp context array,
          firstCompiledExp context arrayLength with
      | some configuration, some configurationLength, some array, some arrayLength =>
          let base := maxCrepExpVar
            [configuration, configurationLength, array, arrayLength] + 1
          let configurationName := base
          let configurationLengthName := base + 1
          let arrayName := base + 2
          let arrayLengthName := base + 3
          let names := [configurationName, configurationLengthName, arrayName, arrayLengthName]
          nestedDecs names [configuration, configurationLength, array, arrayLength]
            (.extCall function configurationName configurationLengthName arrayName arrayLengthName)
      | _, _, _, _ => .skip
  | .raise exception value =>
      match lookupInfo exception context.exceptions with
      | some code =>
          let compiled := compileExp context value
          let temporaries := freshNames context compiled.1.length 1
          if compiled.1.length = Shape.shapeSize compiled.2 then
            .seq
              (nestedDecs temporaries compiled.1
                (crepNestedSeq (storeGlobals 0
                  (temporaries.map .var))))
              (.raise code)
          else .skip
      | none => .skip
  | .return value =>
      let compiled := compileExp context value
      if Shape.shapeSize compiled.2 = 0 then .return [] else .return compiled.1
  | .shMemLoad size .local name address =>
      match lookupInfo name context.vars, firstCompiledExpAnyShape context address with
      | some (_, destination :: _), some address =>
          .shMem (loadMemOpHOL size) destination address
      | _, _ => .skip
  | .shMemLoad _ .global _ _ => .skip
  | .shMemStore size address value =>
      match firstCompiledExpAnyShape context address, firstCompiledExpAnyShape context value with
      | some address, some value =>
          let temporary := maxCrepExpVar [address] + 1
          nestedDecs [temporary] [value] (.shMem (storeMemOpHOL size) temporary address)
      | _, _ => .skip
  | .tick => .tick
  | .annot _ _ => .skip

termination_by structural program

/-! Source-named port of CakeML Pancake's active `comp_func_def`
    (`pan_to_crepScript.sml:337`).  Cake derives the context's `vmax` from
    the flattened parameter shape, then invokes `compile`; keeping that
    construction explicit prevents callers from silently using the legacy
    next-free-slot convention. -/
def panToCrepCompFunc [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (params : List (VarName × Shape))
    (body : Prog α) : CrepProg α :=
  let shapes := params.map Prod.snd
  let vmax := Shape.shapeSize (.comb shapes) - 1
  compileProg
    { context with vars := panToCrepMakeVmap params, maxVar := vmax } body

/-! Flapjack's executable `pan_to_crep$compile_to_crep` analogue, not yet
    HOL-shaped: HOL's definition takes only declarations and builds the
    function and exception maps internally; this function takes an additional
    caller-supplied context. Bead `flapjack-pxn.18.3.1.3` tracks replacement by
    a faithful executable port.

    HOL's `comp_func` sets `vmax` to the greatest parameter slot, whereas the
    existing context-normalized API stores the next free slot in its function
    context.  The subtraction below is therefore intentional and preserves
    the source temporary numbering. -/
def compileFunDeclSource [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declaration : FunDecl α) : CompiledFunction α :=
  { name := declaration.name, params := panToCrepVars declaration.params,
    body := panToCrepCompFunc context declaration.params declaration.body,
    returnShape := declaration.returnShape }

def compileFunctionsSource [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) : List (Decl α) → List (CompiledFunction α)
  | [] => []
  | .function declaration :: declarations =>
      compileFunDeclSource context declaration ::
        compileFunctionsSource context declarations
  | _ :: declarations => compileFunctionsSource context declarations
termination_by declarations => sizeOf declarations

def compileToCrep [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    List (CompiledFunction α) :=
  let context := { context with functions := functionInfos declarations }
  compileFunctionsSource context declarations

/-! HOL finite-map variants used by the RISC-V production path. The parameter
    and function tables are built with `FUPDATE_LIST`; body compilation then
    uses `compileProgHOL` without converting the context to `InfoMap`. -/
/-- HOL `make_vmap_def` (`cakeml/pancake/pan_to_crepScript.sml:327-334`):
    `make_vmap params = let pvars = MAP FST params; shs = MAP SND params;
    ns = GENLIST I (size_of_shape (Comb shs));
    cvars = ZIP (shs, with_shape shs ns) in FEMPTY |++ ZIP (pvars, cvars)`.
    This Flapjack mirror follows the same consecutive slot allocation and
    source-order finite-map update, so a later duplicate name wins. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the produced map is keyed by
-- `VarName` = `String` and stores the production `Shape` (`named : StructName`
-- = `String`) rather than HOL's `varname` = `mlstring` and `shape`
-- (`named : mlstring`); the result is a `FiniteMap` function rather than HOL's
-- `fmap`, rendered by `FUPDATE_LIST FEMPTY` (a left fold) over the source-order
-- allocation, which matches `FEMPTY |++ ZIP`'s later-duplicate-wins semantics.
-- The `names_as_string` qualifier cannot authorize the `Shape` carrier, and no
-- `NameRanged` byte witness applies (the output is a finite map of
-- shape/slot-list entries, not a name). Direct HOL-EVAL rows are recorded in
-- `scripts/hol-probes/crep_vmap_ctxtfc_probe.out` (`vmap_x`/`vmap_y`/
-- `vmap_absent`/`ns_offsets`, plus `vmap_eq_ctxt`) and reproduced by
-- `makeVmapOracle`/`makeVmapHOLOracle`/`duplicateVmapOracle` in
-- `Flapjack/Test/CompileToCrepeParity.lean`, by `vmapCtxtFCGuard` in
-- `Flapjack/Test/PanToCrepCodeRelParity.lean`, and by the `with_shape` rows in
-- `Flapjack/Test/PanWithShapeParity.lean` (probe
-- `scripts/hol-probes/pan_lang_with_shape_probe.out`). Exact-carrier
-- replacement is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`).
def panToCrepMakeVmapHOL (params : List (VarName × Shape)) :
    FiniteMap VarName (Shape × List Nat) :=
  FUPDATE_LIST FEMPTY (compileParamVars params 0).1

def functionInfosHOL (declarations : List (Decl α)) :
    FiniteMap FunName (List (VarName × Shape) × Shape) :=
  /- HOL `alist_to_fmap` is `FOLDR FUPDATE FEMPTY`, so the first duplicate
     function name wins. `FUPDATE_LIST` is a left fold and needs reversal. -/
  FUPDATE_LIST FEMPTY (panToCrepMakeFuncs declarations).reverse

/-- `functionInfosHOL` (the declaration-list adapter) builds exactly the exact
    HOL `make_funcs` finite map of the extracted function entries. -/
theorem functionInfosHOL_eq_makeFuncsHOL (declarations : List (Decl α)) :
    functionInfosHOL declarations = makeFuncsHOL (functionEntries declarations) := by
  rw [functionInfosHOL, makeFuncsHOL, panToCrepMakeFuncs_eq_map]

def panToCrepCompFuncRiscV (context : PanToCrepHOLContext (BitVec width))
    (params : List (VarName × Shape)) (body : Prog (BitVec width)) :
    CrepProg (BitVec width) :=
  let shapes := params.map Prod.snd
  let vmax := Shape.shapeSize (.comb shapes) - 1
  compileProgRiscV
    (panToCrepMkCtxtHOL (panToCrepMakeVmapHOL params)
      context.funcs vmax context.eids) body

/-- HOL `comp_func_def` (`cakeml/pancake/pan_to_crepScript.sml:337-343`):
    `comp_func fs eids params body = let vmap = make_vmap params;
    shapes = MAP SND params; vmax = size_of_shape (Comb shapes) - 1 in
    compile (mk_ctxt vmap fs vmax eids) body`.  This Flapjack mirror follows
    the same clause order, but is NOT an exact HOL port. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): source-reviewed documented
-- carrier mismatch.  HOL `comp_func` is over `mlstring`-keyed maps
-- (`funname`/`eid`), `mlstring` parameter names (`varname`), HOL `shape` with
-- `size_of_shape`, and word-indexed `'a panLang$prog` with `compile`
-- returning `crepLang$prog`; this mirror instead uses `FunName`/`ExceptionId`/
-- `VarName` = `String`, production `Shape` with untagged `Shape.shapeSize`,
-- the untagged `panToCrepMakeVmapHOL`/`panToCrepMkCtxtHOL`, and
-- `compileProgRiscV` over `Prog`/`CrepProg (BitVec width)` (the exact
-- `make_vmap`, `mk_ctxt`, and `compile` carriers are not yet ported).  The
-- `names_as_string` qualifier cannot authorize the Shape/Prog/CrepProg
-- carriers, and no `NameRanged` byte witness exists because the output is a
-- compiled program, not a name.  HOL-EVAL coverage: `make_funcs_def` (the `fs`
-- argument) is probed in `scripts/hol-probes/crep_make_funcs_probe.out`; the
-- `comp_func`/`compile_to_crep` path is exercised by
-- `Flapjack/Test/PanToCrepCodeRelParity.lean`.  Exact replacement is tracked
-- by `flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`; exact
-- `compile` by `flapjack-pxn.18.3.5.8.13`).  Tag withdrawn.
def compFuncHOL
    (compilerFunctions : FiniteMap FunName (List (VarName × Shape) × Shape))
    (exceptionCodes : FiniteMap ExceptionId (BitVec width))
    (params : List (VarName × Shape)) (body : Prog (BitVec width)) :
    CrepProg (BitVec width) :=
  let vmap := panToCrepMakeVmapHOL params
  let shapes := params.map Prod.snd
  let vmax := Shape.shapeSize (.comb shapes) - 1
  compileProgRiscV
    (panToCrepMkCtxtHOL vmap compilerFunctions vmax exceptionCodes) body

/-- `panToCrepCompFuncRiscV` (the record-context adapter) is `compFuncHOL` at
    the context's function and exception maps. -/
theorem panToCrepCompFuncRiscV_eq_compFuncHOL
    (context : PanToCrepHOLContext (BitVec width))
    (params : List (VarName × Shape)) (body : Prog (BitVec width)) :
    panToCrepCompFuncRiscV context params body =
      compFuncHOL context.funcs context.eids params body := rfl

/-! HOL `get_eids_from_decls_def` (`cakeml/pancake/pan_to_crepScript.sml:356-364`):

```
get_eids_from_decls decls =
  let eids = MAP FST (exceptions decls);
      ns   = GENLIST (λx. (n2w x):'a word) (LENGTH eids);
      es   = MAP2 (λx y. (x,y)) eids ns
  in alist_to_fmap es
```

enumerating exception declarations in source order and turning their zero-based
indices into words. HOL `alist_to_fmap` uses `FOLDR FUPDATE FEMPTY`, so the
first duplicate exception name wins.

FLAPJACK-SPECIFIC (not an exact HOL port): this port mirrors the clause
structure and first-binding discipline, but its carriers differ from HOL.
(i) The result is keyed by `ExceptionId` = `String` (PanLang.lean), while HOL
`eid` is `mlstring`. (ii) The input is the production
`List (Decl (BitVec width))`, whose names are `String` and whose shapes are the
production `Shape`, not HOL's word-indexed `'a decl` carrying `mlstring` names
and `shape`. (iii) The output is the function-backed
`FiniteMap ExceptionId (BitVec width)` rather than HOL's
`(mlstring, 'a word) fmap`; the `FUPDATE_LIST ... .reverse` construction is the
Flapjack encoding of `alist_to_fmap`'s right fold. The `names_as_string`
qualifier cannot authorize the `Decl`/`Shape` input carrier or the
`FiniteMap`-vs-`fmap` representation, and no `NameRanged` byte witness exists
because the output is a map of words, not a name.

Direct HOL-EVAL rows are recorded in
`scripts/hol-probes/crep_get_eids_probe.out` (`eids_present`/`eids_second`/
`eids_absent`/`eids_codes_distinct`), reproduced against this definition by
`getEidsGuard` in `Flapjack/Test/PanToCrepCodeRelParity.lean`; the
first-binding duplicate row `duplicate_exceptions` from
`scripts/hol-probes/compile_to_crep_probe.out` is reproduced by
`holDuplicateExceptionProductionOracle` in
`Flapjack/Test/CompileToCrepeParity.lean`.

The exact MlString-keyed carrier replacement is tracked by
`flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`). -/
def panToCrepGetEidsFromDeclsHOL
    (declarations : List (Decl (BitVec width))) :
    FiniteMap ExceptionId (BitVec width) :=
  let names := (exceptionEntries declarations).map Prod.fst
  FUPDATE_LIST FEMPTY
    (names.zip ((List.range names.length).map (BitVec.ofNat width))).reverse

/-! HOL `compile_to_crep_def` (`cakeml/pancake/pan_to_crepScript.sml:383-391`):

```
compile_to_crep decls =
  let prog = functions decls;
      comp = comp_func (make_funcs prog) (get_eids_from_decls decls) in
    MAP (λ(name, params, body, return).
          (name, crep_vars params, comp params body)) prog
```

The Lean port below mirrors that let-structure and operand order clause-for-
clause. It also preserves the triple-shaped output boundary rather than
Flapjack's downstream `CompiledFunction` record (which additionally stores
source return-shape metadata); metadata is attached only in the untagged
adapter below.

FLAPJACK-SPECIFIC (not an exact HOL port): the carriers differ from HOL.
(i) `functions`/`FunName`/`VarName`/`ExceptionId` are `String`-keyed
(PanLang.lean), while HOL `funname`/`varname`/`eid` are `mlstring`.
(ii) The input is the production `List (Decl (BitVec width))`, whose shapes are
the production `Shape`, not HOL's word-indexed `'a decl` carrying `mlstring`
names and `shape`.
(iii) The result is `List (FunName × List Nat × CrepProg (BitVec width))`,
whose `CrepProg` call/exception funnames are `String`, rather than HOL's
`(mlstring # num list # 'a crepLang$prog) list`.
(iv) It delegates to the untagged production helpers `makeFuncsHOL`,
`panToCrepGetEidsFromDeclsHOL`, `compFuncHOL`, and `panToCrepVars`, which are
themselves string/shape-shaped. The `names_as_string` qualifier cannot
authorize the `Decl`/`Shape`/`CrepProg` carriers, and no `NameRanged` byte
witness exists because the output is a list of triples, not a name.

Direct HOL-EVAL rows are recorded in
`scripts/hol-probes/compile_to_crep_probe.out` (`empty`/`raise_const`/
`raise_pair`/`raise_pair_later`/`handled_pair`/`duplicate_exceptions`) and
reproduced against this definition by `holDeclarationOnlyOracle`,
`holPairRaiseProductionOracle`, `holHandledPairProductionOracle`, and
`holDuplicateExceptionProductionOracle` in
`Flapjack/Test/CompileToCrepeParity.lean`.

The exact MlString-keyed carrier replacement is tracked by
`flapjack-pxn.18.3.5.8` (parent `flapjack-pxn.18.3.5.7.2`). -/
def compileToCrepHOL
    (declarations : List (Decl (BitVec width))) :
    List (FunName × List Nat × CrepProg (BitVec width)) :=
  let functions := functionEntries declarations
  let functionMap := makeFuncsHOL functions
  let exceptionMap := panToCrepGetEidsFromDeclsHOL declarations
  functions.map fun (name, parameters, body, _returnShape) =>
    (name, panToCrepVars parameters,
      compFuncHOL functionMap exceptionMap parameters body)

/-! Executable metadata adapter after the `compile_to_crep`-shaped result.
Cake's following Crep passes operate on triples; Flapjack retains the source
return shape in `CompiledFunction` for its existing downstream interfaces. -/
def compileToCrepHOLWithMetadata
    (declarations : List (Decl (BitVec width))) :
    List (CompiledFunction (BitVec width)) :=
  (functionEntries declarations).zipWith
    (fun (_, _, _, returnShape) (name, parameters, body) =>
      { name, params := parameters, body, returnShape })
    (compileToCrepHOL declarations)

theorem compileProg_skip [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) : compileProg context .skip = .skip := by
  simp [compileProg]

theorem compileProg_seq [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (first second : Prog α) :
    compileProg context (.seq first second) =
      .seq (compileProg context first) (compileProg context second) := by
  simp [compileProg]

theorem compileProg_return [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (value : Exp α) :
    compileProg context (.return value) =
      let compiled := compileExp context value
      if Shape.shapeSize compiled.2 = 0 then .return [] else .return compiled.1 := by
  simp [compileProg]

theorem compileProg_extCall_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (configuration configurationLength array arrayLength : Exp α)
    (configuration' configurationLength' array' arrayLength' : CrepExp α)
    (hconfiguration : firstCompiledExp context configuration = some configuration')
    (hconfigurationLength :
      firstCompiledExp context configurationLength = some configurationLength')
    (harray : firstCompiledExp context array = some array')
    (harrayLength : firstCompiledExp context arrayLength = some arrayLength') :
    compileProg context
        (.extCall function configuration configurationLength array arrayLength) =
      nestedDecs [maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 1,
        maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 2,
        maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 3,
        maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 4]
        [configuration', configurationLength', array', arrayLength']
        (.extCall function
          (maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 1)
          (maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 2)
          (maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 3)
          (maxCrepExpVar [configuration', configurationLength', array', arrayLength'] + 4)) := by
  simp [compileProg, hconfiguration, hconfigurationLength, harray, harrayLength,
    nestedDecs]

theorem compileProg_call_handler_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (returnShape : Shape)
    (exception handlerVar : VarName) (exceptionCode : α)
    (handlerProgram : Prog α) (handlerNames : List Nat)
    (compiledArguments : List (CrepExp α))
    (hfunction : lookupInfo function context.functions =
      some ([], returnShape))
    (hexception : lookupInfo exception context.exceptions = some exceptionCode)
    (hhandler : ∃ shape,
      lookupInfo handlerVar context.vars = some (shape, handlerNames))
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (none, some (exception, handlerVar, handlerProgram)))
          function arguments) =
      nestedDecs (allocatedNames context returnShape)
        ((allocatedNames context returnShape).map (fun _ => (.const 0 : CrepExp α)))
        (.call (some (allocatedNames context returnShape,
          some (exceptionCode,
            .seq (expHdlFiniteMap (infoMapToFiniteMap context.vars) handlerVar)
              (compileProg context handlerProgram))))
          function compiledArguments) := by
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hfunction, hexception, harguments,
    functionReturnNames, allocatedNames, infoMapToFiniteMap, expHdlFiniteMap]

/-! The `Call_Ret_Exception` branch of Cake's `pc_compile_correct` splits on
    whether the handler's exception identifier is present in the context's
    exception map.  When it is absent, `compileProg` cannot compile the
    handler and drops it, so the emitted call carries no handler metadata.
    The three equations below expose that degraded shape for the standalone
    and destination-carrying calls; they are the explicit compile-side
    premise for the "exception id in handler not found in context" sub-case. -/

theorem compileProg_call_handler_missing_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (returnShape : Shape)
    (exception handlerVar : VarName)
    (handlerProgram : Prog α)
    (compiledArguments : List (CrepExp α))
    (hfunction : lookupInfo function context.functions =
      some ([], returnShape))
    (hexception : lookupInfo exception context.exceptions = none)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (none, some (exception, handlerVar, handlerProgram)))
          function arguments) =
      nestedDecs (allocatedNames context returnShape)
        ((allocatedNames context returnShape).map (fun _ => (.const 0 : CrepExp α)))
        (.call (some (allocatedNames context returnShape, none))
          function compiledArguments) := by
  simp [compileProg, hfunction, hexception, harguments,
    functionReturnNames, allocatedNames]

theorem compileProg_call_handler_missing_destination_degraded_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (exception handlerVar : VarName)
    (handlerProgram : Prog α)
    (compiledArguments : List (CrepExp α))
    (hexception : lookupInfo exception context.exceptions = none)
    (hnames : callDestinationNames context kind name = none)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (some (kind, name),
          some (exception, handlerVar, handlerProgram))) function arguments) =
      .call none function compiledArguments := by
  simp [compileProg, hexception, hnames, harguments]

theorem compileProg_call_handler_missing_destination_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (names : List Nat)
    (exception handlerVar : VarName)
    (handlerProgram : Prog α)
    (compiledArguments : List (CrepExp α))
    (hexception : lookupInfo exception context.exceptions = none)
    (hnames : callDestinationNames context kind name = some names)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (some (kind, name),
          some (exception, handlerVar, handlerProgram))) function arguments) =
      .call (some (names, none)) function compiledArguments := by
  simp [compileProg, hexception, hnames, harguments]

/-! The `Call_Ret` branch of Cake's `pc_compile_correct` is the
    assignment-producing call with no handler.  `compileProg` keeps the
    flattened destination slots when `wrap_rt` preserves the variable's
    shape and otherwise degrades the call to a tail call
    (`pan_to_crepScript.sml:247-260`).  The two equations below expose those
    emitted shapes as explicit compile-side premises. -/

theorem compileProg_call_destination_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (names : List Nat)
    (compiledArguments : List (CrepExp α))
    (hnames : callDestinationNames context kind name = some names)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (some (kind, name), none)) function arguments) =
      .call (some (names, none)) function compiledArguments := by
  simp [compileProg, hnames, harguments]

theorem compileProg_call_destination_degraded_of_compiled
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (compiledArguments : List (CrepExp α))
    (hnames : callDestinationNames context kind name = none)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (some (kind, name), none)) function arguments) =
      .call none function compiledArguments := by
  simp [compileProg, hnames, harguments]

theorem compileProg_break [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) : compileProg context .break = .break 0 := by
  simp [compileProg]

theorem compileProg_continue [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) : compileProg context .continue = .continue 0 := by
  simp [compileProg]

theorem compileProg_tick [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) : compileProg context .tick = .tick := by
  simp [compileProg]

theorem compileProg_annot [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (tag text : String) :
    compileProg context (.annot tag text) = .skip := by
  simp [compileProg]

theorem compileProg_assign_global [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (value : Exp α) :
    compileProg context (.assign .global name value) = .skip := by
  simp [compileProg]

theorem compileProg_ite_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (condition : Exp α)
    (thenBranch elseBranch : Prog α) (condition' : CrepExp α)
    (rest : List (CrepExp α)) (shape : Shape)
    (hcondition : compileExp context condition = (condition' :: rest, shape)) :
    compileProg context (.ite condition thenBranch elseBranch) =
      .ite condition' (compileProg context thenBranch) (compileProg context elseBranch) := by
  simp [compileProg, hcondition]

theorem compileProg_while_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (condition : Exp α) (body : Prog α)
    (condition' : CrepExp α) (rest : List (CrepExp α)) (shape : Shape)
    (hcondition : compileExp context condition = (condition' :: rest, shape)) :
    compileProg context (.while condition body) = .while condition' (compileProg context body) := by
  simp [compileProg, hcondition]

theorem compileProg_store32_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (address value : Exp α)
    (address' value' : CrepExp α) (addressRest valueRest : List (CrepExp α))
    (addressShape valueShape : Shape)
    (haddress : compileExp context address = (address' :: addressRest, addressShape))
    (hvalue : compileExp context value = (value' :: valueRest, valueShape)) :
    compileProg context (.store32 address value) = .store32 address' value' := by
  simp [compileProg, haddress, hvalue]

theorem compileProg_storeByte_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (address value : Exp α)
    (address' value' : CrepExp α) (addressRest valueRest : List (CrepExp α))
    (addressShape valueShape : Shape)
    (haddress : compileExp context address = (address' :: addressRest, addressShape))
    (hvalue : compileExp context value = (value' :: valueRest, valueShape)) :
    compileProg context (.storeByte address value) = .storeByte address' value' := by
  simp [compileProg, haddress, hvalue]

/-! The remaining `compileProg` decomposition equations expose the emitted
    Crepe shape for the constructors that the assigned-memory bound proof
    (`not_mem_context_assigned_mem_gt`, `pan_to_crepProofScript.sml:1252`)
    must analyse: declarations, declaration-calls, stores, raises,
    primitives, local assignments, and the two shared-memory leaves.  Each
    carries the explicit `compileExp`/`lookupInfo` premise that determines
    the constructor's branch. -/

theorem compileProg_dec_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape) (value : Exp α)
    (body : Prog α) (expressions : List (CrepExp α)) (valueShape : Shape)
    (hvalue : compileExp context value = (expressions, valueShape)) :
    compileProg context (.dec name shape value body) =
      if (allocatedNames context valueShape).length = expressions.length then
        nestedDecs (allocatedNames context valueShape) expressions
          (compileProg { context with
            vars := (name, (valueShape, allocatedNames context valueShape)) :: context.vars,
            maxVar := context.maxVar + Shape.shapeSize valueShape } body)
      else .skip := by
  simp only [compileProg, hvalue]

theorem compileProg_decCall [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (body : Prog α) :
    compileProg context (.decCall name shape function arguments body) =
      nestedDecs (allocatedNames context shape)
        ((allocatedNames context shape).map (fun _ => (.const 0 : CrepExp α)))
        (.seq (.call (some (allocatedNames context shape, none)) function
            (compileArgs context arguments))
          (compileProg { context with
            vars := (name, (shape, allocatedNames context shape)) :: context.vars,
            maxVar := context.maxVar + Shape.shapeSize shape } body)) := by
  simp only [compileProg]

theorem compileProg_store_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (address value : Exp α)
    (address' : CrepExp α) (addressRest : List (CrepExp α)) (addressShape : Shape)
    (values : List (CrepExp α)) (shape : Shape)
    (haddress : compileExp context address = (address' :: addressRest, addressShape))
    (hvalue : compileExp context value = (values, shape)) :
    compileProg context (.store address value) =
      if values.length = Shape.shapeSize shape then
        nestedDecs ((context.maxVar + 1) :: freshNames context values.length 2)
          (address' :: values)
          (crepNestedSeq
            (stores (.var (context.maxVar + 1))
              ((freshNames context values.length 2).map .var) 0 context.bytesInWord))
      else .skip := by
  simp only [compileProg, haddress, hvalue]

theorem compileProg_raise_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (exception : ExceptionId) (value : Exp α) (code : α)
    (expressions : List (CrepExp α)) (shape : Shape)
    (hexception : lookupInfo exception context.exceptions = some code)
    (hvalue : compileExp context value = (expressions, shape)) :
    compileProg context (.raise exception value) =
      if expressions.length = Shape.shapeSize shape then
        .seq (nestedDecs (freshNames context expressions.length 1) expressions
            (crepNestedSeq (storeGlobals 0
              ((freshNames context expressions.length 1).map .var))))
          (.raise code)
      else .skip := by
  simp only [compileProg, hexception, hvalue]

theorem compileProg_primitive_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp α)) (shape : Shape) (names : List Nat)
    (compiledArguments : List (CrepExp α))
    (hlookup : lookupInfo name context.vars = some (shape, names))
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context (.primitive name operator arguments) =
      nestedDecs (freshNames context compiledArguments.length 1) compiledArguments
        (.primitive names operator (freshNames context compiledArguments.length 1)) := by
  simp only [compileProg, hlookup, harguments]

theorem compileProg_assign_local_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (name : VarName) (value : Exp α)
    (shape valueShape : Shape) (names : List Nat) (expressions : List (CrepExp α))
    (hlookup : lookupInfo name context.vars = some (shape, names))
    (hvalue : compileExp context value = (expressions, valueShape)) :
    compileProg context (.assign .local name value) =
      if names.length = expressions.length then
        (if distinctLists names (expressions.flatMap crepExpVars) then
          crepNestedSeq
            (names.zipWith (fun name expression => .assign name expression) expressions)
        else
          nestedDecs (freshNames context names.length 1) expressions
            (crepNestedSeq
              (names.zipWith (fun name temporary => .assign name (.var temporary))
                (freshNames context names.length 1))))
      else .skip := by
  simp only [compileProg, hlookup, hvalue]

theorem compileProg_shMemLoad_local_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (size : OpSize) (name : VarName) (address : Exp α)
    (shape : Shape) (destination : Nat) (destinationRest : List Nat) (address' : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (shape, destination :: destinationRest))
    (haddress : firstCompiledExpAnyShape context address = some address') :
    compileProg context (.shMemLoad size .local name address) =
      .shMem (loadMemOpHOL size) destination address' := by
  simp only [compileProg, hlookup, haddress]

theorem compileProg_shMemStore_of_compiled [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : CompileContext α) (size : OpSize) (address value : Exp α)
    (address' value' : CrepExp α)
    (haddress : firstCompiledExpAnyShape context address = some address')
    (hvalue : firstCompiledExpAnyShape context value = some value') :
    compileProg context (.shMemStore size address value) =
      nestedDecs [maxCrepExpVar [address'] + 1] [value']
        (.shMem (storeMemOpHOL size) (maxCrepExpVar [address'] + 1) address') := by
  simp only [compileProg, haddress, hvalue]

end Flapjack
