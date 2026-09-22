import Flapjack.PanToCrep

/-!
Core statement lowering from Flapjack to Crepe.

This is the structured-local/control-flow portion of `pan_to_crep`. The
function is intentionally extraction-friendly: malformed shape lengths and
front-end constructs whose runtime environments are not ported yet lower to
`Skip`, matching the reference pass's defensive fallback style.
-/

namespace Flapjack

def compileArgs [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expressions : List (Exp α)) : List (CrepExp α) :=
  match expressions with
  | [] => []
  | expression :: expressions =>
      (compileExp context expression).1 ++ compileArgs context expressions
termination_by structural expressions

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

/- `wrap_rt`-based call-destination resolution (`pan_to_crepScript.sml:247`):
    a call target survives only when the destination variable's shape is
    preserved; globals and unknown locals degrade to a tail call. -/
def callDestinationNames (context : CompileContext α) (kind : VarKind)
    (name : VarName) : Option (List Nat) :=
  match kind with
  | .global => none
  | .local =>
      match lookupInfo name context.vars with
      | none => none
      | some info => (wrapRt (some info)).map Prod.snd

def loadMemOp : OpSize → CrepMemOp
  | .op8 => .load8
  | .opW => .load
  | .op32 => .load32
  | .op16 => .load16

def storeMemOp : OpSize → CrepMemOp
  | .op8 => .store8
  | .opW => .store
  | .op32 => .store32
  | .op16 => .store16

def firstCompiledExp [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExp context expression with
  | (compiled :: _, .one) => some compiled
  | _ => none

/-- CakeML's shared-memory compilation only requires the compiled
    address/value list to be nonempty and proceeds with the head word, for
    any shape (`pan_to_crepScript.sml:291-305`). -/
def firstCompiledExpAnyShape [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (expression : Exp α) : Option (CrepExp α) :=
  match compileExp context expression with
  | (compiled :: _, _) => some compiled
  | _ => none

theorem firstCompiledExpAnyShape_of_firstCompiledExp [BEq α] [OfNat α 0] [Add α]
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

/-! Source-named port of CakeML Pancake's `crep_vars_def`
    (`pan_to_crepScript.sml:376`).  The Crepe function interface exposes one
    consecutive slot for every flattened parameter word. -/
def panToCrepVars (params : List (VarName × Shape)) : List Nat :=
  List.range (Shape.shapeSize (.comb (params.map Prod.snd)))

/-! Faithful port of `pan_to_crep$compile` (`compile_def`) from
    `cakeml/pancake/pan_to_crepScript.sml:139-305`.

    The recursive compiler below keeps CakeML's fallback behavior for
    malformed compiled expressions and preserves the source control-flow
    constructors. -/
def compileProg [BEq α] [OfNat α 0] [Add α]
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
                    let handlerSetup :=
                      match lookupInfo handlerVar context.vars with
                      | some (_, names) => assignRet context.bytesInWord names
                      | none => .skip
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
                (crepNestedSeq (storeGlobals 0 context.bytesInWord
                  (temporaries.map .var))))
              (.raise code)
          else .skip
      | none => .skip
  | .return value => .return (compileExp context value).1
  | .shMemLoad size .local name address =>
      match lookupInfo name context.vars, firstCompiledExpAnyShape context address with
      | some (_, destination :: _), some address => .shMem (loadMemOp size) destination address
      | _, _ => .skip
  | .shMemLoad _ .global _ _ => .skip
  | .shMemStore size address value =>
      match firstCompiledExpAnyShape context address, firstCompiledExpAnyShape context value with
      | some address, some value =>
          let temporary := maxCrepExpVar [address] + 1
          nestedDecs [temporary] [value] (.shMem (storeMemOp size) temporary address)
      | _, _ => .skip
  | .tick => .tick
  | .annot _ _ => .skip

termination_by structural program

/-! Source-named port of CakeML Pancake's active `comp_func_def`
    (`pan_to_crepScript.sml:337`).  Cake derives the context's `vmax` from
    the flattened parameter shape, then invokes `compile`; keeping that
    construction explicit prevents callers from silently using the legacy
    next-free-slot convention. -/
def panToCrepCompFunc [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (params : List (VarName × Shape))
    (body : Prog α) : CrepProg α :=
  let shapes := params.map Prod.snd
  let vmax := Shape.shapeSize (.comb shapes) - 1
  compileProg
    { context with vars := panToCrepMakeVmap params, maxVar := vmax } body

/-! Faithful port of `pan_to_crep$compile_to_crep` from
    `cakeml/pancake/pan_to_crepScript.sml:383-391`.

    HOL's `comp_func` sets `vmax` to the greatest parameter slot, whereas the
    existing context-normalized API stores the next free slot in its function
    context.  The subtraction below is therefore intentional and preserves
    the source temporary numbering. -/
def compileFunDeclSource [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declaration : FunDecl α) : CompiledFunction α :=
  { name := declaration.name, params := panToCrepVars declaration.params,
    body := panToCrepCompFunc context declaration.params declaration.body,
    returnShape := declaration.returnShape }

def compileFunctionsSource [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : List (Decl α) → List (CompiledFunction α)
  | [] => []
  | .function declaration :: declarations =>
      compileFunDeclSource context declaration ::
        compileFunctionsSource context declarations
  | _ :: declarations => compileFunctionsSource context declarations
termination_by declarations => sizeOf declarations

def compileToCrep [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (declarations : List (Decl α)) :
    List (CompiledFunction α) :=
  let context := { context with functions := functionInfos declarations }
  compileFunctionsSource context declarations

theorem compileProg_skip [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .skip = .skip := by
  simp [compileProg]

theorem compileProg_seq [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (first second : Prog α) :
    compileProg context (.seq first second) =
      .seq (compileProg context first) (compileProg context second) := by
  simp [compileProg]

theorem compileProg_return [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (value : Exp α) :
    compileProg context (.return value) = .return (compileExp context value).1 := by
  simp [compileProg]

theorem compileProg_extCall_of_compiled [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_call_handler_of_compiled [BEq α] [OfNat α 0] [Add α]
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
            .seq (assignRet context.bytesInWord handlerNames)
              (compileProg context handlerProgram))))
          function compiledArguments) := by
  rcases hhandler with ⟨shape, hhandler⟩
  simp [compileProg, hfunction, hexception, hhandler, harguments,
    functionReturnNames, allocatedNames]

/-! The `Call_Ret_Exception` branch of Cake's `pc_compile_correct` splits on
    whether the handler's exception identifier is present in the context's
    exception map.  When it is absent, `compileProg` cannot compile the
    handler and drops it, so the emitted call carries no handler metadata.
    The three equations below expose that degraded shape for the standalone
    and destination-carrying calls; they are the explicit compile-side
    premise for the "exception id in handler not found in context" sub-case. -/

theorem compileProg_call_handler_missing_of_compiled [BEq α] [OfNat α 0] [Add α]
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
    [BEq α] [OfNat α 0] [Add α]
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
    [BEq α] [OfNat α 0] [Add α]
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
    [BEq α] [OfNat α 0] [Add α]
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
    [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (function : FunName)
    (arguments : List (Exp α)) (kind : VarKind) (name : VarName)
    (compiledArguments : List (CrepExp α))
    (hnames : callDestinationNames context kind name = none)
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context
        (.call (some (some (kind, name), none)) function arguments) =
      .call none function compiledArguments := by
  simp [compileProg, hnames, harguments]

theorem compileProg_break [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .break = .break 0 := by
  simp [compileProg]

theorem compileProg_continue [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .continue = .continue 0 := by
  simp [compileProg]

theorem compileProg_tick [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) : compileProg context .tick = .tick := by
  simp [compileProg]

theorem compileProg_annot [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (tag text : String) :
    compileProg context (.annot tag text) = .skip := by
  simp [compileProg]

theorem compileProg_assign_global [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (value : Exp α) :
    compileProg context (.assign .global name value) = .skip := by
  simp [compileProg]

theorem compileProg_ite_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (condition : Exp α)
    (thenBranch elseBranch : Prog α) (condition' : CrepExp α)
    (rest : List (CrepExp α)) (shape : Shape)
    (hcondition : compileExp context condition = (condition' :: rest, shape)) :
    compileProg context (.ite condition thenBranch elseBranch) =
      .ite condition' (compileProg context thenBranch) (compileProg context elseBranch) := by
  simp [compileProg, hcondition]

theorem compileProg_while_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (condition : Exp α) (body : Prog α)
    (condition' : CrepExp α) (rest : List (CrepExp α)) (shape : Shape)
    (hcondition : compileExp context condition = (condition' :: rest, shape)) :
    compileProg context (.while condition body) = .while condition' (compileProg context body) := by
  simp [compileProg, hcondition]

theorem compileProg_store32_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (address value : Exp α)
    (address' value' : CrepExp α) (addressRest valueRest : List (CrepExp α))
    (addressShape valueShape : Shape)
    (haddress : compileExp context address = (address' :: addressRest, addressShape))
    (hvalue : compileExp context value = (value' :: valueRest, valueShape)) :
    compileProg context (.store32 address value) = .store32 address' value' := by
  simp [compileProg, haddress, hvalue]

theorem compileProg_storeByte_of_compiled [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_dec_of_compiled [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_decCall [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_store_of_compiled [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_raise_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (exception : ExceptionId) (value : Exp α) (code : α)
    (expressions : List (CrepExp α)) (shape : Shape)
    (hexception : lookupInfo exception context.exceptions = some code)
    (hvalue : compileExp context value = (expressions, shape)) :
    compileProg context (.raise exception value) =
      if expressions.length = Shape.shapeSize shape then
        .seq (nestedDecs (freshNames context expressions.length 1) expressions
            (crepNestedSeq (storeGlobals 0 context.bytesInWord
              ((freshNames context expressions.length 1).map .var))))
          (.raise code)
      else .skip := by
  simp only [compileProg, hexception, hvalue]

theorem compileProg_primitive_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp α)) (shape : Shape) (names : List Nat)
    (compiledArguments : List (CrepExp α))
    (hlookup : lookupInfo name context.vars = some (shape, names))
    (harguments : compileArgs context arguments = compiledArguments) :
    compileProg context (.primitive name operator arguments) =
      nestedDecs (freshNames context compiledArguments.length 1) compiledArguments
        (.primitive names operator (freshNames context compiledArguments.length 1)) := by
  simp only [compileProg, hlookup, harguments]

theorem compileProg_assign_local_of_compiled [BEq α] [OfNat α 0] [Add α]
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

theorem compileProg_shMemLoad_local_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (size : OpSize) (name : VarName) (address : Exp α)
    (shape : Shape) (destination : Nat) (destinationRest : List Nat) (address' : CrepExp α)
    (hlookup : lookupInfo name context.vars = some (shape, destination :: destinationRest))
    (haddress : firstCompiledExpAnyShape context address = some address') :
    compileProg context (.shMemLoad size .local name address) =
      .shMem (loadMemOp size) destination address' := by
  simp only [compileProg, hlookup, haddress]

theorem compileProg_shMemStore_of_compiled [BEq α] [OfNat α 0] [Add α]
    (context : CompileContext α) (size : OpSize) (address value : Exp α)
    (address' value' : CrepExp α)
    (haddress : firstCompiledExpAnyShape context address = some address')
    (hvalue : firstCompiledExpAnyShape context value = some value') :
    compileProg context (.shMemStore size address value) =
      nestedDecs [maxCrepExpVar [address'] + 1] [value']
        (.shMem (storeMemOp size) (maxCrepExpVar [address'] + 1) address') := by
  simp only [compileProg, haddress, hvalue]

end Flapjack
