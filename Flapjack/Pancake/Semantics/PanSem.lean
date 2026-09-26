import Flapjack.HolRef
import Flapjack.PanBst
import Flapjack.PanValueFfiClockSemantics

/-!
# Pancake `evaluate`

Source reference: `cakeml/pancake/semantics/panSemScript.sml:556-736`
(`evaluate_def`). The HOL source evaluates one `panLang$prog` against a state
whose `code` field is a finite map. `PanSemEvaluateState` is the existing
list-backed executable compatibility boundary. `panSemEvaluateCodeState` is
the production source-state entry point: it resolves every recursive Call and
DecCall from the finite-support `PanSemState.code` map.

The fuel is only Lean's termination guard. The compatibility entry point uses
its legacy function list; the source-state entry point derives fuel from the
code map and source clock. Observable clock transitions remain those of the
source semantics.
-/

namespace Flapjack

/-- Flapjack's executable operation that clears the source state's local map.
    HOL `panSem$empty_locals` (`panSemScript.sml:436-438`) instead updates the
    finite `mlstring`-keyed map field to `FEMPTY`. This production state uses
    String-keyed unrestricted lookup functions and `PanValue`; it is not the
    HOL state carrier. The more faithful `emptyLocalsHOLExact` helper in
    `PanSem/StateExact.lean` uses `MlString`/`ValueHOL`, but the other map fields
    remain unrestricted and admit infinite support. Keep this declaration
    untagged until the exact finite-map carrier bridge lands
    (`flapjack-pxn.18.3.7.1.3.1.1.2`). -/
def panEmptyLocals (state : PanSemState α ffi) : PanSemState α ffi :=
  { state with locals := fun _ => none }

/-- Faithful context-free port of Cake `panSem$shape_of`
    (`cakeml/pancake/semantics/panSemScript.sml:80`). The source `v` cases
    correspond exhaustively to `PanValue`: `.word w` represents
    `Val (Word w)` because HOL `word_lab` has only its `Word` constructor;
    `.rStruct vs` maps recursively to `Comb (MAP shape_of vs)`; `.nStruct nm
    fields` maps to `Named nm`, with fields ignored on both sides. The HOL
    definition has no premises or side conditions, and these three Lean cases
    have exactly the same behavior. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL `shape_of` returns the
-- `mlstring`-named `panLang$shape`, whereas this Lean function returns the
-- production `Shape` whose `Named` field is `StructName = String`
-- (PanLang.lean aliases `stcname = ``:mlstring```). Constructor clauses match,
-- but the codomain carrier differs, so the tag is withheld until the exact
-- MlString-named `ShapeHOL` is routed here (tracked by `flapjack-pxn.18.3.5.8`,
-- parent `flapjack-0lj`).
def panSemShapeOf : PanValue α → Shape
  | .word _ => .one
  | .rStruct values => .comb (values.map panSemShapeOf)
  | .nStruct name _ => .named name
termination_by value => sizeOf value

/-- Flapjack's context-parameterized scalar-shape function `panValueShape`
    (`Flapjack/PanValues.lean`) ignores its `StructContext` argument and is
    computed by exactly the same three clauses as the tagged exact
    `panSemShapeOf`.  This proves the two functions agree for every context,
    which is the alignment used by `evaluateDecls` (bead
    `flapjack-pxn.18.3.6.4`).  `panValueShape` itself stays untagged because
    HOL `shape_of` has no context parameter. -/
theorem panValueShape_eq_panSemShapeOf_tagged (context : StructContext) (value : PanValue α) :
    panValueShape context value = panSemShapeOf value := by
  induction value using panValueShape.induct with
  | case1 value => simp only [panValueShape, panSemShapeOf]
  | case2 fields ih =>
      simp only [panValueShape, panSemShapeOf]
      exact congrArg Shape.comb (List.map_congr_left ih)
  | case3 name fields => simp only [panValueShape, panSemShapeOf]

/- Exact port of HOL `panSem$word_lab` (`panSemScript.sml:17`):
   `word_lab = Word ('a word)`. A HOL word has positive `dimindex`; Lean's
   `[NeZero width]` gives the same positive-width carrier, with one constructor
   and one `BitVec width` payload. The BitVec width is the canonical finite-word
   representation used throughout this port. The direct production-carrier
   conversions below remain Flapjack-specific infrastructure. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "word_lab"]
inductive HolWordLab (width : Nat) [NeZero width] where
  | word (value : BitVec width)
  deriving BEq, DecidableEq, Repr

/-- The isomorphism from the exact port to production `PanWordLab`. -/
def HolWordLab.toPanWordLab {width : Nat} [NeZero width] :
    HolWordLab width → PanWordLab (BitVec width)
  | .word value => .word value

/-- The isomorphism from production `PanWordLab` to the exact port. -/
def PanWordLab.toHolWordLab {width : Nat} [NeZero width] :
    PanWordLab (BitVec width) → HolWordLab width
  | .word value => .word value

@[simp] theorem HolWordLab.toPanWordLab_toHolWordLab {width : Nat} [NeZero width]
    (value : HolWordLab width) :
    value.toPanWordLab.toHolWordLab = value := by
  cases value <;> rfl

@[simp] theorem PanWordLab.toHolWordLab_toPanWordLab {width : Nat} [NeZero width]
    (value : PanWordLab (BitVec width)) :
    value.toHolWordLab.toPanWordLab = value := by
  cases value <;> rfl

@[simp] theorem HolWordLab.toPanWordLab_word {width : Nat} [NeZero width]
    (value : BitVec width) :
    (HolWordLab.word value).toPanWordLab = PanWordLab.word value := rfl

/-- Source-shaped port of HOL `panSem$v` (`panSemScript.sml:22`,
    `v = Val ('a word_lab) | RStruct (v list) | NStruct stcname ((fldname # v) list) End`).
    As with `HolWordLab`, the payload word is width-indexed. The HOL name
    carriers `stcname`/`fldname` are `mlstring`, while Lean uses `String`, so
    the datatype is not an exact HOL port and carries no `@[hol]` tag; see the
    note below. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL `panSem$v`
-- (`panSemScript.sml:22`) is
-- `Val ('a word_lab) | RStruct (v list) | NStruct stcname ((fldname # v) list)`
-- with `stcname`/`fldname` = `mlstring`, whereas this Lean `nStruct` carries
-- `StructName`/`FieldName = String`. This compatibility carrier is explicitly
-- Flapjack-specific and keeps its word payload in production `PanWordLab`;
-- the exact `ValueHOL` in `PanSem/ValueHOL.lean` uses positive-width
-- `HolWordLab` instead. No tag is attached to this String-backed carrier.
inductive HolValue (width : Nat) where
  | val (value : PanWordLab (BitVec width))
  | rStruct (fields : List (HolValue width))
  | nStruct (name : StructName) (fields : List (FieldName × HolValue width))
  deriving Repr

mutual
  /-- The isomorphism from production `PanValue` to the exact port `HolValue`. -/
  def PanValue.toHolValue {width : Nat} : PanValue (BitVec width) → HolValue width
    | .word value => .val (.word value)
    | .rStruct fields => .rStruct (fields.map PanValue.toHolValue)
    | .nStruct name fields =>
        .nStruct name (fields.map (fun pair : FieldName × PanValue (BitVec width) => (pair.1, pair.2.toHolValue)))
  termination_by value => sizeOf value
  decreasing_by
    all_goals
      simp_wf
      first
      | (rename_i hmem
         have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
         have hmemlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem; have hlt := List.sizeOf_lt_of_mem hmem; omega)
      | omega

  /-- The isomorphism from the exact port `HolValue` to production `PanValue`. -/
  def HolValue.toPanValue {width : Nat} : HolValue width → PanValue (BitVec width)
    | .val (.word bits) => .word bits
    | .rStruct fields => .rStruct (fields.map HolValue.toPanValue)
    | .nStruct name fields =>
        .nStruct name (fields.map (fun pair : FieldName × HolValue width => (pair.1, pair.2.toPanValue)))
  termination_by value => sizeOf value
  decreasing_by
    all_goals
      simp_wf
      first
      | (rename_i hmem
         have hsnd : sizeOf pair.snd < sizeOf pair := by cases pair; simp +arith
         have hmemlt := List.sizeOf_lt_of_mem hmem
         omega)
      | (rename_i hmem; have hlt := List.sizeOf_lt_of_mem hmem; omega)
      | omega
end

mutual
  @[simp] theorem PanValue.toHolValue_toPanValue {width : Nat} (value : PanValue (BitVec width)) :
      value.toHolValue.toPanValue = value := by
    induction value using PanValue.toHolValue.induct with
    | case1 bits =>
        unfold PanValue.toHolValue HolValue.toPanValue
        rfl
    | case2 fields ih =>
        unfold PanValue.toHolValue HolValue.toPanValue
        rw [List.map_map]
        apply congrArg PanValue.rStruct
        simpa using (show List.map (HolValue.toPanValue ∘ PanValue.toHolValue) fields =
              List.map (fun x => x) fields from by
            apply List.map_congr_left
            intro x hx
            exact ih x hx)
    | case3 name fields ih =>
        unfold PanValue.toHolValue HolValue.toPanValue
        rw [List.map_map]
        apply congrArg (PanValue.nStruct name)
        simpa using (show List.map ((fun pair : FieldName × HolValue width => (pair.1, pair.2.toPanValue)) ∘
                fun pair : FieldName × PanValue (BitVec width) => (pair.1, pair.2.toHolValue)) fields =
              List.map (fun x => x) fields from by
            apply List.map_congr_left
            intro pair hmem
            rw [Function.comp_apply, ih pair hmem])

  @[simp] theorem HolValue.toPanValue_toHolValue {width : Nat} (value : HolValue width) :
      value.toPanValue.toHolValue = value := by
    induction value using HolValue.toPanValue.induct with
    | case1 bits =>
        unfold HolValue.toPanValue PanValue.toHolValue
        rfl
    | case2 fields ih =>
        unfold HolValue.toPanValue PanValue.toHolValue
        rw [List.map_map]
        apply congrArg HolValue.rStruct
        simpa using (show List.map (PanValue.toHolValue ∘ HolValue.toPanValue) fields =
              List.map (fun x => x) fields from by
            apply List.map_congr_left
            intro x hx
            exact ih x hx)
    | case3 name fields ih =>
        unfold HolValue.toPanValue PanValue.toHolValue
        rw [List.map_map]
        apply congrArg (HolValue.nStruct name)
        simpa using (show List.map ((fun pair : FieldName × PanValue (BitVec width) => (pair.1, pair.2.toHolValue)) ∘
                fun pair : FieldName × HolValue width => (pair.1, pair.2.toPanValue)) fields =
              List.map (fun x => x) fields from by
            apply List.map_congr_left
            intro pair hmem
            rw [Function.comp_apply, ih pair hmem])
end

structure PanSemEvaluateState (α : Type u) (σ : Type v) where
  structs : StructContext
  /-- Compatibility function table. This list cannot stand in for the
      HOL-finite `PanSemState.code` map in a source Call/DecCall proof. -/
  functions : List (FunName × List VarName × Prog α)
  locals : VarName → Option (PanValue α)
  globals : VarName → Option (PanValue α)
  memory : α → Option (PanValue α)
  ffi : FfiState σ
  clock : Nat
  baseAddress : α
  topAddress : α
  bytesInWord : α
  memoryAccess : Option (PanValueMemoryAccess α) := none
  contracts : Option PanValueCallContracts := none
  memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none

/-! Source-faithful callers carry the Cake memory operations as a required
    field.  The legacy state remains optional for executable compatibility;
    this wrapper is the typed boundary used by exact evaluator proofs. -/
structure PanSemExactState (α : Type u) (σ : Type v) where
  legacy : PanSemEvaluateState α σ
  memoryAccess : PanValueMemoryAccess α

def PanSemExactState.toEvaluateState (state : PanSemExactState α σ) :
    PanSemEvaluateState α σ :=
  { state.legacy with memoryAccess := some state.memoryAccess }

/-- One source `panSem$state.code` entry: typed parameters, function body, and
    return shape. This full entry is kept separately from the legacy runtime
    state's function-name/parameter-name/body triples. -/
structure PanSemFunctionEntry (α : Type u) where
  params : List (VarName × Shape)
  body : Prog α
  returnShape : Shape

/-- State boundary for the source `evaluate_decls` definition. `runtime`
    carries the expression-evaluation fields and preserves all runtime state;
    `code` and `eshapes` model the source finite maps directly, and the
    required `memoryAccess` supplies the source memory-domain/byte behavior;
    declaration evaluation cannot fall back to the permissive legacy memory
    path. In particular, the lossy `runtime.functions` compatibility field is
    not used as `code`. -/
structure PanSemDeclarationState (α : Type u) (σ : Type v) where
  runtime : PanSemEvaluateState α σ
  code : InfoMap (PanSemFunctionEntry α)
  eshapes : InfoMap Shape
  memoryAccess : PanValueMemoryAccess α

mutual
  def panSemExpFuel : Exp α → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
    | .rStruct fields => 1 + panSemExpListFuel fields
    | .rField _ value | .nField _ value | .load32 value | .loadByte value =>
        1 + panSemExpFuel value
    | .nStruct _ fields => 1 + panSemFieldFuel fields
    | .load _ address => 1 + panSemExpFuel address
    | .op _ arguments | .panOp _ arguments => 1 + panSemExpListFuel arguments
    | .cmp _ left right | .shift _ left right =>
        1 + panSemExpFuel left + panSemExpFuel right

  def panSemExpListFuel : List (Exp α) → Nat
    | [] => 0
    | expression :: expressions =>
        panSemExpFuel expression + panSemExpListFuel expressions

  def panSemFieldFuel : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, expression) :: fields => panSemExpFuel expression + panSemFieldFuel fields

  def panSemCallInfoFuel :
      Option (Option (VarKind × VarName) ×
        Option (ExceptionId × VarName × Prog α)) → Nat
    | none => 0
    | some (_, none) => 0
    | some (_, some (_, _, handler)) => panSemProgFuel handler

  def panSemProgFuel : Prog α → Nat
    | .skip => 1
    | .dec _ _ value body => 1 + panSemExpFuel value + panSemProgFuel body
    | .assign _ _ value => 1 + panSemExpFuel value
    | .primitive _ _ arguments => 1 + panSemExpListFuel arguments
    | .store address value | .store32 address value | .storeByte address value =>
        1 + panSemExpFuel address + panSemExpFuel value
    | .seq first second => 1 + panSemProgFuel first + panSemProgFuel second
    | .ite condition thenBranch elseBranch =>
        1 + panSemExpFuel condition + panSemProgFuel thenBranch +
          panSemProgFuel elseBranch
    | .while condition body => 1 + panSemExpFuel condition + panSemProgFuel body
    | .break | .continue | .tick => 1
    | .call info _ arguments => 1 + panSemCallInfoFuel info + panSemExpListFuel arguments
    | .decCall _ _ _ arguments body =>
        1 + panSemExpListFuel arguments + panSemProgFuel body
    | .extCall _ configuration configurationLength array arrayLength =>
        1 + panSemExpFuel configuration + panSemExpFuel configurationLength +
          panSemExpFuel array + panSemExpFuel arrayLength
    | .raise _ value | .return value => 1 + panSemExpFuel value
    | .shMemLoad _ _ _ address => 1 + panSemExpFuel address
    | .shMemStore _ address value =>
        1 + panSemExpFuel address + panSemExpFuel value
    | .annot _ _ => 1

  def panSemFunctionFuel : List (FunName × List VarName × Prog α) → Nat
    | [] => 0
    | (_, _, body) :: functions =>
        max (panSemProgFuel body) (panSemFunctionFuel functions)
end

def panSemEvaluateFuel (state : PanSemEvaluateState α σ)
  (program : Prog α) : Nat :=
  state.clock + max (panSemProgFuel program) (panSemFunctionFuel state.functions) + 1

def panSemEvaluateWithFuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (fuel : Nat) (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  evalPanValueFfiClockProg context primitive handler state.structs state.functions
    state.baseAddress state.topAddress state.bytesInWord fuel state.locals state.globals
    state.memory state.ffi state.clock program
    (memoryAccess := state.memoryAccess) (contracts := state.contracts)
    (memoryHandler := state.memoryHandler)

def panSemEvaluate
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateWithFuel context primitive handler
    (panSemEvaluateFuel state program) state program

/-- Maximum structural evaluation cost of a body stored in the finite source
    code map. The evaluator's internal fuel is derived from the state-owned
    map, never from a detached function list. -/
def panSemCodeBodyFuel (code : PanSemCodeMap α) : Nat :=
  code.foldl (fun fuel binding => max fuel (panSemProgFuel binding.2.2.1)) 0

/-- Conservative structural bound for source-state evaluation. Every executed
    source call and every repeated while iteration consumes source clock, so at
    most `state.clock` such phases execute; each phase is bounded by the larger
    of the entry program and every state-owned function body. -/
def panSemCodeEvaluateFuel (state : PanSemState α ffi)
    (program : Prog α) : Nat :=
  (state.clock + 1) * (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) + 1

theorem panSemCodeEvaluateFuel_covers_clocked_bodies
    (state : PanSemState α ffi) (program : Prog α) :
    state.clock * panSemCodeBodyFuel state.code + panSemProgFuel program <
      panSemCodeEvaluateFuel state program := by
  unfold panSemCodeEvaluateFuel
  have hbody := Nat.le_max_right (panSemProgFuel program)
    (panSemCodeBodyFuel state.code)
  have hprogram := Nat.le_max_left (panSemProgFuel program)
    (panSemCodeBodyFuel state.code)
  calc
    state.clock * panSemCodeBodyFuel state.code + panSemProgFuel program ≤
        state.clock * max (panSemProgFuel program) (panSemCodeBodyFuel state.code) +
          max (panSemProgFuel program) (panSemCodeBodyFuel state.code) := by
      exact Nat.add_le_add (Nat.mul_le_mul_left _ hbody) hprogram
    _ < state.clock * max (panSemProgFuel program) (panSemCodeBodyFuel state.code) +
          state.clock + max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 2 := by
      omega
    _ = (state.clock + 1) *
          (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
      omega

/-! ### Canonical source fuel decomposition

HOL's `pc_compile_correct` Call/DecCall cases need the callee and handler
bodies to run at a fuel derived from the production canonical bound
`panSemCodeEvaluateFuel`, rather than taken as an external premise.  The
lemmas below record (a) that a stored body's structural fuel is bounded by the
state code body fuel, and (b) that the canonical fuel of a Call/DecCall
supplies at least the canonical fuel of the callee, handler and continuation
programs after the dispatch steps the call clauses consume. -/

/-- A `max`-fold never decreases its accumulator. -/
theorem le_foldl_max {β : Type u} (f : β → Nat) (entries : List β) (acc : Nat) :
    acc ≤ entries.foldl (fun acc entry => max acc (f entry)) acc := by
  induction entries generalizing acc with
  | nil => simp
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left acc (f entry)) (ih (max acc (f entry)))

/-- A `max`-fold over a list bounds the value of each member. -/
theorem mem_le_foldl_max {β : Type u} (f : β → Nat) {entries : List β} {entry : β}
    (hmem : entry ∈ entries) (acc : Nat) :
    f entry ≤ entries.foldl (fun acc item => max acc (f item)) acc := by
  induction entries generalizing acc with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons head rest ih =>
      simp only [List.foldl_cons, List.mem_cons] at hmem ⊢
      rcases hmem with heq | hmem
      · subst heq
        exact Nat.le_trans (Nat.le_max_right acc (f entry))
          (le_foldl_max f rest (max acc (f entry)))
      · exact ih hmem (max acc (f head))

/-- Every structural program cost is at least one. -/
theorem panSemProgFuel_pos (program : Prog α) : 1 ≤ panSemProgFuel program := by
  cases program <;> simp [panSemProgFuel] <;> omega

/-- A body stored in the state code map has structural fuel at most the code
    body fuel bound. -/
theorem panSemProgFuel_le_codeBodyFuel_of_mem
    (code : PanSemCodeMap α)
    {entry : FunName × (List (VarName × Shape) × Prog α × Shape)}
    (hmem : entry ∈ code) :
    panSemProgFuel entry.2.2.1 ≤ panSemCodeBodyFuel code := by
  simpa [panSemCodeBodyFuel] using
    mem_le_foldl_max (fun item => panSemProgFuel item.2.2.1) hmem 0

/-- Projection of the canonical fuel through a clock/locals update: only the
    clock field changes, the code field is preserved. -/
theorem panSemCodeEvaluateFuel_update
    (state : PanSemState α ffi) (clock : Nat)
    (locals : VarName → Option (PanValue α)) (program : Prog α) :
    panSemCodeEvaluateFuel { state with clock := clock, locals := locals } program =
      (clock + 1) * (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) + 1 :=
  rfl

/-- **Canonical fuel lower bound.**  When the source clock is positive, the
    canonical fuel of `program` supplies at least the canonical fuel of any
    sub-program whose structural fuel is bounded by `program`'s, after the two
    dispatch steps a source call consumes.  This is the lemma that lets the
    Pan-to-Crep Call/DecCall cases derive the callee, handler and continuation
    fuel instead of assuming `hsourceFuel`. -/
theorem panSemCodeEvaluateFuel_sub_le
    (state : PanSemState α ffi) (program sub : Prog α)
    (locals : VarName → Option (PanValue α))
    (hclock : state.clock ≠ 0)
    (hsub : panSemProgFuel sub ≤
      max (panSemProgFuel program) (panSemCodeBodyFuel state.code)) :
    panSemCodeEvaluateFuel
        { state with clock := decPanClock state.clock, locals := locals } sub
      ≤ panSemCodeEvaluateFuel state program - 2 := by
  rw [panSemCodeEvaluateFuel_update, panSemCodeEvaluateFuel, decPanClock]
  have hpos : 0 < state.clock := Nat.pos_of_ne_zero hclock
  have hsucc : state.clock - 1 + 1 = state.clock :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  rw [hsucc]
  have hM : max (panSemProgFuel sub) (panSemCodeBodyFuel state.code) ≤
      max (panSemProgFuel program) (panSemCodeBodyFuel state.code) :=
    Nat.max_le.2 ⟨hsub, Nat.le_max_right _ _⟩
  have h1 : state.clock *
        (max (panSemProgFuel sub) (panSemCodeBodyFuel state.code) + 1)
      ≤ state.clock *
        (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hM)
  have hMpos : 1 ≤ max (panSemProgFuel program) (panSemCodeBodyFuel state.code) :=
    Nat.le_trans (panSemProgFuel_pos program)
      (Nat.le_max_left (panSemProgFuel program) (panSemCodeBodyFuel state.code))
  have hexp : (state.clock + 1) *
        (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1)
      = state.clock *
          (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) +
        (max (panSemProgFuel program) (panSemCodeBodyFuel state.code) + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hexp]
  omega

/-- A callee body stored in the state code has canonical fuel within the
    canonical Call fuel after the two dispatch steps. -/
theorem panSemCodeEvaluateFuel_call_callee_le
    (state : PanSemState α ffi)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) (body : Prog α)
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (calleeLocals : VarName → Option (PanValue α))
    (hclock : state.clock ≠ 0)
    (hentry : (function, (parameters, body, returnShape)) ∈ state.code) :
    panSemCodeEvaluateFuel
        { state with clock := decPanClock state.clock, locals := calleeLocals } body
      ≤ panSemCodeEvaluateFuel state (.call info function arguments) - 2 := by
  refine panSemCodeEvaluateFuel_sub_le state (.call info function arguments) body
    calleeLocals hclock ?_
  exact Nat.le_trans (panSemProgFuel_le_codeBodyFuel_of_mem state.code hentry)
    (Nat.le_max_right _ _)

/-- A handler program carried in the call metadata has canonical fuel within
    the canonical Call fuel after the two dispatch steps. -/
theorem panSemCodeEvaluateFuel_call_handler_le
    (state : PanSemState α ffi)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) (handlerProgram : Prog α)
    (exceptionId handlerVariable : String)
    (handlerLocals : VarName → Option (PanValue α))
    (hclock : state.clock ≠ 0)
    (hinfo : info = some (none, some (exceptionId, handlerVariable, handlerProgram))) :
    panSemCodeEvaluateFuel
        { state with clock := decPanClock state.clock, locals := handlerLocals }
        handlerProgram
      ≤ panSemCodeEvaluateFuel state (.call info function arguments) - 2 := by
  refine panSemCodeEvaluateFuel_sub_le state (.call info function arguments)
    handlerProgram handlerLocals hclock ?_
  subst hinfo
  simp only [panSemProgFuel, panSemCallInfoFuel]
  omega

/-- **Call dispatch decomposition.**  At the production canonical fuel, the
    code evaluator dispatches a `Call` to the state-owned call clause at
    canonical fuel minus one, so the callee body runs at canonical fuel minus
    two (the `Call` case and the call helper each consume one step). -/
theorem panSemCodeEvaluateFuel_call_delegates
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state (.call info function arguments))
        state.locals state.globals state.memory state.ffi state.clock
        (.call info function arguments) memoryAccess contracts memoryHandler =
      evalPanValueFfiClockCodeCall context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state (.call info function arguments) - 1)
        state.locals state.globals state.memory state.ffi state.clock
        info function arguments memoryAccess contracts memoryHandler := by
  obtain ⟨k, hk⟩ : ∃ k,
      panSemCodeEvaluateFuel state (.call info function arguments) = k + 1 := by
    refine ⟨panSemCodeEvaluateFuel state (.call info function arguments) - 1, ?_⟩
    have hpos : 0 < panSemCodeEvaluateFuel state (.call info function arguments) := by
      simp only [panSemCodeEvaluateFuel]
      omega
    omega
  rw [hk]
  simp only [evalPanValueFfiClockCodeProg, Nat.add_sub_cancel]

/-- The production canonical fuel of a `Call` is at least two, so the two
    dispatch steps (the `Call` case and the state-owned call clause) always
    leave a nonnegative body budget. -/
theorem panSemCodeEvaluateFuel_call_two_le
    (state : PanSemState α ffi)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) :
    2 ≤ panSemCodeEvaluateFuel state (.call info function arguments) := by
  have hclock : 1 ≤ state.clock + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hbody : 1 ≤ max (panSemProgFuel (.call info function arguments))
      (panSemCodeBodyFuel state.code) + 1 :=
    Nat.succ_le_succ (Nat.zero_le _)
  have hmul := Nat.mul_le_mul hclock hbody
  simp only [panSemCodeEvaluateFuel]
  omega

/-- The state-owned call clause runs at canonical fuel minus one, which is one
    more than the body budget `canonical - 2`, so the callee and handler bodies
    recurse at exactly that budget. -/
theorem panSemCodeEvaluateFuel_call_sub_one_eq
    (state : PanSemState α ffi)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) :
    panSemCodeEvaluateFuel state (.call info function arguments) - 1 =
      (panSemCodeEvaluateFuel state (.call info function arguments) - 2) + 1 := by
  have htwo := panSemCodeEvaluateFuel_call_two_le state info function arguments
  omega

/-- Flapjack-specific `Call` branch decomposition at canonical fuel. The production
    code evaluator on a `Call` at canonical fuel equals the state-owned call
    clause evaluated at the syntactically-successor fuel `(canonical - 2) + 1`,
    which exposes the call clause's `fuel + 1` branch and hence the callee body
    recursion at exactly `canonical - 2`.  This turns the callee/handler body
    evaluation premises used by the Pan-to-Crep `Call` case into conclusions
    rather than assumptions. This has no HOL theorem original: HOL's evaluator
    does not use this Flapjack canonical-fuel function. -/
theorem panSemCodeEvaluateFuel_call_decomposition
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ))
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state (.call info function arguments))
        state.locals state.globals state.memory state.ffi state.clock
        (.call info function arguments) memoryAccess contracts memoryHandler =
      evalPanValueFfiClockCodeCall context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        ((panSemCodeEvaluateFuel state (.call info function arguments) - 2) + 1)
        state.locals state.globals state.memory state.ffi state.clock
        info function arguments memoryAccess contracts memoryHandler := by
  rw [panSemCodeEvaluateFuel_call_delegates,
    panSemCodeEvaluateFuel_call_sub_one_eq]

/-- **DecCall dispatch decomposition.** At production canonical fuel, a
    `DecCall` dispatches to its state-owned helper at canonical fuel minus one.
    That helper performs the state-owned code-map Call and continuation, with
    `preserveReturnLocals` enabled for the destination binding. -/
theorem panSemCodeEvaluateFuel_decCall_delegates
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (continuation : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state (.decCall name shape function arguments continuation))
        state.locals state.globals state.memory state.ffi state.clock
        (.decCall name shape function arguments continuation)
        memoryAccess contracts memoryHandler =
      evalPanValueFfiClockCodeDecCall context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state
          (.decCall name shape function arguments continuation) - 1)
        state.locals state.globals state.memory state.ffi state.clock
        name shape function arguments continuation memoryAccess contracts memoryHandler := by
  obtain ⟨k, hk⟩ : ∃ k,
      panSemCodeEvaluateFuel state
        (.decCall name shape function arguments continuation) = k + 1 := by
    refine ⟨panSemCodeEvaluateFuel state
      (.decCall name shape function arguments continuation) - 1, ?_⟩
    have hpos : 0 < panSemCodeEvaluateFuel state
        (.decCall name shape function arguments continuation) := by
      simp only [panSemCodeEvaluateFuel]
      omega
    omega
  rw [hk]
  simp only [evalPanValueFfiClockCodeProg, Nat.add_sub_cancel]

/-- The production canonical fuel of a `DecCall` is at least two, leaving a
    nonnegative body budget after the program and code-map dispatch steps. -/
theorem panSemCodeEvaluateFuel_decCall_two_le
    (state : PanSemState α ffi)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (continuation : Prog α) :
    2 ≤ panSemCodeEvaluateFuel state
      (.decCall name shape function arguments continuation) := by
  have hclock : 1 ≤ state.clock + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hbody : 1 ≤ max
      (panSemProgFuel (.decCall name shape function arguments continuation))
      (panSemCodeBodyFuel state.code) + 1 :=
    Nat.succ_le_succ (Nat.zero_le _)
  have hmul := Nat.mul_le_mul hclock hbody
  simp only [panSemCodeEvaluateFuel]
  omega

/-- The DecCall helper's canonical fuel is one more than the body/continuation
    budget `canonical - 2`. -/
theorem panSemCodeEvaluateFuel_decCall_sub_one_eq
    (state : PanSemState α ffi)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (continuation : Prog α) :
    panSemCodeEvaluateFuel state
        (.decCall name shape function arguments continuation) - 1 =
      (panSemCodeEvaluateFuel state
        (.decCall name shape function arguments continuation) - 2) + 1 := by
  have htwo := panSemCodeEvaluateFuel_decCall_two_le state name shape function
    arguments continuation
  omega

/-- Flapjack-specific `DecCall` branch decomposition: the production
    evaluator at canonical fuel dispatches to the state-owned DecCall helper at
    `(canonical - 2) + 1`, and preserves the callee locals needed by the
    continuation. This is a fuel-interface lemma, not a HOL theorem port. -/
theorem panSemCodeEvaluateFuel_decCall_decomposition
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (bytesInWord : α)
    (state : PanSemState α (FfiState σ))
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (continuation : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α))
    (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ)) :
    evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        (panSemCodeEvaluateFuel state (.decCall name shape function arguments continuation))
        state.locals state.globals state.memory state.ffi state.clock
        (.decCall name shape function arguments continuation)
        memoryAccess contracts memoryHandler =
      evalPanValueFfiClockCodeDecCall context primitive handler state.structs state.code
        state.exceptionShapes state.baseAddress state.topAddress bytesInWord
        ((panSemCodeEvaluateFuel state
          (.decCall name shape function arguments continuation) - 2) + 1)
        state.locals state.globals state.memory state.ffi state.clock
        name shape function arguments continuation memoryAccess contracts memoryHandler := by
  rw [panSemCodeEvaluateFuel_decCall_delegates,
    panSemCodeEvaluateFuel_decCall_sub_one_eq]

/-- A body stored under the called function in a `DecCall` has a canonical
    recursive fuel budget derived from the enclosing state and code map. -/
theorem panSemCodeEvaluateFuel_decCall_callee_le
    (state : PanSemState α ffi)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (continuation calleeBody : Prog α)
    (locals : VarName → Option (PanValue α))
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hclock : state.clock ≠ 0)
    (hentry : panSemCodeLookup state.code function =
      some (parameters, calleeBody, returnShape)) :
    panSemCodeEvaluateFuel
        { state with clock := decPanClock state.clock, locals := locals }
        calleeBody
      ≤ panSemCodeEvaluateFuel state
          (.decCall name shape function arguments continuation) - 2 := by
  have hclockPos : 0 < state.clock := Nat.pos_of_ne_zero hclock
  have hclockDec : decPanClock state.clock + 1 = state.clock := by
    simp [decPanClock, Nat.sub_add_cancel (Nat.succ_le_of_lt hclockPos)]
  have hentryMem : (function, (parameters, calleeBody, returnShape)) ∈ state.code :=
    panSemCodeLookup_mem_binding state.code function
      (parameters, calleeBody, returnShape) hentry
  have hbodyFuel : panSemProgFuel calleeBody ≤ panSemCodeBodyFuel state.code := by
    simpa using panSemProgFuel_le_codeBodyFuel_of_mem state.code hentryMem
  have hcalleeMax : max (panSemProgFuel calleeBody)
      (panSemCodeBodyFuel state.code) = panSemCodeBodyFuel state.code :=
    Nat.max_eq_right hbodyFuel
  have hparentMax : panSemCodeBodyFuel state.code ≤
      max (panSemProgFuel (.decCall name shape function arguments continuation))
        (panSemCodeBodyFuel state.code) := Nat.le_max_right _ _
  have hparentPos : 1 ≤ max
      (panSemProgFuel (.decCall name shape function arguments continuation))
      (panSemCodeBodyFuel state.code) :=
    Nat.le_trans (panSemProgFuel_pos _) (Nat.le_max_left _ _)
  rw [panSemCodeEvaluateFuel_update, panSemCodeEvaluateFuel_update,
    hclockDec, hcalleeMax]
  have hmul := Nat.mul_le_mul_left state.clock
    (Nat.succ_le_succ hparentMax)
  have htotal : state.clock * (panSemCodeBodyFuel state.code + 1) + 3 ≤
      (state.clock + 1) *
        (max (panSemProgFuel
          (.decCall name shape function arguments continuation))
          (panSemCodeBodyFuel state.code) + 1) + 1 := by
    have hslack : state.clock *
        (max (panSemProgFuel
          (.decCall name shape function arguments continuation))
          (panSemCodeBodyFuel state.code) + 1) + 3 ≤
        (state.clock + 1) *
          (max (panSemProgFuel
            (.decCall name shape function arguments continuation))
            (panSemCodeBodyFuel state.code) + 1) + 1 := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    calc
      state.clock * (panSemCodeBodyFuel state.code + 1) + 3 ≤
          state.clock *
            (max (panSemProgFuel
              (.decCall name shape function arguments continuation))
              (panSemCodeBodyFuel state.code) + 1) + 3 := by
                simpa [Nat.succ_eq_add_one] using Nat.add_le_add_right hmul 3
      _ ≤ (state.clock + 1) *
          (max (panSemProgFuel
            (.decCall name shape function arguments continuation))
            (panSemCodeBodyFuel state.code) + 1) + 1 := hslack
  have hminus : state.clock * (panSemCodeBodyFuel state.code + 1) + 1 + 2 ≤
      (state.clock + 1) *
        (max (panSemProgFuel
          (.decCall name shape function arguments continuation))
          (panSemCodeBodyFuel state.code) + 1) + 1 := by
    omega
  omega

/-- A continuation/body program of a `DecCall` has canonical fuel within the
    canonical DecCall fuel after the dispatch steps. -/
theorem panSemCodeEvaluateFuel_decCall_body_le
    (state : PanSemState α ffi)
    (name : VarName) (shape : Shape) (function : FunName)
    (arguments : List (Exp α)) (outerBody sub : Prog α)
    (subLocals : VarName → Option (PanValue α))
    (hclock : state.clock ≠ 0)
    (hsub : panSemProgFuel sub ≤
      max (panSemProgFuel (.decCall name shape function arguments outerBody))
        (panSemCodeBodyFuel state.code)) :
    panSemCodeEvaluateFuel
        { state with clock := decPanClock state.clock, locals := subLocals } sub
      ≤ panSemCodeEvaluateFuel state (.decCall name shape function arguments outerBody) - 1 := by
  -- one dispatch step only for the DecCall continuation
  rw [panSemCodeEvaluateFuel_update, panSemCodeEvaluateFuel, decPanClock]
  have hpos : 0 < state.clock := Nat.pos_of_ne_zero hclock
  have hsucc : state.clock - 1 + 1 = state.clock :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  rw [hsucc]
  have hM : max (panSemProgFuel sub) (panSemCodeBodyFuel state.code) ≤
      max (panSemProgFuel (.decCall name shape function arguments outerBody))
        (panSemCodeBodyFuel state.code) :=
    Nat.max_le.2 ⟨hsub, Nat.le_max_right _ _⟩
  have h1 : state.clock *
        (max (panSemProgFuel sub) (panSemCodeBodyFuel state.code) + 1)
      ≤ state.clock *
        (max (panSemProgFuel (.decCall name shape function arguments outerBody))
          (panSemCodeBodyFuel state.code) + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hM)
  have hMpos : 1 ≤
      max (panSemProgFuel (.decCall name shape function arguments outerBody))
        (panSemCodeBodyFuel state.code) :=
    Nat.le_trans (panSemProgFuel_pos (.decCall name shape function arguments outerBody))
      (Nat.le_max_left (panSemProgFuel (.decCall name shape function arguments outerBody))
        (panSemCodeBodyFuel state.code))
  have hexp : (state.clock + 1) *
        (max (panSemProgFuel (.decCall name shape function arguments outerBody))
          (panSemCodeBodyFuel state.code) + 1)
      = state.clock *
          (max (panSemProgFuel (.decCall name shape function arguments outerBody))
            (panSemCodeBodyFuel state.code) + 1) +
        (max (panSemProgFuel (.decCall name shape function arguments outerBody))
          (panSemCodeBodyFuel state.code) + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hexp]
  omega

/-- Clocked production evaluator whose recursive Call and DecCall clauses read
    each callee from `state.code`. The compatibility function list is empty;
    code lookup and the fuel bound both remain tied to the source state. -/
def panSemEvaluateCodeStateWithFuel
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat)
    (state : PanSemState α (FfiState σ)) (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
    state.exceptionShapes
    state.baseAddress state.topAddress bytesInWord fuel state.locals state.globals
    state.memory state.ffi state.clock program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

/-- Production source-state entry point with a finite-map-derived fuel bound. -/
def panSemEvaluateCodeState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord
    (panSemCodeEvaluateFuel state program) state program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)

/-- Evaluate a production source state using Cake's `memaddrs`,
    `sh_memaddrs`, and `be` fields. The supplied word model describes the
    source word operations; every memory domain and endianness input is
    derived from `state`, while `bytesInWord` is source word-type metadata.
    This boundary must be used for HOL-facing proofs instead of the optional
    no-access compatibility path or a width read from the target state. -/
def panSemEvaluateCodeStateWithMemoryModel
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3]
    [Add α] [Mul α] [Sub α] [AndOp α] [OrOp α] [HXor α α α]
    [ShiftLeft α] [ShiftRight α] [LT α]
    [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (model : PanMemoryModel α) (bytesInWord : α)
    (state : PanSemState α (FfiState σ)) (program : Prog α)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluateCodeState context primitive handler bytesInWord state program
    (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
      state.sharedMemaddrs state.be))
    (contracts := contracts) (memoryHandler := memoryHandler)

/-- Materialise the observable post-state of code-map evaluation. The source
    semantics never updates `state.code`; it is carried verbatim while the
    evaluator updates locals, globals, memory, FFI state, and clock. -/
def panSemCodeStateAfter (state : PanSemState α (FfiState σ))
    (result : PanValueFfiClockResult α σ) : PanSemState α (FfiState σ) :=
  let update (locals globals : VarName → Option (PanValue α))
      (memory : α → Option (PanValue α)) (ffi : FfiState σ) (clock : Nat) :=
    { state with
      locals := locals
      globals := globals
      memory := memory
      ffi := ffi
      clock := clock }
  match result with
  | (.timeout locals globals memory ffi, clock) => update locals globals memory ffi clock
  | (.control control, clock) =>
      match control with
      | .normal locals globals memory ffi
      | .error locals globals memory ffi
      | .returned locals globals memory ffi _
      | .raised locals globals memory ffi _ _
      | .broke locals globals memory ffi
      | .continued locals globals memory ffi
      | .finalFfi locals globals memory ffi _ => update locals globals memory ffi clock

theorem panSemCodeStateAfter_preserves_code
    (state : PanSemState α (FfiState σ)) (result : PanValueFfiClockResult α σ) :
    (panSemCodeStateAfter state result).code = state.code := by
  cases result with
  | mk outcome clock =>
    cases outcome with
    | timeout _ _ _ _ => rfl
    | control control => cases control <;> rfl

/-- Source-state entry point paired with its post-state projection. -/
def panSemEvaluateCodeStateWithPostState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    Option (PanValueFfiClockResult α σ × PanSemState α (FfiState σ)) := do
  let result ← panSemEvaluateCodeState context primitive handler bytesInWord state program
    (memoryAccess := memoryAccess) (contracts := contracts)
    (memoryHandler := memoryHandler)
  pure (result, panSemCodeStateAfter state result)

theorem panSemEvaluateCodeStateWithPostState_eq_map
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) =
      (panSemEvaluateCodeState context primitive handler bytesInWord state program
      (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler)).map
      (fun result => (result, panSemCodeStateAfter state result)) := by
  cases hresult : panSemEvaluateCodeState context primitive handler bytesInWord state
      program (memoryAccess := memoryAccess) (contracts := contracts)
      (memoryHandler := memoryHandler) <;>
    simp [panSemEvaluateCodeStateWithPostState, hresult]

/-- Recursive source-state evaluation leaves the finite, state-owned
    `PanSemState.code` map unchanged. Call and DecCall resolve every callee from
    this map, so this post-state invariant is available to the corresponding
    compiler-correctness cases. -/
theorem panSemEvaluateCodeStateWithPostState_preserves_code
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ))
    (program : Prog α)
    (result : PanValueFfiClockResult α σ)
    (postState : PanSemState α (FfiState σ))
    (heval : panSemEvaluateCodeStateWithPostState context primitive handler
      bytesInWord state program = some (result, postState)) :
    postState.code = state.code := by
  unfold panSemEvaluateCodeStateWithPostState at heval
  cases hresult : panSemEvaluateCodeState context primitive handler bytesInWord
      state program with
  | none => simp [hresult] at heval
  | some evaluated =>
      simp [hresult] at heval
      rcases heval with ⟨rfl, rfl⟩
      exact panSemCodeStateAfter_preserves_code state evaluated

/-! Production-evaluator counterpart of the HOL `evaluate_def` Tick equation
    (`cakeml/pancake/semantics/panSemScript.sml:683-685`) over the production
    source-state evaluator: at clock zero the result is `TimeOut` with cleared
    locals, otherwise `NONE` with the clock decremented and every other state
    component preserved. This is an untagged boundary equation because the
    structured result is reduced rather than HOL's `(prog_result, state)` pair. -/
theorem panSemEvaluateCodeStateWithPostState_tick
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.tick : Prog α) =
      if state.clock = 0 then
        some ((.timeout (fun _ => none) state.globals state.memory state.ffi, 0),
          { state with locals := fun _ => none })
      else
        some ((.control (.normal state.locals state.globals state.memory state.ffi),
            state.clock - 1),
          { state with clock := state.clock - 1 }) := by
  by_cases hclock : state.clock = 0 <;>
    simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
      panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
      panValueFfiClockTimeout, evalPanValueFfiClockCodeProg, hclock]

/-! Production-evaluator counterpart of the HOL `evaluate_def` Skip equation
    (`cakeml/pancake/semantics/panSemScript.sml:557`) over the production
    source-state evaluator: `Skip` yields the normal control result with the
    state (including the clock) carried verbatim. This is an untagged boundary
    equation because the structured result is reduced rather than HOL's
    `(prog_result, state)` pair. -/
theorem panSemEvaluateCodeStateWithPostState_skip
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (state : PanSemState α (FfiState σ)) :
    panSemEvaluateCodeStateWithPostState context primitive handler bytesInWord state
        (.skip : Prog α) =
      some ((.control (.normal state.locals state.globals state.memory state.ffi),
          state.clock), state) := by
  simp [panSemEvaluateCodeStateWithPostState, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemCodeStateAfter,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps]

/-! Exact HOL `evaluate_def` Assign equation
    (`cakeml/pancake/semantics/panSemScript.sml:566-572`) over the production
    source-state evaluator: the source expression is evaluated, the assignment
    is accepted exactly when `is_valid_value` holds, and the accepted value is
    written to the local or global map with the clock and every other state
    component carried verbatim. When the source expression does not evaluate or
    `is_valid_value` rejects the value, the result is an explicit `.error`
    control result with the unchanged state, matching HOL's `(SOME Error, s)`
    (distinct from Lean `none`, which now denotes a missing evaluation result).
    This is an untagged boundary equation because
    the structured result is reduced rather than HOL's `(prog_result, state)`
    pair. -/
theorem panSemEvaluateCodeStateWithFuel_assign
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (vk : VarKind) (name : VarName) (value : Exp α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.assign vk name value : Prog α) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value with
      | some evaluated =>
          if panValueAssignmentValid state.structs state.locals state.globals vk name evaluated then
            match vk with
            | .local =>
                some ((.control (.normal (updatePanValueMap state.locals name evaluated)
                    state.globals state.memory state.ffi), state.clock))
            | .global =>
                some ((.control (.normal state.locals
                    (updatePanValueMap state.globals name evaluated)
                    state.memory state.ffi), state.clock))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord value with
  | none =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue]
  | some evaluated =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue] <;>
      split <;> simp

/-- Production source-state `Assign` equation with an explicit memory access.

    The executed `Assign` leaves thread the caller's `memoryAccess` into the
    source-expression evaluation (`panValueAssignLocalResult` and
    `panValueAssignGlobalResult` both take it), so this equation is stated over
    the same access the evaluator receives.  For a memory-reading source
    (`Load`/`Load32`/`LoadByte`) this is the faithful path: the source state's
    `memaddrs`, `sharedMemaddrs`, and `be` drive the read, and a read outside
    the domain yields HOL's `(SOME Error, s)` carrying the unchanged state.
    Untagged boundary equation because the structured result is reduced rather
    than HOL's `(prog_result, state)` pair.  Reference:
    cakeml/pancake/semantics/panSemScript.sml:566-572 (`Assign`). -/
theorem panSemEvaluateCodeStateWithFuel_assign_withAccess
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (vk : VarKind) (name : VarName) (value : Exp α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.assign vk name value : Prog α)
        (memoryAccess := memoryAccess) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value
          (memoryAccess := memoryAccess) with
      | some evaluated =>
          if panValueAssignmentValid state.structs state.locals state.globals vk name evaluated then
            match vk with
            | .local =>
                some ((.control (.normal (updatePanValueMap state.locals name evaluated)
                    state.globals state.memory state.ffi), state.clock))
            | .global =>
                some ((.control (.normal state.locals
                    (updatePanValueMap state.globals name evaluated)
                    state.memory state.ffi), state.clock))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord value
      (memoryAccess := memoryAccess) with
  | none =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue]
  | some evaluated =>
      cases vk <;>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueAssignLocalResult,
        panValueAssignGlobalResult, evalPanValueExpCounted, hvalue] <;>
      split <;> simp

/-- The `Assign` equation instantiated with the state-derived memory access: the
    source reads memory through `state.memaddrs`, `state.sharedMemaddrs`, and
    `state.be` via the word model, matching the state-owned
    `panSemEvaluateCodeStateWithMemoryModel` entry point.  Untagged boundary
    equation for the same reason as
    `panSemEvaluateCodeStateWithFuel_assign_withAccess`. -/
theorem panSemEvaluateCodeStateWithFuel_assign_state_memory
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (model : PanMemoryModel α) (bytesInWord : α) (fuel : Nat)
    (state : PanSemState α (FfiState σ))
    (vk : VarKind) (name : VarName) (value : Exp α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.assign vk name value : Prog α)
        (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
          state.sharedMemaddrs state.be)) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value
          (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
            state.sharedMemaddrs state.be)) with
      | some evaluated =>
          if panValueAssignmentValid state.structs state.locals state.globals vk name evaluated then
            match vk with
            | .local =>
                some ((.control (.normal (updatePanValueMap state.locals name evaluated)
                    state.globals state.memory state.ffi), state.clock))
            | .global =>
                some ((.control (.normal state.locals
                    (updatePanValueMap state.globals name evaluated)
                    state.memory state.ffi), state.clock))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) :=
  panSemEvaluateCodeStateWithFuel_assign_withAccess context primitive handler bytesInWord
    fuel state vk name value (some (panValueMemoryAccessOfModel model state.memaddrs
      state.sharedMemaddrs state.be))

/-- Production source-state `Dec` equation. When the initialiser evaluates to a
    value whose shape matches the declared shape, the body runs with the
    declaration bound in the local map and, on completion, the declared local is
    restored to its previous binding; a shape mismatch or a failing initialiser
    yields an explicit `Error` control result carrying the unchanged state
    (`panSem`'s `(SOME Error, s)`), distinct from a missing `none` evaluation
    result. The equation is stated over the explicit-fuel evaluator
    because the recursive body call reuses the predecessor fuel, so it cannot be
    phrased against the finite-map-derived entry point. This is an untagged
    boundary equation because the structured result is reduced rather than HOL's
    `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:558-565 (`Dec`). -/
theorem panSemEvaluateCodeStateWithFuel_dec
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.dec name shape value body : Prog α) =
      match evalPanValueExp state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord value with
      | some evaluated =>
          if panShapeMatches (panValueShape state.structs evaluated) shape then
            (panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
                { state with
                  locals := updatePanValueMap state.locals name evaluated } body).map
              (fun result =>
                (panValueFfiClockRestoreLocal name (state.locals name) result.1, result.2))
          else
            some ((.control (.error state.locals state.globals state.memory state.ffi),
              state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalue : evalPanValueExp state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord value with
  | none =>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        panValueDecAcceptedValue, hvalue]
  | some evaluated =>
      by_cases hshape : panShapeMatches (panValueShape state.structs evaluated) shape = true
      · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
          panValueDecAcceptedValue, hvalue, hshape, Option.map_eq_bind]
        rfl
      · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
          panValueDecAcceptedValue, hvalue, hshape]

/-- Production source-state `Primitive` equation. The argument expressions are
    evaluated together; when they all succeed the primitive handler is applied
    and, if the produced value has the same shape as the destination local's
    current binding, that local is updated; any failure yields an explicit
    `Error` control result carrying the unchanged state (`panSem`'s
    `(SOME Error, s)`), distinct from a missing `none` evaluation result. This is
    an untagged boundary equation because the structured result is reduced
    rather than HOL's `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:573-582 (`Primitive`). -/
theorem panSemEvaluateCodeStateWithFuel_primitive
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α)) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.primitive name operator arguments : Prog α) =
      match evalPanValueExps state.structs state.locals state.globals state.memory
          state.baseAddress state.topAddress bytesInWord arguments with
      | some values =>
          match primitive operator values with
          | some evaluated =>
              match state.locals name with
              | some oldValue =>
                  if panShapeMatches (panValueShape state.structs evaluated)
                      (panValueShape state.structs oldValue) then
                    some ((.control (.normal
                        (updatePanValueMap state.locals name evaluated)
                        state.globals state.memory state.ffi), state.clock))
                  else
                    some ((.control (.error state.locals state.globals state.memory state.ffi),
                      state.clock))
              | none =>
                  some ((.control (.error state.locals state.globals state.memory state.ffi),
                    state.clock))
          | none =>
              some ((.control (.error state.locals state.globals state.memory state.ffi),
                state.clock))
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock)) := by
  cases hvalues : evalPanValueExps state.structs state.locals state.globals state.memory
      state.baseAddress state.topAddress bytesInWord arguments with
  | none =>
      simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
        evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
        evalPanValueExpsCounted, hvalues]
  | some values =>
      cases hprim : primitive operator values with
      | none =>
          simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
            evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
            evalPanValueExpsCounted, hvalues, hprim]
      | some evaluated =>
          cases hlocal : state.locals name with
          | none =>
              simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                evalPanValueExpsCounted, hvalues, hprim, hlocal]
          | some oldValue =>
              by_cases hshape : panShapeMatches (panValueShape state.structs evaluated)
                  (panValueShape state.structs oldValue) = true
              · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                  evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                  evalPanValueExpsCounted, hvalues, hprim, hlocal, hshape]
              · simp [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg,
                  evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
                  evalPanValueExpsCounted, hvalues, hprim, hlocal, hshape]
/-- Production source-state `Seq` equation. The first command is evaluated and
    its clock clamped to the entry clock (`fix_clock`); a normal (`NONE`)
    outcome continues with the second command in the resulting state, while any
    other outcome (including an explicit `Error`) is returned unchanged. This is
    an untagged boundary equation because the structured result is reduced
    rather than HOL's `(prog_result, state)` pair. Reference:
    cakeml/pancake/semantics/panSemScript.sml:615-618 (`Seq`). -/
theorem panSemEvaluateCodeStateWithFuel_seq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (first second : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.seq first second : Prog α) =
      match panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
          state first with
      | some firstStep =>
          let fixedStep := fixPanClock state.clock firstStep
          match fixedStep.1 with
          | .control (.normal nextLocals nextGlobals nextMemory nextFfi) =>
              panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel
                { state with
                  locals := nextLocals
                  globals := nextGlobals
                  memory := nextMemory
                  ffi := nextFfi
                  clock := fixedStep.2 } second
          | _ => some fixedStep
      | none => none := by
  simp only [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg, fixPanClock]
  cases h : evalPanValueFfiClockCodeProg context primitive handler state.structs state.code
      state.exceptionShapes state.baseAddress state.topAddress bytesInWord fuel state.locals
      state.globals state.memory state.ffi state.clock first with
  | none => simp
  | some firstStep => rfl

/-- The production source evaluator exposes the `panSem` `If` equation: a
    non-word (or missing) condition yields the explicit `Error` result with the
    unchanged source state, while a word condition evaluates the selected
    branch at the unchanged clock.  The result is the reduced structured pair,
    not HOL's `(prog_result, state)`, so this stays an untagged boundary
    equation.  The condition is evaluated with the caller's `memoryAccess`
    (which the state-owned entry derives from `state.memaddrs`, `state.be`, and
    the word model), so memory-reading conditions do not fall back to the
    legacy whole-cell path.  Reference:
    `cakeml/pancake/semantics/panSemScript.sml:617-620`. -/
theorem panSemEvaluateCodeStateWithFuel_ite
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (bytesInWord : α) (fuel : Nat) (state : PanSemState α (FfiState σ))
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (memoryAccess : Option (PanValueMemoryAccess α) := none)
    (contracts : Option PanValueCallContracts := none)
    (memoryHandler : Option (PanValueMemoryFfiHandler α σ) := none) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.ite condition thenBranch elseBranch : Prog α)
        (memoryAccess := memoryAccess) (contracts := contracts)
        (memoryHandler := memoryHandler) =
      match panValueIteConditionValue state.structs state.baseAddress state.topAddress
          bytesInWord state.locals state.globals state.memory condition memoryAccess with
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock))
      | some conditionValue =>
          panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel state
            (if conditionValue != 0 then thenBranch else elseBranch)
            (memoryAccess := memoryAccess) (contracts := contracts)
            (memoryHandler := memoryHandler) := by
  simp only [panSemEvaluateCodeStateWithFuel, evalPanValueFfiClockCodeProg]
  cases h : panValueIteConditionValue state.structs state.baseAddress state.topAddress
      bytesInWord state.locals state.globals state.memory condition memoryAccess with
  | none => rfl
  | some conditionValue => rfl

/-- The `If` equation instantiated with the
    state-derived memory access: the condition reads memory through
    `state.memaddrs`, `state.sharedMemaddrs`, and `state.be` (via the word
    model), matching the state-owned `panSemEvaluateCodeStateWithMemoryModel`
    entry point.  Untagged boundary equation for the same reason as
    `panSemEvaluateCodeStateWithFuel_ite`. -/
theorem panSemEvaluateCodeStateWithFuel_ite_state_memory
    [BEq α] [OfNat α 0] [OfNat α 1] [OfNat α 2] [OfNat α 3] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (model : PanMemoryModel α) (bytesInWord : α) (fuel : Nat)
    (state : PanSemState α (FfiState σ))
    (condition : Exp α) (thenBranch elseBranch : Prog α) :
    panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord (fuel + 1)
        state (.ite condition thenBranch elseBranch : Prog α)
        (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
          state.sharedMemaddrs state.be)) =
      match panValueIteConditionValue state.structs state.baseAddress state.topAddress
          bytesInWord state.locals state.globals state.memory condition
          (some (panValueMemoryAccessOfModel model state.memaddrs
            state.sharedMemaddrs state.be)) with
      | none =>
          some ((.control (.error state.locals state.globals state.memory state.ffi),
            state.clock))
      | some conditionValue =>
          panSemEvaluateCodeStateWithFuel context primitive handler bytesInWord fuel state
            (if conditionValue != 0 then thenBranch else elseBranch)
            (memoryAccess := some (panValueMemoryAccessOfModel model state.memaddrs
              state.sharedMemaddrs state.be)) :=
  panSemEvaluateCodeStateWithFuel_ite context primitive handler bytesInWord fuel state
    condition thenBranch elseBranch (some (panValueMemoryAccessOfModel model state.memaddrs
      state.sharedMemaddrs state.be))

/-!
  Exact source-memory entry point.

  CakeML's `panSem$evaluate` receives `memaddrs`, `be`, and the word-memory
  operations through its state.  The structured compatibility API keeps an
  optional access field for older callers, but this entry point requires the
  access record explicitly so `Load32`/`LoadByte` cannot silently fall back to
  whole-cell reads.
-/
def panSemEvaluateExact
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (memoryAccess : PanValueMemoryAccess α)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluate context primitive handler
    { state with memoryAccess := some memoryAccess } program

/-! The exact source entrypoint is a state boundary, not a second evaluator:
    it installs the explicit Cake memory operations before evaluating.  Keeping
    this equation named makes exact correctness proofs unable to silently
    select the legacy no-access compatibility path. -/
theorem panSemEvaluateExact_uses_memory_access
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (memoryAccess : PanValueMemoryAccess α)
    (state : PanSemEvaluateState α σ) (program : Prog α) :
    panSemEvaluateExact context primitive handler memoryAccess state program =
      panSemEvaluate context primitive handler
        { state with memoryAccess := some memoryAccess } program := by
  rfl

def panSemEvaluateExactState
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ) (program : Prog α) :
    Option (PanValueFfiClockResult α σ) :=
  panSemEvaluate context primitive handler state.toEvaluateState program

theorem panSemEvaluateExactState_eq
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ) (program : Prog α) :
    panSemEvaluateExactState context primitive handler state program =
      panSemEvaluate context primitive handler state.toEvaluateState program := by
  rfl

/-! A generic source `Raise` equation for the exact state boundary.  The
    evaluator and payload-validity premises remain explicit so this theorem
    does not silently discharge arbitrary exception contracts. -/
theorem panSemEvaluateExactState_raise_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (exception : ExceptionId) (expression : Exp α) (value : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = some value)
    (hvalid : panValueExceptionValid state.legacy.structs
      state.legacy.contracts exception value = true)
    (hlimit : panValuePayloadWithinLimit state.legacy.structs value = true) :
    panSemEvaluateExactState context primitive handler state
        (.raise exception expression) =
      some (.control (.raised (fun _ => none) state.legacy.globals
        state.legacy.memory state.legacy.ffi exception value), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueRaiseResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval, hvalid, hlimit]

/-! Exact source `Return` equation (success case), mirroring the `Raise`
    equation above: the payload is evaluated through the state's required
    memory access and accepted when it fits the 32-word limit. -/
theorem panSemEvaluateExactState_return_of_eval
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (expression : Exp α) (value : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = some value)
    (hlimit : panValuePayloadWithinLimit state.legacy.structs value = true) :
    panSemEvaluateExactState context primitive handler state
        (.return expression) =
      some (.control (.returned (fun _ => none) state.legacy.globals
        state.legacy.memory state.legacy.ffi [value]), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueReturnResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval, hlimit]

/-! Exact source `Return` Error paths: an expression that fails to evaluate and
    a payload that exceeds the 32-word limit both yield `SOME Error` with the
    full unchanged state (HOL `panSemScript.sml:633-640`). -/
theorem panSemEvaluateExactState_return_error_of_eval_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (expression : Exp α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.return expression) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueReturnResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval]

theorem panSemEvaluateExactState_return_error_of_oversized
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (expression : Exp α) (value : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = some value)
    (hlimit : panValuePayloadWithinLimit state.legacy.structs value = false) :
    panSemEvaluateExactState context primitive handler state
        (.return expression) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueReturnResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval, hlimit]

/-! Exact source `Raise` Error paths: an expression that fails to evaluate and
    a payload that fails the exception-shape or size check both yield
    `SOME Error` with the full unchanged state (HOL `panSemScript.sml:641-650`). -/
theorem panSemEvaluateExactState_raise_error_of_eval_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (exception : ExceptionId) (expression : Exp α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.raise exception expression) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueRaiseResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval]

theorem panSemEvaluateExactState_raise_error_of_invalid
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (exception : ExceptionId) (expression : Exp α) (value : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord expression
      (memoryAccess := some state.memoryAccess) = some value)
    (hinvalid : (panValueExceptionValid state.legacy.structs
        state.legacy.contracts exception value &&
        panValuePayloadWithinLimit state.legacy.structs value) = false) :
    panSemEvaluateExactState context primitive handler state
        (.raise exception expression) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockLeaf, evalPanValueFfiClockProg,
    evalPanValueFfiProgSteps, panValueRaiseResult, evalPanValueExpCounted,
    PanSemExactState.toEvaluateState, heval, hinvalid]

/-! Exact source `Call` error equations.  HOL evaluates `OPT_MMAP (eval s)
    argexps` before looking up the callee, and rejects the call with
    `(SOME Error, s)` with the unchanged caller state when an argument fails or
    when the callee is not found.  These equations run the state-derived memory
    access, so a memory-reading argument is gated by the source `memaddrs`; no
    legacy whole-cell fallback is used. -/
theorem panSemEvaluateExactState_call_error_of_arguments_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.call info function arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  have hle : 1 ≤ max (panSemProgFuel (Prog.call info function arguments))
      (panSemFunctionFuel state.legacy.functions) := by
    rw [panSemProgFuel]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k, state.legacy.clock +
      max (panSemProgFuel (Prog.call info function arguments))
        (panSemFunctionFuel state.legacy.functions) = k + 1 := by
    cases h : state.legacy.clock +
        max (panSemProgFuel (Prog.call info function arguments))
          (panSemFunctionFuel state.legacy.functions) with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  rw [hk]
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, harguments]

theorem panSemEvaluateExactState_call_error_of_target_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) ×
      Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α)) (values : List (PanValue α))
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = some values)
    (htarget : panValueCallTarget state.legacy.structs state.legacy.contracts
      function state.legacy.functions values = none) :
    panSemEvaluateExactState context primitive handler state
        (.call info function arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  have hle : 1 ≤ max (panSemProgFuel (Prog.call info function arguments))
      (panSemFunctionFuel state.legacy.functions) := by
    rw [panSemProgFuel]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k, state.legacy.clock +
      max (panSemProgFuel (Prog.call info function arguments))
        (panSemFunctionFuel state.legacy.functions) = k + 1 := by
    cases h : state.legacy.clock +
        max (panSemProgFuel (Prog.call info function arguments))
          (panSemFunctionFuel state.legacy.functions) with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  rw [hk]
  simp [evalPanValueFfiClockCall, panValueCallArgumentsValue, harguments, htarget]

/-- HOL `lookup_code` (`panSemScript.sml:458-467`) rejects a callee whose
    argument shapes or parameter-name distinctness fail, and the `Call` case
    (`:657-662`) then returns `(SOME Error, s)` with the caller state unchanged.
    This is the parameter-validity failure branch, stated over the exact source
    state with the caller's full-state memory access. Untagged: the executed
    result is the reduced structured pair, not HOL's literal `result option`
    pairing. -/
theorem panSemEvaluateExactState_call_error_of_parameters_invalid
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α))
    (harguments :
      evalPanValueExps state.legacy.structs state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord arguments (memoryAccess := some state.memoryAccess) =
        some values)
    (hlookup : lookupPanFunction function state.legacy.functions = some (parameters, body))
    (hinvalid :
      panValueParametersValid state.legacy.structs state.legacy.contracts function values =
        false) :
    panSemEvaluateExactState context primitive handler state (.call info function arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals state.legacy.memory
        state.legacy.ffi), state.legacy.clock) := by
  refine panSemEvaluateExactState_call_error_of_target_none context primitive handler state
    info function arguments (values := values) harguments ?_
  simp [panValueCallTarget, hlookup, hinvalid]

/-- HOL `evaluate (Call ...)` maps a callee that falls through (`NONE`) to
    `(SOME Error, st)` (`panSemScript.sml:668`), preserving the callee's
    post-call locals, globals, memory, FFI state and clock. This is that
    rejection branch over the exact source state, with the caller's full-state
    memory access threaded into argument evaluation. Untagged: the executed
    result is the reduced structured pair, not HOL's literal `result option`
    pairing. -/
theorem panSemEvaluateExactState_call_error_of_callee_normal
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName) (body : Prog α)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (finalClock fuel : Nat)
    (harguments :
      evalPanValueExps state.legacy.structs state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord arguments (memoryAccess := some state.memoryAccess) =
        some values)
    (hlookup : lookupPanFunction function state.legacy.functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters :
      panValueParametersValid state.legacy.structs state.legacy.contracts function values =
        true)
    (hclock : state.legacy.clock ≠ 0)
    (hfuel :
      state.legacy.clock +
          max (panSemProgFuel (Prog.call info function arguments))
            (panSemFunctionFuel state.legacy.functions) = fuel + 1)
    (hbody :
      evalPanValueFfiClockProg context primitive handler state.legacy.structs
        state.legacy.functions state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord fuel calleeLocals state.legacy.globals
        state.legacy.memory state.legacy.ffi (state.legacy.clock - 1) body
        (memoryAccess := some state.memoryAccess) (contracts := state.legacy.contracts)
        (memoryHandler := state.legacy.memoryHandler) =
        some (.control (.normal bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    panSemEvaluateExactState context primitive handler state (.call info function arguments) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  rw [hfuel]
  exact evalPanValueFfiClockCall_callee_normal_error context primitive handler
    state.legacy.structs state.legacy.functions state.legacy.baseAddress
    state.legacy.topAddress state.legacy.bytesInWord fuel state.legacy.locals
    state.legacy.globals state.legacy.memory state.legacy.ffi state.legacy.clock
    info function arguments values parameters calleeLocals bodyLocals finalGlobals
    finalMemory finalFfi body finalClock (memoryAccess := some state.memoryAccess)
    (contracts := state.legacy.contracts) (memoryHandler := state.legacy.memoryHandler)
    harguments hlookup hbind hparameters hclock hbody

/-- Flapjack's exact-state Call equation for a callee Break: the Error result
    retains the callee's final locals, globals, memory, FFI state, and clock.
    Untagged because Lean's structured result is not HOL's literal
    `result option × state` pair. -/
theorem panSemEvaluateExactState_call_error_of_callee_broke
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName) (body : Prog α)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (finalClock fuel : Nat)
    (harguments :
      evalPanValueExps state.legacy.structs state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord arguments (memoryAccess := some state.memoryAccess) =
        some values)
    (hlookup : lookupPanFunction function state.legacy.functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters :
      panValueParametersValid state.legacy.structs state.legacy.contracts function values =
        true)
    (hclock : state.legacy.clock ≠ 0)
    (hfuel :
      state.legacy.clock +
          max (panSemProgFuel (Prog.call info function arguments))
            (panSemFunctionFuel state.legacy.functions) = fuel + 1)
    (hbody :
      evalPanValueFfiClockProg context primitive handler state.legacy.structs
        state.legacy.functions state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord fuel calleeLocals state.legacy.globals
        state.legacy.memory state.legacy.ffi (state.legacy.clock - 1) body
        (memoryAccess := some state.memoryAccess) (contracts := state.legacy.contracts)
        (memoryHandler := state.legacy.memoryHandler) =
        some (.control (.broke bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    panSemEvaluateExactState context primitive handler state (.call info function arguments) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  rw [hfuel]
  exact evalPanValueFfiClockCall_callee_broke_error context primitive handler
    state.legacy.structs state.legacy.functions state.legacy.baseAddress
    state.legacy.topAddress state.legacy.bytesInWord fuel state.legacy.locals
    state.legacy.globals state.legacy.memory state.legacy.ffi state.legacy.clock
    info function arguments values parameters calleeLocals bodyLocals finalGlobals
    finalMemory finalFfi body finalClock (memoryAccess := some state.memoryAccess)
    (contracts := state.legacy.contracts) (memoryHandler := state.legacy.memoryHandler)
    harguments hlookup hbind hparameters hclock hbody

/-- Flapjack's exact-state Call equation for a callee Continue, preserving the
    callee's final state in the resulting Error. Untagged because Lean's
    structured result is not HOL's literal `result option × state` pair. -/
theorem panSemEvaluateExactState_call_error_of_callee_continued
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName) (body : Prog α)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (finalClock fuel : Nat)
    (harguments :
      evalPanValueExps state.legacy.structs state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord arguments (memoryAccess := some state.memoryAccess) =
        some values)
    (hlookup : lookupPanFunction function state.legacy.functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters :
      panValueParametersValid state.legacy.structs state.legacy.contracts function values =
        true)
    (hclock : state.legacy.clock ≠ 0)
    (hfuel :
      state.legacy.clock +
          max (panSemProgFuel (Prog.call info function arguments))
            (panSemFunctionFuel state.legacy.functions) = fuel + 1)
    (hbody :
      evalPanValueFfiClockProg context primitive handler state.legacy.structs
        state.legacy.functions state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord fuel calleeLocals state.legacy.globals
        state.legacy.memory state.legacy.ffi (state.legacy.clock - 1) body
        (memoryAccess := some state.memoryAccess) (contracts := state.legacy.contracts)
        (memoryHandler := state.legacy.memoryHandler) =
        some (.control (.continued bodyLocals finalGlobals finalMemory finalFfi),
          finalClock)) :
    panSemEvaluateExactState context primitive handler state (.call info function arguments) =
      some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  rw [hfuel]
  exact evalPanValueFfiClockCall_callee_continued_error context primitive handler
    state.legacy.structs state.legacy.functions state.legacy.baseAddress
    state.legacy.topAddress state.legacy.bytesInWord fuel state.legacy.locals
    state.legacy.globals state.legacy.memory state.legacy.ffi state.legacy.clock
    info function arguments values parameters calleeLocals bodyLocals finalGlobals
    finalMemory finalFfi body finalClock (memoryAccess := some state.memoryAccess)
    (contracts := state.legacy.contracts) (memoryHandler := state.legacy.memoryHandler)
    harguments hlookup hbind hparameters hclock hbody

/-- Exact-state Flapjack Call equation for a callee Error: the final memory,
    globals, FFI state, and clock survive while locals are cleared. Untagged
    because Lean's structured result is not HOL's literal `result option ×
    state` pair. -/
theorem panSemEvaluateExactState_call_error_of_callee_error
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog α)))
    (function : FunName) (arguments : List (Exp α))
    (values : List (PanValue α)) (parameters : List VarName) (body : Prog α)
    (calleeLocals bodyLocals finalGlobals : VarName → Option (PanValue α))
    (finalMemory : α → Option (PanValue α)) (finalFfi : FfiState σ)
    (finalClock fuel : Nat)
    (harguments :
      evalPanValueExps state.legacy.structs state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord arguments (memoryAccess := some state.memoryAccess) =
        some values)
    (hlookup : lookupPanFunction function state.legacy.functions = some (parameters, body))
    (hbind : bindPanValueParameters parameters values = some calleeLocals)
    (hparameters :
      panValueParametersValid state.legacy.structs state.legacy.contracts function values =
        true)
    (hclock : state.legacy.clock ≠ 0)
    (hfuel :
      state.legacy.clock +
          max (panSemProgFuel (Prog.call info function arguments))
            (panSemFunctionFuel state.legacy.functions) = fuel + 1)
    (hbody :
      evalPanValueFfiClockProg context primitive handler state.legacy.structs
        state.legacy.functions state.legacy.baseAddress state.legacy.topAddress
        state.legacy.bytesInWord fuel calleeLocals state.legacy.globals
        state.legacy.memory state.legacy.ffi (state.legacy.clock - 1) body
        (memoryAccess := some state.memoryAccess) (contracts := state.legacy.contracts)
        (memoryHandler := state.legacy.memoryHandler) =
        some (.control (.error bodyLocals finalGlobals finalMemory finalFfi), finalClock)) :
    panSemEvaluateExactState context primitive handler state (.call info function arguments) =
      some (.control (.error (fun _ => none) finalGlobals finalMemory finalFfi),
        finalClock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  rw [hfuel]
  exact evalPanValueFfiClockCall_callee_error_error context primitive handler
    state.legacy.structs state.legacy.functions state.legacy.baseAddress
    state.legacy.topAddress state.legacy.bytesInWord fuel state.legacy.locals
    state.legacy.globals state.legacy.memory state.legacy.ffi state.legacy.clock
    info function arguments values parameters calleeLocals bodyLocals finalGlobals
    finalMemory finalFfi body finalClock (memoryAccess := some state.memoryAccess)
    (contracts := state.legacy.contracts) (memoryHandler := state.legacy.memoryHandler)
    harguments hlookup hbind hparameters hclock hbody

/-! The legacy function-list evaluator does not carry HOL `state.code`'s
    per-entry `returnShape`; an optional `PanValueCallContracts.returnShapes`
    table is not a sound substitute for that field. The compatibility call
    path therefore does not reject a return based on that table. The exact
    state-owned evaluator checks the source code-map return shape. -/

/-- HOL `Dec` (`panSemScript.sml:558-565`) whose initialiser expression fails to
    evaluate returns `(SOME Error, s)` with the unchanged source state.  Stated
    over the exact source state with the state-owned memory access; untagged
    because the executed result is the reduced structured pair, not HOL's
    literal `result option # state` pairing. -/
theorem panSemEvaluateExactState_dec_error_of_eval_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.dec name shape value body) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  have hle : 1 ≤ max (panSemProgFuel (Prog.dec name shape value body))
      (panSemFunctionFuel state.legacy.functions) := by
    rw [panSemProgFuel]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k, state.legacy.clock +
      max (panSemProgFuel (Prog.dec name shape value body))
        (panSemFunctionFuel state.legacy.functions) = k + 1 := by
    cases h : state.legacy.clock +
        max (panSemProgFuel (Prog.dec name shape value body))
          (panSemFunctionFuel state.legacy.functions) with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  rw [hk]
  simp [panValueDecAcceptedValue, heval]

/-- HOL `Dec` (`panSemScript.sml:558-565`) whose initialiser value does not match
    the declared shape returns `(SOME Error, s)` with the unchanged source state.
    Stated over the exact source state with the state-owned memory access;
    untagged. -/
theorem panSemEvaluateExactState_dec_error_of_shape_mismatch
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (shape : Shape) (value : Exp α) (body : Prog α)
    (lastValue : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = some lastValue)
    (hshape : panShapeMatches (panValueShape state.legacy.structs lastValue)
      shape = false) :
    panSemEvaluateExactState context primitive handler state
        (.dec name shape value body) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  have hle : 1 ≤ max (panSemProgFuel (Prog.dec name shape value body))
      (panSemFunctionFuel state.legacy.functions) := by
    rw [panSemProgFuel]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k, state.legacy.clock +
      max (panSemProgFuel (Prog.dec name shape value body))
        (panSemFunctionFuel state.legacy.functions) = k + 1 := by
    cases h : state.legacy.clock +
        max (panSemProgFuel (Prog.dec name shape value body))
          (panSemFunctionFuel state.legacy.functions) with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  rw [hk]
  simp [panValueDecAcceptedValue, heval, hshape]

theorem panSemEvaluateExactState_primitive_error_of_arguments_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.primitive name operator arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
    evalPanValueExpsCounted, harguments]

theorem panSemEvaluateExactState_primitive_error_of_operator_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (values : List (PanValue α))
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = some values)
    (hprim : primitive operator values = none) :
    panSemEvaluateExactState context primitive handler state
        (.primitive name operator arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
    evalPanValueExpsCounted, harguments, hprim]

theorem panSemEvaluateExactState_primitive_error_of_destination_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (values : List (PanValue α)) (evaluated : PanValue α)
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = some values)
    (hprim : primitive operator values = some evaluated)
    (hlocal : state.legacy.locals name = none) :
    panSemEvaluateExactState context primitive handler state
        (.primitive name operator arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
    evalPanValueExpsCounted, harguments, hprim, hlocal]

theorem panSemEvaluateExactState_primitive_error_of_shape_mismatch
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (name : VarName) (operator : PrimOp) (arguments : List (Exp α))
    (values : List (PanValue α)) (evaluated oldValue : PanValue α)
    (harguments : evalPanValueExps state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord arguments
      (memoryAccess := some state.memoryAccess) = some values)
    (hprim : primitive operator values = some evaluated)
    (hlocal : state.legacy.locals name = some oldValue)
    (hshape : panShapeMatches (panValueShape state.legacy.structs evaluated)
      (panValueShape state.legacy.structs oldValue) = false) :
    panSemEvaluateExactState context primitive handler state
        (.primitive name operator arguments) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValuePrimitiveResult,
    evalPanValueExpsCounted, harguments, hprim, hlocal, hshape]

/-- HOL `panSemScript$evaluate_def` `Assign` returns `SOME Error` with the
unchanged state when the source expression does not evaluate. -/
theorem panSemEvaluateExactState_assign_error_of_eval_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (kind : VarKind) (name : VarName) (value : Exp α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.assign kind name value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  cases kind <;>
    simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
      panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState] <;>
    simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
      panValueAssignLocalResult, panValueAssignGlobalResult,
      evalPanValueExpCounted, heval]

/-- HOL `panSemScript$evaluate_def` `Assign` returns `SOME Error` with the
unchanged state when the destination fails `is_valid_value`. -/
theorem panSemEvaluateExactState_assign_error_of_invalid
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (kind : VarKind) (name : VarName) (value : Exp α) (evaluated : PanValue α)
    (heval : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = some evaluated)
    (hinvalid : panValueAssignmentValid state.legacy.structs state.legacy.locals
      state.legacy.globals kind name evaluated = false) :
    panSemEvaluateExactState context primitive handler state
        (.assign kind name value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  cases kind <;>
    simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
      panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState] <;>
    simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps,
      panValueAssignLocalResult, panValueAssignGlobalResult,
      evalPanValueExpCounted, heval, hinvalid]

/-- HOL `panSemScript$evaluate_def` `Store` returns `SOME Error` with the
unchanged state when the address expression fails to evaluate. -/
theorem panSemEvaluateExactState_store_error_of_address_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.store address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreResult,
    evalPanValueExpCounted, haddress]

/-- HOL `panSemScript$evaluate_def` `Store` returns `SOME Error` with the
unchanged state when the stored-value expression fails to evaluate. -/
theorem panSemEvaluateExactState_store_error_of_value_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord : PanValue α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some addressWord)
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.store address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreResult,
    evalPanValueExpCounted, haddress, hvalue]

/-- HOL `panSemScript$evaluate_def` `Store` returns `SOME Error` with the
unchanged state when the word store fails (for example outside its domain). -/
theorem panSemEvaluateExactState_store_error_of_store_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord : α) (valueWord : PanValue α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some (.word addressWord))
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = some valueWord)
    (hstore : panValueStoreWithAccess state.legacy.memory state.legacy.bytesInWord
      addressWord valueWord (some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.store address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreResult,
    evalPanValueExpCounted, haddress, hvalue, hstore]

/-- HOL `panSemScript$evaluate_def` `Store32` returns `SOME Error` with the
unchanged state when the address expression fails to evaluate. -/
theorem panSemEvaluateExactState_store32_error_of_address_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.store32 address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStore32Result,
    evalPanValueExpCounted, haddress]

/-- HOL `panSemScript$evaluate_def` `Store32` returns `SOME Error` with the
unchanged state when the stored-value expression fails to evaluate. -/
theorem panSemEvaluateExactState_store32_error_of_value_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord : PanValue α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some addressWord)
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.store32 address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStore32Result,
    evalPanValueExpCounted, haddress, hvalue]

/-- HOL `panSemScript$evaluate_def` `Store32` returns `SOME Error` with the
unchanged state when the 32-bit store fails (for example outside its domain). -/
theorem panSemEvaluateExactState_store32_error_of_store_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord valueWord : α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some (.word addressWord))
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = some (.word valueWord))
    (hstore : state.memoryAccess.store32 state.memoryAccess.domain
      state.legacy.memory state.legacy.bytesInWord addressWord valueWord = none) :
    panSemEvaluateExactState context primitive handler state
        (.store32 address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStore32Result,
    evalPanValueExpCounted, haddress, hvalue, hstore]

/-- HOL `panSemScript$evaluate_def` `StoreByte` returns `SOME Error` with the
unchanged state when the address expression fails to evaluate. -/
theorem panSemEvaluateExactState_storeByte_error_of_address_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.storeByte address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreByteResult,
    evalPanValueExpCounted, haddress]

/-- HOL `panSemScript$evaluate_def` `StoreByte` returns `SOME Error` with the
unchanged state when the stored-value expression fails to evaluate. -/
theorem panSemEvaluateExactState_storeByte_error_of_value_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord : PanValue α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some addressWord)
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.storeByte address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreByteResult,
    evalPanValueExpCounted, haddress, hvalue]

/-- HOL `panSemScript$evaluate_def` `StoreByte` returns `SOME Error` with the
unchanged state when the byte store fails (for example outside its domain). -/
theorem panSemEvaluateExactState_storeByte_error_of_store_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α) (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ) (state : PanSemExactState α σ)
    (address value : Exp α) (addressWord valueWord : α)
    (haddress : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord address
      (memoryAccess := some state.memoryAccess) = some (.word addressWord))
    (hvalue : evalPanValueExp state.legacy.structs state.legacy.locals
      state.legacy.globals state.legacy.memory state.legacy.baseAddress
      state.legacy.topAddress state.legacy.bytesInWord value
      (memoryAccess := some state.memoryAccess) = some (.word valueWord))
    (hstore : state.memoryAccess.storeByte state.memoryAccess.domain
      state.legacy.memory state.legacy.bytesInWord addressWord valueWord = none) :
    panSemEvaluateExactState context primitive handler state
        (.storeByte address value) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  simp [evalPanValueFfiClockLeaf, evalPanValueFfiProgSteps, panValueStoreByteResult,
    evalPanValueExpCounted, haddress, hvalue, hstore]

/-- HOL `If` (`panSemScript.sml:617-620`) whose condition does not evaluate to a
    word (either the expression fails or it is not a word value) returns
    `(SOME Error, s)` with the unchanged source state and clock.  Stated over the
    exact source state with the state-owned memory access; untagged boundary
    equation.  Oracle: `scripts/hol-probes/pan_sem_ite_e2e_probe.out`
    (`if_nonword_result=SOME Error`, `if_fail_result=SOME Error`). -/
theorem panSemEvaluateExactState_ite_error_of_condition_none
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    (context : PanValueFfiContext α)
    (primitive : PanPrimitiveHandler α)
    (handler : PanValueStatefulFfiHandler α σ)
    (state : PanSemExactState α σ)
    (condition : Exp α) (thenBranch elseBranch : Prog α)
    (hcondition : panValueIteConditionValue state.legacy.structs
      state.legacy.baseAddress state.legacy.topAddress state.legacy.bytesInWord
      state.legacy.locals state.legacy.globals state.legacy.memory condition
      (some state.memoryAccess) = none) :
    panSemEvaluateExactState context primitive handler state
        (.ite condition thenBranch elseBranch) =
      some (.control (.error state.legacy.locals state.legacy.globals
        state.legacy.memory state.legacy.ffi), state.legacy.clock) := by
  simp only [panSemEvaluateExactState, panSemEvaluate, panSemEvaluateWithFuel,
    panSemEvaluateFuel, evalPanValueFfiClockProg, PanSemExactState.toEvaluateState]
  have hle : 1 ≤ max (panSemProgFuel (Prog.ite condition thenBranch elseBranch))
      (panSemFunctionFuel state.legacy.functions) := by
    rw [panSemProgFuel]
    exact Nat.le_trans (by omega) (Nat.le_max_left _ _)
  obtain ⟨k, hk⟩ : ∃ k, state.legacy.clock +
      max (panSemProgFuel (Prog.ite condition thenBranch elseBranch))
        (panSemFunctionFuel state.legacy.functions) = k + 1 := by
    cases h : state.legacy.clock +
        max (panSemProgFuel (Prog.ite condition thenBranch elseBranch))
          (panSemFunctionFuel state.legacy.functions) with
    | zero => omega
    | succ k => exact ⟨k, rfl⟩
  rw [hk]
  rw [hcondition]
  rfl

/-! Finite-map updates for the source declaration evaluator. `InfoMap` is an
    association-list representation; putting the updated binding first and
    removing older copies gives the same lookup behavior as HOL `|+`. -/
def panSemDeclUpdateInfo [BEq String] (entries : InfoMap β)
    (name : String) (value : β) : InfoMap β :=
  (name, value) :: entries.filter (fun entry => !(entry.1 == name))

/-- Production declaration-globals update: `evaluate_decls` writes a `Decl`
    binding with HOL `s.globals |+ (v,res)`. This is the executable
    `FUPDATE` (`finite_mapTheory.FUPDATE_DEF`) on the finite-map view
    `VarName → Option (PanValue α)`; `panSemDeclUpdateGlobal_eq_FUPDATE` proves
    it is exactly the repo `FUPDATE` under lawful String equality. It is not
    `@[hol]`-tagged because the HOL source (`finite_mapTheory`) is HOL stdlib,
    outside the CakeML submodule, and the repo `FUPDATE` itself quantifies
    `[BEq α]` (the exact `=`-primitive gap is tracked by bead
    `flapjack-pxn.18.5.5.19`). -/
def panSemDeclUpdateGlobal [BEq String]
    (globals : VarName → Option (PanValue α)) (name : VarName)
    (value : PanValue α) : VarName → Option (PanValue α) :=
  fun candidate => if candidate == name then some value else globals candidate

/-- `panSemDeclUpdateGlobal` is exactly the repo `FUPDATE` on the finite-map
    view of `globals`, i.e. HOL `s.globals |+ (name,value)`, under lawful
    String equality. -/
theorem panSemDeclUpdateGlobal_eq_FUPDATE [BEq String] [LawfulBEq String]
    (globals : VarName → Option (PanValue α)) (name : VarName) (value : PanValue α) :
    panSemDeclUpdateGlobal globals name value = FUPDATE globals (name, value) := by
  funext candidate
  by_cases h : candidate = name
  · subst h
    simp [panSemDeclUpdateGlobal, FUPDATE]
  · have h₁ : (candidate == name) = false := beq_eq_false_iff_ne.mpr h
    have h₂ : (name == candidate) = false :=
      beq_eq_false_iff_ne.mpr (fun hh => h hh.symm)
    simp [panSemDeclUpdateGlobal, FUPDATE, h₁, h₂]

/-- Filtering the binding being updated does not change lookups at any other
    key. -/
theorem lookupInfo_filter_not_eq [BEq String] [LawfulBEq String]
    (entries : InfoMap β) (name key : String) (hne : key ≠ name) :
    lookupInfo key (entries.filter (fun entry => !(entry.1 == name))) =
      lookupInfo key entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨candidate, val⟩ := entry
      by_cases hc : candidate = name
      · have hb : (candidate == name) = true := beq_iff_eq.mpr hc
        have hck : (candidate == key) = false :=
          beq_eq_false_iff_ne.mpr (fun h => hne (by rw [← h, hc]))
        rw [show List.filter (fun entry => !(entry.1 == name)) ((candidate, val) :: entries)
              = List.filter (fun entry => !(entry.1 == name)) entries from by
            simp [hb, Bool.not_true]]
        rw [ih]
        simp only [lookupInfo, hck, Bool.false_eq_true, if_false]
      · have hb : (candidate == name) = false := beq_eq_false_iff_ne.mpr hc
        rw [show List.filter (fun entry => !(entry.1 == name)) ((candidate, val) :: entries)
              = (candidate, val) :: List.filter (fun entry => !(entry.1 == name)) entries from by
            simp [hb, Bool.not_false]]
        by_cases hk : candidate = key
        · have hkb : (candidate == key) = true := beq_iff_eq.mpr hk
          simp only [lookupInfo, hkb, if_true]
        · have hkb : (candidate == key) = false := beq_eq_false_iff_ne.mpr hk
          simp only [lookupInfo, hkb, Bool.false_eq_true, if_false]
          exact ih

/-- `panSemDeclUpdateInfo` is exactly HOL `code |+ (name,value)` /
    `eshapes |+ (name,value)` on the finite-map *view* of the association-list
    representation: looking up any key after the update agrees with `FUPDATE`
    of `fun k => lookupInfo k entries`. The assoc-list representation (with
    duplicate removal) is thus related to HOL's `num_map`/finite-map update by
    this bridge; it is untagged for the same stdlib/`[BEq String]` reasons as
    `panSemDeclUpdateGlobal`. -/
theorem lookupInfo_panSemDeclUpdateInfo [BEq String] [LawfulBEq String]
    (entries : InfoMap β) (name : String) (value : β) (key : String) :
    lookupInfo key (panSemDeclUpdateInfo entries name value) =
      FLOOKUP (FUPDATE (fun k => lookupInfo k entries) (name, value)) key := by
  rw [FLOOKUP_update]
  simp only [panSemDeclUpdateInfo, lookupInfo]
  by_cases h : name = key
  · have hb : (name == key) = true := beq_iff_eq.mpr h
    rw [hb]
    simp
  · have hb : (name == key) = false := beq_eq_false_iff_ne.mpr h
    rw [hb]
    simp only [Bool.false_eq_true, if_false]
    exact lookupInfo_filter_not_eq entries name key (fun hh => h hh.symm)

/-! Constructor form of the admissible-declaration premise used by Cake's
    `compile_top_shape_wf`: functions, value declarations, and exceptions are
    admitted; struct-name declarations are excluded. -/
def panSemCompileTopAdmissible : Decl α → Bool
  | .function _ | .decl _ _ _ | .exnDecl _ _ => true
  | .name _ _ => false

/-! Faithful declaration-by-declaration port of Cake
    `panSem$evaluate_decls` (`panSemScript.sml:814-835`). The dedicated
    `code` map retains parameter and return shapes, and `eshapes` retains the
    source exception map. The legacy runtime `functions` list is not used as a
    substitute for the source code map. Unlike `evalPanValueDeclarations`,
    this definition does no struct-name prepass: HOL's `Name` case is a no-op. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): HOL `evaluate_decls` operates on
-- a `panSem$state` whose `code`/`eshapes` are `mlstring`-keyed finite maps,
-- whereas `PanSemDeclarationState` uses `InfoMap` lists keyed by
-- `FunName`/`ExceptionId = String`. The clauses match but the key carrier
-- differs, so the tag is withheld until an exact MlString-keyed state lands
-- (tracked by `flapjack-pxn.18.3.5.8`, parent `flapjack-0lj`).
def evaluateDecls
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α] [Mul α]
    [Sub α] [AndOp α] [OrOp α] [HXor α α α] [ShiftLeft α] [ShiftRight α]
    [LT α] [DecidableRel (fun left right : α => left < right)] [PanCmp α]
    [BEq String]
    (state : PanSemDeclarationState α σ) : List (Decl α) →
      Option (PanSemDeclarationState α σ)
  | [] => some state
  | .name _ _ :: declarations => evaluateDecls state declarations
  | .decl shape name expression :: declarations =>
      match evalPanValueExp state.runtime.structs (fun _ => none)
          state.runtime.globals state.runtime.memory state.runtime.baseAddress
          state.runtime.topAddress state.runtime.bytesInWord expression
          (memoryAccess := some state.memoryAccess) with
      | none => none
      | some value =>
          if panShapeMatches (panValueShape state.runtime.structs value) shape then
            evaluateDecls
              { state with runtime :=
                { state.runtime with globals :=
                    panSemDeclUpdateGlobal state.runtime.globals name value } }
              declarations
          else none
  | .function declaration :: declarations =>
      if declaration.params.all (fun parameter =>
          isWfShape state.runtime.structs parameter.2) &&
          isWfShape state.runtime.structs declaration.returnShape then
        let entry : PanSemFunctionEntry α :=
          { params := declaration.params
            body := declaration.body
            returnShape := declaration.returnShape }
        evaluateDecls
          { state with code := panSemDeclUpdateInfo state.code declaration.name entry }
          declarations
      else none
  | .exnDecl exception shape :: declarations =>
      if (lookupInfo exception state.eshapes).isSome then none
      else if isWfShape state.runtime.structs shape then
        evaluateDecls
          { state with eshapes := panSemDeclUpdateInfo state.eshapes exception shape }
          declarations
      else none
termination_by declarations => sizeOf declarations
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial

end Flapjack
