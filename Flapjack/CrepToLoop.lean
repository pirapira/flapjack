import Flapjack.Loop
import Flapjack.Static
import Flapjack.RiscV.Model

/-!
Initial Crepe-to-Loop lowering for the direct executable fragment. This keeps
the IR close to CakeML's `crep_to_loopScript.sml`; expression side effects,
condition materialization, liveness, and arithmetic expansion are subsequent
passes.
-/

namespace Flapjack

abbrev NatInfoMap (α : Type u) := List (Nat × α)

def lookupNatInfo (name : Nat) : NatInfoMap α → Option α
  | [] => none
  | (candidate, value) :: entries =>
      if candidate == name then some value else lookupNatInfo name entries

structure LoopContext (α : Type u) where
  vars : NatInfoMap Nat
  functions : InfoMap (Nat × Nat)
  maxVar : Nat
  target : RiscV.Architecture
  deriving Repr

/-! Source-named port of CakeML Pancake's `mk_ctxt_def`
    (`crep_to_loopScript.sml:221`).  Keep the constructor argument order
    explicit: target, variable map, function map, and the fresh-variable
    upper bound. -/
def crepMkCtxt {α : Type u}
    (target : RiscV.Architecture) (vmap : NatInfoMap Nat)
    (functions : InfoMap (Nat × Nat)) (maxVar : Nat) : LoopContext α :=
  { vars := vmap, functions := functions, maxVar := maxVar, target := target }

/-! Source-named port of CakeML Pancake's `make_vmap_def`
    (`crep_to_loopScript.sml:230`).  Cake's finite map is populated by
    `ZIP (params, GENLIST I (LENGTH params))`; the list-backed context uses
    the same positional pairs and preserves their lookup order. -/
def crepMakeVmap (params : List Nat) : NatInfoMap Nat :=
  params.zip (List.range params.length)

def findLoopVar (context : LoopContext α) (name : Nat) : Nat :=
  match lookupNatInfo name context.vars with
  | some value => value
  | none => 0

/-! The Crepe primitive carries variable *names*, not expressions.  Cake's
    `crep_to_loop$compile` resolves both destination and argument lists with
    `FLOOKUP` and drops the statement if any name is absent.  Keeping an
    option-valued helper here is important: using `findLoopVar`'s defensive
    zero fallback would silently alias an unknown primitive operand with a
    real local and changes liveness and emitted code. -/
def lookupLoopVars (context : LoopContext α) : List Nat → Option (List Nat)
  | [] => some []
  | name :: names => do
      let mapped ← lookupNatInfo name context.vars
      let rest ← lookupLoopVars context names
      pure (mapped :: rest)
termination_by names => sizeOf names
decreasing_by all_goals decreasing_trivial

/-! Source-named port of `crep_to_loop$find_var` (`find_var_def`,
    `crep_to_loopScript.sml:20`). -/
def crepFindVar (context : LoopContext α) (name : Nat) : Nat :=
  findLoopVar context name

/-! Source-named port of `crep_to_loop$find_lab` (`find_lab_def`,
    `crep_to_loopScript.sml:27`). -/
def crepFindLab [BEq FunName] (context : LoopContext α) (name : FunName) : Nat :=
  match lookupInfo name context.functions with
  | some (label, _) => label
  | none => 0

/-! CakeML's `num_set` prints in ascending order.  Keep the list-backed live
    sets used by the executable port in that same canonical order when
    translating `prog_if`'s `list_insert` result. -/
def insertNatSorted (name : Nat) : List Nat → List Nat
  | [] => [name]
  | head :: tail =>
      if name < head then name :: head :: tail
      else if name = head then head :: tail
      else head :: insertNatSorted name tail

def loopListInsert (names live : List Nat) : List Nat :=
  names.foldl (fun current name => insertNatSorted name current) live

def loopListUnion (left right : List Nat) : List Nat :=
  loopListInsert (left ++ right) []

/-! CakeML's `num_set` insert operations preserve membership and canonical
    order.  The Flapjack live sets are plain sorted lists, so the corresponding
    facts are stated directly for `insertNatSorted`/`loopListInsert`. -/

/-- Membership in an inserted sorted live set, counterpart of CakeML's
    `domain_list_insert` (`sptreeScript.sml:2042`). -/
theorem insertNatSorted_mem (name : Nat) (live : List Nat) (x : Nat) :
    x ∈ insertNatSorted name live ↔ x = name ∨ x ∈ live := by
  induction live with
  | nil => simp [insertNatSorted]
  | cons head tail ih =>
      by_cases hlt : name < head
      · simp [insertNatSorted, hlt, List.mem_cons]
      · by_cases heq : name = head
        · subst heq; simp [insertNatSorted, List.mem_cons]
        · simp only [insertNatSorted, if_neg hlt, if_neg heq, List.mem_cons, ih]
          by_cases h1 : x = name <;> by_cases h2 : x = head <;> by_cases h3 : x ∈ tail <;>
            simp_all

/-- Inserting the same temporary twice is idempotent, the Flapjack counterpart
    of CakeML's `insert_insert_eq`/`insert_shadow`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:380`). -/
theorem insertNatSorted_idem (name : Nat) (live : List Nat) :
    insertNatSorted name (insertNatSorted name live) = insertNatSorted name live := by
  induction live with
  | nil => simp [insertNatSorted]
  | cons head tail ih =>
      by_cases hlt : name < head
      · simp [insertNatSorted, hlt]
      · by_cases heq : name = head
        · subst heq; simp [insertNatSorted]
        · simp only [insertNatSorted, if_neg hlt, if_neg heq, ih]

/-- CakeML's `list_insert_SNOC`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:386`). -/
theorem loopListInsert_snoc (x : Nat) (ys : List Nat) (live : List Nat) :
    loopListInsert (ys ++ [x]) live = insertNatSorted x (loopListInsert ys live) := by
  simp [loopListInsert, List.foldl_append]

/-- CakeML's `list_insert_append`
    (`cakeml/pancake/proofs/crep_to_loopProofScript.sml:414`), in the foldl
    orientation used by the Flapjack executable port. -/
theorem loopListInsert_append (xs ys : List Nat) (live : List Nat) :
    loopListInsert (xs ++ ys) live = loopListInsert ys (loopListInsert xs live) := by
  simp [loopListInsert, List.foldl_append]

/-- Membership in a folded live set; counterpart of CakeML's
    `domain_list_insert` for `list_insert`. -/
theorem loopListInsert_mem (x : Nat) (names : List Nat) (live : List Nat) :
    x ∈ loopListInsert names live ↔ x ∈ names ∨ x ∈ live := by
  induction names generalizing live with
  | nil => simp [loopListInsert]
  | cons name names ih =>
      rw [show loopListInsert (name :: names) live =
          loopListInsert names (insertNatSorted name live) from rfl]
      rw [ih, insertNatSorted_mem]
      by_cases h1 : x = name <;> by_cases h2 : x ∈ names <;> by_cases h3 : x ∈ live <;>
        simp_all [List.mem_cons]

theorem insertNatSorted_cons_lt {a b : Nat} (l : List Nat) (h : a < b) :
    insertNatSorted a (b :: l) = a :: b :: l := by
  simp [insertNatSorted, h]

theorem insertNatSorted_cons_eq {a b : Nat} (l : List Nat) (h : a = b) :
    insertNatSorted a (b :: l) = b :: l := by
  cases h
  simp [insertNatSorted, Nat.lt_irrefl]

theorem insertNatSorted_cons_gt {a b : Nat} (l : List Nat) (h : b < a) :
    insertNatSorted a (b :: l) = b :: insertNatSorted a l := by
  have hlt : ¬ a < b := Nat.not_lt_of_lt h
  have hne : ¬ a = b := by omega
  simp [insertNatSorted, hlt, hne]

theorem insertNatSorted_nil_comm (x y : Nat) :
    insertNatSorted x (insertNatSorted y []) =
      insertNatSorted y (insertNatSorted x []) := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · have hyx : ¬ y < x := Nat.not_lt_of_lt h
    have hne1 : ¬ x = y := by omega
    have hne2 : ¬ y = x := by omega
    simp only [insertNatSorted, if_pos h, if_neg hyx, if_neg hne1, if_neg hne2]
  · subst h; rfl
  · have hxy : ¬ x < y := Nat.not_lt_of_lt h
    have hne1 : ¬ x = y := by omega
    have hne2 : ¬ y = x := by omega
    simp only [insertNatSorted, if_pos h, if_neg hxy, if_neg hne1, if_neg hne2]

theorem insertNatSorted_comm (x y : Nat) :
    ∀ live : List Nat,
      insertNatSorted x (insertNatSorted y live) =
        insertNatSorted y (insertNatSorted x live) := by
  intro live
  induction live with
  | nil => exact insertNatSorted_nil_comm x y
  | cons head tail ih =>
      rcases Nat.lt_trichotomy x head with hxlt | hxeq | hxgt <;>
      rcases Nat.lt_trichotomy y head with hylt | hyeq | hygt <;>
      rcases Nat.lt_trichotomy x y with hxylt | hxyeq | hxygt <;>
      simp_all only [insertNatSorted_cons_lt, insertNatSorted_cons_eq,
        insertNatSorted_cons_gt] <;>
      try (exfalso; omega)


theorem loopListInsert_insertNatSorted_comm (x : Nat) (names : List Nat)
    (live : List Nat) :
    insertNatSorted x (loopListInsert names live) =
      loopListInsert names (insertNatSorted x live) := by
  induction names generalizing live with
  | nil => simp [loopListInsert]
  | cons name names ih =>
      rw [show loopListInsert (name :: names) live =
          loopListInsert names (insertNatSorted name live) from rfl]
      rw [ih (insertNatSorted name live)]
      rw [show loopListInsert (name :: names) (insertNatSorted x live) =
          loopListInsert names (insertNatSorted name (insertNatSorted x live))
            from rfl]
      rw [insertNatSorted_comm name x]

/-! Source-named port of `crep_to_loop$prog_if` (`prog_if_def`,
    `crep_to_loopScript.sml:34`).  The result is a statement list; the caller
    applies `nested_seq` exactly as the original compiler does. -/
def progIf [OfNat α 0] [OfNat α 1]
    (operator : Cmp) (first second : List (LoopProg α))
    (left right : LoopExp α) (condition rightRegister : Nat) (live : List Nat) :
    List (LoopProg α) :=
  first ++ second ++
    [.assign condition left,
     .assign rightRegister right,
     .ite operator condition (.reg rightRegister)
       (.assign condition (.const (1 : α)))
       (.assign condition (.const (0 : α)))
       (loopListInsert [condition, rightRegister] live)]

/-! Source-named RISC-V port of `crep_to_loop$compile_crepop`
    (`compile_crepop_def`, `crep_to_loopScript.sml:42`).  CakeML has an ARMv7
    branch with two distinct long-multiply destinations; ARMv7 is outside the
    supported Flapjack backend, so every supported architecture follows the
    RISC-V same-destination case. -/
def compileCrepOp [OfNat α 0] [OfNat α 1]
    (operator : CrepOp) (_target : RiscV.Architecture)
    (left right tmp : Nat) (_live : List Nat) : List (LoopProg α) × Nat :=
  match operator with
  | .mul => ([.arith (.longMul tmp tmp left right)], tmp)

/-!
This compiler carries the temporary and liveness
state used by the HOL pass. In particular, `Load32`, `LoadByte`, and
comparisons become explicit Loop statements rather than remaining effectful
expressions.
-/

structure LoopCompileExpResult (α : Type u) where
  code : List (LoopProg α)
  expression : LoopExp α
  nextTemp : Nat
  live : List Nat
  deriving Repr

structure LoopCompileExpsResult (α : Type u) where
  expressions : List (LoopExp α)
  code : List (LoopProg α)
  nextTemp : Nat
  live : List Nat
  deriving Repr

def loopCompileExp [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat) :
    CrepExp α → LoopCompileExpResult α
  | .const value => { code := [], expression := .const value, nextTemp := tmp, live := live }
  | .var name =>
      { code := [], expression := .var (findLoopVar context name), nextTemp := tmp, live := live }
  | .load address =>
      let result := loopCompileExp context tmp live address
      { result with expression := .load result.expression }
  | .load32 address =>
      let result := loopCompileExp context tmp live address
      { code := result.code ++ [.assign tmp result.expression, .load32 tmp tmp],
        expression := .var tmp, nextTemp := tmp + 1, live := tmp :: result.live }
  | .loadByte address =>
      let result := loopCompileExp context tmp live address
      { code := result.code ++ [.assign tmp result.expression, .loadByte tmp tmp],
        expression := .var tmp, nextTemp := tmp + 1, live := tmp :: result.live }
  | .loadGlob address =>
      { code := [], expression := .lookup address, nextTemp := tmp, live := live }
  | .op operator arguments =>
      let result := loopCompileExps context tmp live arguments
      { code := result.code, expression := .op operator result.expressions,
        nextTemp := result.nextTemp, live := result.live }
  | .crepOp operator arguments =>
      let result := loopCompileExps context tmp live arguments
      match operator, result.expressions with
      | .mul, [left, right] =>
          let leftTemp := result.nextTemp
          let rightTemp := leftTemp + 1
          let (operationCode, destination) :=
            compileCrepOp .mul context.target leftTemp rightTemp
              (rightTemp + 1) result.live
          { code := result.code ++
              [.assign leftTemp left, .assign rightTemp right] ++ operationCode
            expression := .var destination
            nextTemp := destination + 1
            live := insertNatSorted destination
              (loopListInsert [leftTemp, rightTemp] result.live) }
      | .mul, expressions =>
          let firstTemp := result.nextTemp
          let argumentTemps := List.range expressions.length |>.map
            (fun offset => firstTemp + offset)
          let argumentCode := argumentTemps.zipWith
            (fun name expression => .assign name expression) expressions
          let (operationCode, destination) :=
            compileCrepOp .mul context.target firstTemp (firstTemp + 1)
              (firstTemp + expressions.length) result.live
          { code := result.code ++ argumentCode ++ operationCode
            expression := .var destination
            nextTemp := destination + 1
            live := insertNatSorted destination
              (loopListInsert argumentTemps result.live) }
  | .cmp operator left right =>
      let leftResult := loopCompileExp context tmp live left
      let rightResult := loopCompileExp context leftResult.nextTemp leftResult.live right
      /- Cake's `compile_exp` reserves the next temporary returned by the
         right operand and materializes the comparison into the following two
         names (`tmp' + 1`, `tmp' + 2`).  The old port reused `tmp'` for the
         left operand, shifting every comparison/while temporary by one and
         changing the observable Word/RISC-V artifact. -/
      let leftTemp := rightResult.nextTemp + 1
      let rightTemp := leftTemp + 1
      { code := leftResult.code ++ rightResult.code ++
          [.assign leftTemp leftResult.expression,
           .assign rightTemp rightResult.expression,
           .ite operator leftTemp (.reg rightTemp)
             (.assign leftTemp (.const (by exact 1)))
             (.assign leftTemp (.const (by exact 0)))
             (loopListInsert [leftTemp, rightTemp] rightResult.live)],
        expression := .var leftTemp, nextTemp := rightTemp + 1,
        live := leftTemp :: rightTemp :: rightResult.live }
  | .shift operator left right =>
      let leftResult := loopCompileExp context tmp live left
      let rightResult := loopCompileExp context leftResult.nextTemp leftResult.live right
      { code := leftResult.code ++ rightResult.code,
        expression := .shift operator leftResult.expression rightResult.expression,
        nextTemp := rightResult.nextTemp, live := rightResult.live }
  | .baseAddr => { code := [], expression := .baseAddr, nextTemp := tmp, live := live }
  | .topAddr => { code := [], expression := .topAddr, nextTemp := tmp, live := live }
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  loopCompileExps (context : LoopContext α) (tmp : Nat) (live : List Nat) :
      List (CrepExp α) → LoopCompileExpsResult α
    | [] => { expressions := [], code := [], nextTemp := tmp, live := live }
    | expression :: expressions =>
        let first := loopCompileExp context tmp live expression
        let rest := loopCompileExps context first.nextTemp first.live expressions
        { expressions := first.expression :: rest.expressions,
          code := first.code ++ rest.code, nextTemp := rest.nextTemp, live := rest.live }
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def loopCompileExps [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (expressions : List (CrepExp α)) :
    LoopCompileExpsResult α :=
  loopCompileExp.loopCompileExps context tmp live expressions

def loopTempNames (start count : Nat) : List Nat :=
  (List.range count).map (fun offset => start + offset)

/-! Source-named ports of the small temporary/return-variable helpers from
    `crep_to_loopScript.sml:101-118`. -/
def crepGenTemps (start count : Nat) : List Nat :=
  loopTempNames start count

def crepRtVar (context : NatInfoMap Nat) (value : Option Nat) (nextTemp maxVar : Nat) : Nat :=
  match value with
  | none => nextTemp
  | some name => (lookupNatInfo name context).getD (maxVar + 1)

def crepRtVarsAux (context : NatInfoMap Nat) : List Nat → Option (List Nat)
  | [] => some []
  | name :: names =>
      match lookupNatInfo name context, crepRtVarsAux context names with
      | some value, some values => some (value :: values)
      | _, _ => none

def crepRtVars (context : NatInfoMap Nat) (names : List Nat) (maxVar : Nat) : List Nat :=
  (crepRtVarsAux context names).getD [maxVar + 1]

def loopAssignTemps (names : List Nat) (expressions : List (LoopExp α)) :
    List (LoopProg α) :=
  names.zipWith (fun name expression => .assign name expression) expressions

def loopCompileProg [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) : CrepProg α → LoopProg α
  | .skip => .skip
  | .dec name value body =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      let nextContext := { context with
        vars := (name, result.nextTemp) :: context.vars
        maxVar := result.nextTemp }
      .seq (loopNestedSeq result.code)
        /- Cake's `Dec` assigns the freshly allocated temporary `tmp` and
           extends the context with `v |-> tmp`; using the source binder here
           leaves the Word stage with a different variable identity. -/
        (.seq (.assign result.nextTemp result.expression)
          /- `fl = insert tmp () l` (`crep_to_loopScript.sml:414`) extends the
             *incoming* live set, not the one `compile_exp` returned.  The
             difference is the expression temporaries: `compile_exp` inserts
             them (`LoadByte`, `Load32`, `Cmp`, `Crepop`) so that the code it
             emits can name them, but they are dead once the declared variable
             holds the value, and Cake does not carry them into the body.
             Threading them on instead keeps them in every cutset the body
             emits, which the later passes cannot recover: `loop_live$shrink`
             only intersects cutsets, and a `Loop` whose `Break` restores the
             loop's entry set never shrinks below it. -/
          (loopCompileProg nextContext
            (insertNatSorted result.nextTemp live) body))
  | .assign name value =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      match lookupNatInfo name context.vars with
      | some mappedName =>
          loopNestedSeq (result.code ++ [.assign mappedName result.expression])
      | none => .skip
  | .primitive names operator arguments =>
      match names.mapM (lookupNatInfo · context.vars),
          arguments.mapM (lookupNatInfo · context.vars) with
      | some mappedNames, some mappedArguments =>
          .primitive mappedNames operator mappedArguments
      | _, _ => .skip
  | .store address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let valueTemp := valueResult.nextTemp
      loopNestedSeq (addressResult.code ++ valueResult.code ++
        [.assign valueTemp valueResult.expression,
         .store addressResult.expression valueTemp])
  | .store32 address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let addressTemp := valueResult.nextTemp
      let valueTemp := addressTemp + 1
      loopNestedSeq (addressResult.code ++ valueResult.code ++
        [.assign addressTemp addressResult.expression,
         .assign valueTemp valueResult.expression,
         .store32 addressTemp valueTemp])
  | .storeByte address value =>
      let addressResult := loopCompileExp context (context.maxVar + 1) live address
      let valueResult := loopCompileExp context addressResult.nextTemp addressResult.live value
      let addressTemp := valueResult.nextTemp
      let valueTemp := addressTemp + 1
      loopNestedSeq (addressResult.code ++ valueResult.code ++
        [.assign addressTemp addressResult.expression,
         .assign valueTemp valueResult.expression,
         .storeByte addressTemp valueTemp])
  | .storeGlob address value =>
      let result := loopCompileExp context (context.maxVar + 1) live value
      loopNestedSeq (result.code ++ [.setGlobal address result.expression])
  | .seq first second => .seq (loopCompileProg context live first)
      (loopCompileProg context live second)
  | .ite condition thenBranch elseBranch =>
      -- `crep_to_loopScript.sml:176-181`: both branches and the cutset use
      -- the incoming live set; the condition's own live result is dropped.
      let result := loopCompileExp context (context.maxVar + 1) live condition
      loopNestedSeq (result.code ++
        [.assign result.nextTemp result.expression,
         .ite .notEqual result.nextTemp (.imm (by exact 0))
           (loopCompileProg context live thenBranch)
           (loopCompileProg context live elseBranch) live])
  | .while condition body =>
      -- `crep_to_loopScript.sml:182-188`: the loop entry and exit live sets,
      -- the body, and the inner cutset all use the incoming live set.
      let result := loopCompileExp context (context.maxVar + 1) live condition
      .loop live
        (loopNestedSeq (result.code ++
          [.assign result.nextTemp result.expression,
           .ite .notEqual result.nextTemp (.imm (by exact 0))
              (.seq (loopCompileProg context live body) (.continue 0))
              (.break 0) live]))
        live
  | .break label => .break label
  | .continue label => .continue label
  | .call returnInfo function arguments =>
      let result := loopCompileExps context (context.maxVar + 1) live arguments
      let argumentNames := loopTempNames result.nextTemp result.expressions.length
      let target := match lookupInfo function context.functions with
        | some (label, _) => some label
        | none => some 0
      let call := match returnInfo with
        | none => .call none target argumentNames none
        -- `crep_to_loopScript.sml:189-207`: the call and handler cutsets and
        -- the handler compilation all use the incoming live set.
        | some (returns, none) =>
            let exceptionName := context.maxVar + 1
            .call (some (crepRtVars context.vars returns (context.maxVar + 1), live))
              target argumentNames
              (some (exceptionName, .raise exceptionName, .skip, live))
        | some (returns, some (exception, handler)) =>
            let exceptionName := context.maxVar + 1
            let handlerCode := loopCompileProg context live handler
            .call (some (crepRtVars context.vars returns (context.maxVar + 1), live))
              target argumentNames
              (some (exceptionName,
                .ite .notEqual exceptionName (.imm exception)
                  (.raise exceptionName) (.seq .tick handlerCode) live,
                .skip, live))
      loopNestedSeq (result.code ++ loopAssignTemps argumentNames result.expressions ++ [call])
  | .extCall function configuration configurationLength array arrayLength =>
      match lookupNatInfo configuration context.vars,
          lookupNatInfo configurationLength context.vars,
          lookupNatInfo array context.vars,
          lookupNatInfo arrayLength context.vars with
      | some configuration, some configurationLength, some array, some arrayLength =>
          .ffi function configuration configurationLength array arrayLength live
      | _, _, _, _ => .skip
  | .raise exception =>
      let exceptionName := context.maxVar + 1
      .seq (.assign exceptionName (.const exception)) (.raise exceptionName)
  | .return values =>
      let result := loopCompileExps context (context.maxVar + 1) live values
      let names := loopTempNames result.nextTemp result.expressions.length
      loopNestedSeq
        (result.code ++ loopAssignTemps names result.expressions ++ [.return names])
  | .shMem operator name address =>
      match lookupNatInfo name context.vars with
      | some mappedName =>
          let result := loopCompileExp context (context.maxVar + 1) live address
          loopNestedSeq (result.code ++
            [.shMem operator mappedName result.expression])
      | none => .skip
  | .tick => .tick
termination_by program => sizeOf program

/-! Source-named entrypoint for `crep_to_loop$compile` (`compile_def`,
    `crep_to_loopScript.sml:120`).  The lowering state is already represented
    explicitly by `LoopContext` and the live set argument. -/
def compileCrepToLoop [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (program : CrepProg α) :
    LoopProg α :=
  loopCompileProg context live program

theorem loopCompileProg_skip [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) :
    loopCompileProg context live (.skip : CrepProg α) = .skip := by
  simp [loopCompileProg]

theorem loopCompileProg_extCall [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (function : FunName)
    (configuration configurationLength array arrayLength : Nat)
    (configuration' configurationLength' array' arrayLength' : Nat)
    (hconfiguration : lookupNatInfo configuration context.vars = some configuration')
    (hconfigurationLength :
      lookupNatInfo configurationLength context.vars = some configurationLength')
    (harray : lookupNatInfo array context.vars = some array')
    (harrayLength :
      lookupNatInfo arrayLength context.vars = some arrayLength') :
    loopCompileProg context live
        (.extCall function configuration configurationLength array arrayLength) =
      .ffi function configuration' configurationLength' array' arrayLength' live := by
  simp [loopCompileProg, hconfiguration, hconfigurationLength, harray, harrayLength]

theorem loopCompileProg_seq [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (live : List Nat) (first second : CrepProg α) :
    loopCompileProg context live (.seq first second) =
      .seq (loopCompileProg context live first) (loopCompileProg context live second) := by
  simp [loopCompileProg]

theorem loopCompileExp_const [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (value : α) :
    loopCompileExp context tmp live (.const value) =
      { code := [], expression := .const value, nextTemp := tmp, live := live } := by
  simp [loopCompileExp]

theorem loopCompileExp_load32 [OfNat α 0] [OfNat α 1]
    (context : LoopContext α) (tmp : Nat) (live : List Nat)
    (address : CrepExp α) :
    (loopCompileExp context tmp live (.load32 address)).nextTemp = tmp + 1 := by
  simp [loopCompileExp]

end Flapjack
