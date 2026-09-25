import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.PanStructs
import Flapjack.Pancake.PanSimp
import Flapjack.Pancake.PanLang.Prog

/-!
The core of Pancake's `pan_globals` pass.

Global values are laid out in the heap from `TopAddr`. This module keeps the
word representation abstract and receives the natural-number-to-word map in
the context, allowing the same executable pass to be instantiated with
`BitVec` for the RISC-V backend or with `Nat` in small tests.
-/

namespace Flapjack

structure GlobalPassContext (α : Type u) where
  globals : InfoMap (Shape × α)
  globalsSize : α
  maxGlobalsSize : α
  bytesInWord : α
  fromNat : Nat → α

structure GlobalCompiledProgram (α : Type u) where
  initializers : List (Prog α)
  declarations : List (Decl α)
  context : GlobalPassContext α

def globalAddress [Add α] [Mul α] (context : GlobalPassContext α) (shape : Shape) : α :=
  context.globalsSize + context.bytesInWord * context.fromNat (Shape.shapeSize shape)

def globalCompileExp [BEq String] (context : GlobalPassContext α) : Exp α → Exp α
  | .var .local name => .var .local name
  | .var .global name =>
      match lookupInfo name context.globals with
      | some (shape, address) =>
          .load shape (.op .sub [.topAddr, .const address])
      | none => .const (context.fromNat 0)
  | .rStruct expressions => .rStruct (globalCompileExps context expressions)
  | .rField index expression => .rField index (globalCompileExp context expression)
  | .nStruct _ _ => .const (context.fromNat 0)
  | .nField _ _ => .const (context.fromNat 0)
  | .load shape address => .load shape (globalCompileExp context address)
  | .load32 address => .load32 (globalCompileExp context address)
  | .loadByte address => .loadByte (globalCompileExp context address)
  | .op operator expressions => .op operator (globalCompileExps context expressions)
  | .panOp operator expressions => .panOp operator (globalCompileExps context expressions)
  | .cmp operator left right =>
      .cmp operator (globalCompileExp context left) (globalCompileExp context right)
  | .shift operator left right =>
      .shift operator (globalCompileExp context left) (globalCompileExp context right)
  | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
  | expression => expression
termination_by expression => sizeOf expression
where
  globalCompileExps [BEq String] (context : GlobalPassContext α) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        globalCompileExp context expression :: globalCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalExpVars : Exp α → List VarName
  | .const _ => []
  | .var _ name => [name]
  | .rStruct fields => globalExpVarsList fields
  | .rField _ value => globalExpVars value
  | .nStruct _ fields => globalExpVarsFieldList fields
  | .nField _ value => globalExpVars value
  | .load _ address => globalExpVars address
  | .load32 address => globalExpVars address
  | .loadByte address => globalExpVars address
  | .op _ arguments => globalExpVarsList arguments
  | .panOp _ arguments => globalExpVarsList arguments
  | .cmp _ left right => globalExpVars left ++ globalExpVars right
  | .shift _ left right => globalExpVars left ++ globalExpVars right
  | .baseAddr => []
  | .topAddr => []
  | .bytesInWord => []
termination_by expression => sizeOf expression
where
  globalExpVarsList : List (Exp α) → List VarName
    | [] => []
    | expression :: expressions => globalExpVars expression ++ globalExpVarsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  globalExpVarsFieldList : List (FieldName × Exp α) → List VarName
    | [] => []
    | (_, expression) :: fields => globalExpVars expression ++ globalExpVarsFieldList fields
  termination_by fields => sizeOf fields
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalCompileExpList [BEq String] (context : GlobalPassContext α) :
    List (Exp α) → List (Exp α)
  | [] => []
  | expression :: expressions =>
      globalCompileExp context expression :: globalCompileExpList context expressions
termination_by expressions => sizeOf expressions
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalFreeVars : Prog α → List VarName
  | .skip => []
  | .dec name _ value body =>
      globalExpVars value ++ (globalFreeVars body).filter (· != name)
  | .assign kind name value =>
      (if kind == .local then [name] else []) ++ globalExpVars value
  | .primitive name _ arguments => name :: arguments.flatMap globalExpVars
  | .store address value => globalExpVars address ++ globalExpVars value
  | .store32 address value => globalExpVars address ++ globalExpVars value
  | .storeByte address value => globalExpVars address ++ globalExpVars value
  | .seq first second => globalFreeVars first ++ globalFreeVars second
  | .ite condition thenBranch elseBranch =>
      globalExpVars condition ++ globalFreeVars thenBranch ++ globalFreeVars elseBranch
  | .while condition body => globalExpVars condition ++ globalFreeVars body
  | .break => []
  | .continue => []
  | .call info _ arguments =>
      let destination := match info with
        | some (some (kind, name), _) => if kind == .local then [name] else []
        | _ => []
      let handler := match info with
        | some (_, some (_, handlerVar, program)) => handlerVar :: globalFreeVars program
        | _ => []
      destination ++ handler ++ arguments.flatMap globalExpVars
  | .decCall name _ _ arguments body =>
      name :: globalFreeVars body ++ arguments.flatMap globalExpVars
  | .extCall _ configuration configurationLength array arrayLength =>
      globalExpVars configuration ++ globalExpVars configurationLength ++
        globalExpVars array ++ globalExpVars arrayLength
  | .raise _ value => globalExpVars value
  | .return value => globalExpVars value
  | .shMemLoad _ kind name address =>
      (if kind == .local then [name] else []) ++ globalExpVars address
  | .shMemStore _ address value => globalExpVars address ++ globalExpVars value
  | .tick => []
  | .annot _ _ => []
termination_by program => sizeOf program

def globalApostrophes : Nat → String
  | 0 => ""
  | count + 1 => "'" ++ globalApostrophes count

def globalFreshNameAux [BEq String] (name : String) (names : List String) :
    Nat → Nat → String
  | candidate, 0 => name ++ globalApostrophes candidate
  | candidate, fuel + 1 =>
      let candidateName := name ++ globalApostrophes candidate
      if names.contains candidateName then
        globalFreshNameAux name names (candidate + 1) fuel
      else candidateName

def globalFreshName [BEq String] (name : String) (names : List String) : String :=
  globalFreshNameAux name names 0 names.length

/-! Counterpart of Cake's `fresh_name_correct`
    (`pan_globalsProofScript.sml:993`): the name chosen by the fresh-name search
    is never a member of the list it was searching.  The search starts with
    `names.length` fuel and tries `name`, `name'`, `name''`, ... in turn, so if
    it ran out of fuel it would have found `names.length + 1` distinct candidates
    already present in `names`, which is impossible. -/
theorem globalApostrophes_length (count : Nat) :
    (globalApostrophes count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hsingleton : ("'" : String).length = 1 := rfl
      simp [globalApostrophes, String.length_append, ih, hsingleton]
      omega

theorem globalApostrophes_injective : Function.Injective globalApostrophes := by
  intro left right heq
  have hlen := congrArg String.length heq
  rw [globalApostrophes_length, globalApostrophes_length] at hlen
  exact hlen

theorem append_globalApostrophes_injective (name : String) :
    Function.Injective (fun count => name ++ globalApostrophes count) := by
  intro left right heq
  have hlen := congrArg String.length heq
  rw [String.length_append, String.length_append, globalApostrophes_length,
    globalApostrophes_length] at hlen
  exact Nat.add_left_cancel hlen

theorem globalFreshNameAux_not_mem_or_all_mem [BEq String] [LawfulBEq String]
    (name : String) (names : List String) (candidate fuel : Nat) :
    globalFreshNameAux name names candidate fuel ∉ names ∨
      ∀ k, k ≤ fuel → name ++ globalApostrophes (candidate + k) ∈ names := by
  induction fuel generalizing candidate with
  | zero =>
      rw [globalFreshNameAux]
      by_cases hmem : name ++ globalApostrophes candidate ∈ names
      · exact Or.inr (fun k hk => by
          have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
          subst hk0
          exact hmem)
      · exact Or.inl hmem
  | succ fuel ih =>
      rw [globalFreshNameAux]
      by_cases hcontains :
          names.contains (name ++ globalApostrophes candidate) = true
      · rw [if_pos hcontains]
        rcases ih (candidate + 1) with hnotmem | hall
        · exact Or.inl hnotmem
        · refine Or.inr (fun k hk => ?_)
          cases k with
          | zero =>
              simpa using (List.contains_iff_mem.mp hcontains)
          | succ j =>
              have hj : j ≤ fuel := Nat.succ_le_succ_iff.mp hk
              have hstep : candidate + (j + 1) = candidate + 1 + j := by omega
              rw [hstep]
              exact hall j hj
      · rw [if_neg hcontains]
        exact Or.inl (fun hmem =>
          hcontains (List.contains_iff_mem.mpr hmem))

theorem globalFreshName_not_mem [BEq String] [LawfulBEq String]
    (name : String) (names : List String) :
    globalFreshName name names ∉ names := by
  intro hmem
  rcases globalFreshNameAux_not_mem_or_all_mem name names 0 names.length with
    hnotmem | hall
  · exact hnotmem hmem
  · have hsubset :
        ∀ x ∈ (List.range (names.length + 1)).map
            (fun k => name ++ globalApostrophes k), x ∈ names := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hk
      simpa using hall k (by omega)
    have hnodup :
        ((List.range (names.length + 1)).map
          (fun k => name ++ globalApostrophes k)).Nodup :=
      List.Pairwise.map (fun k => name ++ globalApostrophes k)
        (fun left right hne heq =>
          hne (append_globalApostrophes_injective name heq))
        List.nodup_range
    have hle := List.Nodup.length_le_of_subset hnodup hsubset
    simp at hle
    omega

/-! Counterpart of Cake's `fresh_name_correct'`
    (`pan_globalsProofScript.sml:1003`): a name chosen fresh for `names` is
    also absent from any list whose members all lie in `names`. -/
theorem globalFreshName_not_mem_of_subset [BEq String] [LawfulBEq String]
    (name : String) (names names' : List String)
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    globalFreshName name names ∉ names' := by
  intro hmem
  exact globalFreshName_not_mem name names (hsubset _ hmem)
/-- Maximum `String.length` over a list of names; used only to justify
    termination of the exact `fresh_name` port below. -/
def maxNameLength : List String → Nat
  | [] => 0
  | name :: names => max name.length (maxNameLength names)

theorem length_le_maxNameLength {name : String} {names : List String}
    (hmem : name ∈ names) : name.length ≤ maxNameLength names := by
  induction names with
  | nil => cases hmem
  | cons head tail ih =>
      rw [maxNameLength]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Qualified HOL port of Cake's `fresh_name` (`pan_globalsScript.sml:55`):
    while the candidate is already a member of `names`, append one apostrophe
    and retry.  The Lean clauses match HOL's exactly --
    `if name ∈ names then freshNameHOL (name ++ "'") names else name` versus
    `if MEM name names then fresh_name (strcat name «'») names else name` --
    with `∈` being `String`/list equality and `++`/`strcat` the same
    one-character append.  Termination is proved with a Flapjack-specific
    measure (`maxNameLength`); HOL uses a `strlen`/`MAX_SET` measure, but the
    measure is not operational, and `String.length`/`strlen` occur only there,
    never in the result.  The sole operational difference is the name carrier:
    production `String` versus HOL `mlstring`.

    `name` is byte-observable: the generated name crosses the compiler
    boundary, and the same-module witness `holMlStringWitness_freshNameHOL`
    establishes `NameRanged (freshNameHOL name names)` from the input premise
    `NameRanged name` (only apostrophes are appended).  The executed path
    supplies byte-ranged seeds: `globalCompile` uses `freshNameHOL "" names` and
    `freshNameHOL "vn'" (resultName :: names)`, and `globalNewMainName` uses the
    literal `"main"`.  The `names` list is used only for membership equality,
    never inspected, so it is not a byte-observable identifier.  Direct HOL rows
    are in `scripts/hol-probes/pan_globals_fresh_name_probe.out`; Lean rows and
    the byte-rangedness guard are in
    `Flapjack/Test/PanGlobalsNameByteRangedParity.lean`. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fresh_name_def"
  (names_as_string := [name]) (names_as_string_boundary := [name])]
def freshNameHOL (name : String) (names : List String) : String :=
  if name ∈ names then freshNameHOL (name ++ "'") names else name
termination_by 1 + maxNameLength names - name.length
decreasing_by
  simp_wf
  have hmem : name ∈ names := ‹name ∈ names›
  have hle := length_le_maxNameLength hmem
  have hone : ("'" : String).length = 1 := rfl
  rw [hone]
  omega

/-- Untagged helper: the source-shaped theorem that a name returned by the
    fresh-name search is not a member of the search list. This is the internal
    workhorse used by `globalNewMainName`; the `@[hol]`-tagged exact port of
    Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`) lives in the HOL
    proof counterpart `Flapjack/Pancake/Proofs/PanGlobals.lean`
    (`freshNameHOL_not_mem_hol`), per the HOL-script placement rule. -/
theorem freshNameHOL_not_mem (name : String) (names : List String) :
    freshNameHOL name names ∉ names := by
  fun_induction freshNameHOL name names with
  | case1 name names ih => exact ih
  | case2 name names => assumption

/-- Untagged helper: the source-shaped subset form corresponding to Cake's
    `fresh_name_correct'` (`pan_globalsProofScript.sml:1003`). The
    `@[hol]`-tagged exact port lives in the HOL proof counterpart
    `Flapjack/Pancake/Proofs/PanGlobals.lean`
    (`freshNameHOL_not_mem_of_subset_hol`), per the HOL-script placement rule. -/
theorem freshNameHOL_not_mem_of_subset (name : String) (names names' : List String)
    (hmem : freshNameHOL name names ∈ names')
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    False :=
  freshNameHOL_not_mem name names (hsubset _ hmem)

def globalShapeVal (context : GlobalPassContext α) : Shape → Exp α
  | .one => .const (context.fromNat 0)
  | .named _ => .const (context.fromNat 0)
  | .comb shapes => .rStruct (shapes.map (globalShapeVal context))
termination_by shape => sizeOf shape

def globalCompileProg [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape (globalCompileExp context value)
        (globalCompileProg context body)
  | .assign .global name value =>
      match lookupInfo name context.globals with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value)
      | none => .skip
  | .assign .local name value =>
      .assign .local name (globalCompileExp context value)
  | .primitive name operator arguments =>
      .primitive name operator (globalCompileExpList context arguments)
  | .store address value =>
      .store (globalCompileExp context address) (globalCompileExp context value)
  | .store32 address value =>
      .store32 (globalCompileExp context address) (globalCompileExp context value)
  | .storeByte address value =>
      .storeByte (globalCompileExp context address) (globalCompileExp context value)
  | .seq first second =>
      .seq (globalCompileProg context first) (globalCompileProg context second)
  | .ite condition thenBranch elseBranch =>
      .ite (globalCompileExp context condition)
        (globalCompileProg context thenBranch) (globalCompileProg context elseBranch)
  | .while condition body =>
      .while (globalCompileExp context condition) (globalCompileProg context body)
  | .call info function arguments =>
      let compiledArguments := globalCompileExpList context arguments
      match info with
        | none => .call none function compiledArguments
        | some (none, none) =>
            .call (some (none, none)) function compiledArguments
        | some (none, some (exception, handlerVar, handler)) =>
            .call (some (none, some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.local, name), none) =>
            .call (some (some (.local, name), none)) function compiledArguments
        | some (some (.local, name), some (exception, handlerVar, handler)) =>
            .call (some (some (.local, name), some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.global, name), none) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                .decCall "" shape function compiledArguments
                  (.store (.op .sub [.topAddr, .const address])
                    (.var .local ""))
            | none =>
                .call (some (none, none)) function compiledArguments
        | some (some (.global, name), some (exception, handlerVar, handler)) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                let compiledHandlerProgram := globalCompileProg context handler
                let names := handlerVar :: freeVarIds compiledHandlerProgram ++
                  compiledArguments.flatMap expLocalVars
                let resultName := freshNameHOL "" names
                /- Cake's `compile_def` uses the fixed seed `"vn'"` for its
                   handler flag, independently of the fresh result name. -/
                let flagName := freshNameHOL "vn'" (resultName :: names)
                let handlerBody :=
                  .seq compiledHandlerProgram
                    (.assign .local flagName (.const (context.fromNat 1)))
                let callInfo := some (some (.local, resultName),
                  some (exception, handlerVar, handlerBody))
                let callProgram : Prog α :=
                  .call callInfo function compiledArguments
                let storeAddress : Exp α :=
                  .op .sub [.topAddr, .const address]
                .dec resultName shape (globalShapeVal context shape)
                  (.dec flagName .one (.const (context.fromNat 0))
                    (.seq callProgram
                      (.ite (.var .local flagName) .skip
                        (.store storeAddress
                          (.var .local resultName)))))
            | none =>
                .call (some (none, some (exception, handlerVar,
                  globalCompileProg context handler))) function compiledArguments
  | .decCall name shape function arguments body =>
      .decCall name shape function (globalCompileExpList context arguments)
        (globalCompileProg context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (globalCompileExp context configuration)
        (globalCompileExp context configurationLength) (globalCompileExp context array)
        (globalCompileExp context arrayLength)
  | .raise exception value => .raise exception (globalCompileExp context value)
  | .return value => .return (globalCompileExp context value)
  | .shMemLoad size kind name address =>
      match kind, lookupInfo name context.globals with
      | .local, _ =>
          .shMemLoad size .local name (globalCompileExp context address)
      | .global, some (.one, globalAddress) =>
          let localName := name ++ globalApostrophes 1
          .dec name .one (globalCompileExp context address)
            (.dec localName .one (.const (context.fromNat 0))
              (.seq
                (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress])
                  (.var .local localName))))
      | .global, _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (globalCompileExp context address) (globalCompileExp context value)
  | program => program
termination_by program => sizeOf program

/-- Cake's `exp_ids_compile_globals`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:135`): compiling a
    program against the global context does not change its exception
    identifiers. -/
theorem globalCompileProg_expIds [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (program : Prog α) :
    expIds (globalCompileProg context program) = expIds program := by
  apply globalCompileProg.induct context
    (motive := fun program => expIds (globalCompileProg context program) = expIds program)
  all_goals intro <;> simp_all [globalCompileProg, expIds]

/-! The declaration-order and function-permutation helpers used by
    CakeML's `pan_to_target`.  Keeping these transformations separate from
    global allocation makes their name-preservation contracts reusable by the
    target-facing pipeline. -/

/-- Exact HOL port of Cake's `fperm_name_def`
    (`cakeml/pancake/pan_globalsScript.sml:184-189`):

    HOL `fperm_name f g h = if f = h then g else if g = h then f else h`.

    HOL's `fperm_name_def` carries no type annotation, so HOL generalizes the
    constant to the polymorphic `'a -> 'a -> 'a -> 'a` (HOL equality is defined
    on every type, with no typeclass side condition).  The faithful Lean port is
    therefore generic in `α` with the computable equality instance
    `[DecidableEq α]`, following the tagged generic-`α` HOL ports `afindi_def`
    (`Flapjack/Pancake/PanStructs.lean:20-21`) and `distinct_lists_def`
    (`Flapjack/Pancake/PanCommon.lean:24-25`).  The clauses, branch order, the
    comparison `=` and the result names match HOL exactly with no side
    condition.  The production `String`-specialized form is
    `globalRenameFunctionName` below; it is only a specialization of this
    polymorphic original, so it is deliberately left untagged.  Direct
    HOL/Lean edge-case fixtures: `scripts/hol-probes/pan_globals_fperm_name_probe.out`
    and `Flapjack/Test/PanGlobalsFpermNameParity.lean`. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fperm_name_def"]
def fpermName {α : Type u} [DecidableEq α] (f g h : α) : α :=
  if f = h then g else if g = h then f else h

/-- Production `String`-specialized form of Cake's polymorphic `fperm_name`
    (`fpermName` above): renaming swaps the `source` and `target` function
    names and leaves every other name unchanged.  Its body is exactly the
    reviewed `@[hol]` port `fpermName source target name`, so the executed
    compiler path runs the HOL-shaped definition. -/
-- FLAPJACK-SPECIFIC (`@[hol]` tag WITHDRAWN, documented mismatch, audit beads
-- `flapjack-dlc.52`/`flapjack-dlc.53`): HOL's `fperm_name_def`
-- (`pan_globalsScript.sml:184`) has no type annotation and HOL generalizes it
-- to the polymorphic `'a -> 'a -> 'a -> 'a`.  This declaration instantiates
-- `α := String` (`FunName`), so it is a specialization of the HOL constant
-- rather than the constant itself; the `names_as_string` qualifier does not
-- authorize specializing a polymorphic HOL name to `String`.  The exact
-- polymorphic port is `fpermName` above, which this declaration calls, so the
-- executed path uses the reviewed definition and only the type instantiation
-- remains Flapjack-specific.  Direct HOL/Lean edge-case fixtures:
-- `scripts/hol-probes/pan_globals_fperm_name_probe.out` and
-- `Flapjack/Test/PanGlobalsFpermNameParity.lean`.
def globalRenameFunctionName
    (source target name : FunName) : FunName :=
  fpermName source target name

/-! Counterparts of Cake's `fperm_name_cancel` and `fperm_name_cong`
    (`pan_globalsProofScript.sml:1622,1629`): the source/target renaming is an
    involutive bijection of function names. -/
theorem globalRenameFunctionName_cancel [BEq String] [LawfulBEq String]
    (source target name : FunName) :
    globalRenameFunctionName source target
        (globalRenameFunctionName source target name) = name := by
  unfold globalRenameFunctionName fpermName
  repeat' split <;> simp_all

theorem globalRenameFunctionName_cong [BEq String] [LawfulBEq String]
    (source target left right : FunName) :
    globalRenameFunctionName source target left =
        globalRenameFunctionName source target right ↔
      left = right := by
  constructor
  · intro h
    have := congrArg (globalRenameFunctionName source target) h
    rw [globalRenameFunctionName_cancel, globalRenameFunctionName_cancel] at this
    exact this
  · intro h
    rw [h]

/-! Flapjack-specific structural renaming corresponding clause-for-clause to
    Cake's `fperm_def` (`pan_globalsScript.sml:191-214`). The direct HOL/Lean
    fixture is `pan_globals_fperm_probe.out` /
    `Flapjack/Test/PanGlobalsFpermParity.lean`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.14`): the seven equations (`Dec`, `Seq`,
-- `If`, `While`, `Call` with its optional `rtyp`/handler, `DecCall`, default)
-- match `fperm_def` (`pan_globalsScript.sml:191-214`) clause-for-clause.
-- `fperm` recurses only on program structure and leaves every expression
-- payload untouched, so the body is a faithful transcription of HOL's
-- control flow. The mismatch is the imported program/expression carrier:
-- HOL `fperm` maps `'a prog`, whose `Const` is `'a word`, while `Prog α`
-- embeds the generic `Exp α` with `Const : α`, `Shape`'s `Named` is backed by
-- `String`, and StructName/FieldName/VarName/FunName/ExceptionId are `String`
-- rather than HOL `mlstring` (see the `Exp`/`prog` audit at
-- `Flapjack/Pancake/PanLang.lean:226-269`). Exact width-indexed carriers exist
-- (`ProgHOL`/`ExpHOL`/`ShapeHOL` under `Flapjack/Pancake/PanLang/`) but no
-- `fperm` port is built over them. `names_as_string` could only classify the
-- `call`/`decCall` `FunName` arguments (equality/map-key-only); it cannot
-- authorize the whole program carrier. The executed path is this production
-- definition, so the tag stays withdrawn until the exact-carrier
-- transformation is connected (bead `flapjack-6nn.3.1`; MlString carrier
-- `flapjack-pxn.18.3.5.8`). Direct HOL rows recursive_control / handler /
-- deccall / unchanged / fperm_done are in
-- `scripts/hol-probes/pan_globals_fperm_probe.out` and sampled by
-- `Flapjack/Test/PanGlobalsFpermParity.lean`.
def globalRenameProg
    (source target : FunName) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape value (globalRenameProg source target body)
  | .seq first second =>
      .seq (globalRenameProg source target first) (globalRenameProg source target second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (globalRenameProg source target thenBranch)
        (globalRenameProg source target elseBranch)
  | .while condition body =>
      .while condition (globalRenameProg source target body)
  | .call info function arguments =>
      let renamedInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar,
              globalRenameProg source target handler))
      .call renamedInfo (globalRenameFunctionName source target function) arguments
  | .decCall name shape function arguments body =>
      .decCall name shape (globalRenameFunctionName source target function) arguments
        (globalRenameProg source target body)
  | program => program
termination_by program => sizeOf program

/-! Flapjack-specific structural declaration renaming corresponding
    clause-for-clause to Cake's `fperm_decs_def` (`pan_globalsScript.sml:216`).
    The direct HOL/Lean fixture is `pan_globals_fperm_decs_probe.out` /
    `Flapjack/Test/PanGlobalsFpermDecsParity.lean`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.13`): the three equations (`[]`,
-- `Function fi::decs` renaming `fi.name` via `fperm_name` and `fi.body` via
-- `fperm`, other `d::decs` left in place) match `fperm_decs_def`
-- (`pan_globalsScript.sml:216-221`) clause-for-clause. The mismatch is the
-- imported declaration carrier: production `Decl α` contains `Prog α`/`Exp α`
-- (`Const : α`, String identifiers) and `Shape` (`Named : String`), whereas HOL
-- `decl` carries word-valued expressions with `mlstring` identifiers and
-- `shape`. Exact carriers (`DeclHOL`/`ProgHOL`/`ExpHOL`/`ShapeHOL` under
-- `Flapjack/Pancake/PanLang/`) exist but no `fperm_decs` port is built over
-- them. The `names_as_string` qualifier cannot repair the expression/Shape
-- carrier difference. The executed path is this production definition; keep
-- it untagged until the exact-carrier transformation is connected (bead
-- `flapjack-6nn.3.1`; MlString carrier `flapjack-pxn.18.3.5.8`). Direct HOL
-- rows mixed / empty / singleton_nonfunction are in
-- `scripts/hol-probes/pan_globals_fperm_decs_probe.out` and sampled by
-- `Flapjack/Test/PanGlobalsFpermDecsParity.lean`.
def globalRenameDecls
    (source target : FunName) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with
        name := globalRenameFunctionName source target declaration.name
        body := globalRenameProg source target declaration.body } ::
        globalRenameDecls source target declarations
  | declaration :: declarations =>
      declaration :: globalRenameDecls source target declarations
termination_by declarations => sizeOf declarations

/-! Counterpart of Cake's `fperm_decs_append`
    (`pan_globalsProofScript.sml:1663`): renaming distributes over
    declaration-list concatenation. -/
theorem globalRenameDecls_append [BEq String] (source target : FunName)
    (declarations rest : List (Decl α)) :
    globalRenameDecls source target (declarations ++ rest) =
      globalRenameDecls source target declarations ++
        globalRenameDecls source target rest := by
  induction declarations with
  | nil => simp [globalRenameDecls]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalRenameDecls, ih]

/-! Counterpart of Cake's `functions_fperm_decs`
    (`pan_globalsProofScript.sml:1701`): the function table of a renamed
    declaration list is the renamed function table. -/
theorem functions_globalRenameDecls [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    functions (globalRenameDecls source target declarations) =
      (functions declarations).map (fun entry =>
        (globalRenameFunctionName source target entry.1, entry.2.1,
          globalRenameProg source target entry.2.2.1, entry.2.2.2)) := by
  induction declarations with
  | nil => simp [globalRenameDecls, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalRenameDecls, functions, functionEntries, ih]

theorem nodup_globalRenameFunctionName_map [BEq String] [LawfulBEq String]
    (source target : FunName) (names : List FunName) (hnodup : names.Nodup) :
    (names.map (globalRenameFunctionName source target)).Nodup := by
  induction names with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup ⊢
      obtain ⟨hhead, htail⟩ := hnodup
      refine ⟨?_, ih htail⟩
      intro hmem
      obtain ⟨name, hname, heq⟩ := List.mem_map.mp hmem
      have hnamehead : name = head :=
        (globalRenameFunctionName_cong source target name head).mp heq
      rw [hnamehead] at hname
      exact hhead hname

theorem globalRenameDecls_names_nodup [BEq String] [LawfulBEq String]
    (source target : FunName) (declarations : List (Decl α))
    (hnodup : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions (globalRenameDecls source target declarations)).map
        (fun entry => entry.1)).Nodup := by
  rw [functions_globalRenameDecls, List.map_map]
  have hcomp :
      ((fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
          entry.1) ∘
        (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
          (globalRenameFunctionName source target entry.1, entry.2.1,
            globalRenameProg source target entry.2.2.1, entry.2.2.2))) =
      (globalRenameFunctionName source target) ∘
        (fun entry : FunName × List (VarName × Shape) × Prog α × Shape =>
          entry.1) := by
    funext entry
    rfl
  rw [hcomp, ← List.map_map]
  exact nodup_globalRenameFunctionName_map source target _ hnodup

def globalFunctionNames : List (Decl α) → List FunName
  | [] => []
  | .function declaration :: declarations =>
      declaration.name :: globalFunctionNames declarations
  | _ :: declarations => globalFunctionNames declarations
termination_by declarations => sizeOf declarations

/-! Counterpart of Cake's `exceptions_append`
    (`pan_globalsProofScript.sml:2507`): the exception table distributes over
    list append. -/
theorem exceptionEntries_cons (declaration : Decl α) (declarations : List (Decl α)) :
    exceptionEntries (declaration :: declarations) =
      (match declaration with
       | .exnDecl exception shape =>
           (exception, shape) :: exceptionEntries declarations
       | _ => exceptionEntries declarations) := by
  cases declaration <;> rw [exceptionEntries.eq_def]

theorem exceptionEntries_append (declarations rest : List (Decl α)) :
    exceptionEntries (declarations ++ rest) =
      exceptionEntries declarations ++ exceptionEntries rest := by
  induction declarations with
  | nil => simp [exceptionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [exceptionEntries_cons, ih]

def globalDeclsFilter (predicate : Decl α → Bool) : List (Decl α) → List (Decl α)
  | [] => []
  | declaration :: declarations =>
      if predicate declaration then
        declaration :: globalDeclsFilter predicate declarations
      else globalDeclsFilter predicate declarations
termination_by declarations => sizeOf declarations

theorem globalDeclsFilter_all (predicate : Decl α → Bool)
    (declarations : List (Decl α)) :
    (globalDeclsFilter predicate declarations).all predicate = true := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]; simp [hpred, ih]
      · rw [if_neg hpred]; exact ih

theorem globalDeclsFilter_eq_nil_of_all_not (predicate : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all (fun declaration => !predicate declaration) = true) :
    globalDeclsFilter predicate declarations = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · simp [hpred] at hhead
      · rw [if_neg hpred]; exact ih htail

def globalDeclIsName : Decl α → Bool
  | .name _ _ => true
  | _ => false

def globalDeclIsException : Decl α → Bool
  | .exnDecl _ _ => true
  | _ => false

def globalDeclIsGlobal : Decl α → Bool
  | .decl _ _ _ => true
  | _ => false

def globalDeclIsFunction : Decl α → Bool
  | .function _ => true
  | _ => false

/-! Counterpart of Cake's `EVERY_fperm_decs`
    (`pan_globalsProofScript.sml:2436`): if a predicate holds on every
    non-function declaration and on every renamed function declaration, then
    it holds on every declaration produced by the renaming pass. -/
theorem globalRenameDecls_all_of_predicate [BEq String]
    (source target : FunName) (predicate : Decl α → Bool)
    (declarations : List (Decl α))
    (hother : declarations.all
      (fun declaration => globalDeclIsFunction declaration || predicate declaration) = true)
    (hfunction : declarations.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              name := globalRenameFunctionName source target function.name
              body := globalRenameProg source target function.body })
        | _ => true) = true) :
    (globalRenameDecls source target declarations).all predicate = true := by
  induction declarations with
  | nil => simp [globalRenameDecls]
  | cons declaration declarations ih =>
      have hotherTail : declarations.all
          (fun declaration =>
            globalDeclIsFunction declaration || predicate declaration) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hother
        exact hother.2
      have hfunctionTail : declarations.all
          (fun declaration => match declaration with
            | .function function =>
                predicate (.function { function with
                  name := globalRenameFunctionName source target function.name
                  body := globalRenameProg source target function.body })
            | _ => true) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hfunction
        exact hfunction.2
      have ih' := ih hotherTail hfunctionTail
      have hotherHead := by
        simp only [List.all_cons, Bool.and_eq_true] at hother
        exact hother.1
      have hfunctionHead := by
        simp only [List.all_cons, Bool.and_eq_true] at hfunction
        exact hfunction.1
      cases declaration with
      | function function =>
          simp only [globalRenameDecls, List.all_cons, Bool.and_eq_true]
          exact ⟨hfunctionHead, ih'⟩
      | decl shape name value =>
          simp only [globalRenameDecls, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih'⟩
          simp [globalDeclIsFunction] at hotherHead
          exact hotherHead
      | exnDecl exception shape =>
          simp only [globalRenameDecls, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih'⟩
          simp [globalDeclIsFunction] at hotherHead
          exact hotherHead
      | name struct fields =>
          simp only [globalRenameDecls, List.all_cons, Bool.and_eq_true]
          refine ⟨?_, ih'⟩
          simp [globalDeclIsFunction] at hotherHead
          exact hotherHead

/-! Direct source-shaped counterparts of the declaration predicates from
    `panLangScript.sml:234-249`.  The global-pass predicates above are kept
    as its existing pass-facing names; these names retain the source API. -/
def isDecl : Decl α → Bool
  | .decl _ _ _ => true
  | _ => false

def isExnDecl : Decl α → Bool
  | .exnDecl _ _ => true
  | _ => false

def isName : Decl α → Bool
  | .name _ _ => true
  | _ => false

def sizeOfEids : List (Decl α) → Nat
  | [] => 0
  | declaration :: declarations =>
      if isExnDecl declaration then
        1 + sizeOfEids declarations
      else
        sizeOfEids declarations
termination_by declarations => sizeOf declarations

/-! `pan_simp` maps every function declaration to a function declaration and
    leaves every other declaration unchanged, so it preserves the exception
    identifier count.  This mirrors Cake's `size_of_eids_compile_eq`. -/

theorem isExnDecl_panSimpDecl (declaration : Decl α) :
    isExnDecl (panSimpDecl declaration) = isExnDecl declaration := by
  cases declaration <;> rfl

theorem sizeOfEids_map_panSimpDecl (declarations : List (Decl α)) :
    sizeOfEids (declarations.map panSimpDecl) = sizeOfEids declarations := by
  induction declarations with
  | nil => rw [List.map_nil, sizeOfEids.eq_def]
  | cons declaration declarations ih =>
      rw [List.map_cons, sizeOfEids.eq_def, sizeOfEids.eq_def]
      simp [isExnDecl_panSimpDecl, ih]

theorem sizeOfEids_panSimpDecls (declarations : List (Decl α)) :
    sizeOfEids (panSimpDecls declarations) = sizeOfEids declarations := by
  rw [panSimpDecls_eq_map]
  exact sizeOfEids_map_panSimpDecl declarations

/-- The cons equation for `sizeOfEids`, stated as an `if` on `isExnDecl`. -/
theorem sizeOfEids_cons (declaration : Decl α) (declarations : List (Decl α)) :
    sizeOfEids (declaration :: declarations) =
      if isExnDecl declaration then 1 + sizeOfEids declarations
      else sizeOfEids declarations := by
  cases declaration <;> rw [sizeOfEids.eq_def] <;> simp [isExnDecl]

/-- Cake's `size_of_eids_structs_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:305`): the `pan_structs`
    pass keeps exactly the exception declarations, so the exception-identifier
    count is unchanged. -/
theorem sizeOfEids_structCompileDecls [BEq String]
    (declarations : List (Decl α)) (context : StructPassContext) :
    sizeOfEids (structCompileDecls declarations context).1 =
      sizeOfEids declarations := by
  induction declarations generalizing context with
  | nil => simp [structCompileDecls]
  | cons declaration declarations ih =>
      cases declaration with
      | decl shape name value =>
          simp only [structCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih _
      | function fn =>
          simp only [structCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih context
      | exnDecl exception shape =>
          simp only [structCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih context
      | name structName fields =>
          simp only [structCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih context

/-- Cake's `size_of_eids_structs_compile_eq`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:305`). -/
theorem sizeOfEids_structCompileTop (declarations : List (Decl α)) :
    sizeOfEids (structCompileTop declarations) = sizeOfEids declarations := by
  unfold structCompileTop
  dsimp only
  exact sizeOfEids_structCompileDecls declarations
    (structGetNames { structs := [], locals := [], globals := [] } declarations)

/-! Flapjack-specific source-shaped counterpart (NOT an exact HOL port) of Cake's `resort_decls_def` (`pan_globalsScript.sml:179`):
    declarations are regrouped as names, exceptions, value declarations, and
    functions, in that order.  `globalDeclIsName`/`globalDeclIsException`/
    `globalDeclIsGlobal`/`globalDeclIsFunction` are the HOL `is_name`/
    `is_exn_decl`/`is_decl`/`is_function` predicates. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.16`): the constructor filtering and
-- output order (`FILTER is_name ++ FILTER is_exn_decl ++ FILTER is_decl ++
-- FILTER is_function`) match `resort_decls_def` (`pan_globalsScript.sml:179`)
-- exactly, and `globalDeclIsName`/`globalDeclIsException`/`globalDeclIsGlobal`/
-- `globalDeclIsFunction` are the HOL `is_name`/`is_exn_decl`/`is_decl`/
-- `is_function` predicates. The mismatch is the executed `Decl α` carrier: it
-- is not HOL's `DeclHOL width`. Production `Exp α` stores `α` directly in
-- `Const`, HOL `ExpHOL width` stores `BitVec width` (`'a word`); names and
-- `Shape` also use production `String` instead of HOL `mlstring`. The
-- `(names_as_string := ...)` qualifier only accounts for the last difference,
-- so it cannot justify this tag. Exact carriers (`DeclHOL`/`ProgHOL`/`ExpHOL`/
-- `ShapeHOL`) exist under `Flapjack/Pancake/PanLang/` but this transformation
-- runs on the production carrier. Keep untagged until an exact-carrier
-- definition is connected to the executed path; tracked by bead
-- `flapjack-6nn.3.1` (MlString carrier `flapjack-pxn.18.3.5.8`). Clause/order
-- evidence: `scripts/hol-probes/pan_globals_resort_decls_probe.out` and
-- `Flapjack/Test/PanGlobalsResortDeclsParity.lean`.
def globalResortDecls (declarations : List (Decl α)) : List (Decl α) :=
  globalDeclsFilter globalDeclIsName declarations ++
    globalDeclsFilter globalDeclIsException declarations ++
    globalDeclsFilter globalDeclIsGlobal declarations ++
    globalDeclsFilter globalDeclIsFunction declarations

/-! Flapjack-specific production counterpart of Cake's `new_main_name_def`
    (`pan_globalsScript.sml:224`): it calls `freshNameHOL "main"` on the
    function names projected from the declaration list. The direct behavior
    fixture is `scripts/hol-probes/pan_globals_new_main_name_probe.out`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port; @[hol] tag WITHDRAWN, documented
-- mismatch, audit bead `flapjack-dlc.15`): the body
-- `freshNameHOL "main" (globalFunctionNames declarations)` matches HOL
-- `new_main_name decls = fresh_name «main» (MAP FST (functions decls))`
-- (`pan_globalsScript.sml:224`) once the production projections
-- `globalFunctionNames`/`freshNameHOL` stand for HOL `functions`/`fresh_name`.
-- The mismatch is the input carrier: this consumes generic production
-- `List (Decl α)`, whose expressions carry `Const : α` and whose identifiers
-- and `Shape` are `String`; HOL `new_main_name` consumes word-valued
-- declarations with `Const : 'a word` and `mlstring` identifiers. Exact
-- carriers (`DeclHOL`/`ProgHOL`/`ExpHOL`/`ShapeHOL`) exist under
-- `Flapjack/Pancake/PanLang/`, but no `new_main_name` port runs over them.
-- `names_as_string` and the generated-name boundary witness only address the
-- String/mlstring name difference, not this input-carrier mismatch, so the tag
-- stays withdrawn pending the exact-carrier replacement (bead `flapjack-6nn.3.1`;
-- MlString carrier `flapjack-pxn.18.3.5.8`). Direct HOL rows empty /
-- two_collisions / mixed / absent are in
-- `scripts/hol-probes/pan_globals_new_main_name_probe.out` and sampled by
-- `Flapjack/Test/PanGlobalsNewMainNameParity.lean`.
def globalNewMainName (declarations : List (Decl α)) : FunName :=
  freshNameHOL "main" (globalFunctionNames declarations)

/-! Flapjack-specific freshness property for the synthesized `main` entry-point
    name. The proof-level statement is over generic production `Decl α`, while
    HOL `new_main_name_correct` ranges over word-valued declarations; see the
    exact-carrier replacement bead `flapjack-6nn.3.1`. -/
theorem globalNewMainName_not_mem
    (declarations : List (Decl α)) :
    globalNewMainName declarations ∉ globalFunctionNames declarations :=
  freshNameHOL_not_mem "main" (globalFunctionNames declarations)

/-! ## `holMlStringWitness_*`: same-module byte-boundary witnesses

The `names_as_string` qualifier (`Flapjack/HolRef.lean`) records Lean `String`
fields standing for HOL `mlstring` names.  Declarations tagged with it are
expected to carry a checked `holMlStringWitness_*` witness **in the same
module**, establishing the byte-range condition of the generated names.  HOL
`mlstring` is a list of 8-bit characters, so a generated name must never contain
a code point `>= 256`; `Flapjack.Pancake.PanLang.NameRanged` is exactly that
condition (and is definitionally the parser-chain `StringByteRanged`).

The witnesses below are premise-aware: `freshNameHOL`, `globalFreshNameAux`, and
`globalFreshName` may append apostrophes to an input name, so they preserve
byte-rangedness only when the input name is byte-ranged. `globalNewMainName`
starts from the literal `"main"` and therefore needs no premise. The witness
for `freshNameHOL` supports its names-only `names_as_string` tag; the
`globalNewMainName` witness remains a Flapjack production byte-safety fact and
does not establish that its generic declaration carrier matches HOL. -/

private theorem nameRanged_append {s₁ s₂ : String}
    (h₁ : Flapjack.Pancake.PanLang.NameRanged s₁)
    (h₂ : Flapjack.Pancake.PanLang.NameRanged s₂) :
    Flapjack.Pancake.PanLang.NameRanged (s₁ ++ s₂) := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem nameRanged_quote : Flapjack.Pancake.PanLang.NameRanged "'" := by
  unfold Flapjack.Pancake.PanLang.NameRanged
  decide

private theorem globalApostrophes_nameRanged (count : Nat) :
    Flapjack.Pancake.PanLang.NameRanged (globalApostrophes count) := by
  induction count with
  | zero =>
      simp [globalApostrophes, Flapjack.Pancake.PanLang.NameRanged]
  | succ count ih =>
      rw [globalApostrophes]
      exact nameRanged_append nameRanged_quote ih

/-- Witness: the source-shaped HOL `fresh_name` port preserves byte-rangedness
    of the input name (it only appends apostrophes). -/
theorem holMlStringWitness_freshNameHOL (name : String) (names : List String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) := by
  fun_induction freshNameHOL name names with
  | case1 name names ih =>
      exact ih (nameRanged_append h nameRanged_quote)
  | case2 name names => exact h

/-- Witness: the fuel-bounded production fresh-name search preserves
    byte-rangedness of the input name. -/
theorem holMlStringWitness_globalFreshNameAux [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String)
    (candidate fuel : Nat) :
    Flapjack.Pancake.PanLang.NameRanged
      (globalFreshNameAux name names candidate fuel) := by
  induction fuel generalizing candidate with
  | zero =>
      rw [globalFreshNameAux]
      exact nameRanged_append h (globalApostrophes_nameRanged candidate)
  | succ fuel ih =>
      rw [globalFreshNameAux]
      by_cases hc : names.contains (name ++ globalApostrophes candidate) = true
      · rw [if_pos hc]
        exact ih (candidate + 1)
      · rw [if_neg hc]
        exact nameRanged_append h (globalApostrophes_nameRanged candidate)

/-- Witness: production `globalFreshName` preserves byte-rangedness of the input
    name. -/
theorem holMlStringWitness_globalFreshName [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String) :
    Flapjack.Pancake.PanLang.NameRanged (globalFreshName name names) :=
  holMlStringWitness_globalFreshNameAux name h names 0 names.length

/-- Production safety witness: `globalNewMainName` outputs a byte-ranged
    string because its seed is the literal `"main"`. This is not evidence that
    the generic declaration input is HOL's word-valued carrier. -/
theorem holMlStringWitness_globalNewMainName (declarations : List (Decl α)) :
    Flapjack.Pancake.PanLang.NameRanged (globalNewMainName declarations) := by
  unfold globalNewMainName
  exact holMlStringWitness_freshNameHOL "main" (globalFunctionNames declarations)
    (by unfold Flapjack.Pancake.PanLang.NameRanged; decide)


/-! Flapjack-specific source-shaped counterpart (NOT an exact HOL port) of Cake's `dec_shapes_def` (`pan_globalsScript.sml:228`): the
    shape projection skips function, name, and exception declarations and
    keeps the shape of each value declaration, in order. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): source review for bead
-- `flapjack-dlc.12`. HOL `dec_shapes_def` (`pan_globalsScript.sml:228-234`) is
-- the five-clause projection `Function _::ds |-> dec_shapes ds`,
-- `Decl sh _ _::ds |-> sh::dec_shapes ds`, `Name _ _::ds |-> dec_shapes ds`,
-- `ExnDecl _ _::ds |-> dec_shapes ds`, `[] |-> []`; the Lean clauses match that
-- order and shape selection clause-for-clause. The mismatch is the imported
-- declaration carrier: the executed function consumes production `Decl α`
-- (whose `Exp α.Const` payload is a generic word `α`, not HOL's
-- `ExpHOL width.Const : 'a word` fixed width, and whose identifiers/`Shape`
-- are `String`, not HOL `mlstring`), so the statement ranges over inputs HOL
-- cannot represent. `(names_as_string := ...)` cannot authorize a whole
-- declaration carrier; no byte witness applies. Keep untagged until an
-- exact-carrier definition is connected to the executed path; tracked by
-- `flapjack-6nn.3.1` with `flapjack-pxn.18.3.5.8`. Clause/order evidence:
-- `scripts/hol-probes/pan_globals_dec_shapes_probe.out` rows `empty=[]`,
-- `mixed=[Comb [One; Named «S»]; One]`, `functions_only=[]`, sampled by
-- `Flapjack/Test/PanGlobalsDecShapesParity.lean`.
def globalDeclShapes : List (Decl α) → List Shape
  | [] => []
  | .function _ :: declarations => globalDeclShapes declarations
  | .decl shape _ _ :: declarations => shape :: globalDeclShapes declarations
  | .name _ _ :: declarations => globalDeclShapes declarations
  | .exnDecl _ _ :: declarations => globalDeclShapes declarations
termination_by declarations => sizeOf declarations

/-! Shape-projection counterparts of Cake's `dec_shapes` lemmas from
    `pan_globalsProofScript.sml:2328-2361`.  The global pass reassociates and
    filters declarations, and these lemmas record that the shape projection is
    unchanged by that reorganisation. -/

theorem globalDeclShapes_nil : globalDeclShapes ([] : List (Decl α)) = [] := by
  rw [globalDeclShapes.eq_def]

theorem globalDeclShapes_cons (declaration : Decl α) (declarations : List (Decl α)) :
    globalDeclShapes (declaration :: declarations) =
      (match declaration with
       | .decl shape _ _ => shape :: globalDeclShapes declarations
       | _ => globalDeclShapes declarations) := by
  cases declaration <;> rw [globalDeclShapes.eq_def]

theorem globalDeclShapes_append (declarations rest : List (Decl α)) :
    globalDeclShapes (declarations ++ rest) =
      globalDeclShapes declarations ++ globalDeclShapes rest := by
  induction declarations with
  | nil => rw [List.nil_append, globalDeclShapes_nil, List.nil_append]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalDeclShapes_cons, ih]

/-- Cake's `dec_shapes_compile_prog`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:241`): `pan_simp` only
    rewrites function bodies, so the collected declaration shapes are
    unchanged. -/
theorem globalDeclShapes_panSimpDecls (declarations : List (Decl α)) :
    globalDeclShapes (panSimpDecls declarations) = globalDeclShapes declarations := by
  rw [panSimpDecls_eq_map]
  induction declarations with
  | nil => simp [globalDeclShapes_nil]
  | cons declaration declarations ih =>
      cases declaration <;> simp [panSimpDecl, globalDeclShapes_cons, ih]

/-- Cake's `function_names_compile_prog`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:248`): `pan_simp` only
    rewrites function bodies, so the function-name table is unchanged. -/
theorem functions_names_panSimpDecls (declarations : List (Decl α)) :
    (functions (panSimpDecls declarations)).map Prod.fst =
      (functions declarations).map Prod.fst := by
  rw [functions_panSimpDecls, List.map_map]
  rfl

/-- Cake's `no_names_compile_prog`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:318`): `pan_simp` keeps
    the restriction that no declaration is a structure name, matching
    `is_function ∨ is_decl ∨ is_exn_decl`. -/
theorem panSimpDecls_all_not_name (declarations : List (Decl α))
    (hall : declarations.all (fun declaration => !isName declaration) = true) :
    (panSimpDecls declarations).all (fun declaration => !isName declaration) =
      true := by
  rw [panSimpDecls_eq_map]
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hall ⊢
      obtain ⟨hhead, htail⟩ := hall
      cases declaration <;> simp_all [panSimpDecl, isName]

theorem globalDeclShapes_of_functions (declarations : List (Decl α))
    (hfunctions : ∀ declaration ∈ declarations, globalDeclIsFunction declaration = true) :
    globalDeclShapes declarations = [] := by
  induction declarations with
  | nil => rw [globalDeclShapes.eq_def]
  | cons declaration declarations ih =>
      have hdecl : globalDeclIsFunction declaration = true :=
        hfunctions declaration (by simp)
      have hrest : ∀ d ∈ declarations, globalDeclIsFunction d = true :=
        fun d hd => hfunctions d (by simp [hd])
      cases declaration <;> simp_all [globalDeclIsFunction, globalDeclShapes_cons]

theorem mem_globalDeclsFilter {predicate : Decl α → Bool} {declaration : Decl α}
    {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    predicate declaration = true := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact hpred
        · exact ih htail
      · simp [hpred] at hmem
        exact ih hmem

theorem globalDeclShapes_globalDeclsFilter_not_function (declarations : List (Decl α)) :
    globalDeclShapes
        (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
          declarations) =
      globalDeclShapes declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def, globalDeclShapes.eq_def]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      cases declaration <;> simp only [globalDeclIsFunction] at ih ⊢ <;> simp [globalDeclShapes_cons, ih]

theorem globalDeclShapes_globalDeclsFilter_function (declarations : List (Decl α)) :
    globalDeclShapes (globalDeclsFilter globalDeclIsFunction declarations) = [] :=
  globalDeclShapes_of_functions _
    (fun _ hmem => mem_globalDeclsFilter (predicate := globalDeclIsFunction) hmem)

theorem globalDeclShapes_globalDeclsFilter_name (declarations : List (Decl α)) :
    globalDeclShapes (globalDeclsFilter globalDeclIsName declarations) = [] := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def, globalDeclShapes.eq_def]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      cases declaration <;> simp only [globalDeclIsName] at ih ⊢ <;> simp [globalDeclShapes_cons, ih]

theorem globalDeclShapes_globalDeclsFilter_exception (declarations : List (Decl α)) :
    globalDeclShapes (globalDeclsFilter globalDeclIsException declarations) = [] := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def, globalDeclShapes.eq_def]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      cases declaration <;> simp only [globalDeclIsException] at ih ⊢ <;> simp [globalDeclShapes_cons, ih]

theorem globalDeclShapes_globalDeclsFilter_global (declarations : List (Decl α)) :
    globalDeclShapes (globalDeclsFilter globalDeclIsGlobal declarations) =
      globalDeclShapes declarations := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def, globalDeclShapes.eq_def]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      cases declaration <;> simp only [globalDeclIsGlobal] at ih ⊢ <;> simp [globalDeclShapes_cons, ih]

theorem globalDeclShapes_globalResortDecls (declarations : List (Decl α)) :
    globalDeclShapes (globalResortDecls declarations) =
      globalDeclShapes declarations := by
  rw [globalResortDecls, globalDeclShapes_append, globalDeclShapes_append,
    globalDeclShapes_append, globalDeclShapes_globalDeclsFilter_name,
    globalDeclShapes_globalDeclsFilter_exception,
    globalDeclShapes_globalDeclsFilter_global,
    globalDeclShapes_globalDeclsFilter_function]
  simp

/-! Counterpart of Cake's `exceptions_FILTER_is_function`
    (`pan_globalsProofScript.sml:2515`). -/
theorem exceptionEntries_globalDeclsFilter_of_true
    {predicate : Decl α → Bool}
    (hexn : ∀ exception shape, predicate (.exnDecl exception shape) = true)
    (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter predicate declarations) =
      exceptionEntries declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter, exceptionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]
      · rw [if_neg hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]

theorem exceptionEntries_globalDeclsFilter_of_false
    {predicate : Decl α → Bool}
    (hexn : ∀ exception shape, predicate (.exnDecl exception shape) = false)
    (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter predicate declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, exceptionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]
      · rw [if_neg hpred]
        cases declaration <;> simp_all

theorem exceptionEntries_filter_function (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_not_function (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
      declarations) = exceptionEntries declarations :=
  exceptionEntries_globalDeclsFilter_of_true (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_exception (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsException declarations) =
      exceptionEntries declarations :=
  exceptionEntries_globalDeclsFilter_of_true (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_name (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsName declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_global (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsGlobal declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

/-! Predicate helpers behind Cake's `not_is_function`
    (`pan_globalsProofScript.sml:2527`): name, value, and exception
    declarations are never function declarations. The exact HOL-shaped
    conjunction is the `@[hol]`-tagged `not_is_function` in the proof
    counterpart `Flapjack.Pancake.Proofs.PanGlobals`. -/
theorem isName_not_function (declaration : Decl α) :
    isName declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isName, globalDeclIsFunction]

theorem isDecl_not_function (declaration : Decl α) :
    isDecl declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isDecl, globalDeclIsFunction]

theorem isExnDecl_not_function (declaration : Decl α) :
    isExnDecl declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isExnDecl, globalDeclIsFunction]

/-! Counterparts of Cake's `functions_filter_nil`, `functions_FILTER_exn_decl`,
    and `functions_FILTER_is_name` (`pan_globalsProofScript.sml:2967, 2042,
    2049`): filtering by a predicate that excludes function declarations
    leaves an empty function table. -/
theorem functions_globalDeclsFilter_nil_of_predicate
    (predicate : Decl α → Bool)
    (hpredicate : ∀ declaration, predicate declaration = true →
      globalDeclIsFunction declaration = false)
    (declarations : List (Decl α)) :
    functions (globalDeclsFilter predicate declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, functions, functionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        have hnotfun := hpredicate declaration hpred
        cases declaration <;> simp [globalDeclIsFunction] at hnotfun
        all_goals simp [functions, functionEntries]
        all_goals exact ih
      · rw [if_neg hpred]
        exact ih

theorem functions_globalDeclsFilter_not_function (declarations : List (Decl α)) :
    functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _
    (fun declaration hpred => by simpa using hpred) declarations

theorem functions_globalDeclsFilter_exnDecl (declarations : List (Decl α)) :
    functions (globalDeclsFilter isExnDecl declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ isExnDecl_not_function declarations

theorem functions_globalDeclsFilter_isName (declarations : List (Decl α)) :
    functions (globalDeclsFilter isName declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ isName_not_function declarations

theorem functions_globalDeclsFilter_isDecl (declarations : List (Decl α)) :
    functions (globalDeclsFilter isDecl declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ isDecl_not_function declarations

theorem globalDeclIsGlobal_not_function (declaration : Decl α) :
    globalDeclIsGlobal declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsGlobal, globalDeclIsFunction]

theorem globalDeclIsName_not_function (declaration : Decl α) :
    globalDeclIsName declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsName, globalDeclIsFunction]

theorem globalDeclIsException_not_function (declaration : Decl α) :
    globalDeclIsException declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsException, globalDeclIsFunction]

theorem functions_globalDeclsFilter_globalName (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsName declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsName_not_function
    declarations

theorem functions_globalDeclsFilter_globalException (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsException declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsException_not_function
    declarations

theorem functions_globalDeclsFilter_isGlobal (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsGlobal declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsGlobal_not_function
    declarations

theorem functions_globalDeclsFilter_isFunction (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsFunction declarations) =
      functions declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter, functions, functionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : globalDeclIsFunction declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [globalDeclIsFunction, functions, functionEntries]
      · rw [if_neg hpred]
        cases declaration <;> simp_all [globalDeclIsFunction, functions, functionEntries]

theorem functions_append (declarations rest : List (Decl α)) :
    functions (declarations ++ rest) = functions declarations ++ functions rest := by
  induction declarations with
  | nil => simp [functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [functions, functionEntries, ih]

/-! Counterpart of Cake's `resort_decls_preserve_functions`
    (`pan_globalsProofScript.sml:2055`): resorting declarations leaves the
    function table unchanged. -/
theorem functions_globalResortDecls (declarations : List (Decl α)) :
    functions (globalResortDecls declarations) = functions declarations := by
  rw [globalResortDecls, functions_append, functions_append, functions_append,
    functions_globalDeclsFilter_globalName,
    functions_globalDeclsFilter_globalException,
    functions_globalDeclsFilter_isGlobal, List.nil_append, List.nil_append,
    List.nil_append, functions_globalDeclsFilter_isFunction]

/-! Counterpart of Cake's `fperm_decs_decls`
    (`pan_globalsProofScript.sml:2023`): renaming leaves a declaration list
    with no function declarations unchanged. -/
theorem globalRenameDecls_eq_self_of_no_functions [BEq String]
    (source target : FunName) (declarations : List (Decl α))
    (hnone : declarations.all
      (fun declaration => !globalDeclIsFunction declaration) = true) :
    globalRenameDecls source target declarations = declarations := by
  induction declarations with
  | nil => simp [globalRenameDecls]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hnone
      obtain ⟨hhead, htail⟩ := hnone
      have hnotfun : globalDeclIsFunction declaration = false := by
        simpa using hhead
      cases declaration with
      | function declaration =>
          simp [globalDeclIsFunction] at hnotfun
      | decl shape name value =>
          simp [globalRenameDecls, ih htail]
      | exnDecl exception shape =>
          simp [globalRenameDecls, ih htail]
      | name struct fields =>
          simp [globalRenameDecls, ih htail]

/-! Counterpart of Cake's `fperm_decs_FILTER_is_function`
    (`pan_globalsProofScript.sml:2032`): renaming commutes with filtering to
    the function declarations. -/
theorem globalRenameDecls_filter_function [BEq String]
    (source target : FunName) (declarations : List (Decl α)) :
    globalRenameDecls source target
        (globalDeclsFilter globalDeclIsFunction declarations) =
      globalDeclsFilter globalDeclIsFunction
        (globalRenameDecls source target declarations) := by
  induction declarations with
  | nil => simp [globalDeclsFilter, globalRenameDecls]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : globalDeclIsFunction declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | function declaration =>
            simp [globalRenameDecls, globalDeclsFilter, globalDeclIsFunction, ih]
        | decl shape name value => simp [globalDeclIsFunction] at hpred
        | exnDecl exception shape => simp [globalDeclIsFunction] at hpred
        | name struct fields => simp [globalDeclIsFunction] at hpred
      · rw [if_neg hpred]
        cases declaration <;>
          simp_all [globalRenameDecls, globalDeclsFilter, globalDeclIsFunction]

/-! Counterpart of Cake's `FILTER_decs_fperm_decs`
    (`pan_globalsProofScript.sml:2832`): renaming commutes with filtering to
    the non-function declarations. -/
theorem globalDeclsFilter_cons_true (predicate : Decl α → Bool)
    (declaration : Decl α) (declarations : List (Decl α))
    (hkeep : predicate declaration = true) :
    globalDeclsFilter predicate (declaration :: declarations) =
      declaration :: globalDeclsFilter predicate declarations := by
  simp [globalDeclsFilter, hkeep]

theorem globalDeclsFilter_cons_false (predicate : Decl α → Bool)
    (declaration : Decl α) (declarations : List (Decl α))
    (hdrop : predicate declaration = false) :
    globalDeclsFilter predicate (declaration :: declarations) =
      globalDeclsFilter predicate declarations := by
  simp [globalDeclsFilter, hdrop]

theorem globalRenameDecls_filter_not_function [BEq String]
    (source target : FunName) (declarations : List (Decl α)) :
    globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        (globalRenameDecls source target declarations) =
      globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
        declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter, globalRenameDecls]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalRenameDecls]
          rw [globalDeclsFilter_cons_false _ _ _
              (by simp [globalDeclIsFunction]),
            globalDeclsFilter_cons_false _ _ _
              (by simp [globalDeclIsFunction])]
          exact ih
      | decl shape name value =>
          simp only [globalRenameDecls]
          rw [globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction]),
            globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction])]
          rw [ih]
      | exnDecl exception shape =>
          simp only [globalRenameDecls]
          rw [globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction]),
            globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction])]
          rw [ih]
      | name struct fields =>
          simp only [globalRenameDecls]
          rw [globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction]),
            globalDeclsFilter_cons_true _ _ _
              (by simp [globalDeclIsFunction])]
          rw [ih]

def globalFindFunction [BEq String] (name : FunName) :
    List (Decl α) → Option (FunDecl α)
  | [] => none
  | .function declaration :: declarations =>
      if declaration.name == name then some declaration
      else globalFindFunction name declarations
  | _ :: declarations => globalFindFunction name declarations
termination_by declarations => sizeOf declarations

def globalCollect [Add α] [Mul α] (context : GlobalPassContext α) :
    List (Decl α) → GlobalPassContext α
  | [] => context
  | .decl shape name _ :: declarations =>
      let address := globalAddress context shape
      globalCollect { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } declarations
  | _ :: declarations => globalCollect context declarations

def globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := globalCompileProg context declaration.body } ::
        globalCompileDecls context declarations
  | .exnDecl exception shape :: declarations =>
      .exnDecl exception shape :: globalCompileDecls context declarations
  | _ :: declarations => globalCompileDecls context declarations

/-! Counterpart of the append structure of Cake's `compile_decls_append`
    (`pan_globalsProofScript.sml:1997`).  The function/exception projection
    does not thread the context, so appending splits as an ordinary append. -/
theorem globalCompileDecls_append [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations rest : List (Decl α)) :
    globalCompileDecls context (declarations ++ rest) =
      globalCompileDecls context declarations ++
        globalCompileDecls context rest := by
  induction declarations with
  | nil => simp [globalCompileDecls]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalCompileDecls, ih]

def globalCompileInitializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Prog α)
  | [] => []
  | .decl shape _name value :: declarations =>
      /- `pan_globals$compile_decs` computes this declaration's address from
         the context before recursing.  In particular, duplicate names must
         retain the address of each declaration's own store; looking them up
         in the final map would incorrectly give every initializer the last
         declaration's address. -/
      let address := globalAddress context shape
      let nextContext := { context with
        globals := (_name, (shape, address)) :: context.globals
        globalsSize := address }
      let initializer :=
        .store (.op .sub [.topAddr, .const address])
          (globalCompileExp context value)
      initializer :: globalCompileInitializers nextContext declarations
  | _ :: declarations => globalCompileInitializers context declarations

/-- Cake's `compile_decs_no_exp_ids_main`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:174`): every compiled
    global initializer mentions no exception identifiers, because each one is a
    plain store. -/
theorem globalCompileInitializers_expIds [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    ∀ initializer ∈ globalCompileInitializers context declarations,
      expIds initializer = [] := by
  induction declarations generalizing context with
  | nil => simp [globalCompileInitializers]
  | cons declaration declarations ih =>
      cases declaration with
      | decl shape name value =>
          simp only [globalCompileInitializers, List.mem_cons]
          intro initializer hmem
          rcases hmem with rfl | hmem
          · simp [expIds]
          · exact ih _ initializer hmem
      | function function => simpa [globalCompileInitializers] using ih context
      | exnDecl exception shape => simpa [globalCompileInitializers] using ih context
      | name struct fields => simpa [globalCompileInitializers] using ih context

/-! Counterpart of the context-threading append structure of Cake's
    `compile_decls_append` (`pan_globalsProofScript.sml:1997`): initializers
    of an appended program are the first part's initializers followed by the
    second part's initializers evaluated under the context `globalCollect`
    reaches after the first part. -/
theorem globalCompileInitializers_append [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations rest : List (Decl α)) :
    globalCompileInitializers context (declarations ++ rest) =
      globalCompileInitializers context declarations ++
        globalCompileInitializers (globalCollect context declarations) rest := by
  induction declarations generalizing context with
  | nil => simp [globalCompileInitializers, globalCollect]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalCompileInitializers, globalCollect, ih]

/-! The four-result shape of Pancake's `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:160`).  Global declarations become initializer
    stores, while functions and exception declarations remain in their own
    source-order lists; the collected context carries the updated addresses. -/
structure GlobalCompileDecsResult (α : Type u) where
  initializers : List (Prog α)
  functions : List (Decl α)
  exceptions : List (Decl α)
  context : GlobalPassContext α

/-! Flapjack-specific context-threading counterpart of HOL
    `pan_globals$compile_decs_def` (`pan_globalsScript.sml:160-176`): each
    function body is compiled using the context at its position in the list.
    This declaration is not tagged as an exact port. Unlike HOL's fixed word
    operations, it accepts arbitrary `bytesInWord`/`fromNat` context fields,
    `[Add α]`/`[Mul α]`, and potentially non-lawful `[BEq String]`.
    Bead `flapjack-pxn.18.5.2.20.1.1` tracks the canonical-word-context port;
    production `globalCompileDecs` now calls this threaded implementation. -/
def globalCompileDecsThreaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → GlobalCompileDecsResult α
  | [] => { initializers := [], functions := [], exceptions := [], context := context }
  | .function declaration :: declarations =>
      let rest := globalCompileDecsThreaded context declarations
      { initializers := rest.initializers
        functions := .function { declaration with
            body := globalCompileProg context declaration.body } :: rest.functions
        exceptions := rest.exceptions
        context := rest.context }
  | .exnDecl exception shape :: declarations =>
      let rest := globalCompileDecsThreaded context declarations
      { rest with exceptions := .exnDecl exception shape :: rest.exceptions }
  | .name _ _ :: declarations => globalCompileDecsThreaded context declarations
  | .decl shape name value :: declarations =>
      let address := globalAddress context shape
      let nextContext := { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      let rest := globalCompileDecsThreaded nextContext declarations
      { initializers :=
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value) :: rest.initializers
        functions := rest.functions
        exceptions := rest.exceptions
        context := rest.context }

theorem globalCompileDecsThreaded_functions_all_isFunction [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (globalCompileDecsThreaded context declarations).functions.all globalDeclIsFunction =
      true := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecsThreaded, List.all_cons, globalDeclIsFunction,
            Bool.true_and]
          exact ih context
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih context

theorem globalCompileDecsThreaded_functions_eq_nil_of_no_functions
    [BEq String] [Add α] [Mul α] (declarations : List (Decl α)) :
    ∀ context, declarations.all (fun declaration => !globalDeclIsFunction declaration) = true →
      (globalCompileDecsThreaded context declarations).functions = [] := by
  induction declarations with
  | nil => intro context _; rfl
  | cons declaration declarations ih =>
      intro context hnone
      cases declaration with
      | function function =>
          simp [List.all_cons, globalDeclIsFunction] at hnone
      | decl shape name value =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2
      | exnDecl exception shape =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2
      | name struct fields =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2

/-- Flapjack-specific (untagged) append law for the context-threading pass:
    appending two declaration lists appends the three output lists and runs the
    second list under the context reached by the first. -/
theorem globalCompileDecsThreaded_append [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (decs rest : List (Decl α)) :
    globalCompileDecsThreaded context (decs ++ rest) =
      let first := globalCompileDecsThreaded context decs
      let second := globalCompileDecsThreaded first.context rest
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } := by
  induction decs generalizing context with
  | nil => simp [globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih context]
      | decl shape name value =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih _]
      | exnDecl exception shape =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih _]
      | name struct fields =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih context]

def globalCompileDecs [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    GlobalCompileDecsResult α :=
  let collected := globalCollect context declarations
  { initializers := globalCompileInitializers context declarations
    functions := (globalCompileDecsThreaded context declarations).functions
    exceptions := globalDeclsFilter globalDeclIsException
      (globalCompileDecls collected declarations)
    context := collected }

theorem globalCompileDecsThreaded_initializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (globalCompileDecsThreaded context declarations).initializers =
      globalCompileInitializers context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded, globalCompileInitializers]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context
      | decl shape name value =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          congr 1
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context

theorem globalCompileDecsThreaded_context [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (globalCompileDecsThreaded context declarations).context =
      globalCollect context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded, globalCollect]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecsThreaded, globalCollect]
          exact ih context
      | decl shape name value =>
          simpa only [globalCompileDecsThreaded, globalCollect] using ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded, globalCollect]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded, globalCollect]
          exact ih context

theorem globalCompileDecsThreaded_functions_names [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (functions (globalCompileDecsThreaded context declarations).functions).map
        (fun entry => entry.1) =
      (functions declarations).map (fun entry => entry.1) := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp [globalCompileDecsThreaded, functions, functionEntries, ih]
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih context

theorem globalCompileDecsThreaded_functions_of_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    (globalCompileDecsThreaded context declarations).functions =
      declarations.map (fun declaration => match declaration with
        | .function function =>
            .function { function with
              body := globalCompileProg context function.body }
        | _ => declaration) := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hfunction : globalDeclIsFunction declaration = true := hhead
      cases declaration with
      | function function => simp [globalCompileDecsThreaded, ih context htail]
      | decl shape name value => simp [globalDeclIsFunction] at hfunction
      | exnDecl exception shape => simp [globalDeclIsFunction] at hfunction
      | name struct fields => simp [globalDeclIsFunction] at hfunction

theorem globalCompileDecsThreaded_functions_all_of_predicate [BEq String] [Add α] [Mul α]
    (declarations : List (Decl α)) (predicate : Decl α → Bool) :
    (∀ context, declarations.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true) →
    ∀ context, (globalCompileDecsThreaded context declarations).functions.all
      predicate = true := by
  induction declarations with
  | nil => intro _ context; simp [globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      intro hsource context
      cases declaration with
      | function function =>
          have h := hsource context
          simp only [List.all_cons, Bool.and_eq_true] at h
          simp only [globalCompileDecsThreaded, List.all_cons, Bool.and_eq_true]
          exact ⟨h.1, ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context⟩
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context

theorem globalCompileDecsThreaded_exceptions_eq_filter [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecsThreaded context code).exceptions =
      globalDeclsFilter globalDeclIsException code := by
  induction code generalizing context with
  | nil => simp [globalCompileDecsThreaded, globalDeclsFilter]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecsThreaded, globalDeclsFilter, globalDeclIsException, ih]

theorem exceptionEntries_globalCompileDecsThreaded_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    exceptionEntries (globalCompileDecsThreaded context code).functions = [] := by
  induction code generalizing context with
  | nil => simp [globalCompileDecsThreaded, exceptionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecsThreaded, exceptionEntries_cons, ih]

theorem globalDeclsFilter_isDecl_all_not_function [BEq String] [Add α] [Mul α]
    (code : List (Decl α)) :
    (globalDeclsFilter isDecl code).all
      (fun declaration => !globalDeclIsFunction declaration) = true := by
  induction code with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [isDecl, globalDeclIsFunction]
      · rw [if_neg hpred]
        exact ih

theorem globalCompileDecsThreaded_functions_expIds [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (functions (globalCompileDecsThreaded context code).functions).map
        (fun entry => expIds entry.2.2.1) =
      (functions code).map (fun entry => expIds entry.2.2.1) := by
  induction code generalizing context with
  | nil => simp [globalCompileDecsThreaded, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp [globalCompileDecsThreaded, functions, functionEntries,
            globalCompileProg_expIds, ih]
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih context

theorem sizeOfEids_globalCompileDecsThreaded_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    sizeOfEids (globalCompileDecsThreaded context code).functions = 0 := by
  induction code generalizing context with
  | nil => simp [globalCompileDecsThreaded, sizeOfEids]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecsThreaded, sizeOfEids_cons, isExnDecl, ih]

/-- HOL-shaped context for `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:8-14`): the three HOL fields
    `globals`/`globals_size`/`max_globals_size` over a `width`-bit word.

    HOL `globals` is an extensional finite map (`varname |-> shape # 'a word`).
    Here it is rendered by the repository's `FiniteMap` (`α → Option β`), whose
    Lean type also admits lookups with infinite support.  For `compile_exp` this
    is adequate without a finite-support invariant: the HOL `compile_exp` clauses
    consult `globals` only through `FLOOKUP`, and every HOL finite map embeds as
    one such lookup function; on those embedded (HOL-representable) contexts the
    Lean clauses agree clause-for-clause, so the extra infinite-support lookup
    functions do not alter the port.  No cross-system finite-map equivalence is
    claimed beyond that local use.

    HOL word types satisfy `dimindex > 0`; the Lean rendering therefore
    restricts these canonical word defs with `[NeZero width]` rather than
    admitting `width = 0`.  The canonical instances are `width = 8`, `32`, or
    `64`. -/
structure CakeContext (width : Nat) where
  globals : FiniteMap String (Shape × BitVec width)
  globalsSize : BitVec width
  maxGlobalsSize : BitVec width

/-- HOL `bytes_in_word` for `width`-bit words: `n2w (dimindex DIV 8)`. -/
def cakeBytesInWord (width : Nat) : BitVec width := BitVec.ofNat width (width / 8)

/-- The address HOL `compile_decs` assigns to a freshly declared global
    (`pan_globalsScript.sml:162`):
    `globals_size + bytes_in_word * n2w (size_of_shape sh)`. -/
def cakeAddress {width : Nat} (context : CakeContext width) (shape : Shape) :
    BitVec width :=
  context.globalsSize + cakeBytesInWord width * BitVec.ofNat width (Shape.shapeSize shape)

/-- HOL `shape_val` (`panLangScript.sml:190-196`). -/
def cakeShapeVal {width : Nat} (context : CakeContext width) : Shape → Exp (BitVec width)
  | .one => .const (BitVec.ofNat width 0)
  | .named _ => .const (BitVec.ofNat width 0)
  | .comb shapes => .rStruct (shapes.map (cakeShapeVal context))
termination_by shape => sizeOf shape

/-- Interpret a production `GlobalPassContext` over `BitVec width` as a
    canonical HOL-shaped `CakeContext`: the association-list `globals` become a
finite-map lookup through `lookupInfo`, keeping the size fields.  This is
    the production-to-canonical direction of the adapter required by
    `flapjack-pxn.18.5.2.20.2`. The fixed-width executed path calls the (currently untagged)
    `compileDecsCake`; equality of the context field's data representation
    remains to be proved. -/
def cakeContextOfPass [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : CakeContext width :=
  { globals := fun key => lookupInfo key context.globals
    globalsSize := context.globalsSize
    maxGlobalsSize := context.maxGlobalsSize }

/-- Canonical-word hypothesis for the adapter: the production context uses
    HOL's fixed `bytes_in_word = n2w (dimindex DIV 8)` and `n2w`. -/
def GlobalPassContext.IsCakeCanonical {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  context.bytesInWord = cakeBytesInWord width ∧
    ∀ value : Nat, context.fromNat value = BitVec.ofNat width value

/-- Under the canonical-word hypothesis the production global address
    (`GlobalPassContext`-based) agrees with the canonical HOL address. -/
theorem cakeAddress_ofPass [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width))
    (hcanonical : context.IsCakeCanonical) (shape : Shape) :
    cakeAddress (cakeContextOfPass context) shape = globalAddress context shape := by
  rcases hcanonical with ⟨hbytes, hfrom⟩
  simp [cakeAddress, cakeContextOfPass, globalAddress, hbytes, hfrom]

/-- `cakeContextOfPass` commutes with the `Decl` context update: prepending a
    global to the production association list is exactly `FUPDATE` on the
    extracted finite map. -/
theorem cakeContextOfPass_update [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String)
    (shape : Shape) (address : BitVec width) :
    cakeContextOfPass { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      = { cakeContextOfPass context with
          globals := FUPDATE (cakeContextOfPass context).globals
            (name, (shape, address))
          globalsSize := address } := by
  simp only [cakeContextOfPass]
  rfl

/-- Explicit-field form of `cakeContextOfPass_update`, convenient for rewriting
    `rw [← ...]` in the full-record adapter. -/
theorem cakeContextOfPass_update_fields [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String)
    (shape : Shape) (address : BitVec width) :
    cakeContextOfPass { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      = { globals := FUPDATE (cakeContextOfPass context).globals (name, (shape, address))
          globalsSize := address
          maxGlobalsSize := (cakeContextOfPass context).maxGlobalsSize } := by
  simp only [cakeContextOfPass]
  rfl

/-- Adapter: production `shape_val` agrees with the canonical `cakeShapeVal`
    through `cakeContextOfPass`, under the canonical-word hypothesis. -/
theorem globalShapeVal_cakeShapeVal [BEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical)
    (shape : Shape) :
    globalShapeVal context shape = cakeShapeVal (cakeContextOfPass context) shape := by
  induction shape using cakeShapeVal.induct with
  | case1 => simp only [globalShapeVal, cakeShapeVal, hcanonical.2 0]
  | case2 name => simp only [globalShapeVal, cakeShapeVal, hcanonical.2 0]
  | case3 shapes ih =>
      simp only [globalShapeVal, cakeShapeVal]
      congr 1
      exact List.map_congr_left ih

/-- Source-reviewed Flapjack mirror (NOT an exact HOL port; `@[hol]` tag WITHDRAWN, documented
    carrier mismatch, audit bead `flapjack-dlc.11`) of HOL `pan_globals$compile_exp_def`
    (`cakeml/pancake/pan_globalsScript.sml:18-46`).  The fifteen HOL clauses map
    one-for-one onto the Lean clauses in the same order:
    `Var Local` is the identity; `Var Global` looks the name up in
    `CakeContext.globals` (HOL `FLOOKUP ctxt.globals`) and yields
    `Load sh (Op Sub [TopAddr; Const addr])` on a hit, `Const 0w` on a miss;
    `RStruct`/`RField` recurse; `NStruct`/`NField` yield `Const 0w`;
    `Load`/`LoadByte`/`Load32` recurse into the address; `Op`/`Panop` map over
    the arguments; `Cmp`/`Shift` recurse into both operands; `TopAddr` becomes
    `Op Sub [TopAddr; Const max_globals_size]`; and the HOL catch-all clause
    `compile_exp ctxt e = e` (`Const`, `BaseAddr`, `BytesInWord`) is the Lean fallthrough
    `expression => expression`.

    The definition cannot carry an exact tag because the carriers differ: HOL
    works over `'a pan_globals$context` and `'a panLang$exp` with
    `globals : varname |-> shape # 'a word` (mlstring keys), the HOL `shape`
    datatype, and a positive-width `'a word`, while this mirror uses the
    production `CakeContext width` (String-keyed globals), production
    `Exp (BitVec width)` and production `Shape`, plus an executable-only
    `[NeZero width]`.  These are structural carriers, not identifiers, so the
    `names_as_string` qualifier does not authorise them; and no same-module
    `NameRanged` witness applies because the result is an expression, not a
    name.

    Direct HOL oracle: `scripts/hol-probes/pan_globals_compile_exp_probe.out`
    (rows `local`, `global_hit`, `global_miss`, `top_addr`, `nested`), replayed
    by `Flapjack/Test/PanGlobalsCompileExpParity.lean`.  Exact-carrier
    replacement is tracked by `flapjack-pxn.18.3.5.8` (parent
    `flapjack-pxn.18.3.5.7.2`). -/
def compileExpCake {width : Nat} [NeZero width] (context : CakeContext width) :
    Exp (BitVec width) → Exp (BitVec width)
  | .var .local name => .var .local name
  | .var .global name =>
      match FLOOKUP context.globals name with
      | some (shape, address) => .load shape (.op .sub [.topAddr, .const address])
      | none => .const (BitVec.ofNat width 0)
  | .rStruct expressions => .rStruct (compileExpCakeList context expressions)
  | .rField index expression => .rField index (compileExpCake context expression)
  | .nStruct _ _ => .const (BitVec.ofNat width 0)
  | .nField _ _ => .const (BitVec.ofNat width 0)
  | .load shape address => .load shape (compileExpCake context address)
  | .load32 address => .load32 (compileExpCake context address)
  | .loadByte address => .loadByte (compileExpCake context address)
  | .op operator expressions => .op operator (compileExpCakeList context expressions)
  | .panOp operator expressions => .panOp operator (compileExpCakeList context expressions)
  | .cmp operator left right =>
      .cmp operator (compileExpCake context left) (compileExpCake context right)
  | .shift operator left right =>
      .shift operator (compileExpCake context left) (compileExpCake context right)
  | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
  | expression => expression
termination_by expression => sizeOf expression
where
  compileExpCakeList {width : Nat} [NeZero width] (context : CakeContext width) :
      List (Exp (BitVec width)) → List (Exp (BitVec width))
    | [] => []
    | expression :: expressions =>
        compileExpCake context expression :: compileExpCakeList context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- List counterpart of `compileExpCake` for external callers; mirrors HOL's
    `MAP (compile_exp ctxt)`. -/
def compileExpCakeArgs {width : Nat} [NeZero width] (context : CakeContext width) :
    List (Exp (BitVec width)) → List (Exp (BitVec width))
  | [] => []
  | expression :: expressions =>
      compileExpCake context expression :: compileExpCakeArgs context expressions
termination_by expressions => sizeOf expressions
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/- Adapter for the expression compiler: on the `cakeContextOfPass` view of a
    canonical production context, the `compileExpCake` helper (currently untagged) agrees
    with the production `globalCompileExp`.  Only the two fallback spots
    (`fromNat 0` vs `n2w 0`) need the canonical-word hypothesis; the global
    lookup is `lookupInfo` on both sides. -/
mutual
  theorem compileExpCake_cakeContextOfPass [BEq String] {width : Nat} [NeZero width]
      (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical) :
      (expression : Exp (BitVec width)) →
        compileExpCake (cakeContextOfPass context) expression = globalCompileExp context expression
    | .var .local _ => by simp only [compileExpCake, globalCompileExp]
    | .var .global name => by
        simp only [compileExpCake, globalCompileExp, cakeContextOfPass, FLOOKUP,
          hcanonical.2 0]
        cases lookupInfo name context.globals <;> rfl
    | .rStruct expressions => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCakeList_cakeContextOfPass context hcanonical expressions]
    | .rField _ expression => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical expression]
    | .nStruct _ _ => by
        simp only [compileExpCake, globalCompileExp, hcanonical.2 0]
    | .nField _ _ => by
        simp only [compileExpCake, globalCompileExp, hcanonical.2 0]
    | .load _ address => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical address]
    | .load32 address => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical address]
    | .loadByte address => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical address]
    | .op _ expressions => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCakeList_cakeContextOfPass context hcanonical expressions]
    | .panOp _ expressions => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCakeList_cakeContextOfPass context hcanonical expressions]
    | .cmp _ left right => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical left,
          compileExpCake_cakeContextOfPass context hcanonical right]
    | .shift _ left right => by
        simp only [compileExpCake, globalCompileExp,
          compileExpCake_cakeContextOfPass context hcanonical left,
          compileExpCake_cakeContextOfPass context hcanonical right]
    | .const _ => by simp only [compileExpCake, globalCompileExp]
    | .baseAddr => by simp only [compileExpCake, globalCompileExp]
    | .topAddr => by simp only [compileExpCake, globalCompileExp, cakeContextOfPass]
    | .bytesInWord => by simp only [compileExpCake, globalCompileExp]
  theorem compileExpCakeList_cakeContextOfPass [BEq String] {width : Nat} [NeZero width]
      (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical) :
      (expressions : List (Exp (BitVec width))) →
        compileExpCake.compileExpCakeList (cakeContextOfPass context) expressions =
          globalCompileExp.globalCompileExps context expressions
    | [] => by
        simp only [compileExpCake.compileExpCakeList, globalCompileExp.globalCompileExps]
    | expression :: expressions => by
        simp only [compileExpCake.compileExpCakeList, globalCompileExp.globalCompileExps,
          compileExpCake_cakeContextOfPass context hcanonical expression,
          compileExpCakeList_cakeContextOfPass context hcanonical expressions]
end

/-- Adapter for the argument-list compiler used by `compileProgCake`: on the
    `cakeContextOfPass` view of a canonical production context, the canonical
    `compileExpCakeArgs` agrees with the production `globalCompileExpList`. -/
theorem compileExpCakeArgs_cakeContextOfPass [BEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical) :
    (expressions : List (Exp (BitVec width))) →
      compileExpCakeArgs (cakeContextOfPass context) expressions =
        globalCompileExpList context expressions
  | [] => by
      simp only [compileExpCakeArgs, globalCompileExpList]
  | expression :: expressions => by
      simp only [compileExpCakeArgs, globalCompileExpList,
        compileExpCake_cakeContextOfPass context hcanonical expression,
        compileExpCakeArgs_cakeContextOfPass context hcanonical expressions]

/-- Flapjack analogue of HOL `pan_globals$compile_def`
    (`pan_globalsScript.sml:69-149`) over the canonical word context
    `CakeContext`. Constructor equations were compared branch-by-branch with
    HOL; the global-return-handler branch uses `freshNameHOL`, `freeVarIds`,
    and `expLocalVars` as their matching HOL definitions require.

    This remains untagged because the carriers differ: `CakeContext.globals`
    is `FiniteMap String (Shape × BitVec width)`, and this definition consumes
    and returns production `Prog (BitVec width)` with String identifiers. HOL
    `context.globals` is `mlstring |-> shape # word`, and `compile` consumes
    and returns exact `ProgHOL width` with `MlString` identifiers. The implicit
    `[LawfulBEq String]` supports the production map lookup/update operations;
    it does not bridge these carriers. There is no byte-range premise on the
    arbitrary program/context inputs, so `names_as_string` cannot qualify this
    definition. Exact-carrier work is tracked by `flapjack-pxn.18.3.5.8`.
    Direct HOL rows in `pan_globals_compile_probe.out` pin local/global/missing
    assignments, sequencing, global loads, and a handled global destination. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): keep the exact-carrier gap above
-- explicit until `compile` is defined over `ProgHOL` and an MlString-keyed
-- context.
def compileProgCake [LawfulBEq String] {width : Nat} [NeZero width] (context : CakeContext width) :
    Prog (BitVec width) → Prog (BitVec width)
  | .dec name shape value body =>
      .dec name shape (compileExpCake context value) (compileProgCake context body)
  | .assign .global name value =>
      match FLOOKUP context.globals name with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address]) (compileExpCake context value)
      | none => .skip
  | .assign .local name value => .assign .local name (compileExpCake context value)
  | .primitive name operator arguments =>
      .primitive name operator (compileExpCakeArgs context arguments)
  | .store address value =>
      .store (compileExpCake context address) (compileExpCake context value)
  | .store32 address value =>
      .store32 (compileExpCake context address) (compileExpCake context value)
  | .storeByte address value =>
      .storeByte (compileExpCake context address) (compileExpCake context value)
  | .seq first second =>
      .seq (compileProgCake context first) (compileProgCake context second)
  | .ite condition thenBranch elseBranch =>
      .ite (compileExpCake context condition)
        (compileProgCake context thenBranch) (compileProgCake context elseBranch)
  | .while condition body =>
      .while (compileExpCake context condition) (compileProgCake context body)
  | .call info function arguments =>
      let compiledArguments := compileExpCakeArgs context arguments
      match info with
        | none => .call none function compiledArguments
        | some (none, none) =>
            .call (some (none, none)) function compiledArguments
        | some (none, some (exception, handlerVar, handler)) =>
            .call (some (none, some (exception, handlerVar,
              compileProgCake context handler))) function compiledArguments
        | some (some (.local, name), none) =>
            .call (some (some (.local, name), none)) function compiledArguments
        | some (some (.local, name), some (exception, handlerVar, handler)) =>
            .call (some (some (.local, name), some (exception, handlerVar,
              compileProgCake context handler))) function compiledArguments
        | some (some (.global, name), none) =>
            match FLOOKUP context.globals name with
            | some (shape, address) =>
                .decCall "" shape function compiledArguments
                  (.store (.op .sub [.topAddr, .const address])
                    (.var .local ""))
            | none =>
                .call (some (none, none)) function compiledArguments
        | some (some (.global, name), some (exception, handlerVar, handler)) =>
            match FLOOKUP context.globals name with
            | some (shape, address) =>
                let compiledHandlerProgram := compileProgCake context handler
                let names := handlerVar :: freeVarIds compiledHandlerProgram ++
                  compiledArguments.flatMap expLocalVars
                let resultName := freshNameHOL "" names
                /- Cake's `compile_def` uses the fixed seed `"vn'"` for its
                   handler flag, independently of the fresh result name. -/
                let flagName := freshNameHOL "vn'" (resultName :: names)
                let handlerBody :=
                  .seq compiledHandlerProgram
                    (.assign .local flagName (.const (BitVec.ofNat width 1)))
                let callInfo := some (some (.local, resultName),
                  some (exception, handlerVar, handlerBody))
                let callProgram : Prog (BitVec width) :=
                  .call callInfo function compiledArguments
                let storeAddress : Exp (BitVec width) :=
                  .op .sub [.topAddr, .const address]
                .dec resultName shape (cakeShapeVal context shape)
                  (.dec flagName .one (.const (BitVec.ofNat width 0))
                    (.seq callProgram
                      (.ite (.var .local flagName) .skip
                        (.store storeAddress
                          (.var .local resultName)))))
            | none =>
                .call (some (none, some (exception, handlerVar,
                  compileProgCake context handler))) function compiledArguments
  | .decCall name shape function arguments body =>
      .decCall name shape function (compileExpCakeArgs context arguments)
        (compileProgCake context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (compileExpCake context configuration)
        (compileExpCake context configurationLength) (compileExpCake context array)
        (compileExpCake context arrayLength)
  | .raise exception value => .raise exception (compileExpCake context value)
  | .return value => .return (compileExpCake context value)
  | .shMemLoad size kind name address =>
      match kind, FLOOKUP context.globals name with
      | .local, _ =>
          .shMemLoad size .local name (compileExpCake context address)
      | .global, some (.one, globalAddress) =>
          let localName := name ++ globalApostrophes 1
          .dec name .one (compileExpCake context address)
            (.dec localName .one (.const (BitVec.ofNat width 0))
              (.seq
                (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress])
                  (.var .local localName))))
      | .global, _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (compileExpCake context address) (compileExpCake context value)
  | program => program
termination_by program => sizeOf program

@[simp] theorem FLOOKUP_cakeContextOfPass_globals [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (key : String) :
    (cakeContextOfPass context).globals key = lookupInfo key context.globals := rfl

/-- The `shMemLoad` clause of the production/canonical agreement, isolated so
    the `FLOOKUP`/match on the global table reduces on both sides. -/
theorem compileProgCake_shMemLoad_eq [BEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical)
    (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp (BitVec width)) :
    compileProgCake (cakeContextOfPass context) (.shMemLoad size kind name address)
      = globalCompileProg context (.shMemLoad size kind name address) := by
  unfold compileProgCake globalCompileProg
  simp only [FLOOKUP, FLOOKUP_cakeContextOfPass_globals]
  cases h : lookupInfo name context.globals with
  | none => cases kind <;> simp_all [compileExpCake_cakeContextOfPass context hcanonical]
  | some pair =>
      obtain ⟨shape, globalAddress⟩ := pair
      cases shape <;> cases kind <;>
        simp_all [compileExpCake_cakeContextOfPass context hcanonical, hcanonical.2]

/-- Production `globalCompileProg` agrees with the
    `compileProgCake` under the canonical word-context view. This is the
    program half of the executed-path adapter for
    `flapjack-pxn.18.5.2.20.2`. -/
theorem globalCompileProg_cakeContextOfPass [BEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical) :
    (program : Prog (BitVec width)) →
      compileProgCake (cakeContextOfPass context) program = globalCompileProg context program := by
  apply globalCompileProg.induct context
    (motive := fun program =>
      compileProgCake (cakeContextOfPass context) program = globalCompileProg context program)
  all_goals
    intros
    simp_all [compileProgCake, globalCompileProg, FLOOKUP,
      FLOOKUP_cakeContextOfPass_globals,
      compileProgCake_shMemLoad_eq context hcanonical,
      compileExpCake_cakeContextOfPass context hcanonical,
      compileExpCakeArgs_cakeContextOfPass context hcanonical,
      globalShapeVal_cakeShapeVal context hcanonical, hcanonical.2]

/-- HOL-shaped output of `compile_decs`. -/
structure CakeCompileDecsResult (width : Nat) where
  initializers : List (Prog (BitVec width))
  functions : List (Decl (BitVec width))
  exceptions : List (Decl (BitVec width))
  context : CakeContext width

/-- Source-shaped port (Flapjack-specific; NOT an exact HOL port) of HOL `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:160-176`) over the canonical word context
    `CakeContext`: a function body is compiled (`compileProgCake`) under the
    context as of its own position, and a `Decl` computes
    `globals_size + bytes_in_word * n2w (size_of_shape sh)`, extends `globals`
    by `FUPDATE` and updates `globals_size` for the declarations that follow.
    Every clause matches HOL directly; `ExnDecl` conses the exception, `Name`
    is skipped, and the empty list returns the context unchanged.

    `CakeContext.globals` renders HOL's extensional finite map by the
    repository's `FiniteMap` (`α → Option β`), which also admits lookups with
    infinite support.  As recorded for `compileExpCake`, the HOL `compile_decs`
    clauses consult `globals` only through `FLOOKUP`/`FUPDATE`, and every HOL
    finite map embeds as one such lookup function, so on HOL-representable
    contexts the Lean clauses agree clause-for-clause; the extra
    infinite-support lookups do not alter the port.  No cross-system finite-map
    equivalence is claimed beyond that local use.  `width` is restricted by
    `[NeZero width]`, as HOL `dimindex` is positive, and the name equality is
    `[LawfulBEq String]` so the `==` used by `FUPDATE`/`FLOOKUP` reflects HOL's
    `=`. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): `CakeContext.globals` is keyed by
-- production `String` and `Exp`/`Prog`/`Decl` names are `String`, while HOL
-- `pan_globalsScript.sml` keys `ctxt.globals` by `mlstring`. The exact MlString
-- identifier carrier is tracked by `flapjack-pxn.18.3.5.8` (parent
-- `flapjack-pxn.18.3.5.7.2`).
def compileDecsCake [LawfulBEq String] {width : Nat} [NeZero width] (context : CakeContext width) :
    List (Decl (BitVec width)) → CakeCompileDecsResult width
  | [] => { initializers := [], functions := [], exceptions := [], context := context }
  | .function declaration :: declarations =>
      let rest := compileDecsCake context declarations
      { initializers := rest.initializers
        functions := .function { declaration with
            body := compileProgCake context declaration.body } :: rest.functions
        exceptions := rest.exceptions
        context := rest.context }
  | .exnDecl exception shape :: declarations =>
      let rest := compileDecsCake context declarations
      { rest with exceptions := .exnDecl exception shape :: rest.exceptions }
  | .name _ _ :: declarations => compileDecsCake context declarations
  | .decl shape name value :: declarations =>
      let address := cakeAddress context shape
      let nextContext := { context with
        globals := FUPDATE context.globals (name, (shape, address))
        globalsSize := address }
      let rest := compileDecsCake nextContext declarations
      { initializers :=
          .store (.op .sub [.topAddr, .const address])
            (compileExpCake context value) :: rest.initializers
        functions := rest.functions
        exceptions := rest.exceptions
        context := rest.context }

/-- Full-record adapter: the canonical `compileDecsCake` over the extracted
    `CakeContext` agrees, field by field, with the production
    `globalCompileDecsThreaded` whenever the production context is
    canonical-word (`IsCakeCanonical`).  All four fields (initializers,
    functions, exceptions, context) are covered; the `context` field is stated
    through `cakeContextOfPass` because the finite-map representation cannot be
    turned back into a lossless association list. -/
theorem compileDecsCake_cakeContextOfPass [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical)
    (declarations : List (Decl (BitVec width))) :
    compileDecsCake (cakeContextOfPass context) declarations =
      { initializers := (globalCompileDecsThreaded context declarations).initializers
        functions := (globalCompileDecsThreaded context declarations).functions
        exceptions := (globalCompileDecsThreaded context declarations).exceptions
        context :=
          cakeContextOfPass (globalCompileDecsThreaded context declarations).context } := by
  induction declarations generalizing context with
  | nil => simp only [compileDecsCake, globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [compileDecsCake, globalCompileDecsThreaded]
          rw [ih context hcanonical]
          simp only [globalCompileProg_cakeContextOfPass context hcanonical]
      | exnDecl exception shape =>
          simp only [compileDecsCake, globalCompileDecsThreaded]
          rw [ih context hcanonical]
      | name struct fields => exact ih context hcanonical
      | decl shape name value =>
          simp only [compileDecsCake, globalCompileDecsThreaded]
          simp only [cakeAddress_ofPass context hcanonical shape]
          erw [← cakeContextOfPass_update_fields context name shape (globalAddress context shape)]
          rw [ih { context with
              globals := (name, (shape, globalAddress context shape)) :: context.globals
              globalsSize := globalAddress context shape } hcanonical]
          simp only [compileExpCake_cakeContextOfPass context hcanonical value]

theorem compileDecsCake_functions_all_isFunction [LawfulBEq String] {width : Nat} [NeZero width]
    (context : CakeContext width) (declarations : List (Decl (BitVec width))) :
    (compileDecsCake context declarations).functions.all globalDeclIsFunction = true := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [compileDecsCake, List.all_cons, globalDeclIsFunction, Bool.true_and]
          exact ih context
      | decl shape name value =>
          simp only [compileDecsCake]
          exact ih _
      | exnDecl exception shape =>
          simp only [compileDecsCake]
          exact ih context
      | name struct fields =>
          simp only [compileDecsCake]
          exact ih context

theorem compileDecsCake_functions_eq_nil_of_no_functions [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) :
    ∀ context, declarations.all (fun declaration => !globalDeclIsFunction declaration) = true →
      (compileDecsCake context declarations).functions = [] := by
  induction declarations with
  | nil => intro context _; rfl
  | cons declaration declarations ih =>
      intro context hnone
      cases declaration with
      | function function =>
          simp [List.all_cons, globalDeclIsFunction] at hnone
      | decl shape name value =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [compileDecsCake]
          exact ih _ hnone.2
      | exnDecl exception shape =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [compileDecsCake]
          exact ih _ hnone.2
      | name struct fields =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [compileDecsCake]
          exact ih _ hnone.2

theorem compileDecsCake_append [LawfulBEq String] {width : Nat} [NeZero width] (context : CakeContext width)
    (decs rest : List (Decl (BitVec width))) :
    compileDecsCake context (decs ++ rest) =
      let first := compileDecsCake context decs
      let second := compileDecsCake first.context rest
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } := by
  induction decs generalizing context with
  | nil => simp [compileDecsCake]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [List.cons_append, compileDecsCake]
          rw [ih context]
      | decl shape name value =>
          simp only [List.cons_append, compileDecsCake]
          rw [ih _]
      | exnDecl exception shape =>
          simp only [List.cons_append, compileDecsCake]
          rw [ih _]
      | name struct fields =>
          simp only [List.cons_append, compileDecsCake]
          rw [ih context]

/-! Counterpart of Cake's `compile_decs_preserve_functions`
    (`pan_globalsProofScript.sml:2062`): compiling declarations preserves the
    function-name table. -/
theorem functions_names_globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (functions (globalCompileDecls context declarations)).map
        (fun entry => entry.1) =
      (functions declarations).map (fun entry => entry.1) := by
  induction declarations with
  | nil => simp [globalCompileDecls, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalCompileDecls, functions, functionEntries, ih]

theorem globalCompileDecls_all_not_function [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hnone : declarations.all
      (fun declaration => !globalDeclIsFunction declaration) = true) :
    (globalCompileDecls context declarations).all
      (fun declaration => !globalDeclIsFunction declaration) = true := by
  induction declarations with
  | nil => simp [globalCompileDecls]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hnone
      obtain ⟨hhead, htail⟩ := hnone
      cases declaration <;>
        simp_all [globalCompileDecls, globalDeclIsFunction]

theorem globalCompileDecs_preserve_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (functions (globalCompileDecs context code).functions).map
        (fun entry => entry.1) =
      (functions code).map (fun entry => entry.1) := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_names context code

/-! Counterpart of Cake's `compile_decs_EVERY_is_function`
    (`pan_globalsProofScript.sml:1977`): every declaration the compilation
    pass emits into the function table is itself a function declaration. -/
theorem globalCompileDecs_functions_all_isFunction [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context code).functions.all globalDeclIsFunction = true := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_all_isFunction context code

/-! Counterpart of Cake's `compile_decs_decls_thm`
    (`pan_globalsProofScript.sml:1967`): a program whose declarations contain
    no functions compiles to an empty function table. -/
theorem globalCompileDecs_functions_eq_nil_of_no_functions [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (code : List (Decl α))
    (hnone : code.all (fun declaration => !globalDeclIsFunction declaration) = true) :
    (globalCompileDecs context code).functions = [] := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_eq_nil_of_no_functions code context hnone

/-! Counterpart of Cake's `compile_decs_EVERY`
    (`pan_globalsProofScript.sml:1986`): every function of the compiled table
    satisfies a predicate that holds of each source function once its body has
    been compiled with the collected context. -/
theorem globalDeclsFilter_globalCompileDecls_all_of_predicate [BEq String]
    [Add α] [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α))
    (predicate : Decl α → Bool)
    (hsource : declarations.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true) :
    (globalDeclsFilter globalDeclIsFunction
        (globalCompileDecls context declarations)).all predicate = true := by
  induction declarations with
  | nil => simp [globalCompileDecls, globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hsource
      obtain ⟨hhead, htail⟩ := hsource
      cases declaration with
      | function function =>
          simp [globalCompileDecls, globalDeclsFilter, globalDeclIsFunction,
            hhead, ih htail]
      | decl shape name value =>
          exact ih htail
      | exnDecl exception shape =>
          simp [globalCompileDecls, globalDeclsFilter, globalDeclIsFunction,
            ih htail]
      | name struct fields =>
          exact ih htail

theorem globalCompileDecs_functions_all_of_predicate [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (predicate : Decl α → Bool)
    (hsource : ∀ context, code.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true) :
    (globalCompileDecs context code).functions.all predicate = true := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_all_of_predicate code predicate
    hsource context

/-! Counterpart of Cake's `compile_decs_exns_are_exns`
    (`pan_globalsProofScript.sml:2448`): the exception table is exactly the
    exception declarations of the source program. -/
theorem globalDeclsFilter_isException_globalCompileDecls [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalDeclsFilter globalDeclIsException
        (globalCompileDecls context declarations) =
      globalDeclsFilter globalDeclIsException declarations := by
  induction declarations with
  | nil => simp [globalCompileDecls, globalDeclsFilter]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecls, globalDeclsFilter, globalDeclIsException, ih]

theorem globalCompileDecs_exceptions_eq_filter [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context code).exceptions =
      globalDeclsFilter globalDeclIsException code := by
  simp only [globalCompileDecs]
  exact globalDeclsFilter_isException_globalCompileDecls
    (globalCollect context code) code

/-! Fieldwise link between the executed polymorphic `globalCompileDecs` and the
    `compileDecsCake` helper (currently untagged). The three declaration-list fields agree
    under the canonical context view; the contexts themselves are deliberately
    not compared as data because `CakeContext.globals` is a finite map while the
    production context keeps an association list. -/
theorem globalCompileDecs_fields_cakeContextOfPass [LawfulBEq String] {width : Nat}
    [NeZero width] (context : GlobalPassContext (BitVec width))
    (hcanonical : context.IsCakeCanonical)
    (declarations : List (Decl (BitVec width))) :
    (compileDecsCake (cakeContextOfPass context) declarations).initializers =
        (globalCompileDecs context declarations).initializers ∧
      (compileDecsCake (cakeContextOfPass context) declarations).functions =
        (globalCompileDecs context declarations).functions ∧
      (compileDecsCake (cakeContextOfPass context) declarations).exceptions =
        (globalCompileDecs context declarations).exceptions := by
  rw [compileDecsCake_cakeContextOfPass context hcanonical declarations]
  refine ⟨?_, ?_, ?_⟩
  · show (globalCompileDecsThreaded context declarations).initializers =
      (globalCompileDecs context declarations).initializers
    exact globalCompileDecsThreaded_initializers context declarations
  · show (globalCompileDecsThreaded context declarations).functions =
      (globalCompileDecs context declarations).functions
    rfl
  · show (globalCompileDecsThreaded context declarations).exceptions =
      (globalCompileDecs context declarations).exceptions
    exact (globalCompileDecsThreaded_exceptions_eq_filter context declarations).trans
      (globalCompileDecs_exceptions_eq_filter context declarations).symm

theorem functions_globalDeclsFilter_isException (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsException declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _
    (fun declaration hpred => by
      cases declaration <;> simp_all [globalDeclIsException, globalDeclIsFunction])
    declarations

/-- Cake's `functions_compile_decs_exns`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:519`): the exception
    component of `compile_decs` contains no function declarations. -/
theorem globalCompileDecs_exceptions_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    functions (globalCompileDecs context code).exceptions = [] := by
  rw [globalCompileDecs_exceptions_eq_filter]
  exact functions_globalDeclsFilter_isException code

theorem globalDeclsFilter_eq_self_of_all (predicate : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all predicate = true) :
    globalDeclsFilter predicate declarations = declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      rw [globalDeclsFilter_cons_true predicate declaration declarations hhead,
        ih htail]

/-! Counterpart of Cake's `compile_decs_functions_thm`
    (`pan_globalsProofScript.sml:1967`): a function-only declaration list
    compiles to no initializer stores, no exception declarations, an unchanged
    collected context, and a function table that is the source list with each
    body compiled under that unchanged context. -/
theorem globalCollect_of_functions [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    globalCollect context declarations = context := by
  induction declarations with
  | nil => simp [globalCollect]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hfunction : globalDeclIsFunction declaration = true := hhead
      cases declaration with
      | function function => simp [globalCollect, ih htail]
      | decl shape name value => simp [globalDeclIsFunction] at hfunction
      | exnDecl exception shape => simp [globalDeclIsFunction] at hfunction
      | name struct fields => simp [globalDeclIsFunction] at hfunction

theorem globalCompileInitializers_of_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    globalCompileInitializers context declarations = [] := by
  induction declarations with
  | nil => simp [globalCompileInitializers]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hfunction : globalDeclIsFunction declaration = true := hhead
      cases declaration with
      | function function => simp [globalCompileInitializers, ih htail]
      | decl shape name value => simp [globalDeclIsFunction] at hfunction
      | exnDecl exception shape => simp [globalDeclIsFunction] at hfunction
      | name struct fields => simp [globalDeclIsFunction] at hfunction

theorem globalCompileDecls_all_isFunction [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    (globalCompileDecls context declarations).all globalDeclIsFunction = true := by
  induction declarations with
  | nil => simp [globalCompileDecls]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hfunction : globalDeclIsFunction declaration = true := hhead
      cases declaration with
      | function function =>
          simp [globalCompileDecls, globalDeclIsFunction, ih htail]
      | decl shape name value => simp [globalDeclIsFunction] at hfunction
      | exnDecl exception shape => simp [globalDeclIsFunction] at hfunction
      | name struct fields => simp [globalDeclIsFunction] at hfunction

theorem globalCompileDecls_of_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    globalCompileDecls context declarations =
      declarations.map (fun declaration => match declaration with
        | .function function =>
            .function { function with
              body := globalCompileProg context function.body }
        | _ => declaration) := by
  induction declarations with
  | nil => simp [globalCompileDecls]
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hhead, htail⟩ := hall
      have hfunction : globalDeclIsFunction declaration = true := hhead
      cases declaration with
      | function function => simp [globalCompileDecls, ih htail]
      | decl shape name value => simp [globalDeclIsFunction] at hfunction
      | exnDecl exception shape => simp [globalDeclIsFunction] at hfunction
      | name struct fields => simp [globalDeclIsFunction] at hfunction

theorem globalCompileDecs_functions_thm [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    (globalCompileDecs context declarations).initializers = [] ∧
    (globalCompileDecs context declarations).functions =
      declarations.map (fun declaration => match declaration with
        | .function function =>
            .function { function with
              body := globalCompileProg context function.body }
        | _ => declaration) ∧
    (globalCompileDecs context declarations).exceptions = [] ∧
    (globalCompileDecs context declarations).context = context := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [globalCompileDecs]
    exact globalCompileInitializers_of_functions context declarations hall
  · simp only [globalCompileDecs]
    exact globalCompileDecsThreaded_functions_of_functions context declarations hall
  · simp only [globalCompileDecs]
    rw [globalDeclsFilter_isException_globalCompileDecls]
    refine globalDeclsFilter_eq_nil_of_all_not globalDeclIsException declarations ?_
    refine List.all_eq_true.mpr (fun declaration hmem => ?_)
    have hfunction : globalDeclIsFunction declaration = true :=
      List.all_eq_true.mp hall declaration hmem
    cases declaration <;> simp_all [globalDeclIsFunction, globalDeclIsException]
  · simp only [globalCompileDecs]
    exact globalCollect_of_functions context declarations hall

/-! Counterpart of Cake's `compile_decs_FILTER_decs`
    (`pan_globalsProofScript.sml:2822`): filtering the source program down to its
    global declarations leaves the collected context and the initializer stores
    unchanged, and empties the function and exception tables. -/
theorem globalCollect_filter_isDecl [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCollect context (globalDeclsFilter isDecl declarations) =
      globalCollect context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalDeclsFilter, globalCollect]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp only [globalCollect, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        cases declaration with
        | decl shape name value => simp [isDecl] at hpred
        | function function =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context
        | exnDecl exception shape =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context
        | name struct fields =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context

theorem globalCompileInitializers_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCompileInitializers context (globalDeclsFilter isDecl declarations) =
      globalCompileInitializers context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalDeclsFilter, globalCompileInitializers]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp only [globalCompileInitializers, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        cases declaration with
        | decl shape name value => simp [isDecl] at hpred
        | function function =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context
        | exnDecl exception shape =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context
        | name struct fields =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context

theorem globalCompileDecls_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCompileDecls context (globalDeclsFilter isDecl declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, globalCompileDecls]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp [globalCompileDecls, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        exact ih

theorem globalCompileDecs_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context (globalDeclsFilter isDecl code)).initializers =
        (globalCompileDecs context code).initializers ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).functions = [] ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).exceptions = [] ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).context =
        (globalCompileDecs context code).context := by
  simp only [globalCompileDecs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact globalCompileInitializers_filter_isDecl context code
  · exact globalCompileDecsThreaded_functions_eq_nil_of_no_functions
      (globalDeclsFilter isDecl code) context
      (globalDeclsFilter_isDecl_all_not_function code)
  · rw [globalCollect_filter_isDecl, globalCompileDecls_filter_isDecl]
    simp [globalDeclsFilter]
  · exact globalCollect_filter_isDecl context code

/-! Successful-start helper for Flapjack's top-level global compiler. This
    Option-valued helper is used by invariants that require a named start
    function to exist. HOL's public `compile_top` is total and returns `[]`
    when the start function is absent; `globalCompileTopForStart` below
    implements that behavior. -/
def globalCompileTopForStartSome [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α))
    (start : FunName) : Option (List (Decl α)) :=
  match globalFindFunction start declarations with
  | none => none
  | some entry =>
      let resorted := globalResortDecls declarations
      let renamedStart := globalNewMainName declarations
      let renamed := globalRenameDecls start renamedStart resorted
      let maxGlobalsSize :=
        bytesInWord * fromNat
          ((globalDeclShapes renamed).map Shape.shapeSize |>.foldl (· + ·) 0)
      let initial : GlobalPassContext α :=
        { globals := []
          globalsSize := fromNat 0
          maxGlobalsSize := maxGlobalsSize
          bytesInWord := bytesInWord
          fromNat := fromNat }
      let compiled := globalCompileDecs initial renamed
      let parameters := entry.params.map (fun (name, _) => Exp.var .local name)
      let newMain : Decl α :=
        .function
          { name := start
            inline := false
            exported := false
            params := entry.params
            body := .seq (nestedSeq compiled.initializers)
              (.call none renamedStart parameters)
            returnShape := entry.returnShape }
      some (compiled.exceptions ++ [newMain] ++ compiled.functions)

/-! Generalized total compiler analogue. Its word size and natural-number
    conversion are explicit so Flapjack callers can use different targets; it
    is not itself the exact HOL `compile_top` interface. The fixed-word
    `globalCompileTopCake` wrapper below is the source-shaped interface. -/
def globalCompileTopForStart [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α))
    (start : FunName) : List (Decl α) :=
  (globalCompileTopForStartSome bytesInWord fromNat declarations start).getD []

/-! Canonical fixed-word top-level compiler. Its global pass runs through the
    `compileDecsCake` over a `CakeContext` (currently untagged); the polymorphic
    `globalCompileTopForStartSome` above remains available for arbitrary word
    types. `globalCompileTopForStartSomeCake_eq` proves the two compute the same
    output list, so the executed fixed-word path below can use the canonical
    definition without changing observable behavior. -/
def globalCompileTopForStartSomeCake [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    Option (List (Decl (BitVec width))) :=
  match globalFindFunction start declarations with
  | none => none
  | some entry =>
      let resorted := globalResortDecls declarations
      let renamedStart := globalNewMainName declarations
      let renamed := globalRenameDecls start renamedStart resorted
      let maxGlobalsSize :=
        cakeBytesInWord width * BitVec.ofNat width
          ((globalDeclShapes renamed).map Shape.shapeSize |>.foldl (· + ·) 0)
      let initial : GlobalPassContext (BitVec width) :=
        { globals := []
          globalsSize := BitVec.ofNat width 0
          maxGlobalsSize := maxGlobalsSize
          bytesInWord := cakeBytesInWord width
          fromNat := BitVec.ofNat width }
      let compiled := compileDecsCake (cakeContextOfPass initial) renamed
      let parameters := entry.params.map (fun (name, _) => Exp.var .local name)
      let newMain : Decl (BitVec width) :=
        .function
          { name := start
            inline := false
            exported := false
            params := entry.params
            body := .seq (nestedSeq compiled.initializers)
              (.call none renamedStart parameters)
            returnShape := entry.returnShape }
      some (compiled.exceptions ++ [newMain] ++ compiled.functions)

theorem globalCompileTopForStartSomeCake_eq [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    globalCompileTopForStartSomeCake declarations start =
      globalCompileTopForStartSome (cakeBytesInWord width) (BitVec.ofNat width)
        declarations start := by
  unfold globalCompileTopForStartSomeCake globalCompileTopForStartSome
  cases globalFindFunction start declarations with
  | none => rfl
  | some entry =>
      simp only
      congr 1
      generalize hrenamed : globalRenameDecls start (globalNewMainName declarations)
        (globalResortDecls declarations) = renamed
      have hfields := globalCompileDecs_fields_cakeContextOfPass
        (context := { globals := []
                      globalsSize := BitVec.ofNat width 0
                      maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
                        ((globalDeclShapes renamed).map Shape.shapeSize |>.foldl (· + ·) 0)
                      bytesInWord := cakeBytesInWord width
                      fromNat := BitVec.ofNat width })
        (by refine ⟨rfl, fun value => rfl⟩) renamed
      simp only [hfields.1, hfields.2.1, hfields.2.2]

/-! HOL's `compile_top` fixes its compiler context to
    `bytes_in_word` and `n2w`. For a word of `width` bits, those are represented
    by `width / 8` and `BitVec.ofNat width` respectively. This wrapper keeps
    those choices out of the caller interface while remaining polymorphic in
    the HOL word width. -/
-- FLAPJACK-SPECIFIC (not an exact HOL port): the statement is keyed by the
-- production identifiers `FunName`/`VarName` = `String`, while HOL
-- `pan_globalsScript.sml` keys names by `funname`/`varname` = `mlstring`.
-- The exact MlString identifier carrier is tracked by `flapjack-pxn.18.3.5.8`
-- (parent `flapjack-pxn.18.3.5.7.2`).
def globalCompileTopCake [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    List (Decl (BitVec width)) :=
  (globalCompileTopForStartSomeCake declarations start).getD []

theorem globalCompileTopCake_eq [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) (start : FunName) :
    globalCompileTopCake declarations start =
      globalCompileTopForStart (cakeBytesInWord width) (BitVec.ofNat width)
        declarations start := by
  simp only [globalCompileTopCake, globalCompileTopForStart,
    globalCompileTopForStartSomeCake_eq declarations start]

theorem globalDecls_all_or_of_all_left (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all other = true) :
    declarations.all
      (fun declaration => predicate declaration || other declaration) = true := by
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      obtain ⟨hhead, htail⟩ := hall
      exact ⟨by simp [hhead], ih htail⟩

theorem globalDecls_all_or_of_all_right (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all predicate = true) :
    declarations.all
      (fun declaration => predicate declaration || other declaration) = true := by
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      obtain ⟨hhead, htail⟩ := hall
      exact ⟨by simp [hhead], ih htail⟩

/-! Counterpart of Cake's `compile_top_only_functions_or_exns`
    (`pan_globalsProofScript.sml:2611`): the declaration list produced by the
    start-function entry point consists only of compiled functions and
    exception declarations. -/
theorem globalCompileDecs_result_all_function_or_exception [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α))
    (extra : Decl α) (hextra : globalDeclIsFunction extra = true) :
    ((globalCompileDecs context declarations).exceptions ++ [extra] ++
        (globalCompileDecs context declarations).functions).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  simp only [globalCompileDecs]
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact globalDecls_all_or_of_all_left globalDeclIsFunction
      globalDeclIsException _ (globalDeclsFilter_all globalDeclIsException _)
  · simp [hextra]
  · exact globalDecls_all_or_of_all_right globalDeclIsFunction
      globalDeclIsException _
      (globalCompileDecsThreaded_functions_all_isFunction context declarations)

/-! Flapjack stage invariant: compiling declarations preserves their exception
    projection. This supports top-level exception reasoning but is not itself
    a port of Cake's `exceptions_compile_top`, which also assumes the
    requested start function is present. -/
theorem exceptionEntries_globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    exceptionEntries (globalCompileDecls context declarations) =
      exceptionEntries declarations := by
  induction declarations with
  | nil => simp [globalCompileDecls, exceptionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecls, exceptionEntries_cons, ih]

theorem exceptionEntries_globalRenameDecls [BEq String]
    (source target : FunName) (declarations : List (Decl α)) :
    exceptionEntries (globalRenameDecls source target declarations) =
      exceptionEntries declarations := by
  induction declarations with
  | nil => simp [globalRenameDecls, exceptionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalRenameDecls, exceptionEntries_cons, ih]

theorem exceptionEntries_globalResortDecls (declarations : List (Decl α)) :
    exceptionEntries (globalResortDecls declarations) =
      exceptionEntries declarations := by
  simp [globalResortDecls, exceptionEntries_append,
    exceptionEntries_filter_name, exceptionEntries_filter_exception,
    exceptionEntries_filter_global, exceptionEntries_filter_function]

/-! Successful-start helper lemma for Flapjack's exception projection. The
    Option premise is intentionally about `globalCompileTopForStartSome`; the
    total HOL `compile_top` returns no declarations when the start is absent,
    so exception preservation for that branch is not claimed. -/
theorem globalCompileTopForStart_exceptionEntries [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α))
    (start : FunName) (compiled : List (Decl α))
    (hcompile : globalCompileTopForStartSome bytesInWord fromNat declarations start =
      some compiled) :
    exceptionEntries compiled = exceptionEntries declarations := by
  unfold globalCompileTopForStartSome at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some entry =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      simp only [globalCompileDecs]
      rw [exceptionEntries_append, exceptionEntries_append,
        exceptionEntries_filter_exception,
        exceptionEntries_globalCompileDecls,
        exceptionEntries_globalCompileDecsThreaded_functions,
        exceptionEntries_globalRenameDecls, exceptionEntries_globalResortDecls]
      simp [exceptionEntries]

theorem globalFunctionNames_eq_functions_map (declarations : List (Decl α)) :
    globalFunctionNames declarations =
      (functions declarations).map (fun entry => entry.1) := by
  induction declarations with
  | nil => rw [globalFunctionNames.eq_def]; rfl
  | cons declaration declarations ih =>
      cases declaration <;> rw [globalFunctionNames.eq_def] <;>
        simp [functions, functionEntries, ih]

theorem globalFindFunction_name_mem [BEq String] [LawfulBEq String]
    (name : FunName) (declarations : List (Decl α)) (entry : FunDecl α)
    (hfind : globalFindFunction name declarations = some entry) :
    entry.name = name ∧ name ∈ globalFunctionNames declarations := by
  induction declarations with
  | nil => simp [globalFindFunction] at hfind
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          rw [globalFindFunction.eq_def] at hfind
          by_cases hname : (function.name == name) = true
          · simp only [hname, if_pos] at hfind
            have heq : entry = function := (Option.some.inj hfind).symm
            subst heq
            refine ⟨beq_iff_eq.mp hname, ?_⟩
            rw [globalFunctionNames.eq_def]
            exact List.mem_cons.mpr (Or.inl (beq_iff_eq.mp hname).symm)
          · simp only [hname] at hfind
            obtain ⟨hnameeq, hmem⟩ := ih hfind
            refine ⟨hnameeq, ?_⟩
            rw [globalFunctionNames.eq_def]
            exact List.mem_cons.mpr (Or.inr hmem)
      | decl shape name' value =>
          rw [globalFindFunction.eq_def] at hfind
          obtain ⟨hnameeq, hmem⟩ := ih hfind
          refine ⟨hnameeq, ?_⟩
          rw [globalFunctionNames.eq_def]
          exact hmem
      | exnDecl exception shape =>
          rw [globalFindFunction.eq_def] at hfind
          obtain ⟨hnameeq, hmem⟩ := ih hfind
          refine ⟨hnameeq, ?_⟩
          rw [globalFunctionNames.eq_def]
          exact hmem
      | name struct fields =>
          rw [globalFindFunction.eq_def] at hfind
          obtain ⟨hnameeq, hmem⟩ := ih hfind
          refine ⟨hnameeq, ?_⟩
          rw [globalFunctionNames.eq_def]
          exact hmem

theorem globalRenameFunctionName_eq_source_iff [BEq String] [LawfulBEq String]
    (source target name : FunName) :
    globalRenameFunctionName source target name = source ↔ name = target := by
  unfold globalRenameFunctionName fpermName
  by_cases h1 : source = name
  · rw [if_pos h1]
    rw [h1]
    exact eq_comm
  · rw [if_neg h1]
    by_cases h2 : target = name
    · rw [if_pos h2]
      exact ⟨fun _ => h2.symm, fun _ => rfl⟩
    · rw [if_neg h2]
      exact ⟨fun h => absurd h.symm h1, fun h => absurd h.symm h2⟩

theorem mem_map_globalRenameFunctionName_source [BEq String] [LawfulBEq String]
    (source target : FunName) (names : List FunName) :
    source ∈ names.map (globalRenameFunctionName source target) ↔
      target ∈ names := by
  rw [List.mem_map]
  constructor
  · rintro ⟨name, hname, heq⟩
    have hname_target : name = target :=
      (globalRenameFunctionName_eq_source_iff source target name).mp heq
    rwa [hname_target] at hname
  · intro htarget
    refine ⟨target, htarget, ?_⟩
    unfold globalRenameFunctionName fpermName
    by_cases hst : source = target
    · rw [if_pos hst]
      exact hst.symm
    · rw [if_neg hst]
      simp

theorem globalCompileDecs_functions_names [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    ((functions (globalCompileDecs context declarations).functions).map
        (fun entry => entry.1)) =
      (functions declarations).map (fun entry => entry.1) := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_names context declarations

theorem functions_globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    functions (globalCompileDecls context declarations) =
      (functions declarations).map (fun entry =>
        (entry.1, entry.2.1, globalCompileProg context entry.2.2.1, entry.2.2.2)) := by
  induction declarations with
  | nil => simp [globalCompileDecls, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [globalCompileDecls, functions, functionEntries, ih]

/-- Cake's `compile_decs_exp_ids`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:153`): compiling the
    global declarations does not change the exception identifiers of the
    function bodies. -/
theorem globalCompileDecs_functions_expIds [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (functions (globalCompileDecs context code).functions).map
        (fun entry => expIds entry.2.2.1) =
      (functions code).map (fun entry => expIds entry.2.2.1) := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_expIds context code

theorem functions_globalRenameDecls_map_fst [BEq String] (source target : FunName)
    (declarations : List (Decl α)) :
    ((functions (globalRenameDecls source target declarations)).map
        (fun entry => entry.1)) =
      ((functions declarations).map (fun entry => entry.1)).map
        (globalRenameFunctionName source target) := by
  simp only [functions_globalRenameDecls, List.map_map]
  rfl

/-! Successful-start helper lemma for function-name uniqueness. This uses the
    Option-valued found-start helper, not the total `compile_top` interface. -/
theorem globalCompileTopForStart_names_nodup [BEq String] [LawfulBEq String]
    [Add α] [Mul α] (bytesInWord : α) (fromNat : Nat → α)
    (declarations : List (Decl α)) (start : FunName) (compiled : List (Decl α))
    (hcompile : globalCompileTopForStartSome bytesInWord fromNat declarations start =
      some compiled)
    (hnodup : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions compiled).map (fun entry => entry.1)).Nodup := by
  unfold globalCompileTopForStartSome at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some entry =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      rw [functions_append, functions_append]
      rw [globalCompileDecs_exceptions_eq_filter,
        functions_globalDeclsFilter_globalException, List.nil_append]
      rw [List.map_append]
      simp only [functions, functionEntries, List.map_cons, List.map_nil,
        List.singleton_append]
      rw [globalCompileDecs_functions_names, functions_globalRenameDecls_map_fst,
        functions_globalResortDecls]
      rw [List.nodup_cons]
      refine ⟨?_, ?_⟩
      · intro hmem
        have hmem' : globalNewMainName declarations ∈
            (functions declarations).map (fun entry => entry.1) :=
          (mem_map_globalRenameFunctionName_source start
            (globalNewMainName declarations)
            ((functions declarations).map (fun entry => entry.1))).mp hmem
        rw [← globalFunctionNames_eq_functions_map] at hmem'
        exact globalNewMainName_not_mem declarations hmem'
      · exact nodup_globalRenameFunctionName_map start
          (globalNewMainName declarations) _ hnodup

/-! Cake's `size_of_eids_compile_top`
    (`cakeml/pancake/proofs/pan_to_wordProofScript.sml:364`): the exception
    identifier count is preserved by the whole top-level compilation.  The
    counting lemmas below are the ingredients: appends add, the exception
    filter keeps the same count, and compilation/renaming/partitioning each
    preserve it. -/

theorem sizeOfEids_append (xs ys : List (Decl α)) :
    sizeOfEids (xs ++ ys) = sizeOfEids xs + sizeOfEids ys := by
  induction xs with
  | nil => simp [sizeOfEids]
  | cons d ds ih =>
      rw [List.cons_append, sizeOfEids_cons, sizeOfEids_cons, ih]
      split <;> omega

theorem sizeOfEids_globalDeclsFilter_isException (xs : List (Decl α)) :
    sizeOfEids (globalDeclsFilter globalDeclIsException xs) = sizeOfEids xs := by
  induction xs with
  | nil => simp [globalDeclsFilter, sizeOfEids]
  | cons d ds ih =>
      simp only [globalDeclsFilter]
      by_cases h : globalDeclIsException d = true
      · rw [if_pos h, sizeOfEids_cons, sizeOfEids_cons]
        have hExn : isExnDecl d = true := by
          cases d <;> simp_all [globalDeclIsException, isExnDecl]
        rw [if_pos hExn, if_pos hExn]
        exact congrArg (fun n => 1 + n) ih
      · rw [if_neg h, sizeOfEids_cons]
        have hExn : isExnDecl d = false := by
          cases d <;> simp_all [globalDeclIsException, isExnDecl]
        rw [if_neg (by simp [hExn])]
        exact ih

theorem sizeOfEids_globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (xs : List (Decl α)) :
    sizeOfEids (globalCompileDecls context xs) = sizeOfEids xs := by
  induction xs with
  | nil => simp [globalCompileDecls, sizeOfEids]
  | cons d ds ih =>
      cases d with
      | function fn =>
          simp only [globalCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | exnDecl e sh =>
          simp only [globalCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | decl sh nm v =>
          simp only [globalCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | name nm flds =>
          simp only [globalCompileDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih

theorem sizeOfEids_globalRenameDecls [BEq String] (source target : FunName)
    (xs : List (Decl α)) :
    sizeOfEids (globalRenameDecls source target xs) = sizeOfEids xs := by
  induction xs with
  | nil => simp [globalRenameDecls, sizeOfEids]
  | cons d ds ih =>
      cases d with
      | function fn =>
          simp only [globalRenameDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | exnDecl e sh =>
          simp only [globalRenameDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | decl sh nm v =>
          simp only [globalRenameDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih
      | name nm flds =>
          simp only [globalRenameDecls]
          simpa [sizeOfEids_cons, isExnDecl] using ih

theorem sizeOfEids_globalDeclsFilter_isFunction (xs : List (Decl α)) :
    sizeOfEids (globalDeclsFilter globalDeclIsFunction xs) = 0 := by
  induction xs with
  | nil => simp [globalDeclsFilter, sizeOfEids]
  | cons d ds ih =>
      cases d <;>
        simp_all [globalDeclsFilter, globalDeclIsFunction, sizeOfEids_cons,
          isExnDecl]

theorem sizeOfEids_globalDeclsFilter_isName (xs : List (Decl α)) :
    sizeOfEids (globalDeclsFilter globalDeclIsName xs) = 0 := by
  induction xs with
  | nil => simp [globalDeclsFilter, sizeOfEids]
  | cons d ds ih =>
      cases d <;>
        simp_all [globalDeclsFilter, globalDeclIsName, sizeOfEids_cons,
          isExnDecl]

theorem sizeOfEids_globalDeclsFilter_isGlobal (xs : List (Decl α)) :
    sizeOfEids (globalDeclsFilter globalDeclIsGlobal xs) = 0 := by
  induction xs with
  | nil => simp [globalDeclsFilter, sizeOfEids]
  | cons d ds ih =>
      cases d <;>
        simp_all [globalDeclsFilter, globalDeclIsGlobal, sizeOfEids_cons,
          isExnDecl]

theorem sizeOfEids_globalResortDecls (xs : List (Decl α)) :
    sizeOfEids (globalResortDecls xs) = sizeOfEids xs := by
  rw [globalResortDecls, sizeOfEids_append, sizeOfEids_append, sizeOfEids_append,
    sizeOfEids_globalDeclsFilter_isName,
    sizeOfEids_globalDeclsFilter_isException,
    sizeOfEids_globalDeclsFilter_isGlobal,
    sizeOfEids_globalDeclsFilter_isFunction]
  omega

theorem sizeOfEids_globalCompileDecs_exceptions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    sizeOfEids (globalCompileDecs context code).exceptions = sizeOfEids code := by
  simp only [globalCompileDecs]
  rw [sizeOfEids_globalDeclsFilter_isException, sizeOfEids_globalCompileDecls]

theorem sizeOfEids_globalCompileDecs_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    sizeOfEids (globalCompileDecs context code).functions = 0 := by
  simp only [globalCompileDecs]
  exact sizeOfEids_globalCompileDecsThreaded_functions context code

/-! Successful-start helper lemma for exception-identifier counts. The
    successful-start condition is explicit because the total HOL `compile_top`
    discards declarations on a missing start function. -/
theorem globalCompileTopForStart_sizeOfEids [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α))
    (start : FunName) (compiled : List (Decl α))
    (hcompile : globalCompileTopForStartSome bytesInWord fromNat declarations start =
      some compiled) :
    sizeOfEids compiled = sizeOfEids declarations := by
  unfold globalCompileTopForStartSome at hcompile
  cases hfind : globalFindFunction start declarations with
  | none => simp [hfind] at hcompile
  | some entry =>
      simp only [hfind, Option.some.injEq] at hcompile
      subst hcompile
      have hnil : sizeOfEids ([] : List (Decl α)) = 0 := by
        rw [sizeOfEids.eq_def]
      rw [sizeOfEids_append, sizeOfEids_append,
        sizeOfEids_globalCompileDecs_exceptions,
        sizeOfEids_globalCompileDecs_functions,
        sizeOfEids_globalRenameDecls, sizeOfEids_globalResortDecls]
      simp [sizeOfEids_cons, isExnDecl, hnil]

def globalCompileTop [BEq String] [Add α] [Mul α]
    (bytesInWord : α) (fromNat : Nat → α) (declarations : List (Decl α)) :
    GlobalCompiledProgram α :=
  let initial : GlobalPassContext α :=
    { globals := []
      globalsSize := fromNat 0
      maxGlobalsSize := fromNat 0
      bytesInWord := bytesInWord
      fromNat := fromNat }
  let collected := globalCollect initial declarations
  let context := { collected with maxGlobalsSize := collected.globalsSize }
  let initializerContext := { initial with maxGlobalsSize := collected.globalsSize }
  { initializers := globalCompileInitializers initializerContext declarations
    declarations := globalCompileDecls context declarations
    context := context }

@[simp] theorem globalCompileExp_local [BEq String]
    (context : GlobalPassContext α) (name : VarName) :
    globalCompileExp context (.var .local name) = .var .local name := by
  simp [globalCompileExp]

theorem globalCompileExp_topAddr [BEq String]
    (context : GlobalPassContext α) :
    globalCompileExp context .topAddr =
      .op .sub [.topAddr, .const context.maxGlobalsSize] := by
  simp [globalCompileExp]

theorem globalCompileExp_global [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (name : VarName) (shape : Shape) (address : α)
    (lookup : lookupInfo name context.globals = some (shape, address)) :
    globalCompileExp context (.var .global name) =
      .load shape (.op .sub [.topAddr, .const address]) := by
  simp [globalCompileExp, lookup]

theorem globalCompileProg_seq [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (first second : Prog α) :
    globalCompileProg context (.seq first second) =
      .seq (globalCompileProg context first) (globalCompileProg context second) := by
  simp [globalCompileProg]

theorem globalCollect_decl [Add α] [Mul α]
    (context : GlobalPassContext α) (shape : Shape) (name : String)
    (value : Exp α) :
    (globalCollect context [.decl shape name value]).globalsSize =
      globalAddress context shape := by
  simp [globalCollect]

theorem globalCompileDecsThreaded_functions_thm [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α))
    (hall : declarations.all globalDeclIsFunction = true) :
    (globalCompileDecsThreaded context declarations).initializers = [] ∧
    (globalCompileDecsThreaded context declarations).functions =
      declarations.map (fun declaration => match declaration with
        | .function function =>
            .function { function with
              body := globalCompileProg context function.body }
        | _ => declaration) ∧
    (globalCompileDecsThreaded context declarations).exceptions = [] ∧
    (globalCompileDecsThreaded context declarations).context = context := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [globalCompileDecsThreaded_initializers]
    exact globalCompileInitializers_of_functions context declarations hall
  · exact globalCompileDecsThreaded_functions_of_functions context declarations hall
  · rw [globalCompileDecsThreaded_exceptions_eq_filter]
    refine globalDeclsFilter_eq_nil_of_all_not globalDeclIsException declarations ?_
    refine List.all_eq_true.mpr (fun declaration hmem => ?_)
    have hfunction : globalDeclIsFunction declaration = true :=
      List.all_eq_true.mp hall declaration hmem
    cases declaration <;> simp_all [globalDeclIsFunction, globalDeclIsException]
  · rw [globalCompileDecsThreaded_context]
    exact globalCollect_of_functions context declarations hall

theorem globalCompileDecsThreaded_result_all_function_or_exception [BEq String]
    [Add α] [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α))
    (extra : Decl α) (hextra : globalDeclIsFunction extra = true) :
    ((globalCompileDecsThreaded context declarations).exceptions ++ [extra] ++
        (globalCompileDecsThreaded context declarations).functions).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [globalCompileDecsThreaded_exceptions_eq_filter]
    exact globalDecls_all_or_of_all_left globalDeclIsFunction
      globalDeclIsException _ (globalDeclsFilter_all globalDeclIsException _)
  · simp [hextra]
  · exact globalDecls_all_or_of_all_right globalDeclIsFunction
      globalDeclIsException _
      (globalCompileDecsThreaded_functions_all_isFunction context declarations)

end Flapjack
