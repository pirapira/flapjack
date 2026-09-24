import Flapjack.Pancake.Semantics.LoopSem

/-!
# Properties of the Lean `loopSem` machine state

Counterpart module for `cakeml/pancake/semantics/loopPropsScript.sml`.

The HOL script states properties of `loopSem$get_vars` / `set_vars` and of
`get_var_imm` over the word-length-indexed `loopSem$state`.  As everywhere in
this development the carrier is width-specialized to `BitVec width` with
`[NeZero width]` (HOL word types have positive `dimindex`; `BitVec 0` has no
HOL counterpart), while generic helpers stay untagged.
-/

namespace Flapjack

/-! ## `get_vars`

Faithful port of HOL `loopSem$get_vars` (`loopSemScript.sml:98-106`): read the
listed variables from the machine state's local map in order, failing as soon
as one is absent:

```
(get_vars [] s = SOME []) /\
(get_vars (v::vs) s =
   case lookup v s.locals of
   | NONE => NONE
   | SOME x => case get_vars vs s of
               | NONE => NONE
               | SOME xs => SOME (x::xs))
```

HOL's `s.locals` is an `sptree$num_map` rendered extensionally here as
`LoopMachineState.locals : Nat → Option (LoopValue W)`. -/
def getVars (names : List Nat) (state : LoopMachineState W F) :
    Option (List (LoopValue W)) :=
  match names with
  | [] => some []
  | name :: names =>
      match state.locals name with
      | none => none
      | some value =>
          match getVars names state with
          | none => none
          | some values => some (value :: values)

@[simp] theorem getVars_nil (state : LoopMachineState W F) :
    getVars [] state = some [] := rfl

/-- Width-indexed exact HOL counterpart of `get_vars_def`
    (`loopSemScript.sml:98`). -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "get_vars_def"]
def getVarsHOL {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) :
    Option (List (LoopValue (BitVec width))) :=
  getVars names state

theorem getVarsHOL_eq_getVars {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) :
    getVarsHOL names state = getVars names state := rfl

/-! ## Clock and locals transport properties

These are the `loopPropsScript.sml` lemmas that only observe how `get_vars` and
`get_var_imm` read the local map / clock.  The generic versions are untagged
infrastructure; the tagged statements below are width-indexed. -/

theorem getVars_local_clock_upd_eq (names : List Nat) (state : LoopMachineState W F)
    (locals : Nat → Option (LoopValue W)) (ck : Nat) :
    getVars names { state with locals := locals, clock := ck } =
      getVars names { state with locals := locals } := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [getVars]
      cases h : locals name with
      | none => rfl
      | some value => rw [ih]

theorem getVars_clock_upd_eq (names : List Nat) (state : LoopMachineState W F)
    (ck : Nat) :
    getVars names { state with clock := ck } = getVars names state := by
  induction names with
  | nil => rfl
  | cons name names ih =>
      simp only [getVars]
      rw [ih]

/-- Exact port of HOL `get_var_imm_add_clk_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:251-255`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_var_imm_add_clk_eq"]
theorem getVarImmHOL_add_clock_eq {width : Nat} [NeZero width]
    (operand : RegImm (BitVec width)) (state : LoopMachineState (BitVec width) F)
    (ck : Nat) :
    getVarImmHOL operand { state with clock := ck } = getVarImmHOL operand state := by
  cases operand <;> rfl

/-- Exact port of HOL `get_vars_local_clock_upd_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:260-266`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_local_clock_upd_eq"]
theorem getVarsHOL_local_clock_upd_eq {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F)
    (locals : Nat → Option (LoopValue (BitVec width))) (ck : Nat) :
    getVarsHOL names { state with locals := locals, clock := ck } =
      getVarsHOL names { state with locals := locals } :=
  getVars_local_clock_upd_eq names state locals ck

/-- Exact port of HOL `get_vars_clock_upd_eq`
    (`cakeml/pancake/semantics/loopPropsScript.sml:269-275`). -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "get_vars_clock_upd_eq"]
theorem getVarsHOL_clock_upd_eq {width : Nat} [NeZero width]
    (names : List Nat) (state : LoopMachineState (BitVec width) F) (ck : Nat) :
    getVarsHOL names { state with clock := ck } = getVarsHOL names state :=
  getVars_clock_upd_eq names state ck

end Flapjack
