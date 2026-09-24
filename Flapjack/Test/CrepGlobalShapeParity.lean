import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.Pancake.Semantics.CrepSem.Eval
import Flapjack.Pancake.Semantics.CrepProps

/-!
Direct runtime checks against `scripts/hol-probes/crep_eval_probe.out` and
`crep_store_global_probe.out`. Cake's `crepSem` globals are indexed by `5 word`
and store `word_lab` cells; these checks cover a nonempty read, a missing key,
an insert that preserves a sibling, and a read after `StoreGlob`.
-/

namespace Flapjack.Test.CrepGlobalShapeParity

open Flapjack

def noNatMemory : Nat → PanWordLab Nat := fun _ => .word 0
def noNatDomain : Nat → Bool := fun _ => false

def globalState : CrepRuntimeState Nat Unit :=
  { locals := fun _ => none
    globals := updateCrepRuntimeGlobal
      (updateCrepRuntimeGlobal (fun _ => none) (4 : BitVec 5) (.word 11))
      (8 : BitVec 5) (.word 9)
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    memoryModel := natCrepRuntimeMemoryModel
    bytesInWord := 0
    ffiContext := natCrepRuntimeFfiContext
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

def runtimeHandler : CrepRuntimeFfiHandler Nat Unit Unit :=
  fun _ state => CrepRuntimeFfiResponse.returned state []

def noPrimitive : CrepPrimitiveHandler Nat := fun _ _ => none

/- HOL crep_store_global_probe: set_globals_direct has a hit at global 4,
   preserves the local 3, and leaves local 9 absent. This checks the observable
   update behavior; it does not claim the whole Lean runtime-state type is a
   port of HOL crepSem$state. -/
def directUpdateState : CrepRuntimeState Nat Unit :=
  { globalState with locals := fun name => if name == 3 then some (.word 7) else none }

#guard let state := setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState
       state.globals (4 : BitVec 5) == some (.word 22) &&
       state.locals 3 == some (.word 7) &&
       (state.locals 9).isNone

/- HOL crep_eval_probe: eval_global_hit=SOME (Word 11w). -/
#guard evalCrepRuntimeExp globalState (.loadGlob (4 : BitVec 5)) == some 11
#guard evalCrepRuntimeExp globalState (.loadGlob (36 : BitVec 5)) == some 11

/- HOL crep_eval_probe: eval_global_miss=NONE. -/
#guard (evalCrepRuntimeExp globalState (.loadGlob (12 : BitVec 5))).isNone

/- HOL crep_store_global_probe: StoreGlob inserts the wrapped cell and leaves
   the unrelated global at address eight unchanged. -/
#guard match evalCrepRuntimeProg runtimeHandler noPrimitive 2 globalState
    (.storeGlob (4 : BitVec 5) (.const 22)) with
  | some (.normal, state) =>
      state.globals (4 : BitVec 5) == some (.word 22) &&
      state.globals (8 : BitVec 5) == some (.word 9)
  | _ => false

/- HOL crep_store_global_probe: storing then evaluating LoadGlob returns the
   word_lab value as a Crep expression word. -/
#guard match evalCrepRuntimeProg runtimeHandler noPrimitive 3 globalState
    (.seq (.storeGlob (4 : BitVec 5) (.const 11)) .skip) with
  | some (.normal, state) =>
      evalCrepRuntimeExp state (.loadGlob (4 : BitVec 5)) == some 11
  | _ => false

/- HOL `crepSem$set_globals_def` (crepSemScript.sml:61) is the record update
   `s with globals := s.globals |+ (gv,w)` on the 11-field state. The exact
   HOL-shaped port is `setCrepHolGlobals` over `CrepHolState`; the production
   14-field `setCrepRuntimeGlobals` is the untagged adapter, and
   `setCrepRuntimeGlobals_eq_FUPDATE` records the same body through FUPDATE. -/
example :
    setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState =
      { directUpdateState with
        globals := FUPDATE directUpdateState.globals ((4 : BitVec 5), .word 22) } :=
  setCrepRuntimeGlobals_eq_FUPDATE (4 : BitVec 5) (.word 22) directUpdateState

/- Exact HOL-shaped state fixture for the 11-field `CrepHolState`. -/
def holState : CrepHolState Nat Unit :=
  { locals := fun name => if name == 3 then some (.word 7) else none
    globals := updateCrepRuntimeGlobal (fun _ => none) (4 : BitVec 5) (.word 11)
    code := FEMPTY
    memory := noNatMemory
    memaddrs := noNatDomain
    shMemaddrs := noNatDomain
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

/-- The exact HOL-shaped `setCrepHolGlobals` has HOL's `FUPDATE` body. -/
example :
    setCrepHolGlobals (4 : BitVec 5) (.word 22) holState =
      { holState with globals := FUPDATE holState.globals ((4 : BitVec 5), .word 22) } :=
  rfl

/- HOL `crepProps$FLOOKUP_set_globals` (crepPropsScript.sml:297) over the
   11-field `CrepHolState`: writing a global cell leaves every local lookup
   unchanged. -/
example :
    FLOOKUP (setCrepHolGlobals (4 : BitVec 5) (.word 22) holState).locals 3 =
      FLOOKUP holState.locals 3 :=
  flookup_setCrepHolGlobals_locals (4 : BitVec 5) (.word 22) holState 3

/-- Production adapter: the exact HOL-shaped update commutes with
   `CrepHolState.toRuntime`, so the executable `setCrepRuntimeGlobals` performs
   the same global update. -/
def holState64 : CrepHolState (RiscV.Word 64) Unit :=
  { locals := fun name => if name == 3 then some (.word (7 : RiscV.Word 64)) else none
    globals := updateCrepRuntimeGlobal (fun _ => none) (4 : BitVec 5)
      (.word (11 : RiscV.Word 64))
    code := FEMPTY
    memory := fun _ => .word 0
    memaddrs := fun _ => false
    shMemaddrs := fun _ => false
    clock := 3
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := 12
    topAddress := 13 }

example :
    (setCrepHolGlobals (4 : BitVec 5) (.word (22 : RiscV.Word 64)) holState64).toRuntime =
      setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) holState64.toRuntime :=
  setCrepHolGlobals_toRuntime (4 : BitVec 5) (.word 22) holState64

/-- Production routing: `setCrepRuntimeGlobals` derives its globals component
   from the tagged HOL-shaped `setCrepHolGlobals` on `toHolState`. -/
example :
    (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).toHolState =
      setCrepHolGlobals (4 : BitVec 5) (.word 22) directUpdateState.toHolState :=
  setCrepRuntimeGlobals_toHolState (4 : BitVec 5) (.word 22) directUpdateState

/-- The three runtime configuration fields survive the production StoreGlob
   update unchanged. -/
example :
    (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).memoryModel =
        directUpdateState.memoryModel ∧
      (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).bytesInWord =
        directUpdateState.bytesInWord ∧
      (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).ffiContext =
        directUpdateState.ffiContext :=
  ⟨rfl, rfl, rfl⟩

/- Untagged production adapter: writing a global cell on the 14-field runtime
   state leaves every local lookup unchanged. -/
example :
    FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 3 =
      FLOOKUP directUpdateState.locals 3 :=
  flookup_setCrepRuntimeGlobals_locals (4 : BitVec 5) (.word 22) directUpdateState 3

#guard FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 3 ==
    some (.word 7) &&
  FLOOKUP (setCrepRuntimeGlobals (4 : BitVec 5) (.word 22) directUpdateState).locals 9 == none

/- HOL `crep_fix_clock_probe`: `fix_clock` (crepSemScript.sml:150-152) keeps the
   result, clamps the clock to the smaller of old/new, and preserves locals.
   These checks use the 11-field `CrepHolState`; they do not claim a whole
   program evaluator. -/
def holBase : CrepHolState Nat Unit := directUpdateState.toHolState

-- fix_clock_clamps: old clock 5, new clock 9 -> 5.
example :
    (fixCrepHolClock { holBase with clock := 5 }
      ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), { holBase with clock := 9 })).2.clock = 5 := by
  simp [fixCrepHolClock]

-- fix_clock_keeps_lower: old clock 5, new clock 3 -> 3.
example :
    (fixCrepHolClock { holBase with clock := 5 }
      ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), { holBase with clock := 3 })).2.clock = 3 := by
  simp [fixCrepHolClock]

-- Result preserved.
example :
    (fixCrepHolClock holBase ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), holBase)).1 =
      (CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit) := rfl

-- Locals preserved.
example :
    (fixCrepHolClock holBase ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), holBase)).2.locals =
      holBase.locals := rfl

-- `fix_clock_IMP_LESS_EQ` bound.
example :
    (fixCrepHolClock { holBase with clock := 5 }
      ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), { holBase with clock := 9 })).2.clock ≤ 5 :=
  fixCrepHolClock_clock_le { holBase with clock := 5 } (CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit)
    { holBase with clock := 9 }

#guard (fixCrepHolClock { holBase with clock := 5 }
          ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), { holBase with clock := 9 })).2.clock == 5 &&
        (fixCrepHolClock { holBase with clock := 5 }
          ((CrepRuntimeResult.normal : CrepRuntimeResult Nat Unit), { holBase with clock := 3 })).2.clock == 3

/- HOL `crep_local_updates_probe`: exact `set_var_def`/`upd_locals_def`/
   `empty_locals_def` (crepSemScript.sml:55-73) over the 11-field
   `CrepHolState`. These are local-state helpers only, not a program
   evaluator. -/
def localBase : CrepHolState Nat Unit :=
  { holBase with
    locals := FUPDATE (FEMPTY : FiniteMap Nat (PanWordLab Nat))
      ((2 : Nat), PanWordLab.word (9 : Nat))
    clock := 5
    baseAddress := 3
    topAddress := 100 }

-- set_var_hit.
example :
    FLOOKUP (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).locals 1 =
      some (PanWordLab.word (7 : Nat)) := by
  rfl

-- set_var_keeps_other.
example :
    FLOOKUP (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).locals 2 =
      some (PanWordLab.word (9 : Nat)) := by
  rfl

-- upd_locals_replace: `FEMPTY |++ varargs`, so the old binding is dropped.
example :
    FLOOKUP (updCrepHolLocals [(1, PanWordLab.word (3 : Nat))] localBase).locals 1 =
        some (PanWordLab.word (3 : Nat)) ∧
      FLOOKUP (updCrepHolLocals [(1, PanWordLab.word (3 : Nat))] localBase).locals 2 =
        none := by
  constructor <;> rfl

-- empty_locals_none.
example :
    FLOOKUP (emptyCrepHolLocals localBase).locals 2 = none := by
  rfl

-- set_var_fields_preserved.
example :
    (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).clock = 5 ∧
      (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).baseAddress = 3 ∧
      (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).topAddress = 100 :=
  ⟨rfl, rfl, rfl⟩

-- empty_locals_fields_preserved.
example :
    (emptyCrepHolLocals localBase).clock = 5 ∧
      (emptyCrepHolLocals localBase).memory = localBase.memory :=
  ⟨rfl, rfl⟩

#guard FLOOKUP (setCrepHolVar 1 (PanWordLab.word (7 : Nat)) localBase).locals 1 ==
          some (PanWordLab.word (7 : Nat)) &&
        FLOOKUP (updCrepHolLocals [(1, PanWordLab.word (3 : Nat))] localBase).locals 2 ==
          none &&
        FLOOKUP (emptyCrepHolLocals localBase).locals 2 == none

/-! ## Production local-update adapters to the tagged HOL local defs

These are Flapjack-only (untagged) bridge lemmas connecting the runtime
`updateCrepRuntimeLocal`/`clearCrepRuntimeLocals`/`assignCrepRuntimeLocals`
state updates to the tagged HOL `setCrepHolVar`/`updCrepHolLocals`/
`emptyCrepHolLocals` definitions on the 11-field projection. -/

-- HOL `crepSem$set_var_def` body on the function-represented locals map.
example :
    updateCrepRuntimeLocal directUpdateState.locals 3 (.word (9 : Nat)) =
      FUPDATE directUpdateState.locals (3, PanWordLab.word (9 : Nat)) :=
  updateCrepRuntimeLocal_eq_FUPDATE directUpdateState.locals 3 (.word (9 : Nat))

-- Production `setCrepRuntimeLocal` is the same record update.
example :
    setCrepRuntimeLocal 3 (.word (9 : Nat)) directUpdateState =
      { directUpdateState with
        locals :=
          updateCrepRuntimeLocal directUpdateState.locals 3 (.word (9 : Nat)) } :=
  setCrepRuntimeLocal_eq_update 3 (.word (9 : Nat)) directUpdateState

-- Commutes with the tagged HOL `setCrepHolVar` under `toHolState`.
example :
    (setCrepRuntimeLocal 3 (.word (9 : Nat)) directUpdateState).toHolState =
      setCrepHolVar 3 (PanWordLab.word (9 : Nat)) directUpdateState.toHolState :=
  setCrepRuntimeLocal_toHolState 3 (.word (9 : Nat)) directUpdateState

-- Commutes with the tagged HOL `emptyCrepHolLocals` under `toHolState`.
example :
    (clearCrepRuntimeLocals directUpdateState).toHolState =
      emptyCrepHolLocals directUpdateState.toHolState :=
  clearCrepRuntimeLocals_toHolState directUpdateState

-- Production `assignCrepRuntimeLocals` is HOL's `|++`/`FUPDATE_LIST` fold.
example :
    assignCrepRuntimeLocals directUpdateState.locals [1, 2] [(5 : Nat), 6] =
      some (FUPDATE_LIST directUpdateState.locals
        [(1, PanWordLab.word (5 : Nat)), (2, PanWordLab.word (6 : Nat))]) := by
  rw [assignCrepRuntimeLocals_eq_FUPDATE_LIST]
  rfl

-- `Call`-clause callee setup from the empty map is HOL's `upd_locals` body.
example :
    assignCrepRuntimeLocals (fun _ => none) [1, 2] [(5 : Nat), 6] =
      some (FUPDATE_LIST FEMPTY
        [(1, PanWordLab.word (5 : Nat)), (2, PanWordLab.word (6 : Nat))]) :=
  assignCrepRuntimeLocals_empty_eq [1, 2] [(5 : Nat), 6] rfl

-- Writing that map into a state projects to the tagged HOL `updCrepHolLocals`.
example :
    ({ directUpdateState with
        locals := FUPDATE_LIST FEMPTY
          [(1, PanWordLab.word (5 : Nat)), (2, PanWordLab.word (6 : Nat))] }).toHolState =
      updCrepHolLocals
        [(1, PanWordLab.word (5 : Nat)), (2, PanWordLab.word (6 : Nat))]
        directUpdateState.toHolState :=
  setCrepRuntimeLocalsFEMPTY_toHolState _ directUpdateState

-- The primitive/`Dec` production fold routes through `setCrepRuntimeLocal`
-- (hence the tagged HOL `set_var`), agreeing with the raw locals fold.
example :
    (List.foldl (fun s (p : Nat × Nat) => setCrepRuntimeLocal p.1 (.word p.2) s)
        directUpdateState [(1, 5), (2, 6)]).locals =
      List.foldl (fun l (p : Nat × Nat) => updateCrepRuntimeLocal l p.1 (.word p.2))
        directUpdateState.locals [(1, 5), (2, 6)] := by
  rw [foldl_setCrepRuntimeLocal_eq [(1, 5), (2, 6)] directUpdateState]

-- The state-level primitive local assignment agrees with the locals-level one.
example :
    setCrepRuntimeLocalsExisting [1, 2] [(5 : Nat), 6] directUpdateState =
      (crepRuntimeAssignExisting directUpdateState.locals [1, 2] [(5 : Nat), 6]).map
        (fun locals => { directUpdateState with locals := locals }) :=
  setCrepRuntimeLocalsExisting_eq [1, 2] [(5 : Nat), 6] directUpdateState

-- Concrete observations mirroring crep_local_updates_probe.out under the
-- production adapters.
#guard FLOOKUP (setCrepRuntimeLocal 3 (.word (9 : Nat)) directUpdateState).toHolState.locals 3 ==
          some (PanWordLab.word (9 : Nat)) &&
        FLOOKUP (setCrepRuntimeLocal 5 (.word (9 : Nat)) directUpdateState).toHolState.locals 3 ==
          some (PanWordLab.word (7 : Nat)) &&
        (FLOOKUP (clearCrepRuntimeLocals directUpdateState).toHolState.locals 3).isNone

/-! ## Call-path destination update

The executable `crepRuntimeCall` returned-with-destinations branch now runs the
local assignment through `setCrepRuntimeLocalsExisting`, whose fold routes the
tagged HOL `set_var` (`setCrepRuntimeLocal`) and whose failure checks are
unchanged. HOL `crepSem$upd_locals` (`|++`, `FUPDATE_LIST`) is pinned by
`crep_local_updates_probe.out` (`upd_locals_replace=T`) and
`crep_locals_wordlab_probe.out` (`locals_upd_locals_cells`). -/

/-- State with destination locals 1 and 2 already present, as the Call path
    requires (HOL assigns onto existing word variables). -/
def callDestState : CrepRuntimeState Nat Unit :=
  { directUpdateState with
    locals := fun name =>
      if name == 1 then some (.word 0) else if name == 2 then some (.word 0)
      else directUpdateState.locals name }

/-- The production Call-destination helper updates the listed locals and keeps
    the others, exactly like HOL `upd_locals`/`FUPDATE_LIST`. -/
example :
    (setCrepRuntimeLocalsExisting [1, 2] [(5 : Nat), 6] callDestState).map
        (fun state => (FLOOKUP state.locals 1, FLOOKUP state.locals 2, FLOOKUP state.locals 3, FLOOKUP state.locals 9)) =
      some (some (.word 5), some (.word 6), some (.word 7), none) := by
  rfl

/-- The Call-destination helper keeps HOL's failure behavior: a length mismatch
    and a missing destination local both return `none`. -/
example :
    setCrepRuntimeLocalsExisting [1, 2] [(5 : Nat)] callDestState = none ∧
      setCrepRuntimeLocalsExisting [9] [(5 : Nat)] callDestState = none := by
  constructor <;> rfl

#guard (setCrepRuntimeLocalsExisting [1, 2] [(5 : Nat), 6] callDestState).map
          (fun state => (FLOOKUP state.locals 1, FLOOKUP state.locals 2, FLOOKUP state.locals 3)) ==
        some (some (.word 5), some (.word 6), some (.word 7)) &&
      (setCrepRuntimeLocalsExisting [1, 2] [(5 : Nat)] callDestState).isNone &&
      (setCrepRuntimeLocalsExisting [9] [(5 : Nat)] callDestState).isNone

/-- Exact HOL `lookup_code_def` over the finite map. Mirrors the direct HOL
    oracle `scripts/hol-probes/crep_lookup_code_probe.out`
    (`lookup_code_valid=SOME (Word 7w)`, `lookup_code_missing=NONE`). -/
def lookupCodeMap : FunName → Option (List Nat × CrepProg Nat) :=
  fun name => if name == "id" then some ([1], CrepProg.skip) else none

example :
    (lookupCrepHolCode lookupCodeMap "id" [PanWordLab.word 7]).map
        (fun pair => FLOOKUP pair.2 1) = some (some (PanWordLab.word 7)) := by
  rfl

example : lookupCrepHolCode lookupCodeMap "missing" [] = none := by
  rfl

#guard (lookupCrepHolCode lookupCodeMap "id" [PanWordLab.word 7]).map
          (fun pair => FLOOKUP pair.2 1) == some (some (PanWordLab.word 7)) &&
        (lookupCrepHolCode lookupCodeMap "missing" []).isNone &&
        (lookupCrepHolCode lookupCodeMap "id" [PanWordLab.word 7, PanWordLab.word 8]).isNone

/-- HOL `crepSem$mem_load_def` over the 11-field state: valid cell read and
    out-of-domain miss, matching `scripts/hol-probes/crep_mem_load_probe.out`
    (`mem_load_valid=SOME (Word 7w)`, `mem_load_invalid=NONE`). -/
def memLoadBase : CrepHolState Nat Unit :=
  { holBase with
    memory := fun address => if address == 8 then .word 7 else .word 0
    memaddrs := fun address => address == 8 }

example : memLoadCrepHol (8 : Nat) memLoadBase = some (.word 7) := by
  rfl

example : memLoadCrepHol (9 : Nat) memLoadBase = none := by
  rfl

/-- The production runtime load is the tagged HOL `mem_load` on `toHolState`. -/
example : crepRuntimeLoad globalState (8 : Nat) =
    (memLoadCrepHol (8 : Nat) globalState.toHolState).map panTheWord :=
  crepRuntimeLoad_eq_memLoadCrepHol globalState (8 : Nat)

#guard (memLoadCrepHol (8 : Nat) memLoadBase == some (.word 7)) &&
  (memLoadCrepHol (9 : Nat) memLoadBase).isNone

/-- Direct observations of the width-polymorphic tagged HOL `crep_op_def` port
    `crepOpCrep`, matching `scripts/hol-probes/crep_op_probe.out` (HOL uses
    `64 word`, i.e. `BitVec 64`):
    `op_mul_two=SOME 21w`, `op_mul_one/op_mul_three/op_mul_empty=NONE`. -/
example : crepOpCrep 64 .mul [(7 : BitVec 64), 3] = some 21 := by rfl

example : crepOpCrep 64 .mul [(7 : BitVec 64)] = none := by rfl

example : crepOpCrep 64 .mul [(7 : BitVec 64), 3, 1] = none := by rfl

example : crepOpCrep 64 .mul ([] : List (BitVec 64)) = none := by rfl

/-- Width polymorphism: the tagged port also works at 8-bit words. -/
example : crepOpCrep 8 .mul [(7 : BitVec 8), 3] = some 21 := by rfl

/-- The tagged port equals the generic untagged helper at every width. -/
example : crepOpCrep 64 .mul [(7 : BitVec 64), 3] = crepOpValue .mul [(7 : BitVec 64), 3] := by
  rw [crepOpCrep_eq_crepOpValue]

/-- The production `.crepOp` evaluator clause is the HOL `OPT_MMAP`-then-`crep_op`
    shape: at `.mul` the evaluated operands feed the generic value helper
    `crepOpValue`, which is the tagged `crepOpCrep` at `BitVec width`. -/
example :
    evalCrepRuntimeExp globalState (.crepOp .mul [.const (7 : Nat), .const 3]) =
      some 21 := by
  simp [evalCrepRuntimeExp]

#guard (crepOpCrep 64 .mul [(7 : BitVec 64), 3] == some 21) &&
  (crepOpCrep 64 .mul [(7 : BitVec 64)]).isNone &&
  (crepOpCrep 64 .mul [(7 : BitVec 64), 3, 1]).isNone &&
  (crepOpCrep 64 .mul ([] : List (BitVec 64))).isNone

/-- Canonical RISC-V 64 runtime state used for the executed `.crepOp` path. -/
def bv64State : CrepRuntimeState (RiscV.Word 64) Unit :=
  ({ locals := fun _ => none, globals := FEMPTY, code := FEMPTY,
     memory := fun _ => .word 0, memaddrs := fun _ => false,
     shMemaddrs := fun _ => false, clock := 1, bigEndian := false,
     ffi := natCrepRuntimeFfiState, baseAddress := 0, topAddress := 0 } :
    CrepHolState (RiscV.Word 64) Unit).toRuntime

/-- Canonical RV64 executed-path instantiation: evaluating `.crepOp .mul` on a
    `BitVec 64` runtime state is the tagged `crepOpCrep 64`, via the generic
    `crepOpValue` helper and `crepOpCrep_eq_crepOpValue`. -/
example :
    evalCrepRuntimeExp bv64State
        (.crepOp .mul [.const (7 : RiscV.Word 64), .const (3 : RiscV.Word 64)]) =
      crepOpCrep 64 .mul [(7 : RiscV.Word 64), 3] := by
  rw [evalCrepRuntimeExp_crepOp_eq, crepOpCrep_eq_crepOpValue]
  simp only [evalCrepRuntimeExp]

#guard evalCrepRuntimeExp bv64State
    (.crepOp .mul [.const (7 : RiscV.Word 64), .const (3 : RiscV.Word 64)]) == some 21

end Flapjack.Test.CrepGlobalShapeParity
