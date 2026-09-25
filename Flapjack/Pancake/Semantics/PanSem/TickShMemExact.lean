import Flapjack.Pancake.Semantics.PanSem.StoreExact
import Flapjack.Pancake.Semantics.PanSem.ShMemExact

/-! # Exact panSem `Tick` and `ShMemLoad`/`ShMemStore` clause steps

HOL `panSem$evaluate` (`cakeml/pancake/semantics/panSemScript.sml`):

* `Tick` (`:653-655`): `if s.clock = 0 then (SOME TimeOut, empty_locals s)
  else (NONE, dec_clock s)`.
* `ShMemLoad` (`:604-610`): `case eval s ad of SOME (ValWord addr) =>
  (case lookup_kvar vk v s of SOME (ValWord _) => sh_mem_load vk v addr (nb_op op) s
   | _ => (SOME Error, s)) | _ => (SOME Error, s)`.
* `ShMemStore` (`:611-614`): `case (eval s ad, eval s e) of
  (SOME (ValWord addr), SOME (ValWord bytes)) => sh_mem_store bytes addr (nb_op op) s
  | _ => (SOME Error, s)`.

The `Tick` step is a closed exact clause over the exact `PanSemStateExact`
carrier. The shared-memory clause steps are callback-parameterised over the
exact `sh_mem_load`/`sh_mem_store` bodies (owned as separate exact-carrier
definitions); the evaluate-level argument checks are proved here. These
declarations are clause-level infrastructure and are deliberately NOT tagged
with `evaluate_def` (that tag belongs to the whole fourteen-clause conjunction).
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- Exact HOL `Tick` clause (`panSemScript.sml:653-655`) over the exact
`mlstring`-keyed source state: at clock zero a timeout with cleared locals,
otherwise normal completion with the clock decremented. -/
def tickStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  if state.clock = 0 then
    (some .timeOut, emptyLocalsHOLExact state)
  else
    (none, decClockHOLExact state)

@[simp]
theorem tickStepHOLExact_clock_zero {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (hclock : state.clock = 0) :
    tickStepHOLExact state = (some .timeOut, emptyLocalsHOLExact state) := by
  simp [tickStepHOLExact, hclock]

theorem tickStepHOLExact_clock_pos {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (hclock : state.clock ≠ 0) :
    tickStepHOLExact state = (none, decClockHOLExact state) := by
  simp [tickStepHOLExact, hclock]

/-- Exact HOL `ShMemLoad` clause (`panSemScript.sml:604-610`) over the exact
`mlstring`-keyed source state. The actual shared-memory effect is delegated to
`runShMemLoad`, which must be the exact `sh_mem_load`; this step only performs
the HOL argument checks (address evaluates to a word, destination kind/name is a
current word-valued binding) and passes `nb_op op`. -/
def shMemLoadStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemLoad : VarKind → MlS → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match lookupKvarHOLExact kind name state with
      | some (.val (.word _)) => runShMemLoad kind name addr (nbOpHOL operator) state
      | _ => (some .error, state)
  | _ => (some .error, state)

theorem shMemLoadStepHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemLoad : VarKind → MlS → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (addr : RiscV.Word width) (word : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hlocal : lookupKvarHOLExact kind name state = some (.val (.word word))) :
    shMemLoadStepHOLExact state operator kind name address evalExpression runShMemLoad =
      runShMemLoad kind name addr (nbOpHOL operator) state := by
  simp only [shMemLoadStepHOLExact, haddr, hlocal]

theorem shMemLoadStepHOLExact_address_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemLoad : VarKind → MlS → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (haddr : evalExpression state address = none) :
    shMemLoadStepHOLExact state operator kind name address evalExpression runShMemLoad =
      (some .error, state) := by
  simp only [shMemLoadStepHOLExact, haddr]

theorem shMemLoadStepHOLExact_local_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemLoad : VarKind → MlS → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (addr : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hlocal : lookupKvarHOLExact kind name state = none) :
    shMemLoadStepHOLExact state operator kind name address evalExpression runShMemLoad =
      (some .error, state) := by
  simp only [shMemLoadStepHOLExact, haddr, hlocal]

theorem shMemLoadStepHOLExact_local_rStruct {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemLoad : VarKind → MlS → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (addr : RiscV.Word width) (fields : List (ValueHOL width))
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hlocal : lookupKvarHOLExact kind name state = some (.rStruct fields)) :
    shMemLoadStepHOLExact state operator kind name address evalExpression runShMemLoad =
      (some .error, state) := by
  simp only [shMemLoadStepHOLExact, haddr, hlocal]

/-- Exact HOL `ShMemStore` clause (`panSemScript.sml:611-614`) over the exact
`mlstring`-keyed source state. The actual shared-memory effect is delegated to
`runShMemStore`, which must be the exact `sh_mem_store`; this step only performs
the HOL argument checks (address and value both evaluate to words) and passes
the value, address and `nb_op op`. -/
def shMemStoreStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemStore : RiscV.Word width → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match evalExpression state value with
      | some (.val (.word bytes)) => runShMemStore bytes addr (nbOpHOL operator) state
      | _ => (some .error, state)
  | _ => (some .error, state)

theorem shMemStoreStepHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemStore : RiscV.Word width → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (addr bytes : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hvalue : evalExpression state value = some (.val (.word bytes))) :
    shMemStoreStepHOLExact state operator address value evalExpression runShMemStore =
      runShMemStore bytes addr (nbOpHOL operator) state := by
  simp only [shMemStoreStepHOLExact, haddr, hvalue]

theorem shMemStoreStepHOLExact_address_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemStore : RiscV.Word width → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (haddr : evalExpression state address = none) :
    shMemStoreStepHOLExact state operator address value evalExpression runShMemStore =
      (some .error, state) := by
  simp only [shMemStoreStepHOLExact, haddr]

theorem shMemStoreStepHOLExact_value_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (operator : OpSize)
    (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (runShMemStore : RiscV.Word width → RiscV.Word width → Nat →
      PanSemStateExact width σ → Option (PanSemResultExact width) × PanSemStateExact width σ)
    (addr : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hvalue : evalExpression state value = some (.rStruct [])) :
    shMemStoreStepHOLExact state operator address value evalExpression runShMemStore =
      (some .error, state) := by
  simp only [shMemStoreStepHOLExact, haddr, hvalue]

/-- The exact HOL `ShMemLoad` clause: the evaluate-level argument checks plus
the exact `sh_mem_load` body (`shMemLoadHOLExact`) at `nb_op op`. -/
def shMemLoadClauseHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match lookupKvarHOLExact kind name state with
      | some (.val (.word _)) => shMemLoadHOLExact state kind name addr (nbOpHOL operator)
      | _ => (some .error, state)
  | _ => (some .error, state)

theorem shMemLoadClauseHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (addr word : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hlocal : lookupKvarHOLExact kind name state = some (.val (.word word))) :
    shMemLoadClauseHOLExact state operator kind name address evalExpression =
      shMemLoadHOLExact state kind name addr (nbOpHOL operator) := by
  simp only [shMemLoadClauseHOLExact, haddr, hlocal]

theorem shMemLoadClauseHOLExact_local_none {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (addr : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hlocal : lookupKvarHOLExact kind name state = none) :
    shMemLoadClauseHOLExact state operator kind name address evalExpression =
      (some .error, state) := by
  simp only [shMemLoadClauseHOLExact, haddr, hlocal]

/-- The exact HOL `ShMemStore` clause: the evaluate-level argument checks plus
the exact `sh_mem_store` body (`shMemStoreHOLExact`) at `nb_op op`. -/
def shMemStoreClauseHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state address with
  | some (.val (.word addr)) =>
      match evalExpression state value with
      | some (.val (.word bytes)) => shMemStoreHOLExact state bytes addr (nbOpHOL operator)
      | _ => (some .error, state)
  | _ => (some .error, state)

theorem shMemStoreClauseHOLExact_ok {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (addr bytes : RiscV.Word width)
    (haddr : evalExpression state address = some (.val (.word addr)))
    (hvalue : evalExpression state value = some (.val (.word bytes))) :
    shMemStoreClauseHOLExact state operator address value evalExpression =
      shMemStoreHOLExact state bytes addr (nbOpHOL operator) := by
  simp only [shMemStoreClauseHOLExact, haddr, hvalue]

/-- The exact shared-memory load clause changes data/local/FFI fields only; it
    leaves both memory-domain predicates available to the recursive context. -/
theorem shMemLoadClauseHOLExact_preservesDomains {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.memaddrs =
        state.memaddrs ∧
    (shMemLoadClauseHOLExact state operator kind name address evalExpression).2.shMemaddrs =
        state.shMemaddrs := by
  constructor
  · unfold shMemLoadClauseHOLExact shMemLoadHOLExact
    all_goals (repeat' (first | split))
    all_goals simp [emptyLocalsHOLExact, setKvarHOLExact]
    all_goals cases kind <;> rfl
  · unfold shMemLoadClauseHOLExact shMemLoadHOLExact
    all_goals (repeat' (first | split))
    all_goals simp [emptyLocalsHOLExact, setKvarHOLExact]
    all_goals cases kind <;> rfl

/-- The exact shared-memory store clause leaves both memory-domain predicates
    unchanged; its successful case only updates the FFI field. -/
theorem shMemStoreClauseHOLExact_preservesDomains {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.memaddrs =
        state.memaddrs ∧
    (shMemStoreClauseHOLExact state operator address value evalExpression).2.shMemaddrs =
        state.shMemaddrs := by
  constructor
  · unfold shMemStoreClauseHOLExact shMemStoreHOLExact
    all_goals (repeat' (first | split))
    all_goals simp
  · unfold shMemStoreClauseHOLExact shMemStoreHOLExact
    all_goals (repeat' (first | split))
    all_goals simp

end Flapjack
