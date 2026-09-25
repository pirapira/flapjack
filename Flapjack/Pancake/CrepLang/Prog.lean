import Flapjack.Pancake.CrepLang.Exp
import Flapjack.Pancake.PanLang

/-!
Exact width-indexed carrier for the Crepe program syntax.

`cakeml/pancake/crepLangScript.sml:41-66` defines

```
Datatype:
  prog = Skip
       | Dec varname ('a exp) prog
       | Assign    varname  ('a exp)
       | Primitive (varname list) panLang$primop (varname list)
       | Store     ('a exp) ('a exp)
       | Store32 ('a exp) ('a exp)
       | StoreByte ('a exp) ('a exp)
       | StoreGlob (5 word) ('a exp)
       | Seq prog prog
       | If    ('a exp) prog prog
       | While ('a exp) prog
       | Break num
       | Continue num
       | Call (((varname list) # ((('a word) # prog) option)) option)
              funname (('a exp) list)
       | ExtCall funname varname varname varname varname
       | Raise ('a word)
       | Return (('a exp) list)
       | ShMem memop varname ('a exp)
       | Tick;
End
```

The production `Flapjack.CrepProg (α)` in `Flapjack/Pancake/CrepLang.lean` is
generic over `α` and stores its `Call`/`ExtCall` names as `String`, so it is
not an exact port (HOL `funname = mlstring`); it stays untagged.
`CrepProgHOL` is the exact carrier: the word type is `BitVec width` with
`[NeZero width]`, the function names are the faithful `MlString`, and the
expression/`ShMem` payloads use the exact `CrepExpHOL`/`CrepMemOp` carriers.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Exact port of `crepLang$prog` (`cakeml/pancake/crepLangScript.sml:41-66`):
19 constructors in HOL order, `funname` as the faithful `MlString`, `varname`
as `Nat`, the `'a exp` payload as `CrepExpHOL width`, the `('a word)` payloads
as `BitVec width`, and `memop` as `CrepMemOp`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "prog"]
inductive CrepProgHOL (width : Nat) [NeZero width] where
  | skip
  | dec (name : Nat) (value : CrepExpHOL width) (body : CrepProgHOL width)
  | assign (name : Nat) (value : CrepExpHOL width)
  | primitive (names : List Nat) (operator : PrimOp) (args : List Nat)
  | store (address value : CrepExpHOL width)
  | store32 (address value : CrepExpHOL width)
  | storeByte (address value : CrepExpHOL width)
  | storeGlob (address : BitVec 5) (value : CrepExpHOL width)
  | seq (first second : CrepProgHOL width)
  | ite (condition : CrepExpHOL width) (thenBranch elseBranch : CrepProgHOL width)
  | while (condition : CrepExpHOL width) (body : CrepProgHOL width)
  | break (label : Nat)
  | continue (label : Nat)
  | call (returnInfo : Option (List Nat × Option (BitVec width × CrepProgHOL width)))
      (name : MlString) (args : List (CrepExpHOL width))
  | extCall (function : MlString) (configuration configurationLength array arrayLength : Nat)
  | raise (exception : BitVec width)
  | return (values : List (CrepExpHOL width))
  | shMem (operator : CrepMemOp) (name : Nat) (address : CrepExpHOL width)
  | tick
  deriving Repr

/-- `NameRanged` for the production `String` function names: every code unit is
a byte, so `MlString.ofString`/`toStringOfBytes` round-trip exactly. -/
def CrepNameRanged (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 256

/-- Production-to-HOL direction: forget the exact carrier. -/
def crepProgToHOL {width : Nat} [NeZero width] : CrepProg (BitVec width) → CrepProgHOL width
  | .skip => .skip
  | .dec name value body => .dec name (crepExpToHOL value) (crepProgToHOL body)
  | .assign name value => .assign name (crepExpToHOL value)
  | .primitive names operator args => .primitive names operator args
  | .store address value => .store (crepExpToHOL address) (crepExpToHOL value)
  | .store32 address value => .store32 (crepExpToHOL address) (crepExpToHOL value)
  | .storeByte address value => .storeByte (crepExpToHOL address) (crepExpToHOL value)
  | .storeGlob address value => .storeGlob address (crepExpToHOL value)
  | .seq first second => .seq (crepProgToHOL first) (crepProgToHOL second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepExpToHOL condition) (crepProgToHOL thenBranch) (crepProgToHOL elseBranch)
  | .while condition body => .while (crepExpToHOL condition) (crepProgToHOL body)
  | .break label => .break label
  | .continue label => .continue label
  | .call none name args => .call none (ofString name) (args.map crepExpToHOL)
  | .call (some (returns, none)) name args =>
      .call (some (returns, none)) (ofString name) (args.map crepExpToHOL)
  | .call (some (returns, some (handler, body))) name args =>
      .call (some (returns, some (handler, crepProgToHOL body))) (ofString name)
        (args.map crepExpToHOL)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall (ofString function) configuration configurationLength array arrayLength
  | .raise exception => .raise exception
  | .return values => .return (values.map crepExpToHOL)
  | .shMem operator name address => .shMem operator name (crepExpToHOL address)
  | .tick => .tick
termination_by p => sizeOf p
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProg.dec.sizeOf_spec, CrepProg.seq.sizeOf_spec,
        CrepProg.ite.sizeOf_spec, CrepProg.while.sizeOf_spec, CrepProg.call.sizeOf_spec];
       omega)

/-- HOL-to-production direction: the exact carrier is a `CrepProg` at the same
width, with the `MlString` names decoded to `String`. -/
def crepProgOfHOL {width : Nat} [NeZero width] : CrepProgHOL width → CrepProg (BitVec width)
  | .skip => .skip
  | .dec name value body => .dec name (crepExpOfHOL value) (crepProgOfHOL body)
  | .assign name value => .assign name (crepExpOfHOL value)
  | .primitive names operator args => .primitive names operator args
  | .store address value => .store (crepExpOfHOL address) (crepExpOfHOL value)
  | .store32 address value => .store32 (crepExpOfHOL address) (crepExpOfHOL value)
  | .storeByte address value => .storeByte (crepExpOfHOL address) (crepExpOfHOL value)
  | .storeGlob address value => .storeGlob address (crepExpOfHOL value)
  | .seq first second => .seq (crepProgOfHOL first) (crepProgOfHOL second)
  | .ite condition thenBranch elseBranch =>
      .ite (crepExpOfHOL condition) (crepProgOfHOL thenBranch) (crepProgOfHOL elseBranch)
  | .while condition body => .while (crepExpOfHOL condition) (crepProgOfHOL body)
  | .break label => .break label
  | .continue label => .continue label
  | .call none name args => .call none (toStringOfBytes name) (args.map crepExpOfHOL)
  | .call (some (returns, none)) name args =>
      .call (some (returns, none)) (toStringOfBytes name) (args.map crepExpOfHOL)
  | .call (some (returns, some (handler, body))) name args =>
      .call (some (returns, some (handler, crepProgOfHOL body))) (toStringOfBytes name)
        (args.map crepExpOfHOL)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall (toStringOfBytes function) configuration configurationLength array arrayLength
  | .raise exception => .raise exception
  | .return values => .return (values.map crepExpOfHOL)
  | .shMem operator name address => .shMem operator name (crepExpOfHOL address)
  | .tick => .tick
termination_by p => sizeOf p
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec, CrepProgHOL.call.sizeOf_spec];
       omega)

@[simp] theorem crepExpMapToHOL_ofHOL {width : Nat} [NeZero width]
    (l : List (CrepExpHOL width)) :
    l.map (crepExpToHOL ∘ crepExpOfHOL) = l := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [Function.comp_apply, ih]

@[simp] theorem crepExpMapOfHOL_toHOL {width : Nat} [NeZero width]
    (l : List (CrepExp (BitVec width))) :
    l.map (crepExpOfHOL ∘ crepExpToHOL) = l := by
  induction l with
  | nil => rfl
  | cons head tail ih => simp [Function.comp_apply, ih]

@[simp] theorem crepProgToHOL_crepProgOfHOL {width : Nat} [NeZero width] :
    (p : CrepProgHOL width) → crepProgToHOL (crepProgOfHOL p) = p := by
  intro p
  fun_induction crepProgOfHOL p <;>
    simp_all [crepProgToHOL, Flapjack.Basis.Pure.MlString.ofString_toStringOfBytes]

/-- Byte-ranged predicate for the production side: every function name must be
`CrepNameRanged` (the only `String`-valued fields of `CrepProg`). -/
def CrepProgNameRanged {width : Nat} : CrepProg (BitVec width) → Prop
  | .skip => True
  | .dec _ _ body => CrepProgNameRanged body
  | .assign _ _ => True
  | .primitive _ _ _ => True
  | .store _ _ => True
  | .store32 _ _ => True
  | .storeByte _ _ => True
  | .storeGlob _ _ => True
  | .seq first second => CrepProgNameRanged first ∧ CrepProgNameRanged second
  | .ite _ thenBranch elseBranch =>
      CrepProgNameRanged thenBranch ∧ CrepProgNameRanged elseBranch
  | .while _ body => CrepProgNameRanged body
  | .break _ => True
  | .continue _ => True
  | .call none name _ => CrepNameRanged name
  | .call (some (_, none)) name _ => CrepNameRanged name
  | .call (some (_, some (_, body))) name _ =>
      CrepNameRanged name ∧ CrepProgNameRanged body
  | .extCall function _ _ _ _ => CrepNameRanged function
  | .raise _ => True
  | .return _ => True
  | .shMem _ _ _ => True
  | .tick => True
termination_by p => sizeOf p
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProg.dec.sizeOf_spec, CrepProg.seq.sizeOf_spec,
        CrepProg.ite.sizeOf_spec, CrepProg.while.sizeOf_spec, CrepProg.call.sizeOf_spec];
       omega)

@[simp] theorem crepProgOfHOL_crepProgToHOL {width : Nat} [NeZero width] :
    (p : CrepProg (BitVec width)) → CrepProgNameRanged p →
      crepProgOfHOL (crepProgToHOL p) = p := by
  intro p
  fun_induction crepProgToHOL p
  case case14 name args =>
    intro h
    simp only [CrepProgNameRanged] at h
    simpa [crepProgOfHOL] using
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name h
  case case15 returns name args =>
    intro h
    simp only [CrepProgNameRanged] at h
    simpa [crepProgOfHOL] using
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name h
  case case16 returns handler body name args ih =>
    intro h
    simp only [CrepProgNameRanged] at h
    obtain ⟨hname, hbody⟩ := h
    simp_all [CrepNameRanged, crepProgOfHOL,
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes]
  case case17 function configuration configurationLength array arrayLength =>
    intro h
    simp only [CrepProgNameRanged] at h
    simpa [crepProgOfHOL] using
      Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function h
  all_goals (intro h <;>
    simp_all [CrepProgNameRanged, crepProgOfHOL])

/-! ## Exact-carrier `crepLang` helpers

The `...W` wrappers in `Flapjack/Pancake/CrepLang.lean` carry the HOL tags but
are indexed over the production `CrepProg (BitVec width)`, whose `Call`/`ExtCall`
names are `String` rather than HOL's `mlstring`. The definitions below are the
genuine exact-carrier versions over `CrepProgHOL`/`CrepExpHOL`, needed by the
exact `pan_to_crep$compile_def` path (`flapjack-pxn.18.3.5.8.13`). -/

/-- Exact port of HOL `crepLang$nested_seq_def`
    (`cakeml/pancake/crepLangScript.sml:89`):
    `nested_seq [] = Skip` and `nested_seq (e::es) = Seq e (nested_seq es)`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "nested_seq_def"]
def crepNestedSeqHOL {width : Nat} [NeZero width] :
    List (CrepProgHOL width) → CrepProgHOL width
  | [] => .skip
  | statement :: statements => .seq statement (crepNestedSeqHOL statements)

/-- Exact port of HOL `crepLang$load_globals_def`
    (`cakeml/pancake/crepLangScript.sml:115-119`):
    `load_globals _ 0 = []` and
    `load_globals ad (SUC n) = LoadGlob ad :: load_globals (ad+1w) n`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "load_globals_def"]
def loadGlobalsHOL {width : Nat} [NeZero width] (address : BitVec 5) (count : Nat) :
    List (CrepExpHOL width) :=
  match count with
  | 0 => []
  | count + 1 => .loadGlob address :: loadGlobalsHOL (address + 1) count

/-- Exact port of HOL `crepLang$nested_decs_def`
    (`cakeml/pancake/crepLangScript.sml:102-107`):
    `nested_decs [] [] p = p`, `nested_decs (n::ns) (e::es) p = Dec n e (nested_decs ns es p)`,
    and both length-mismatch clauses give `Skip`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "nested_decs_def"]
def nestedDecsHOL {width : Nat} [NeZero width] (names : List Nat)
    (values : List (CrepExpHOL width)) (body : CrepProgHOL width) : CrepProgHOL width :=
  match names, values with
  | [], [] => body
  | name :: names, value :: values => .dec name value (nestedDecsHOL names values body)
  | _, _ => .skip

/-- Exact-shaped `stores` over the exact `CrepProgHOL` carrier, matching HOL
    `crepLang$stores_def` (`cakeml/pancake/crepLangScript.sml:95-100`). The
    exact HOL tag for `stores_def` is carried by the production `storesW`; this
    is the same function over `CrepProgHOL`, needed for the exact `seq_store_empty`
    lemmas. -/
def storesHOL {width : Nat} [NeZero width] (address : CrepExpHOL width)
    (values : List (CrepExpHOL width)) (offset : BitVec width) :
    List (CrepProgHOL width) :=
  match values with
  | [] => []
  | value :: values =>
      let destination := if offset == 0 then address else .op .add [address, .const offset]
      .store destination value ::
        storesHOL address values (offset + BitVec.ofNat width (width / 8))

/-- Exact-shaped `store_globals` over the exact `CrepProgHOL` carrier, matching
    HOL `crepLang$store_globals_def` (`cakeml/pancake/crepLangScript.sml:109-113`).
    The exact HOL tag for `store_globals_def` is carried by the production
    `storeGlobalsW`; this is the same function over `CrepProgHOL`. -/
def storeGlobalsHOL {width : Nat} [NeZero width] (address : BitVec 5)
    (values : List (CrepExpHOL width)) : List (CrepProgHOL width) :=
  match values with
  | [] => []
  | value :: values => .storeGlob address value :: storeGlobalsHOL (address + 1) values

@[simp] theorem crepProgToHOL_crepNestedSeqHOL {width : Nat} [NeZero width]
    (statements : List (CrepProg (BitVec width))) :
    crepProgToHOL (crepNestedSeq statements) =
      crepNestedSeqHOL (statements.map crepProgToHOL) := by
  induction statements with
  | nil => simp [crepNestedSeq, crepNestedSeqHOL, crepProgToHOL]
  | cons head tail ih => simp [crepNestedSeq, crepNestedSeqHOL, crepProgToHOL, ih]

@[simp] theorem crepProgOfHOL_crepNestedSeqHOL {width : Nat} [NeZero width]
    (statements : List (CrepProgHOL width)) :
    crepProgOfHOL (crepNestedSeqHOL statements) =
      crepNestedSeq (statements.map crepProgOfHOL) := by
  induction statements with
  | nil => simp [crepNestedSeq, crepNestedSeqHOL, crepProgOfHOL]
  | cons head tail ih => simp [crepNestedSeq, crepNestedSeqHOL, crepProgOfHOL, ih]

@[simp] theorem crepExpMapToHOL_loadGlobals {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobals (α := BitVec width) address count).map crepExpToHOL =
      loadGlobalsHOL address count := by
  induction count generalizing address with
  | zero => simp [loadGlobals, loadGlobalsHOL]
  | succ count ih => simp [loadGlobals, loadGlobalsHOL, crepExpToHOL, ih]

@[simp] theorem crepExpMapOfHOL_loadGlobals {width : Nat} [NeZero width]
    (address : BitVec 5) (count : Nat) :
    (loadGlobalsHOL address count).map crepExpOfHOL =
      loadGlobals (α := BitVec width) address count := by
  induction count generalizing address with
  | zero => simp [loadGlobals, loadGlobalsHOL]
  | succ count ih => simp [loadGlobals, loadGlobalsHOL, crepExpOfHOL, ih]

@[simp] theorem crepProgToHOL_nestedDecs {width : Nat} [NeZero width] (names : List Nat)
    (values : List (CrepExp (BitVec width))) (body : CrepProg (BitVec width)) :
    crepProgToHOL (nestedDecs names values body) =
      nestedDecsHOL names (values.map crepExpToHOL) (crepProgToHOL body) := by
  induction names generalizing values body with
  | nil =>
      cases values with
      | nil => simp [nestedDecs, nestedDecsHOL]
      | cons value values => simp [nestedDecs, crepProgToHOL, nestedDecsHOL]
  | cons name names ih =>
      cases values with
      | nil => simp [nestedDecs, crepProgToHOL, nestedDecsHOL]
      | cons value values => simp [nestedDecs, nestedDecsHOL, crepProgToHOL, ih]

/-- Exact port of HOL `crepLang$assigned_free_vars_def`
    (`cakeml/pancake/crepLangScript.sml:149-162`) over the exact `CrepProgHOL`
    carrier. The clauses are in HOL order; `Dec` filters the declared name out of
    the body's free variables and `ShMem` contributes its result variable. -/
@[hol "cakeml/pancake/crepLangScript.sml" "assigned_free_vars_def"]
def crepAssignedFreeVarsHOL {width : Nat} [NeZero width] :
    CrepProgHOL width → List Nat
  | .skip => []
  | .dec name _ body =>
      (crepAssignedFreeVarsHOL body).filter (fun candidate => candidate != name)
  | .assign name _ => [name]
  | .primitive names _ _ => names
  | .seq first second =>
      crepAssignedFreeVarsHOL first ++ crepAssignedFreeVarsHOL second
  | .ite _ thenBranch elseBranch =>
      crepAssignedFreeVarsHOL thenBranch ++ crepAssignedFreeVarsHOL elseBranch
  | .while _ body => crepAssignedFreeVarsHOL body
  | .call (some (returns, some (_, handler))) _ _ =>
      returns ++ crepAssignedFreeVarsHOL handler
  | .call (some (returns, none)) _ _ => returns
  | .shMem _ name _ => [name]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Exact port of HOL `crepLang$assigned_vars_def`
    (`cakeml/pancake/crepLangScript.sml:164-177`) over the exact `CrepProgHOL`
    carrier. The clauses are in HOL order; `Dec` conses the declared name onto the
    body's assigned variables. -/
@[hol "cakeml/pancake/crepLangScript.sml" "assigned_vars_def"]
def crepAssignedVarsHOL {width : Nat} [NeZero width] :
    CrepProgHOL width → List Nat
  | .skip => []
  | .dec name _ body => name :: crepAssignedVarsHOL body
  | .assign name _ => [name]
  | .primitive names _ _ => names
  | .seq first second =>
      crepAssignedVarsHOL first ++ crepAssignedVarsHOL second
  | .ite _ thenBranch elseBranch =>
      crepAssignedVarsHOL thenBranch ++ crepAssignedVarsHOL elseBranch
  | .while _ body => crepAssignedVarsHOL body
  | .call (some (returns, some (_, handler))) _ _ =>
      returns ++ crepAssignedVarsHOL handler
  | .call (some (returns, none)) _ _ => returns
  | .shMem _ name _ => [name]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

@[simp] theorem crepProgToHOL_crepAssignedFreeVars {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) :
    crepAssignedFreeVarsHOL (crepProgToHOL program) = crepAssignedFreeVars program := by
  induction program using crepProgToHOL.induct <;>
    simp_all [crepProgToHOL, crepAssignedFreeVarsHOL, crepAssignedFreeVars]

@[simp] theorem crepProgToHOL_crepAssignedVars {width : Nat} [NeZero width]
    (program : CrepProg (BitVec width)) :
    crepAssignedVarsHOL (crepProgToHOL program) = crepAssignedVars program := by
  induction program using crepProgToHOL.induct <;>
    simp_all [crepProgToHOL, crepAssignedVarsHOL, crepAssignedVars]

end Flapjack
