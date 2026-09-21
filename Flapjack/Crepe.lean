import Flapjack.Language

/-!
The Crepe intermediate language.

Crepe is Flapjack after structured locals have been flattened into word-sized
locals. This mirrors `cakeml/pancake/crepLangScript.sml`; target-specific word
operations remain abstract in the polymorphic value type.
-/

namespace Flapjack

inductive CrepOp where
  | mul
  deriving DecidableEq, Repr

inductive CrepExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | load (address : CrepExp α)
  | load32 (address : CrepExp α)
  | loadByte (address : CrepExp α)
  | loadGlob (address : α)
  | op (operator : BinOp) (args : List (CrepExp α))
  | crepOp (operator : CrepOp) (args : List (CrepExp α))
  | cmp (operator : Cmp) (left right : CrepExp α)
  | shift (operator : Shift) (left right : CrepExp α)
  | baseAddr
  | topAddr
  deriving BEq, Repr

inductive CrepMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

inductive CrepProg (α : Type u) where
  | skip
  | dec (name : Nat) (value : CrepExp α) (body : CrepProg α)
  | assign (name : Nat) (value : CrepExp α)
  | primitive (names : List Nat) (operator : PrimOp) (args : List Nat)
  | store (address value : CrepExp α)
  | store32 (address value : CrepExp α)
  | storeByte (address value : CrepExp α)
  | storeGlob (address : α) (value : CrepExp α)
  | seq (first second : CrepProg α)
  | ite (condition : CrepExp α) (thenBranch elseBranch : CrepProg α)
  | while (condition : CrepExp α) (body : CrepProg α)
  | break (label : Nat)
  | continue (label : Nat)
  | call (returnInfo : Option (List Nat × Option (α × CrepProg α)))
      (name : FunName) (args : List (CrepExp α))
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Nat)
  | raise (exception : α)
  | return (values : List (CrepExp α))
  | shMem (operator : CrepMemOp) (name : Nat) (address : CrepExp α)
  | tick
  deriving Repr

/-! Faithful port of `crepLang$assigned_free_vars` from
    `cakeml/pancake/crepLangScript.sml:149-162`. -/
def crepAssignedFreeVars : CrepProg α → List Nat
  | .skip => []
  | .dec name _ body =>
      (crepAssignedFreeVars body).filter (fun candidate => candidate != name)
  | .assign name _ => [name]
  | .primitive names _ _ => names
  | .seq first second => crepAssignedFreeVars first ++ crepAssignedFreeVars second
  | .ite _ thenBranch elseBranch =>
      crepAssignedFreeVars thenBranch ++ crepAssignedFreeVars elseBranch
  | .while _ body => crepAssignedFreeVars body
  | .call (some (returns, some (_, handler))) _ _ =>
      returns ++ crepAssignedFreeVars handler
  | .call (some (returns, none)) _ _ => returns
  | .shMem _ name _ => [name]
  | _ => []
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def crepExpVars : CrepExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .load address | .load32 address | .loadByte address => crepExpVars address
  | .loadGlob _ => []
  | .op _ expressions | .crepOp _ expressions => crepExpVarsList expressions
  | .cmp _ left right | .shift _ left right => crepExpVars left ++ crepExpVars right
  | .baseAddr | .topAddr => []
termination_by expression => sizeOf expression
where
  crepExpVarsList : List (CrepExp α) → List Nat
    | [] => []
    | expression :: expressions => crepExpVars expression ++ crepExpVarsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-! Faithful port of `crepLang$exps` from
    `cakeml/pancake/crepLangScript.sml:193-207`.

    The result preserves expression nodes while recursively flattening the
    expression lists of `Op` and `Crepop`, matching HOL's `FLAT (MAP exps)`. -/
def crepExps : CrepExp α → List (CrepExp α)
  | expression@(.const _) => [expression]
  | expression@(.var _) => [expression]
  | .load address | .load32 address | .loadByte address => crepExps address
  | expression@(.loadGlob _) => [expression]
  | .op _ expressions | .crepOp _ expressions => crepExpsList expressions
  | .cmp _ left right | .shift _ left right => crepExps left ++ crepExps right
  | expression@(.baseAddr) | expression@(.topAddr) => [expression]
termination_by expression => sizeOf expression
where
  crepExpsList : List (CrepExp α) → List (CrepExp α)
    | [] => []
    | expression :: expressions => crepExps expression ++ crepExpsList expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

def distinctLists (left right : List Nat) : Bool :=
  left.all (fun name => !right.contains name)

@[simp] theorem crepExpVars_const (value : α) :
    crepExpVars (.const value) = [] := by
  simp [crepExpVars]

def loadShape [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 =>
      let loaded := if address == 0 then .load value else .load (.op .add [value, .const address])
      loaded :: loadShape (address + stride) stride count value

/-- Original-domain counterpart of Cake's `length_load_shape_eq_shape`
    (`cakeml/pancake/semantics/crepPropsScript.sml:30`). -/
theorem loadShape_length [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) :
    (loadShape address stride count value).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadShape, ih]

/-- Original-domain counterpart of Cake's `load_shape_el_rel`
    (`cakeml/pancake/proofs/pan_to_crepProofScript.sml:114`): the `n`-th
    loaded word reads from `address + n * stride`. -/
theorem loadShape_getElem (address stride count n : Nat) (value : CrepExp Nat)
    (h : n < count) :
    (loadShape address stride count value)[n]? =
      some (if address + n * stride == 0 then .load value
            else .load (.op .add [value, .const (address + n * stride)])) := by
  induction count generalizing address n with
  | zero => simp at h
  | succ count ih =>
      cases n with
      | zero => simp [loadShape]
      | succ k =>
          have hk : k < count := by omega
          rw [loadShape]
          simp only [List.getElem?_cons_succ]
          rw [ih (address + stride) k hk]
          have haddr : (address + stride) + k * stride = address + (k + 1) * stride := by
            rw [Nat.add_mul, Nat.one_mul]
            ac_rfl
          simp only [haddr]

def crepNestedSeq : List (CrepProg α) → CrepProg α
  | [] => .skip
  | statement :: statements => .seq statement (crepNestedSeq statements)

/-! Faithful port of Cake `crep_seqs_def` from
    `cakeml/pancake/pan_passesScript.sml:377`: flatten only `Seq` nodes,
    preserving the left-to-right order of all other Crepe statements. -/
def crepSeqs : CrepProg α → List (CrepProg α)
  | .seq first second => crepSeqs first ++ crepSeqs second
  | program => [program]
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

def stores [BEq α] [OfNat α 0] [Add α]
    (address : CrepExp α) : List (CrepExp α) → α → α → List (CrepProg α)
  | [], _, _ => []
  | value :: values, offset, stride =>
      let destination := if offset == 0 then address else .op .add [address, .const offset]
      .store destination value :: stores address values (offset + stride) stride

def nestedDecs : List Nat → List (CrepExp α) → CrepProg α → CrepProg α
  | [], [], body => body
  | name :: names, value :: values, body => .dec name value (nestedDecs names values body)
  | _, _, _ => .skip

def storeGlobals [Add α] (address stride : α) : List (CrepExp α) → List (CrepProg α)
  | [] => []
  | value :: values => .storeGlob address value :: storeGlobals (address + stride) stride values

def loadGlobals [Add α] (address stride : α) (count : Nat) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 => .loadGlob address :: loadGlobals (address + stride) stride count

/-- Faithful port of Cake `crepProps$length_load_globals_eq_read_size`
    (`cakeml/pancake/semantics/crepPropsScript.sml:467`). -/
theorem loadGlobals_length [Add α] (address stride : α) (count : Nat) :
    (loadGlobals address stride count).length = count := by
  induction count generalizing address with
  | zero => rfl
  | succ count ih => simp [loadGlobals, ih]

/-- Faithful port of Cake `crepProps$el_load_globals_elem`
    (`cakeml/pancake/semantics/crepPropsScript.sml:474`), generalised to an
    explicit additive stride on `Nat`: the `n`-th generated load reads the
    address `address + n * stride`. -/
theorem loadGlobals_getElem (address stride count n : Nat) (h : n < count) :
    (loadGlobals address stride count)[n]? =
      some (.loadGlob (address + n * stride)) := by
  induction count generalizing address n with
  | zero => simp at h
  | succ count ih =>
      cases n with
      | zero => simp [loadGlobals]
      | succ k =>
          simp only [loadGlobals, List.getElem?_cons_succ]
          rw [ih (address + stride) k (by omega)]
          congr 1
          rw [Nat.add_mul, Nat.one_mul]
          ac_rfl

def assignRet [OfNat α 0] [Add α] (wordStride : α) (names : List Nat) : CrepProg α :=
  crepNestedSeq (names.zipWith (fun name value => .assign name value)
    (loadGlobals (0 : α) wordStride names.length))

end Flapjack
