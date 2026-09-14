import Flapjack.CrepToLoop

/-!
Structural analyses for the Loop language. These are the list-based
counterparts of CakeML's `loop_live` inputs; a later pass can replace the
lists with a finite-set representation without changing the syntax layer.
-/

namespace Flapjack

def loopVarsOfExp : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopVarsOfExp address
  | .op _ arguments => arguments.flatMap loopVarsOfExp
  | .crepOp _ arguments => arguments.flatMap loopVarsOfExp
  | .cmp _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .shift _ left right => loopVarsOfExp left ++ loopVarsOfExp right
  | .baseAddr => []
  | .topAddr => []

/-! Source-shaped port of `loop_live$vars_of_exp`
    (`cakeml/pancake/loop_liveScript.sml:11`).  HOL carries the live names as
    a canonical `num_set`; the Lean syntax layer keeps lists, so fold the
    expression reads into the existing sorted insertion helper. -/
def varsOfExp (expression : LoopExp α) (live : List Nat) : List Nat :=
  (loopVarsOfExp expression).foldr insertNatSorted live

/-! Faithful port of CakeML Pancake's `locals_touched_def` from
    `cakeml/pancake/loopLangScript.sml:77`.  The source definition is used on
    the original Loop expressions, before the later Flapjack-only `crepOp` and
    comparison expression forms are introduced; those forms are nevertheless
    handled structurally here so the analysis remains total on `LoopExp`. -/
def loopLocalsTouched : LoopExp α → List Nat
  | .const _ => []
  | .var name => [name]
  | .lookup _ => []
  | .load address => loopLocalsTouched address
  | .op _ arguments => arguments.flatMap loopLocalsTouched
  | .crepOp _ arguments => arguments.flatMap loopLocalsTouched
  | .cmp _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .shift _ left right => loopLocalsTouched left ++ loopLocalsTouched right
  | .baseAddr => []
  | .topAddr => []

@[simp] theorem loopLocalsTouched_const (value : α) :
    loopLocalsTouched (.const value) = [] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_var (α : Type u) (name : Nat) :
    loopLocalsTouched (α := α) (.var name) = [name] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_lookup (address : α) :
    loopLocalsTouched (.lookup address) = [] := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_load (address : LoopExp α) :
    loopLocalsTouched (.load address) = loopLocalsTouched address := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_op (operator : BinOp)
    (arguments : List (LoopExp α)) :
    loopLocalsTouched (.op operator arguments) =
      arguments.flatMap loopLocalsTouched := by
  simp [loopLocalsTouched]

@[simp] theorem loopLocalsTouched_shift (operator : Shift)
    (left right : LoopExp α) :
    loopLocalsTouched (.shift operator left right) =
      loopLocalsTouched left ++ loopLocalsTouched right := by
  simp [loopLocalsTouched]

def loopAssignedVars : LoopProg α → List Nat
  | .skip => []
  | .assign name _ => [name]
  | .primitive destinations _ _ => destinations
  | .arith operation =>
      match operation with
      | .longMul left right _ _ => [left, right]
      | .longDiv left right _ _ _ => [left, right]
      | .div destination _ _ => [destination]
  | .load32 _ destination => [destination]
  | .loadByte _ destination => [destination]
  | .seq first second => loopAssignedVars first ++ loopAssignedVars second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopAssignedVars thenBranch ++ loopAssignedVars elseBranch
  | .locValue destination _ => [destination]
  | .shMem _ destination _ => [destination]
  | .mark body => loopAssignedVars body
  | .loop _ body _ => loopAssignedVars body
  | .call none _ _ _ => []
  | .call (some (returns, _)) _ _ none => returns
  | .call (some (returns, _)) _ _ (some (exception, handler, normal, _)) =>
      returns ++ exception :: loopAssignedVars handler ++ loopAssignedVars normal
  | _ => []

def loopInsert (name : Nat) (names : List Nat) : List Nat :=
  if name ∈ names then names else name :: names

def loopInsertAll : List Nat → List Nat → List Nat
  | [], names => names
  | name :: rest, names => loopInsert name (loopInsertAll rest names)

theorem loopInsert_nodup (name : Nat) (names : List Nat)
    (hnames : names.Nodup) : (loopInsert name names).Nodup := by
  by_cases hname : name ∈ names
  · simp [loopInsert, hname, hnames]
  · simp [loopInsert, hname, hnames]

theorem loopInsertAll_nodup (added names : List Nat)
    (hnames : names.Nodup) : (loopInsertAll added names).Nodup := by
  induction added generalizing names with
  | nil => exact hnames
  | cons name rest ih =>
      exact loopInsert_nodup name (loopInsertAll rest names)
        (ih names hnames)

def loopAccVars : LoopProg α → List Nat → List Nat
  | .seq first second, names => loopAccVars first (loopAccVars second names)
  | .break _, names => names
  | .continue _, names => names
  | .loop _ body _, names => loopAccVars body names
  | .ite _ condition right thenBranch elseBranch _, names =>
      let names := loopAccVars thenBranch (loopAccVars elseBranch names)
      loopInsert condition (match right with | .reg value => value :: names | .imm _ => names)
  | .arith operation, names =>
      match operation with
      | .longMul left right _ _ => loopInsertAll [left, right] names
      | .longDiv left right _ _ _ => loopInsertAll [left, right] names
      | .div destination _ _ => loopInsert destination names
  | .mark body, names => loopAccVars body names
  | .tick, names => names
  | .skip, names => names
  | .fail, names => names
  | .raise _, names => names
  | .return _, names => names
  | .call none _ _ _, names => names
  | .call (some (returns, _)) _ _ none, names =>
      loopInsertAll returns names
  | .call (some (returns, _)) _ _
      (some (exception, handler, normal, _)), names =>
      let names := loopAccVars handler (loopAccVars normal names)
      loopInsert exception (loopInsertAll returns names)
  | .locValue destination _label, names => loopInsert destination names
  | .assign destination _, names => loopInsert destination names
  | .primitive destinations _ _, names => loopInsertAll destinations names
  | .shMem _ destination _, names => loopInsert destination names
  | .store _ _, names => names
  | .setGlobal _ _, names => names
  | .load32 _ destination, names => loopInsert destination names
  | .loadByte _ destination, names => loopInsert destination names
  | .store32 _ _, names => names
  | .storeByte _ _, names => names
  | .ffi _ _ _ _ _ _, names => names

theorem loopVarsOfExp_load (address : LoopExp α) :
    loopVarsOfExp (.load address) = loopVarsOfExp address := by
  simp [loopVarsOfExp]

theorem loopAssignedVars_seq (first second : LoopProg α) :
    loopAssignedVars (.seq first second) =
      loopAssignedVars first ++ loopAssignedVars second := by
  simp [loopAssignedVars]

theorem loopAccVars_skip (names : List Nat) :
    loopAccVars (.skip : LoopProg α) names = names := by
  rfl

end Flapjack
