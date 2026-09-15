import Flapjack.Word

/-!
# Loop-to-word context lookup

Faithful ports of the compilation-context functions at the top of CakeML's
`pancake/loop_to_wordScript.sml`:

* `find_var_def` (line 10): look a loop variable up in the compilation
  context; a variable that is not present maps to wordLang register `0`.
* `find_reg_imm_def` (line 17): apply `find_var` to the register case of a
  register/immediate operand.
* `make_ctxt_def` (line 152): assign consecutive even registers starting at
  `2` to a list of variables.

The context is an association list with first-match lookup and cons-insertion,
matching the observable behaviour of the script's `num |-> num` context
(`LN`/`insert`/`lookup`) for the distinct variable names produced by
`comp_func`.
-/

namespace Flapjack.LoopToWord

/-- Context lookup with first-match semantics and cons-insertion, mirroring
the script's `lookup`/`insert` on a `num |-> num` finite map. -/
def lookupVar : Nat → List (Nat × Nat) → Option Nat
  | _, [] => none
  | name, (key, value) :: rest =>
      if key = name then some value else lookupVar name rest

/-- Script `insert x n l` with later insertions overriding earlier ones. -/
def insertVar (name register : Nat) (context : List (Nat × Nat)) :
    List (Nat × Nat) :=
  (name, register) :: context

/-- Port of `find_var_def` (loop_to_wordScript.sml:10). -/
def findVar (context : List (Nat × Nat)) (name : Nat) : Nat :=
  (lookupVar name context).getD 0

/-- Port of `find_reg_imm_def` (loop_to_wordScript.sml:17). -/
def findRegImm (context : List (Nat × Nat)) : RegImm α → RegImm α
  | .imm value => .imm value
  | .reg name => .reg (findVar context name)

/-- Port of `make_ctxt_def` (loop_to_wordScript.sml:152).  The first variable
receives register `next`; each following variable receives the next even
register. -/
def makeCtxt : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [], context => context
  | next, name :: rest, context =>
      makeCtxt (next + 2) rest (insertVar name next context)

/-! A list-backed representation of CakeML's `num_set` for the executable
    Loop-to-Word boundary.  The source `toNumSet_def` builds an sptree set by
    recursively inserting each input name; `loopInsert` is the existing
    first-occurrence list-set adapter used by the RISC-V path. -/
def toNumSet : List Nat → List Nat
  | [] => []
  | name :: names => loopInsert name (toNumSet names)

theorem toNumSet_nodup (names : List Nat) : (toNumSet names).Nodup := by
  induction names with
  | nil => simp [toNumSet]
  | cons name names ih =>
      exact loopInsert_nodup name (toNumSet names) ih

/-! `sptree$toAList` is not insertion order.  Its `foldi` walks the binary
    Patricia tree using `lrnext`; retaining that order is observable because
    `loop_to_word$make_ctxt` assigns consecutive Word registers to
    `fromNumSet (acc_vars ...)`. -/
inductive NumSetTree where
  | empty
  | singleton
  | branch (left right : NumSetTree)
  | branchSingleton (left right : NumSetTree)

def numSetLrnextFuel : Nat → Nat → Nat
  | 0, _ => 1
  | _fuel + 1, 0 => 1
  | fuel + 1, value + 1 =>
      2 * numSetLrnextFuel fuel (value / 2)

def numSetLrnext (value : Nat) : Nat :=
  numSetLrnextFuel (value + 1) value

def numSetInsertFuel : Nat → Nat → NumSetTree → NumSetTree
  | 0, _, tree => tree
  | _fuel + 1, 0, .empty => .singleton
  | _fuel + 1, 0, .singleton => .singleton
  | _fuel + 1, 0, .branch left right => .branchSingleton left right
  | _fuel + 1, 0, .branchSingleton left right => .branchSingleton left right
  | fuel + 1, key + 1, .empty =>
      if (key + 1) % 2 = 0 then
        .branch (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branch .empty (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .singleton =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty) .empty
      else
        .branchSingleton .empty (numSetInsertFuel fuel (((key + 1) - 1) / 2) .empty)
  | fuel + 1, key + 1, .branch left right =>
      if (key + 1) % 2 = 0 then
        .branch (numSetInsertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branch left (numSetInsertFuel fuel (((key + 1) - 1) / 2) right)
  | fuel + 1, key + 1, .branchSingleton left right =>
      if (key + 1) % 2 = 0 then
        .branchSingleton (numSetInsertFuel fuel (((key + 1) - 1) / 2) left) right
      else
        .branchSingleton left (numSetInsertFuel fuel (((key + 1) - 1) / 2) right)

def numSetInsert (key : Nat) (tree : NumSetTree) : NumSetTree :=
  numSetInsertFuel (key + 1) key tree

def numSetToAList : NumSetTree → Nat → List Nat → List Nat
  | .empty, _, accumulated => accumulated
  | .singleton, index, accumulated => index :: accumulated
  | .branch left right, index, accumulated =>
      let increment := numSetLrnext index
      numSetToAList right (index + increment)
        (numSetToAList left (index + 2 * increment) accumulated)
  | .branchSingleton left right, index, accumulated =>
      let increment := numSetLrnext index
      numSetToAList right (index + increment)
        (index :: numSetToAList left (index + 2 * increment) accumulated)

def fromNumSet (set : List Nat) : List Nat :=
  let tree := (toNumSet set).foldr (fun key tree => numSetInsert key tree) .empty
  numSetToAList tree 0 []

/-! List-backed port of `mk_new_cutset_def` from
    `loop_to_wordScript.sml:51-53`.  The source always retains register zero
    and maps each live source variable through `find_var` before rebuilding the
    finite set. -/
def mkNewCutset (context : List (Nat × Nat)) (live : List Nat) : List Nat :=
  loopInsert 0 (toNumSet ((fromNumSet live).map (findVar context)))

theorem mkNewCutset_nodup (context : List (Nat × Nat)) (live : List Nat) :
    (mkNewCutset context live).Nodup := by
  exact loopInsert_nodup 0 _ (toNumSet_nodup _)

/-! List-backed `difference` for the source's finite sets.  The left-hand
    order is retained because it is the order exposed by `fromNumSet` at the
    comp_func boundary. -/
def differenceNumSet (names excluded : List Nat) : List Nat :=
  names.filter (fun name => name ∉ excluded)

/-! Port of `comp_func_def` from `loop_to_wordScript.sml:164-169`.
    `loopAccVars` supplies the source `acc_vars` set, parameters are removed,
    `makeCtxt` assigns the consecutive even registers, and the existing
    `loopToWordProg` supplies the first component of `comp`. -/
def loopToWordCompFunc [OfNat α 1] (name : Nat) (params : List Nat)
    (body : LoopProg α) : WordProg α :=
  let assigned := loopAccVars body []
  let variables := fromNumSet (differenceNumSet assigned (toNumSet params))
  let context := makeCtxt 2 (params ++ variables) []
  /- CakeML's `comp_func` seeds the label counter with `(name, 2)`
     (`loop_to_wordScript.sml:166-168`). -/
  (loopToWordProgFrom { vars := context } name 2 body).1

/-! Port of `compile_prog_def` from `loop_to_wordScript.sml:171-174`.
    The source adds one entry slot to each function's parameter count while
    preserving source order. -/
def loopToWordCompileProg [OfNat α 1] :
    List (Nat × List Nat × LoopProg α) →
      List (Nat × Nat × WordProg α)
  | [] => []
  | (name, params, body) :: functions =>
      (name, params.length + 1, loopToWordCompFunc name params body) ::
        loopToWordCompileProg functions

/-! Port of `compile_def` from `loop_to_wordScript.sml:176-177`. -/
def loopToWordCompile [OfNat α 1]
    (program : List (Nat × List Nat × LoopProg α)) :
    List (Nat × Nat × WordProg α) :=
  loopToWordCompileProg program

end Flapjack.LoopToWord
