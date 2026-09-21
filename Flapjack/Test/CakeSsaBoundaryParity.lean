import Flapjack.RiscV.Allocator

/-! Direct HOL parity for the Return and Alloc rows of CakeML's
    `full_ssa_cc_trans`.  The expected shapes come from the canonical Cake
    `word_allocScript.sml` equations (`ssa_cc_trans_def`), evaluated with two
    ABI parameters.  This is deliberately separate from the temporary-name,
    branch, and loop fixtures in `CakeSsaTempParity`. -/

namespace Flapjack.Test.CakeSsaBoundaryParity

open Flapjack

def returnProgram : WordProg Nat :=
  .return 0 [2]

def returnBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 2 returnProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.move 0 [(2, 9)]) (.return 5 [2])) => true
  | _ => false

#guard returnBoundaryGuard

/- Cake's Return row maps every returned source value to its ABI result slot;
   this two-value case is the direct `GENLIST (2 * (x + 1))` shape. -/
def returnMultiProgram : WordProg Nat :=
  .return 0 [2, 4]

def returnMultiBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 3 returnMultiProgram).2.2 with
  | .seq (.move 1 [(9, 0), (13, 2), (17, 4)])
      (.seq (.move 0 [(2, 13), (4, 17)]) (.return 9 [2, 4])) => true
  | _ => false

#guard returnMultiBoundaryGuard

def allocProgram : WordProg Nat :=
  .alloc 2 ([], [])

def allocBoundaryGuard : Bool :=
  match (wordFullSsaCcTrans 2 allocProgram).2.2 with
  | .seq (.move 1 [(5, 0), (9, 2)])
      (.seq (.move 0 [])
        (.seq (.move 1 [(2, 9)])
          (.seq (.alloc 2 ([], [])) (.move 0 [])))) => true
  | _ => false

#guard allocBoundaryGuard

def parityGuard : Bool :=
  returnBoundaryGuard && returnMultiBoundaryGuard && allocBoundaryGuard

#guard parityGuard
#eval parityGuard

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("full_ssa_cc_trans Return preserves Cake ABI reconciliation",
        returnBoundaryGuard),
      ("full_ssa_cc_trans Return preserves Cake multi-value ABI reconciliation",
        returnMultiBoundaryGuard),
      ("full_ssa_cc_trans Alloc preserves Cake stack boundary moves",
        allocBoundaryGuard) ]
  let mut ok := true
  for (name, result) in checks do
    if result then
      IO.println s!"PASS {name}"
    else
      IO.println s!"FAIL {name}"
      ok := false
  pure ok

end Flapjack.Test.CakeSsaBoundaryParity
