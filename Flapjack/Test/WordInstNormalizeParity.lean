import Flapjack.RiscV.WordInstSelect

/-!
# Cake `pull_exp`/`flatten_exp` constant-placement oracle (GH #1024)

Cake's instruction selection applies `flatten_exp` after `pull_exp`:

```
inst_select c temp (Assign v exp) =
  (inst_select_exp c v temp o flatten_exp o pull_exp) exp
```

`pull_exp` funnels constants to the head of the operand list
(`optimize_consts`/`reduce_const` -> `Op op (Const w :: rest)`), and
`flatten_exp (Op op (x::xs)) = Op op [flatten_exp (Op op xs); flatten_exp x]`
puts the head last, so a source `t + 1` is normalized to the constant-second
shape `Op Add [Var t, Const 1]` that `inst_select_exp`'s immediate case turns
into a single `addi`.

The port currently has no `optimize_consts`/`reduce_const`: `wordInstPullOps`
reverses the operand list and `wordInstFlattenExp` keeps the head first, so
`Op Add [Var t, Const 1]` normalizes to the constant-first
`Op Add [Const 1, Var t]` and the constant is materialized instead of folded.
Subtraction already agrees, because the port's constant-right `convert_sub`
composes with its head-first flatten exactly like Cake's constant-left
`convert_sub` composes with Cake's head-last flatten.

This module pins the Cake-expected normal form and the port's current
divergence so the gap stays tracked against the original oracle; the faithful
fix is the Cake pair `convert_sub [x, Const w] = Op Add [Const (-w), x]`
together with the head-last `flatten_exp`, or a port of `optimize_consts`.
-/

namespace Flapjack.Test.WordInstNormalizeParity

open Flapjack Flapjack.RiscV

/-- Cake's normal form of `t + 1` puts the constant second. -/
def cakeAddNormalForm : WordExp Nat := .op .add [.var 7, .const 1]

/-- The source `t + 1` as Pancake parses it (constant second). -/
def addSource : WordExp Nat := .op .add [.var 7, .const 1]

/-- Does `expression` have the shape `Op Add [Var _, Const _]` (constant second)? -/
def addVarConstShape : WordExp α → Bool
  | .op .add args =>
      match args with
      | [a, b] =>
          (match a with | .var _ => true | _ => false) &&
          (match b with | .const _ => true | _ => false)
      | _ => false
  | _ => false

/-- Does `expression` have the shape `Op Add [Const _, Var _]` (constant first)? -/
def addConstVarShape : WordExp α → Bool
  | .op .add args =>
      match args with
      | [a, b] =>
          (match a with | .const _ => true | _ => false) &&
          (match b with | .var _ => true | _ => false)
      | _ => false
  | _ => false

/-- Does `expression` have the shape `Op Add [Var _, Const value]` for the
given constant? -/
def addVarConstValueShape [BEq α] (value : α) : WordExp α → Bool
  | .op .add args =>
      match args with
      | [a, b] =>
          (match a with | .var _ => true | _ => false) &&
          (match b with | .const other => other == value | _ => false)
      | _ => false
  | _ => false

def matchesCakeNormalForm : Bool :=
  addVarConstShape (wordInstNormalizeExp (α := Nat) addSource)

def normalizesConstantFirst : Bool :=
  addConstVarShape (wordInstNormalizeExp (α := Nat) addSource)

def cakeOracleShapeMatches : Bool :=
  addVarConstShape cakeAddNormalForm

def subtractionOrderMatches : Bool :=
  addVarConstValueShape ((0 : BitVec 64) - 8)
    (wordInstNormalizeExp (α := BitVec 64) (.op .sub [.var 7, .const 8]))

def constFirstSourceMatches : Bool :=
  addVarConstShape (wordInstNormalizeExp (α := Nat) (.op .add [.const 1, .var 7]))

#guard cakeOracleShapeMatches
#guard subtractionOrderMatches
#guard constFirstSourceMatches
#guard normalizesConstantFirst
#guard !matchesCakeNormalForm

def runChecks : IO Bool := do
  let checks : List (String × Bool) :=
    [ ("the Cake constant-fold oracle normal form is pinned", cakeOracleShapeMatches)
    , ("subtraction normalization already matches the Cake oracle", subtractionOrderMatches)
    , ("a constant-first source normalizes like the Cake oracle", constFirstSourceMatches)
    , ("the port still normalizes t + 1 with the constant first", normalizesConstantFirst)
    , ("the port has not yet reached the Cake constant-second normal form", !matchesCakeNormalForm)
    ]
  let mut ok := true
  for (label, passed) in checks do
    if passed then
      IO.println s!"PASS {label}"
    else
      IO.println s!"FAIL {label}"
      ok := false
  pure ok

end Flapjack.Test.WordInstNormalizeParity