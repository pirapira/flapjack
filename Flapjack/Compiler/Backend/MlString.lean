import Flapjack.HolRef

/-!
# Faithful Cake `mlstring` carrier

Lean counterpart of `cakeml/basis/pure/mlstringScript.sml`:

```
Datatype:
  mlstring = implode string
End
```

HOL `string` is `char list`, and HOL `char` is the canonical 256-element type
(`HOL/src/string/stringScript.sml` defines it through the bijection
`CHR : num -> char`, `ORD : char -> num`).  `HolChar` models HOL `char` by
`BitVec 8`, the canonical 256-element carrier, exactly as HOL `word` types are
modeled by `BitVec width` throughout Flapjack.  The single constructor `implode`
of `MlString` is then exactly HOL's `mlstring = implode string`, so the datatype
is shape-exact and carries no word-width or typeclass side condition.

This is the carrier needed to make the `stackLang`/`stack_names` program
theorems exact, since HOL `stackLang$prog` is polymorphic in a single word type
and its FFI constructor stores an `mlstring`, whereas the executable
`Flapjack.Compiler.Backend.StackCarrier.ProgW` uses Lean `String`.
-/

namespace Flapjack.Compiler.Backend.MlString

/-- Model of HOL `char`: the canonical 256-element type.  HOL `char` is an
abstract type with a bijection `CHR`/`ORD` to the 256 values; `BitVec 8` has the
same cardinality and exposes the same data, matching the repo convention of
modeling HOL word types with `BitVec`. -/
abbrev HolChar := BitVec 8

/-- Exact port of HOL `Datatype: mlstring = implode string`
    (`cakeml/basis/pure/mlstringScript.sml:19-21`).

    `string` is `char list`; with `HolChar = BitVec 8` the field is
    `List (BitVec 8)`.  Single-constructor datatype with no side condition. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "mlstring"]
inductive MlString where
  | implode (data : List HolChar)
  deriving Repr, DecidableEq

namespace MlString

/-- HOL `explode`: the underlying character list.  Structural accessor matching
    `mlstringScript.sml:70-72` (`explode s = explode_aux s 0 (strlen s)`, with
    `explode (strlit ls) = ls`).  Untagged infrastructure. -/
def explode : MlString → List HolChar
  | .implode data => data

@[simp] theorem explode_implode (data : List HolChar) :
    explode (.implode data) = data := rfl

/-- HOL `implode_explode` (`mlstringScript.sml:86-90`). -/
@[simp] theorem implode_explode (s : MlString) : MlString.implode (explode s) = s := by
  cases s
  rfl

end MlString

end Flapjack.Compiler.Backend.MlString
