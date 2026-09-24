import Flapjack.Compiler.Backend.StackLang
import Flapjack.Pancake.WordLang

/-!
# Shared-word StackLang carrier

HOL `cakeml/compiler/backend/stackLangScript.sml:24-67` declares

```
Datatype:
  prog = Skip | Inst ('a inst) | ... | If cmp num ('a reg_imm) ...
       | ShMemOp memop num ('a addr) | ...
End
```

i.e. the program type has exactly **one** type parameter `'a`, shared by the
instruction, register-immediate, and address positions.  The generic Lean
`Flapjack.Compiler.Backend.StackLang.Prog` deliberately keeps seven independent
parameters (`Inst Cmp RegImm Binop Memop Addr MlString`) so it can host
different executable carriers; it is therefore strictly more general than HOL.

This module records the canonical single-word-parameter instantiation of that
datatype, using the faithful `asm` ports (`WordLangInst`, `WordRegImm`,
`WordLangAddr`) over one shared word type `α` and HOL's fixed `mlstring`
(carried here as `String`).  HOL-shaped statements about `stackLang$prog` must
be stated over `ProgW`; the executable seven-parameter form remains a separate,
more general artefact.

Nothing here carries an `@[hol]` tag: the declaration has no single HOL
counterpart (the seven-parameter `Prog` is a Flapjack generalisation), and the
carrier alone does not prove any HOL theorem.
-/

namespace Flapjack.Compiler.Backend.StackCarrier

/-- Canonical single-word-parameter `stackLang$prog` carrier: `Inst`/`RegImm`/
`Addr` all share one word type, with HOL's fixed `mlstring` (`String`) and the
HOL-matching `Cmp`/`BinOp`/`WordMemOp`. -/
abbrev ProgW (α : Type) : Type :=
  StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp (WordLangAddr α) String

/-- Definitional unfolding of the canonical carrier. -/
theorem progW_eq (α : Type) :
    ProgW α =
      StackLang.Prog (WordLangInst α) Cmp (WordRegImm α) BinOp WordMemOp
        (WordLangAddr α) String := rfl

/-- Single-word-parameter instruction carrier (HOL `'a inst`). -/
abbrev InstW (α : Type) : Type := WordLangInst α

/-- Single-word-parameter register-immediate carrier (HOL `'a reg_imm`). -/
abbrev RegImmW (α : Type) : Type := WordRegImm α

/-- Single-word-parameter address carrier (HOL `'a addr`). -/
abbrev AddrW (α : Type) : Type := WordLangAddr α

end Flapjack.Compiler.Backend.StackCarrier
