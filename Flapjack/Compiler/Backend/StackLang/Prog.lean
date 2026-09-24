import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Encoders.Asm

/-!
# Exact width-indexed `stackLang$prog` carrier

Counterpart submodule of `cakeml/compiler/backend/stackLangScript.sml`, holding
the exact shared-word instantiation of the generic `Flapjack.Compiler.Backend.StackLang.Prog`
syntax over the exact asm payload carriers from
`Flapjack.Compiler.Encoders.Asm` and the faithful
`Flapjack.Basis.Pure.MlString.MlString` FFI carrier.

HOL `stackLang$prog` (`stackLangScript.sml:27-66`) is polymorphic in a single
word type `'a`; its `FFI` constructor stores an opaque `mlstring`
(`cakeml/basis/pure/mlstringScript.sml:19-21`).  Instantiating all seven
parameters of the generic Lean `Prog` on that one word dimension reproduces all
34 constructor arities and field types exactly, so this is the HOL-shaped
program carrier.
-/

namespace Flapjack.Compiler.Backend.StackLang

open Flapjack.Compiler.Encoders.Asm

/-- The exact HOL `stackLang$prog` carrier over an arbitrary word type `α`,
using the faithful generic payload mirrors and the faithful `MlString` FFI
field (unlike `StackCarrier.ProgW`, whose FFI field is Lean `String`).

HOL `prog` (`stackLangScript.sml:27-66`) is polymorphic in one word type `'a`
and its `FFI` field is `mlstring`; instantiating the seven parameters of the
generic Lean `Prog` on that single dimension with `MlString` in the FFI field is
exact for an arbitrary `α`, exactly as HOL permits an arbitrary `'a`.  This is
the polymorphic exact carrier used by the program-level helper ports;
`HolProg` is the width-indexed exact carrier over the `Hol*` payload
inductives. -/
abbrev ProgM (α : Type) : Type :=
  Flapjack.Compiler.Backend.StackLang.Prog (WordLangInst α) Cmp (WordRegImm α)
    BinOp WordMemOp (WordLangAddr α) Flapjack.Basis.Pure.MlString.MlString

/-- Exact width-indexed `stackLang$prog` (`cakeml/compiler/backend/stackLangScript.sml:27-66`)
over the exact asm payload carriers.  This instantiates the seven-parameter
`Flapjack.Compiler.Backend.StackLang.Prog` with the exact `HolInst`/`HolCmp`/
`HolRegImm`/`HolBinop`/`HolMemop`/`HolAddr` carriers plus the faithful `MlString`
FFI carrier, so the program type has a single shared word dimension like HOL and
the `FFI` field matches HOL's opaque `mlstring = implode string`
(`cakeml/basis/pure/mlstringScript.sml:19-21`).  All 34 constructor arities and
field types match `stackLangScript.sml:27-66`; the only `@[hol]`-tagged
program-level declaration is this instantiation.  The production
`StackCarrier.ProgW` (`String` FFI) is a separate untagged carrier; the
kernel-checked `String`<->`MlString` bridge between the two lives in
`Flapjack/Compiler/Backend/MlStringBridge.lean`. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "prog"]
abbrev HolProg (width : Nat) [NeZero width] :=
  Flapjack.Compiler.Backend.StackLang.Prog (HolInst width) HolCmp (HolRegImm width)
    HolBinop HolMemop (HolAddr width) Flapjack.Basis.Pure.MlString.MlString

end Flapjack.Compiler.Backend.StackLang