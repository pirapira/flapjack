import Flapjack.Compiler.Backend.StackLang
import Flapjack.Compiler.Encoders.Asm

/-!
# Canonical single-word-parameter stackLang carrier

HOL `stackLangScript.sml:24-67` parameterises `prog` by a SINGLE word type
`'a`.  The generic `StackLang.Prog` keeps seven independent parameters; `ProgW`
collapses them onto the HOL word dimension by instantiating the word-carrying
slots with the exact width-indexed asm carriers (`HolInst`/`HolRegImm`/
`HolAddr`) and fixing the monomorphic `asm$cmp`/`asm$binop`/`asm$memop` slots
to `Cmp`/`BinOp`/`WordMemOp`.

This module is separate from `StackLang.lean` so that importing the asm
carriers does not pull the `wordLang` carrier namespace into every importer of
`StackLang`.

NOT TAGGED: the only remaining difference from HOL `prog` is the `ffi` field.
HOL uses the opaque `mlstring` (`cakeml/basis/pure/mlstringScript.sml:20`,
`mlstring = implode string`), which has no kernel-checked Lean counterpart in
the tree; `ProgW` fixes it to `String`.  An exact `prog` tag therefore needs a
faithful `mlstring` carrier (or an explicit decision to equate `String` with
`mlstring`); this is the remaining prerequisite recorded on
`flapjack-pxn.18.5.15.3.11`.  Every word-carrying field is already exact.
-/

namespace Flapjack.Compiler.Backend.StackLang

abbrev ProgW (width : Nat) :=
  Prog (Flapjack.Compiler.Encoders.Asm.HolInst width)
    Flapjack.Cmp (Flapjack.Compiler.Encoders.Asm.HolRegImm width)
    Flapjack.BinOp Flapjack.WordMemOp
    (Flapjack.Compiler.Encoders.Asm.HolAddr width) String

end Flapjack.Compiler.Backend.StackLang
