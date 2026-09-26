import Flapjack.HolRef

/-!
Primary Lean counterpart of `cakeml/semantics/astScript.sml` (the CakeML
abstract syntax).

Only the exact `ast$shift` carrier used by the Pancake source syntax and the
assembly/wordLang shift operations is ported here so far. The remaining
declarations of the script (`lit`, `arith`, `exp`, `dec`, ...) are an open
inventory item and are not modelled by this module.
-/

namespace Flapjack

/-- Exact port of HOL `ast$shift` (`cakeml/semantics/astScript.sml:21`):
`Datatype shift = Lsl | Lsr | Asr | Ror`. The four nullary constructors and
their order match; there is no payload, width parameter, or side condition.
This is the source-level shift datatype that `panLangScript.sml:19`
(`Type shift = ``:ast$shift```) aliases and that `asmScript.sml`'s `arith`
carrier uses. The panLang alias itself is the separate tagged
`Flapjack.PanLangShift` in `Flapjack/Pancake/PanLang.lean`. -/
@[hol "cakeml/semantics/astScript.sml" "shift"]
inductive Shift where
  | lsl
  | lsr
  | asr
  | ror
  deriving DecidableEq, Repr

end Flapjack
