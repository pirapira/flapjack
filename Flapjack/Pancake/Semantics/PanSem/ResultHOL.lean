/-
Exact HOL `panSem$result` carrier.

HOL `cakeml/pancake/semantics/panSemScript.sml:68-76` declares

```
Datatype:
  result = Error
         | TimeOut
         | Break
         | Continue
         | Return    ('a v)
         | Exception mlstring ('a v)
         | FinalFFI final_event
End
```

This module ports that datatype exactly: the payloads use the faithful
`ValueHOL` carrier, the exception identifier uses the exact `mlstring` carrier
(`Flapjack.Basis.Pure.MlString.MlString`) and `FinalFFI` carries the exact
`final_event` carrier (`Flapjack.HolFinalEvent`, tagged `final_event` in
`Flapjack/FfiHOL.lean`). It is a prerequisite for the exact `sh_mem_load`,
`sh_mem_store` and `evaluate` ports, which need to return HOL's
`result option`.
-/

import Flapjack.FfiHOL
import Flapjack.Basis.Pure.MlString
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

namespace Flapjack

/-- Exact port of HOL `panSem$result` (`panSemScript.sml:68-76`): `Error`,
    `TimeOut`, `Break`, `Continue`, `Return`, `Exception` and `FinalFFI`, with
    payload carriers over the faithful `ValueHOL`, `mlstring` and
    `final_event`. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "result"]
inductive ResultHOL (width : Nat) [NeZero width] where
  | error
  | timeOut
  | break
  | continue
  | return (value : ValueHOL width)
  | exception (name : Flapjack.Basis.Pure.MlString.MlString) (value : ValueHOL width)
  | finalFfi (event : HolFinalEvent)
  deriving Repr

end Flapjack