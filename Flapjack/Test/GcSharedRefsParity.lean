import Flapjack.Compiler.Backend.WordGcFunctions

/-! Kernel regression for the `refs_to_addresses` port over the faithful
`gc_shared` carriers.

`Flapjack/Compiler/Backend/WordGcFunctions.lean` ports the original HOL
`refs_to_addresses_def` (`cakeml/compiler/backend/proofs/word_gcFunctionsScript.sml`)
over `HeapElement`/`HeapAddress` in `Flapjack/Compiler/Backend/GcShared.lean`.
The expected results below are the captured outputs of the original HOL
definition in `scripts/hol-probes/word_gc_functions_probe.out`, checked by
`scripts/check-hol-probe-rows.py`:

* `gc_refs_to_addresses_empty=[]`
* `gc_refs_to_addresses_basic=[Pointer 0 1000w; Data 2000w]`
* `gc_refs_to_addresses_skip=[Data 3000w]`

The payloads are exactly the 64-bit words used in the original probe rows. -/

namespace Flapjack.Test.GcSharedRefsParity

open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordGcFunctions

example :
    refs_to_addresses ([] : List (HeapElement (BitVec 64) (BitVec 64))) = [] := by
  rfl

example :
    refs_to_addresses
        ([HeapElement.dataElement
            [HeapAddress.pointer 0 (1000 : BitVec 64), HeapAddress.data (2000 : BitVec 64)]
            2 (9 : BitVec 64),
          HeapElement.unused 3,
          HeapElement.forwardPointer 1 (1000 : BitVec 64) 4] :
          List (HeapElement (BitVec 64) (BitVec 64))) =
      [HeapAddress.pointer 0 (1000 : BitVec 64), HeapAddress.data (2000 : BitVec 64)] := by
  rfl

example :
    refs_to_addresses
        ([HeapElement.unused 1,
          HeapElement.dataElement [HeapAddress.data (3000 : BitVec 64)] 5 (7 : BitVec 64)] :
          List (HeapElement (BitVec 64) (BitVec 64))) =
      [HeapAddress.data (3000 : BitVec 64)] := by
  rfl

end Flapjack.Test.GcSharedRefsParity
