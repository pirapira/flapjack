import Flapjack.HolRef

/-!
# Exact `gc_shared` heap carriers

Counterpart of the HOL `gc_shared` data structures
(`cakeml/compiler/backend/gc/gc_sharedScript.sml`).

The HOL definitions are

```
Datatype: heap_address = Pointer num 'a | Data 'a End
Datatype: heap_element =
  Unused num | ForwardPointer num 'a num | DataElement (('a heap_address) list) num 'b End
```

`num` is rendered as `Nat` and `('a heap_address) list` as `List (HeapAddress α)`.
Only the two carriers used by `word_gcFunctions$refs_to_addresses` are ported
here; the `gc_state` record is not needed by that definition and is left to a
future GC-simulation port.
-/

namespace Flapjack
namespace Compiler
namespace Backend

/-- Exact Lean rendering of the HOL `heap_address` datatype
`heap_address = Pointer num 'a | Data 'a`. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_address"]
inductive HeapAddress (α : Type) : Type where
  /-- `Pointer num 'a`: a pointer with an index and an address value. -/
  | pointer (index : Nat) (addr : α)
  /-- `Data 'a`: a direct data address. -/
  | data (addr : α)
  deriving Repr

/-- Exact Lean rendering of the HOL `heap_element` datatype
`Unused num | ForwardPointer num 'a num | DataElement (('a heap_address) list) num 'b`. -/
@[hol "cakeml/compiler/backend/gc/gc_sharedScript.sml" "heap_element"]
inductive HeapElement (α β : Type) : Type where
  /-- `Unused num`. -/
  | unused (n : Nat)
  /-- `ForwardPointer num 'a num`. -/
  | forwardPointer (n : Nat) (addr : α) (ptr : Nat)
  /-- `DataElement (('a heap_address) list) num 'b`. -/
  | dataElement (ptrs : List (HeapAddress α)) (n : Nat) (data : β)
  deriving Repr

end Backend
end Compiler
end Flapjack
