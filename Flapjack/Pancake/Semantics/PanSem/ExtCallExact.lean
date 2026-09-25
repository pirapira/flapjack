/-
# Exact `ExtCall` clause step over the exact MlString carrier

This module ports the `ExtCall` clause of HOL `panSem$evaluate_def`
(`cakeml/pancake/semantics/panSemScript.sml:711-726`) over the exact,
`mlstring`-keyed `PanSemStateExact` carrier:

```
evaluate (ExtCall ffi_index ptr1 len1 ptr2 len2, s) =
  case (eval s ptr1, eval s len1, eval s ptr2, eval s len2) of
  | SOME (ValWord sz1), SOME (ValWord ad1), SOME (ValWord sz2), SOME (ValWord ad2) =>
      (case (read_bytearray sz1 (w2n ad1) (mem_load_byte s.memory s.memaddrs s.be),
             read_bytearray sz2 (w2n ad2) (mem_load_byte s.memory s.memaddrs s.be)) of
       | SOME bytes, SOME bytes2 =>
         (case call_FFI s.ffi (ExtCall ffi_index) bytes bytes2 of
          | FFI_final outcome => (SOME (FinalFFI outcome), empty_locals s)
          | FFI_return new_ffi new_bytes =>
              let nmem = write_bytearray sz2 new_bytes s.memory s.memaddrs s.be in
               (NONE, s with <| memory := nmem; ffi := new_ffi |>))
       | _ => (SOME Error, s))
  | res => (SOME Error, s))
```

The four arguments are evaluated independently by the caller-supplied
`evalExpression`; the byte reads use the tagged exact `panMemLoadByteHOL`
(`mem_load_byte_def`) through `readBytearrayHOL` (`read_bytearray_def`), the
call uses the tagged exact `callFFIHOL` (`call_FFI_def`), and the returned bytes
are written back with the tagged exact `panWriteBytearrayHOL`
(`write_bytearray_def`). `word8` lists are carried as `BitVec 8` in the exact
`HolFfiState`; the small untagged converters below only bridge `UInt8` (used by
the memory codec) with `BitVec 8` (used by the FFI carrier).

This declaration is deliberately UNTAGGED: the tag belongs on the whole mutual
`evaluate_def` once the recursive dispatcher exists, not on one callback
step. The direct original-HOL rows for this clause are
`extcall_clause_returned`, `extcall_clause_bad_read`, and
`extcall_clause_final` in `scripts/hol-probes/pan_sem_e2e_probe.out`.
-/
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.FfiHOL

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- Bridge a `word8` list carried as `UInt8` (the memory codec's byte type) to
    the exact FFI carrier's `BitVec 8`. -/
def bytesToHOL (bytes : List UInt8) : List (BitVec 8) := bytes.map UInt8.toBitVec

/-- Bridge the exact FFI carrier's `BitVec 8` byte list back to the memory
    codec's `UInt8` byte type. -/
def bytesFromHOL (bytes : List (BitVec 8)) : List UInt8 := bytes.map UInt8.ofBitVec

/-- Exact `ExtCall` clause step over `PanSemStateExact`.  The four expression
    arguments are evaluated through `evalExpression`; both byte arrays must read
    successfully; a terminal FFI result clears the locals, and a returned FFI
    result writes the returned bytes back through the exact `write_bytearray`
    and installs the new FFI state. -/
def extCallStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS)
    (ptr1 len1 ptr2 len2 : ExpHOL width) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state ptr1, evalExpression state len1,
        evalExpression state ptr2, evalExpression state len2 with
  | some (.val (.word address1)), some (.val (.word length1)),
    some (.val (.word address2)), some (.val (.word length2)) =>
      match readBytearrayHOL address1 length1.toNat
              (panMemLoadByteHOL state.memory state.memaddrs state.be),
            readBytearrayHOL address2 length2.toNat
              (panMemLoadByteHOL state.memory state.memaddrs state.be) with
      | some bytes, some bytes2 =>
          match callFFIHOL state.ffi (.extCall function)
              (bytesToHOL bytes) (bytesToHOL bytes2) with
          | .final event => (some (.finalFfi event), emptyLocalsHOLExact state)
          | .ret newFfi newBytes =>
              (none, { state with
                        memory := panWriteBytearrayHOL address2 (bytesFromHOL newBytes)
                          state.memory state.memaddrs state.be,
                        ffi := newFfi })
      | _, _ => (some .error, state)
  | _, _, _, _ => (some .error, state)

/-- The exact HOL `ExtCall` clause does not change the ordinary memory domain.
    Its returned-byte branch updates only memory and FFI; the final branch
    clears only locals. This lets the recursive evaluator reuse the existing
    `memaddrs` decision procedure after the call. -/
theorem extCallStepHOLExact_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.memaddrs =
      state.memaddrs := by
  unfold extCallStepHOLExact
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

/-- The exact HOL `ExtCall` clause leaves the shared-memory domain unchanged. -/
theorem extCallStepHOLExact_shMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width) :
    (extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2).2.shMemaddrs =
      state.shMemaddrs := by
  unfold extCallStepHOLExact
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

/-- If any of the four argument evaluations fails, the clause returns `Error`. -/
theorem extCallStepHOLExact_eval_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width)
    (h : evalExpression state ptr1 = none) :
    extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2
      = (some .error, state) := by
  simp [extCallStepHOLExact, h]

/-- If both byte-array reads do not succeed, the clause returns `Error`. -/
theorem extCallStepHOLExact_read_error {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width)
    (address1 length1 address2 length2 : RiscV.Word width)
    (h1 : evalExpression state ptr1 = some (.val (.word address1)))
    (h2 : evalExpression state len1 = some (.val (.word length1)))
    (h3 : evalExpression state ptr2 = some (.val (.word address2)))
    (h4 : evalExpression state len2 = some (.val (.word length2)))
    (hread : readBytearrayHOL address1 length1.toNat
        (panMemLoadByteHOL state.memory state.memaddrs state.be) = none) :
    extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2
      = (some .error, state) := by
  simp [extCallStepHOLExact, h1, h2, h3, h4, hread]

/-- A terminal FFI result clears the locals and returns `FinalFFI`. -/
theorem extCallStepHOLExact_final {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width)
    (address1 length1 address2 length2 : RiscV.Word width)
    (bytes bytes2 : List UInt8) (event : HolFinalEvent)
    (h1 : evalExpression state ptr1 = some (.val (.word address1)))
    (h2 : evalExpression state len1 = some (.val (.word length1)))
    (h3 : evalExpression state ptr2 = some (.val (.word address2)))
    (h4 : evalExpression state len2 = some (.val (.word length2)))
    (hread1 : readBytearrayHOL address1 length1.toNat
        (panMemLoadByteHOL state.memory state.memaddrs state.be) = some bytes)
    (hread2 : readBytearrayHOL address2 length2.toNat
        (panMemLoadByteHOL state.memory state.memaddrs state.be) = some bytes2)
    (hcall : callFFIHOL state.ffi (.extCall function) (bytesToHOL bytes) (bytesToHOL bytes2)
        = .final event) :
    extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2
      = (some (.finalFfi event), emptyLocalsHOLExact state) := by
  simp [extCallStepHOLExact, h1, h2, h3, h4, hread1, hread2, hcall]

/-- A returned FFI result writes the returned bytes back at the second address
    and installs the new FFI state. -/
theorem extCallStepHOLExact_returned {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width))
    (function : MlS) (ptr1 len1 ptr2 len2 : ExpHOL width)
    (address1 length1 address2 length2 : RiscV.Word width)
    (bytes bytes2 : List UInt8) (newFfi : HolFfiState σ) (newBytes : List (BitVec 8))
    (h1 : evalExpression state ptr1 = some (.val (.word address1)))
    (h2 : evalExpression state len1 = some (.val (.word length1)))
    (h3 : evalExpression state ptr2 = some (.val (.word address2)))
    (h4 : evalExpression state len2 = some (.val (.word length2)))
    (hread1 : readBytearrayHOL address1 length1.toNat
        (panMemLoadByteHOL state.memory state.memaddrs state.be) = some bytes)
    (hread2 : readBytearrayHOL address2 length2.toNat
        (panMemLoadByteHOL state.memory state.memaddrs state.be) = some bytes2)
    (hcall : callFFIHOL state.ffi (.extCall function) (bytesToHOL bytes) (bytesToHOL bytes2)
        = .ret newFfi newBytes) :
    extCallStepHOLExact state evalExpression function ptr1 len1 ptr2 len2
      = (none, { state with
                   memory := panWriteBytearrayHOL address2 (bytesFromHOL newBytes)
                     state.memory state.memaddrs state.be,
                   ffi := newFfi }) := by
  simp [extCallStepHOLExact, h1, h2, h3, h4, hread1, hread2, hcall]

end Flapjack
