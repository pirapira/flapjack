import Flapjack.Pancake.Semantics.PanSem.DecExact
import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.FfiHOL

/-!
# Exact HOL `panSem$sh_mem_load` / `sh_mem_store` over the faithful state

HOL `panSemScript.sml:510-547` defines the shared-memory primitives over the
whole `('a,'ffi) panSem$state`, calling `call_FFI s.ffi (SharedMem MappedRead /
MappedWrite)` and encoding the address/value with the HOL standard-library
`byte$word_to_bytes` / `word_of_bytes` (outside the CakeML submodule, so the
bit-vector renderings below carry no `@[hol]` tag).  The results are HOL
`(result option # state)` pairs; here they are `Option (PanSemResultExact
width) × PanSemStateExact width σ`.

The `nb` byte-count argument comes from `nb_op` (`nbOpHOL`, exact); `nb = 0`
addresses `s.sh_memaddrs` directly and passes the whole word, while `nb ≠ 0`
addresses `byte_align` (here `panByteAlignHOL`).  Load installs the read value
into `set_kvar vk v` on success and clears locals on a final event; store leaves
the state otherwise unchanged and only updates `ffi`.
-/

namespace Flapjack

open Flapjack (VarKind OpSize)
open Flapjack.Pancake.PanLang (MlS)

/-- Untagged BitVec-8 rendering of HOL standard-library `byte$word_to_bytes`
    (`HOL/src/n-bit/byteScript.sml:450`), matching `panGetByteHOL` byte for byte.
    That dependency lives outside the CakeML submodule, so no `@[hol]` tag. -/
def panWordToBytesHOL {width : Nat} [NeZero width] (value : RiscV.Word width)
    (bigEndian : Bool) : List (BitVec 8) :=
  (List.range (width / 8)).map (fun index =>
    BitVec.ofNat 8 (panGetByteHOL (BitVec.ofNat width index) value bigEndian).toNat)

/-- Untagged BitVec-8 rendering of HOL standard-library `byte$word_of_bytes`
    (`HOL/src/n-bit/byteScript.sml:197`): fold `set_byte` over the bytes,
    incrementing the address by one, matching the recursive HOL shape
    `word_of_bytes be a (b::bs) = set_byte a b (word_of_bytes be (a+1) bs) be`.
    HOL standard library, so no `@[hol]` tag. -/
def panWordOfBytesHOL {width : Nat} [NeZero width] (bigEndian : Bool)
    (address : RiscV.Word width) : List (BitVec 8) → RiscV.Word width
  | [] => 0
  | byte :: rest =>
      panSetByteHOL address (BitVec.ofNat width byte.toNat)
        (panWordOfBytesHOL bigEndian (address + 1) rest) bigEndian

/-- Exact port of HOL `panSem$sh_mem_load`
    (`panSemScript.sml:510-527`).  When `nb = 0` the address itself must be in
    `sh_memaddrs`; otherwise the `byte_align`ed address must be.  The FFI call
    uses the unaligned address bytes in both cases (`word_to_bytes addr F`).
    A `FFI_final` outcome yields `SOME (FinalFFI outcome)` with cleared locals;
    a `FFI_return` installs `set_kvar vk v (ValWord (word_of_bytes F 0w bytes))`
    and the new ffi state. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "sh_mem_load_def"]
def shMemLoadHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  if nb = 0 then
    if state.shMemaddrs address then
      match callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), emptyLocalsHOLExact state)
      | .ret newFfi newBytes =>
          (none, { setKvarHOLExact kind name
                    (.val (.word (panWordOfBytesHOL false 0 newBytes))) state with
                  ffi := newFfi })
    else (some .error, state)
  else
    if state.shMemaddrs (panByteAlignHOL address) then
      match callFFIHOL state.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), emptyLocalsHOLExact state)
      | .ret newFfi newBytes =>
          (none, { setKvarHOLExact kind name
                    (.val (.word (panWordOfBytesHOL false 0 newBytes))) state with
                  ffi := newFfi })
    else (some .error, state)

/-- Exact port of HOL `panSem$sh_mem_store`
    (`panSemScript.sml:529-547`).  The FFI configuration is the value bytes
    (`word_to_bytes w F`, truncated to `nb` when `nb ≠ 0`) followed by the
    address bytes.  On `FFI_final` the state is returned unchanged; on
    `FFI_return` only `ffi` is updated.  Membership uses the address for
    `nb = 0` and the `byte_align`ed address otherwise. -/
@[hol "cakeml/pancake/semantics/panSemScript.sml" "sh_mem_store_def"]
def shMemStoreHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (word : RiscV.Word width) (address : RiscV.Word width) (nb : Nat) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  if nb = 0 then
    if state.shMemaddrs address then
      match callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL word false ++ panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), state)
      | .ret newFfi _ => (none, { state with ffi := newFfi })
    else (some .error, state)
  else
    if state.shMemaddrs (panByteAlignHOL address) then
      match callFFIHOL state.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
          ((panWordToBytesHOL word false).take nb ++ panWordToBytesHOL address false) with
      | .final event => (some (.finalFfi event), state)
      | .ret newFfi _ => (none, { state with ffi := newFfi })
    else (some .error, state)

end Flapjack