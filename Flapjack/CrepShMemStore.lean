import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.sh_mem_store`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:186-208`.

This is the source-width transition: the destination local must hold a word;
zero width sends the complete word followed by the original address, while a
nonzero width takes the requested prefix of the word bytes and still sends the
original address.  The byte-aligned address is used only for the domain check.
Returned FFI calls update only FFI state; final calls return `FinalFFI` while
preserving the state, as in the source.
-/

namespace Flapjack

def crepRuntimeShMemStore (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    CrepRuntimeStep α σ FfiFinalEvent :=
  match state.locals name with
  | none => (.error, state)
  | some value =>
      let alignedAddress :=
        if width = 0 then address
        else state.memoryModel.byteAlign state.bytesInWord address
      if !state.shMemaddrs alignedAddress then
        (.error, state)
      else
        let valueBytes := state.ffiContext.wordToBytes value false
        let addressBytes := state.ffiContext.wordToBytes address false
        let payload :=
          if width = 0 then valueBytes ++ addressBytes
          else valueBytes.take width ++ addressBytes
        match callFfi state.ffi (.sharedMem .mappedWrite)
            [UInt8.ofNat width] payload with
        | .final event => (.finalFfi event, state)
        | .returned ffi _ => (.normal, { state with ffi := ffi })

def crepShMemStore (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    CrepRuntimeStep α σ FfiFinalEvent :=
  crepRuntimeShMemStore state name address width

@[simp] theorem crepShMemStore_eq_runtime (state : CrepRuntimeState α σ)
    (name : Nat) (address : α) (width : Nat) :
    crepShMemStore state name address width =
      crepRuntimeShMemStore state name address width := by
  rfl

end Flapjack
