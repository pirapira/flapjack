import Flapjack.CrepeRuntime

/-!
# Pancake `crepSem.sh_mem_op`

Source reference: `cakeml/pancake/semantics/crepSemScript.sml:210-218`.

The source definition is a dispatcher, selecting the zero, one, two, or four
byte variant of `sh_mem_load`/`sh_mem_store`.  Keep that dispatch explicit at
the source-shaped runtime boundary; the underlying operation preserves the
source address for the FFI payload and applies the source aligned-address
domain check.
-/

namespace Flapjack

def crepShMemOp (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (operator : CrepMemOp)
    (name : Nat) (address : α) : CrepRuntimeStep α σ ε :=
  match operator with
  | .load => crepRuntimeSharedMem handler state .load name address
  | .store => crepRuntimeSharedMem handler state .store name address
  | .load8 => crepRuntimeSharedMem handler state .load8 name address
  | .store8 => crepRuntimeSharedMem handler state .store8 name address
  | .load16 => crepRuntimeSharedMem handler state .load16 name address
  | .store16 => crepRuntimeSharedMem handler state .store16 name address
  | .load32 => crepRuntimeSharedMem handler state .load32 name address
  | .store32 => crepRuntimeSharedMem handler state .store32 name address

@[simp] theorem crepShMemOp_load (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .load name address =
      crepRuntimeSharedMem handler state .load name address := by
  rfl

@[simp] theorem crepShMemOp_store (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .store name address =
      crepRuntimeSharedMem handler state .store name address := by
  rfl

@[simp] theorem crepShMemOp_load8 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .load8 name address =
      crepRuntimeSharedMem handler state .load8 name address := by
  rfl

@[simp] theorem crepShMemOp_store8 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .store8 name address =
      crepRuntimeSharedMem handler state .store8 name address := by
  rfl

@[simp] theorem crepShMemOp_load16 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .load16 name address =
      crepRuntimeSharedMem handler state .load16 name address := by
  rfl

@[simp] theorem crepShMemOp_store16 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .store16 name address =
      crepRuntimeSharedMem handler state .store16 name address := by
  rfl

@[simp] theorem crepShMemOp_load32 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .load32 name address =
      crepRuntimeSharedMem handler state .load32 name address := by
  rfl

@[simp] theorem crepShMemOp_store32 (handler : CrepRuntimeFfiHandler α σ ε)
    (state : CrepRuntimeState α σ) (name : Nat) (address : α) :
    crepShMemOp handler state .store32 name address =
      crepRuntimeSharedMem handler state .store32 name address := by
  rfl

end Flapjack
