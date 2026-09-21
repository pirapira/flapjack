import Flapjack.PanValueFfiSemantics

/-!
# FFI event-prefix monotonicity

These are the local transition lemmas used by Cake's
`evaluate_io_events_mono`.  The concrete Cake FFI paths append events through
`callFfi`, so their incoming event trace is always a prefix of the outgoing
trace.  User-supplied accelerator handlers are intentionally not included:
they are arbitrary state transformers and need an explicit event-preservation
premise before they can participate in the same theorem.
-/

namespace Flapjack

variable {α σ : Type}

def panValueFfiSharedResultFfi : PanValueFfiSharedResult α σ → FfiState σ
  | .loaded ffi _ => ffi
  | .stored ffi => ffi
  | .final ffi _ => ffi

def panValueFfiExtCallResultFfi : PanValueFfiExtCallResult α σ → FfiState σ
  | .returned _ ffi => ffi
  | .final ffi _ => ffi

theorem panValueFfiSharedLoad_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : PanValueFfiContext α) (ffi : FfiState σ)
    (size : OpSize) (address : α) (result : PanValueFfiSharedResult α σ)
    (hresult : panValueFfiSharedLoad context ffi size address = some result) :
    ffi.ioEvents <+: (panValueFfiSharedResultFfi result).ioEvents := by
  unfold panValueFfiSharedLoad at hresult
  by_cases hdomain :
      context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · simp [hdomain] at hresult
    cases hcall : callFfi ffi (.sharedMem .mappedRead)
        [UInt8.ofNat (panValueFfiWidth size)] (context.wordToBytes address false) with
    | returned nextFfi bytes =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      have hprefix := callFfi_return_ioEvents_prefix ffi (.sharedMem .mappedRead)
        [UInt8.ofNat (panValueFfiWidth size)] (context.wordToBytes address false)
        nextFfi bytes hcall
      cases hresult
      simpa [panValueFfiSharedResultFfi] using hprefix
    | final event =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      cases hresult
      exact ⟨[], by simp [panValueFfiSharedResultFfi]⟩
  · simp [hdomain] at hresult

theorem panValueFfiSharedStore_ioEvents_prefix
    [BEq α] [OfNat α 0] [OfNat α 1] [Add α]
    (context : PanValueFfiContext α) (ffi : FfiState σ)
    (size : OpSize) (address value : α)
    (result : PanValueFfiSharedResult α σ)
    (hresult : panValueFfiSharedStore context ffi size address value = some result) :
    ffi.ioEvents <+: (panValueFfiSharedResultFfi result).ioEvents := by
  unfold panValueFfiSharedStore at hresult
  by_cases hdomain :
      context.sharedDomain (panValueFfiSharedAddress context size address) = true
  · simp [hdomain] at hresult
    cases hcall : callFfi ffi (.sharedMem .mappedWrite)
        [UInt8.ofNat (panValueFfiWidth size)] _ with
    | returned nextFfi bytes =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      have hprefix := callFfi_return_ioEvents_prefix ffi (.sharedMem .mappedWrite)
        [UInt8.ofNat (panValueFfiWidth size)] _ nextFfi bytes hcall
      cases hresult
      simpa [panValueFfiSharedResultFfi] using hprefix
    | final event =>
      rw [hcall] at hresult
      simp only [Option.some.injEq] at hresult
      cases hresult
      exact ⟨[], by simp [panValueFfiSharedResultFfi]⟩
  · simp [hdomain] at hresult

theorem panValueFfiExtCall_ioEvents_prefix
    [BEq α] [Add α] [OfNat α 1]
    (access : PanValueMemoryAccess α) (context : PanValueFfiContext α)
    (memory : α → Option (PanValue α)) (bytesInWord : α)
    (ffi : FfiState σ) (function : FunName)
    (configuration configurationLength array arrayLength : α)
    (result : PanValueFfiExtCallResult α σ)
    (hresult : panValueFfiExtCall access context memory bytesInWord ffi function
      configuration configurationLength array arrayLength = some result) :
    ffi.ioEvents <+: (panValueFfiExtCallResultFfi result).ioEvents := by
  simp [panValueFfiExtCall] at hresult
  cases hconfiguration : panValueFfiReadBytes access context memory bytesInWord
      configuration (context.valueToNat configurationLength) with
  | none => rw [hconfiguration] at hresult; simp at hresult
  | some configurationBytes =>
    rw [hconfiguration] at hresult
    cases harray : panValueFfiReadBytes access context memory bytesInWord
        array (context.valueToNat arrayLength) with
    | none => rw [harray] at hresult; simp at hresult
    | some arrayBytes =>
      rw [harray] at hresult
      simp only [Option.bind_some] at hresult
      cases hcall : callFfi ffi (.extCall function) configurationBytes arrayBytes with
      | returned nextFfi bytes =>
        rw [hcall] at hresult
        simp only [Option.some.injEq] at hresult
        have hprefix := callFfi_return_ioEvents_prefix ffi (.extCall function)
          configurationBytes arrayBytes nextFfi bytes hcall
        cases hresult
        simpa [panValueFfiExtCallResultFfi] using hprefix
      | final event =>
        rw [hcall] at hresult
        simp only [Option.some.injEq] at hresult
        cases hresult
        exact ⟨[], by simp [panValueFfiExtCallResultFfi]⟩

end Flapjack
