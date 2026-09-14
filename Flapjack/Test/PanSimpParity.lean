import Flapjack.PanSimp

namespace Flapjack.Test.PanSimpParity

open Flapjack

/-! The expected values are the direct HOL evaluation of
    `pan_simp$SmartSeq` from `pan_simpScript.sml:13-16`. -/
theorem smart_seq_skip_skip :
    smartSeq (.skip : Prog Nat) .skip = .skip := by
  rfl

theorem smart_seq_skip_tick :
    smartSeq (.skip : Prog Nat) .tick = .tick := by
  rfl

theorem smart_seq_tick_skip :
    smartSeq (.tick : Prog Nat) .skip = .seq .tick .skip := by
  rfl

theorem smart_seq_tick_tick :
    smartSeq (.tick : Prog Nat) .tick = .seq .tick .tick := by
  rfl

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_assoc` from `pan_simpScript.sml:18-40`. -/
theorem seq_assoc_skip_skip :
    seqAssoc (.skip : Prog Nat) .skip = .skip := by
  simp [seqAssoc]

theorem seq_assoc_tick_skip :
    seqAssoc (.tick : Prog Nat) .skip = .tick := by
  simp [seqAssoc]

theorem seq_assoc_tick_seq_skip_tick :
    seqAssoc (.tick : Prog Nat) (.seq .skip .tick) = .seq .tick .tick := by
  simp [seqAssoc, smartSeq]

theorem seq_assoc_tick_return :
    seqAssoc (.tick : Prog Nat) (.return (.const 7)) =
      .seq .tick (.return (.const 7)) := by
  simp [seqAssoc, smartSeq]

/-! The expected values are the direct HOL evaluation of
    `pan_simp$seq_call_ret` from `pan_simpScript.sml:42-49`. -/
theorem seq_call_ret_matching_return :
    seqCallRet
        (.seq
          (.call (some (some (.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [seqCallRet]

theorem seq_call_ret_mismatching_return :
    seqCallRet
        (.seq
          (.call (some (some (.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [seqCallRet]

theorem seq_call_ret_fallback :
    seqCallRet (.tick : Prog Nat) = .tick := by
  rfl

/-! The expected values are the direct HOL evaluation of
    `pan_simp$ret_to_tail` from `pan_simpScript.sml:50-66`. -/
theorem ret_to_tail_skip :
    retToTail (.skip : Prog Nat) = .skip := by
  simp [retToTail]

theorem ret_to_tail_matching_return :
    retToTail
        (.seq
          (.call (some (some (.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [retToTail, seqCallRet]

theorem ret_to_tail_mismatching_return :
    retToTail
        (.seq
          (.call (some (some (.local, "r"), none)) "f" [])
          (.return (.var .local "s")) : Prog Nat) =
      .seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "s")) := by
  simp [retToTail, seqCallRet]

/- The HOL handler fixture uses exception id `0`; Lean's `ExceptionId` is a
   string, so the parity witness normalizes that identifier to `"E"`. -/
theorem ret_to_tail_handler_seq :
    retToTail
        (.call
          (some (some (.local, "r"), some ("E", "h", .seq .tick .tick)))
          "f" [] : Prog Nat) =
      .call
        (some (some (.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] := by
  simp [retToTail, seqCallRet]

def isSkip : Prog Nat → Bool
  | .skip => true
  | _ => false

def isTick : Prog Nat → Bool
  | .tick => true
  | _ => false

def isTickSkip : Prog Nat → Bool
  | .seq .tick .skip => true
  | _ => false

def isTickTick : Prog Nat → Bool
  | .seq .tick .tick => true
  | _ => false

def isTickReturn : Prog Nat → Bool
  | .seq .tick (.return (.const 7)) => true
  | _ => false

def isTailCall : Prog Nat → Bool
  | .call none "f" [] => true
  | _ => false

def isMismatchingCall : Prog Nat → Bool
  | .seq
      (.call (some (some (.local, "r"), none)) "f" [])
      (.return (.var .local "s")) => true
  | _ => false

def isHandlerSeq : Prog Nat → Bool
  | .call
      (some (some (.local, "r"), some ("E", "h", .seq .tick .tick)))
      "f" [] => true
  | _ => false

def parityGuard : Bool :=
  isSkip (smartSeq (.skip : Prog Nat) .skip) &&
    isTick (smartSeq (.skip : Prog Nat) .tick) &&
    isTickSkip (smartSeq (.tick : Prog Nat) .skip) &&
    isTickTick (smartSeq (.tick : Prog Nat) .tick) &&
    isSkip (seqAssoc (.skip : Prog Nat) .skip) &&
    isTick (seqAssoc (.tick : Prog Nat) .skip) &&
    isTickTick (seqAssoc (.tick : Prog Nat) (.seq .skip .tick)) &&
    isTickReturn (seqAssoc (.tick : Prog Nat) (.return (.const 7))) &&
    isTailCall (seqCallRet
      (.seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (seqCallRet
      (.seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isTick (seqCallRet (.tick : Prog Nat)) &&
    isSkip (retToTail (.skip : Prog Nat)) &&
    isTailCall (retToTail
      (.seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "r")) : Prog Nat)) &&
    isMismatchingCall (retToTail
      (.seq
        (.call (some (some (.local, "r"), none)) "f" [])
        (.return (.var .local "s")) : Prog Nat)) &&
    isHandlerSeq (retToTail
      (.call
        (some (some (.local, "r"), some ("E", "h", .seq .tick .tick)))
        "f" [] : Prog Nat))

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail source parity"
  else
    IO.println "FAIL pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail source parity"
  pure parityGuard

end Flapjack.Test.PanSimpParity
