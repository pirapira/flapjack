import Flapjack.PanSimp
import Flapjack.PanSimpEvaluate
import Flapjack.PanGlobals

namespace Flapjack.Test.PanSimpParity

open Flapjack

def evaluatorContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun value _ => [UInt8.ofNat value]
    wordOfBytes := fun _ bytes =>
      match bytes with
      | byte :: _ => byte.toNat
      | [] => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun byte => byte.toNat
    valueToNat := id }

def evaluatorHandler : PanValueStatefulFfiHandler Nat Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def evaluatorFfi : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

theorem clocked_seq_skip_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 .skip := by
  exact evalPanValueFfiClockProg_seq_skip evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi .skip

theorem clocked_skip_seq_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 1 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 (.seq .skip .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 0 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1 .skip := by
  exact evalPanValueFfiClockProg_skip_seq evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 0 1
    (fun _ => none) (fun _ => none) (fun _ => none) evaluatorFfi .skip

theorem clocked_while_body_same_matches_cake :
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.while (.const 0) .skip) =
    evalPanValueFfiClockProg evaluatorContext (fun _ _ => none)
      evaluatorHandler [] [] 0 0 8 2 (fun _ => none) (fun _ => none)
      (fun _ => none) evaluatorFfi 1
      (.while (.const 0) (.annot "tag" "text")) := by
  have hsame := evalPanValueFfiClockProg_while_body_same evaluatorContext
    (fun _ _ => none) evaluatorHandler [] [] 0 0 8 (.const 0) .skip
    (.annot "tag" "text") (hbody := by
      intro fuel clock locals globals memory ffi memoryAccess contracts memoryHandler
      cases fuel with
      | zero => simp [evalPanValueFfiClockProg]
      | succ fuel =>
          simp [evalPanValueFfiClockProg, evalPanValueFfiClockLeaf,
            evalPanValueFfiProgSteps])
  exact hsame 2 1 (fun _ => none) (fun _ => none)
    (fun _ => none) evaluatorFfi none none none

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

/-! Cake's `exp_ids_seq_assoc_eq` preservation theorem: associating a
sequence does not change the statically reachable exception identifiers. -/
theorem exp_ids_seq_assoc_preserves_raise :
    expIds (seqAssoc (.skip : Prog Nat)
      (.seq (.raise "E" (.const 0)) .tick)) = ["E"] := by
  simpa [expIds] using expIds_seqAssoc (.skip : Prog Nat)
    (.seq (.raise "E" (.const 0)) .tick)

/-! Cake's `exp_ids_ret_to_tail_eq` preservation theorem, exercised through
    a nested call handler as well as the outer program. -/
theorem exp_ids_ret_to_tail_preserves_raise :
    expIds (retToTail (.raise "E" (.const 0) : Prog Nat)) = ["E"] := by
  simpa [expIds] using expIds_retToTail
    (.raise "E" (.const 0) : Prog Nat)

theorem exp_ids_ret_to_tail_preserves_nested_raise :
    expIds (retToTail
      (.call
        (some (some (.local, "r"), some ("E", "h",
          .seq (.raise "E2" (.const 0)) .tick)))
        "f" [] : Prog Nat)) = ["E", "E2"] := by
  simpa [expIds] using expIds_retToTail
    (.call
      (some (some (.local, "r"), some ("E", "h",
        .seq (.raise "E2" (.const 0)) .tick)))
      "f" [] : Prog Nat)

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

/-! The expected values are the direct HOL evaluation of
    `pan_simp$compile` from `pan_simpScript.sml:68-72`. -/
theorem pan_simp_compile_skip :
    panSimpProg (.skip : Prog Nat) = .skip := by
  simp [panSimpProg, seqAssoc, retToTail]

theorem pan_simp_compile_seq_skip_tick :
    panSimpProg (.seq (.skip : Prog Nat) .tick) = .tick := by
  simp [panSimpProg, seqAssoc, retToTail, smartSeq]

theorem pan_simp_compile_tail_call :
    panSimpProg
        (.seq
          (.call (some (some (.local, "r"), none)) "f" [])
          (.return (.var .local "r")) : Prog Nat) =
      .call none "f" [] := by
  simp [panSimpProg, seqAssoc, retToTail, seqCallRet, smartSeq]

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

/-! `pan_simp$compile_prog` (`pan_simpScript.sml:74-81`) maps `compile` over
    function declarations and preserves every non-function declaration. -/
def compileProgDeclsFixture : List (Decl Nat) :=
  [.decl .one "g" (.const 7),
   .function
     { name := "f", inline := false, exported := false, params := [],
       body := .seq .skip .tick, returnShape := .one }]

def compileProgDeclsParity : Bool :=
  match panSimpDecls compileProgDeclsFixture with
  | [.decl .one "g" (.const 7), .function declaration] =>
      match declaration.body with
      | .tick => true
      | _ => false
  | _ => false

#guard compileProgDeclsParity

theorem pan_simp_compile_prog_map :
    panSimpDecls compileProgDeclsFixture =
      compileProgDeclsFixture.map panSimpDecl := by
  exact panSimpDecls_eq_map compileProgDeclsFixture

theorem pan_simp_compile_prog_size_of_eids :
    sizeOfEids (panSimpDecls compileProgDeclsFixture) =
      sizeOfEids compileProgDeclsFixture := by
  exact sizeOfEids_panSimpDecls compileProgDeclsFixture

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
        "f" [] : Prog Nat)) &&
    isSkip (panSimpProg (.skip : Prog Nat)) &&
    isTick (panSimpProg (.seq (.skip : Prog Nat) .tick)) &&
    isTailCall (panSimpProg
      (.seq
            (.call (some (some (.local, "r"), none)) "f" [])
            (.return (.var .local "r")) : Prog Nat))

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  if parityGuard then
    IO.println "PASS pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  else
    IO.println "FAIL pan_simp SmartSeq/seq_assoc/seq_call_ret/ret_to_tail/compile source parity"
  IO.println "PASS pan_simp clocked evaluate_seq_skip/evaluate_skip_seq Cake equations"
  IO.println "PASS pan_simp clocked evaluate_while_body_same Cake equation"
  pure parityGuard

end Flapjack.Test.PanSimpParity
