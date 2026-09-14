import Flapjack.CrepeArith

namespace Flapjack.Test.CrepeSimpProgParity

/-! Direct parity for `crep_arith$simp_prog_def`
    (`crep_arithScript.sml:83`).  The guard covers expression rewriting in
    assignments, declarations, stores, branches, calls and handlers, while
    also checking that untouched control nodes retain their source shape. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepSimpProg
      (.assign 1 (.crepOp .mul [.var 2, .const (word8 2)])) with
  | .assign 1 (.shift .lsl (.var 2) (.const value)) => value == word8 1
  | _ => false) &&
  (match crepSimpProg
      (.dec 1 (.crepOp .mul [.const (word8 2), .const (word8 3)])
        (.return [.var 1])) with
  | .dec 1 (.const value) (.return [.var 1]) => value == word8 6
  | _ => false) &&
  (match crepSimpProg
      (.store (.var 2) (.crepOp .mul [.var 3, .const (word8 2)])) with
  | .store (.var 2) (.shift .lsl (.var 3) (.const value)) => value == word8 1
  | _ => false) &&
  (match crepSimpProg
      (.ite (.crepOp .mul [.var 2, .const (word8 2)])
        (.assign 1 (.const (word8 4)))
        (.while (.crepOp .mul [.var 3, .const (word8 2)]) .skip)) with
  | .ite (.shift .lsl (.var 2) (.const first))
      (.assign 1 (.const value))
      (.while (.shift .lsl (.var 3) (.const second)) .skip) =>
      first == word8 1 && second == word8 1 && value == word8 4
  | _ => false) &&
  (match crepSimpProg
      (.call (some ([1], some (word8 7,
        .assign 2 (.crepOp .mul [.var 3, .const (word8 2)]))))
        "f" [.var 4]) with
  | .call (some ([1], some (value, .assign 2
      (.shift .lsl (.var 3) (.const shift))))
      ) "f" [.var 4] => value == word8 7 && shift == word8 1
  | _ => false) &&
  (match crepSimpProg (.break 3 : CrepProg (RiscV.Word 8)) with
  | .break 3 => true
  | _ => false)

#eval parityGuard
#guard parityGuard

end Flapjack.Test.CrepeSimpProgParity
