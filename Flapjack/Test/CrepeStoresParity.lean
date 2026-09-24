import Flapjack.Pancake.CrepLang

/-!
# Original-domain parity for `crepLang$stores`

The expected shapes come from the direct HOL-EVAL fixture
`scripts/hol-probes/crep_stores_probe.out`, sourced from
`cakeml/pancake/crepLangScript.sml:95-100`.
-/

namespace Flapjack.Test.CrepeStoresParity

open Flapjack

def isEmpty : List (CrepProg Nat) → Bool
  | [] => true
  | _ => false

def isZeroTwo : List (CrepProg Nat) → Bool
  | [.store (.var 3) (.const first),
     .store (.op .add [.var 3, .const firstOffset]) (.const second)] =>
      first == 7 && firstOffset == 4 && second == 9
  | _ => false

def isNonzeroTwo : List (CrepProg Nat) → Bool
  | [.store (.op .add [.var 3, .const firstOffset]) (.const first),
     .store (.op .add [.var 3, .const secondOffset]) (.const second)] =>
      firstOffset == 4 && first == 7 && secondOffset == 8 && second == 9
  | _ => false

def isEmptyW : List (CrepProg (BitVec 32)) → Bool
  | [] => true
  | _ => false

def isZeroTwoW : List (CrepProg (BitVec 32)) → Bool
  | [.store (.var 3) (.const first),
     .store (.op .add [.var 3, .const firstOffset]) (.const second)] =>
      first == (7 : BitVec 32) && firstOffset == (4 : BitVec 32) &&
        second == (9 : BitVec 32)
  | _ => false

def isNonzeroTwoW : List (CrepProg (BitVec 32)) → Bool
  | [.store (.op .add [.var 3, .const firstOffset]) (.const first),
     .store (.op .add [.var 3, .const secondOffset]) (.const second)] =>
      firstOffset == (4 : BitVec 32) && first == (7 : BitVec 32) &&
        secondOffset == (8 : BitVec 32) && second == (9 : BitVec 32)
  | _ => false

/-- Width-indexed `storesW` reproduces the same HOL oracle rows at 32 bits. -/
def widthParityGuard : Bool :=
  isEmptyW (storesW (width := 32) (.var 3) [] (0 : BitVec 32)) &&
  isZeroTwoW (storesW (.var 3) [.const 7, .const 9] (0 : BitVec 32)) &&
  isNonzeroTwoW (storesW (.var 3) [.const 7, .const 9] (4 : BitVec 32))

/-- Bridge: the generic stride-parametric `stores` at the machine byte width is
    the exact width-indexed `storesW`. -/
example : storesW (width := 32) (.var 3) [.const 7, .const 9] (0 : BitVec 32) =
    stores (.var 3) [.const 7, .const 9] 0 4 :=
  storesW_eq_stores (.var 3) [.const 7, .const 9] (0 : BitVec 32)

#guard widthParityGuard

def parityGuard : Bool :=
  isEmpty (stores (.var 3) [] 0 4) &&
  isZeroTwo (stores (.var 3) [.const 7, .const 9] 0 4) &&
  isNonzeroTwo (stores (.var 3) [.const 7, .const 9] 4 4)

#eval parityGuard
#guard parityGuard

def runChecks : IO Bool := do
  let results := [
    isEmpty (stores (.var 3) [] 0 4),
    isZeroTwo (stores (.var 3) [.const 7, .const 9] 0 4),
    isNonzeroTwo (stores (.var 3) [.const 7, .const 9] 4 4),
    widthParityGuard]
  match results with
  | [empty, zeroTwo, nonzeroTwo, widthOk] =>
      if empty then IO.println "PASS crep stores empty" else IO.println "FAIL crep stores empty"
      if zeroTwo then IO.println "PASS crep stores zero offset" else IO.println "FAIL crep stores zero offset"
      if nonzeroTwo then IO.println "PASS crep stores nonzero offset" else IO.println "FAIL crep stores nonzero offset"
      if widthOk then IO.println "PASS crep stores width-indexed fixed stride" else IO.println "FAIL crep stores width-indexed fixed stride"
      pure (empty && zeroTwo && nonzeroTwo && widthOk)
  | _ =>
      IO.println "FAIL crep stores result arity"
      pure false

end Flapjack.Test.CrepeStoresParity
