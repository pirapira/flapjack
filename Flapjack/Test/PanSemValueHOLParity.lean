import Flapjack.HolRef
import Flapjack.Basis.Pure.MlString
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Direct original-HOL parity for the exact `panSem$v`, `flatten_def`, `pan_primop_def`

The oracle rows are committed in `scripts/hol-probes/pan_flatten_probe.out`
(`word`, `record`, `named`) and
`scripts/hol-probes/pan_sem_pan_primop_probe.out`
(`pan_primop_basic = SOME [90; 0]`, `pan_primop_overflow = SOME [44; 1]`,
`pan_primop_carry_is_bit = SOME [13; 0]`, `pan_primop_wrong_length = NONE`,
`pan_primop_non_word = NONE`).  The fixtures below instantiate the exact
`ValueHOL` carriers and reproduce each row.

Bead: `flapjack-0lj.3.1`.
-/

namespace Flapjack.Test.PanSemValueHOLParity

open Flapjack
open Flapjack.Pancake.PanLang (ShapeHOL)

/-- Flatten rows from `pan_flatten_probe.out` (width 64). -/
def flattenWord : Bool :=
  flattenHOL (.val (.word (3 : BitVec 64))) == [HolWordLab.word 3]

def flattenRecord : Bool :=
  flattenHOL
      (.rStruct [.val (.word (3 : BitVec 64)),
        .rStruct [.val (.word (5 : BitVec 64)), .val (.word (7 : BitVec 64))]])
    == [HolWordLab.word 3, HolWordLab.word 5, HolWordLab.word 7]

def flattenNamed : Bool :=
  flattenHOL
      (.nStruct (Flapjack.Basis.Pure.MlString.ofString "Pair")
        [(Flapjack.Basis.Pure.MlString.ofString "left", .val (.word (3 : BitVec 64))),
         (Flapjack.Basis.Pure.MlString.ofString "right",
            .rStruct [.val (.word (5 : BitVec 64)), .val (.word (7 : BitVec 64))])])
    == [HolWordLab.word 3, HolWordLab.word 5, HolWordLab.word 7]

/-- Project a `RStruct` pair of word values to their numeric payloads. -/
def primopWords (result : Option (ValueHOL 8)) : Option (List Nat) :=
  match result with
  | some (.rStruct [.val (.word left), .val (.word right)]) =>
      some [left.toNat, right.toNat]
  | _ => none

def primopBasic : Bool :=
  primopWords
      (panPrimopHOLExact .addCarry
        [.val (.word (40 : BitVec 8)), .val (.word (50 : BitVec 8)),
         .val (.word (0 : BitVec 8))]) == some [90, 0]

def primopOverflow : Bool :=
  primopWords
      (panPrimopHOLExact .addCarry
        [.val (.word (200 : BitVec 8)), .val (.word (100 : BitVec 8)),
         .val (.word (0 : BitVec 8))]) == some [44, 1]

def primopCarryIsBit : Bool :=
  primopWords
      (panPrimopHOLExact .addCarry
        [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8)),
         .val (.word (2 : BitVec 8))]) == some [13, 0]

def primopWrongLength : Bool :=
  (primopWords
      (panPrimopHOLExact .addCarry
        [.val (.word (5 : BitVec 8)), .val (.word (7 : BitVec 8))])).isNone

def primopNonWord : Bool :=
  (primopWords
      (panPrimopHOLExact .addCarry
        [.val (.word (5 : BitVec 8)), .rStruct [], .val (.word (3 : BitVec 8))])).isNone

/-- `shape_of_def` rows from `pan_shape_of_probe.out` (width 64):
`word = One`, `rstruct = Comb [One; One]`, `nstruct = Named «Pair»`.  `ShapeHOL`
derives only `Repr`, so these compare by pattern match. -/
def shapeOfWord : Bool :=
  match shapeOfHOLExact (width := 64) (.val (.word (3 : BitVec 64))) with
  | .one => true
  | _ => false

def shapeOfRecord : Bool :=
  match shapeOfHOLExact (width := 64)
      (.rStruct [.val (.word (3 : BitVec 64)), .val (.word (5 : BitVec 64))]) with
  | .comb [.one, .one] => true
  | _ => false

def shapeOfNamed : Bool :=
  match shapeOfHOLExact (width := 64)
      (.nStruct (Flapjack.Basis.Pure.MlString.ofString "Pair") []) with
  | .named name => decide (name = Flapjack.Basis.Pure.MlString.ofString "Pair")
  | _ => false

def valueHOLGuard : Bool :=
  flattenWord && flattenRecord && flattenNamed &&
    primopBasic && primopOverflow && primopCarryIsBit &&
    primopWrongLength && primopNonWord &&
    shapeOfWord && shapeOfRecord && shapeOfNamed

#guard flattenWord
#guard flattenRecord
#guard flattenNamed
#guard primopBasic
#guard primopOverflow
#guard primopCarryIsBit
#guard primopWrongLength
#guard primopNonWord
#guard shapeOfWord
#guard shapeOfRecord
#guard shapeOfNamed
#guard valueHOLGuard

/-- Run the exact-`ValueHOL` parity checks. -/
def runChecks : IO Bool := do
  if valueHOLGuard then
    IO.println "PASS exact panSem v/flatten/pan_primop/shape_of over MlString/HolWordLab carriers (11 HOL rows)"
    pure true
  else
    IO.println "FAIL exact panSem v/flatten/pan_primop/shape_of over MlString/HolWordLab carriers"
    pure false

end Flapjack.Test.PanSemValueHOLParity
