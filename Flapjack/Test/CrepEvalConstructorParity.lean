import Flapjack.Pancake.Semantics.CrepSem
import Flapjack.RiscV.PanMemory
import Flapjack.Pancake.Proofs.CrepArith.ExactStateProjection

/-!
Direct width-8 word-result constructor checks matching
`scripts/hol-probes/crep_eval_probe.out`. The evaluator equations are generic
in their word carrier and do not pass through `riscvCrepWordTarget`; the state
below only supplies the production evaluator's existing runtime fields.
-/

namespace Flapjack.Test.CrepEvalConstructorParity

open Flapjack

def word8 (n : Nat) : RiscV.Word 8 := BitVec.ofNat 8 n

def word8FfiContext : PanValueFfiContext (RiscV.Word 8) where
  sharedDomain := fun _ => false
  byteAlign := fun address => address
  bigEndian := false
  wordToBytes := fun value _ => [UInt8.ofNat value.toNat]
  wordOfBytes := fun _ bytes => BitVec.ofNat 8 ((bytes.headD 0).toNat)
  wordToByte := fun value => UInt8.ofNat value.toNat
  byteToWord := fun byte => BitVec.ofNat 8 byte.toNat
  valueToNat := fun value => value.toNat

def probeState : CrepRuntimeState (RiscV.Word 8) Unit :=
  { locals := fun name => if name == 1 then some (.word (word8 7)) else none
    globals := fun address =>
      if address == (4 : BitVec 5) then some (.word (word8 11)) else none
    code := FEMPTY
    memory := fun address => if address == word8 3 then .word (word8 9) else .word 0
    memaddrs := fun address => address == word8 3
    shMemaddrs := fun _ => false
    memoryModel := RiscV.panRiscVMemoryModel
    bytesInWord := word8 1
    ffiContext := word8FfiContext
    clock := 0
    bigEndian := false
    ffi := natCrepRuntimeFfiState
    baseAddress := word8 12
    topAddress := word8 13 }

/-! The exact-field projection fixture below uses the same width-8 state rows
    as `scripts/hol-probes/crep_eval_probe.out`. It keeps the HOL finite-map,
    `CrepProgHOL` code-map, `HolWordLab`, and `HolFfiState` carriers at the
    boundary, then checks the source evaluator observation for Local, Load,
    and LoadGlob. -/
def exactCrepLocals : CrepLocalsExact 8 :=
  FUPDATE FEMPTY (1, HolWordLab.word (word8 7))

def exactCrepGlobals : FiniteMap (BitVec 5) (HolWordLab 8) :=
  FUPDATE FEMPTY (4, HolWordLab.word (word8 11))

def exactCrepCode : CrepCodeMapExact 8 := fun _ => none

def exactCrepMemory (address : BitVec 8) : HolWordLab 8 :=
  if address == word8 3 then HolWordLab.word (word8 9) else HolWordLab.word (word8 0)

def exactCrepMemaddrs (address : BitVec 8) : Prop := address = word8 3

local instance : DecidablePred exactCrepMemaddrs := fun address => by
  unfold exactCrepMemaddrs
  infer_instance

def exactCrepShMemaddrs (_address : BitVec 8) : Prop := False

local instance : DecidablePred exactCrepShMemaddrs := fun _ => isFalse id

def exactCrepFfi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

def exactCrepProjection : CrepHolState (Fin 8 → Bool) Unit :=
  crepSourceEvalStateOfHOLFields exactCrepLocals exactCrepGlobals exactCrepCode
    exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
    (word8 12) (word8 13) natCrepRuntimeFfiState

def word8Bits (value : Nat) : Fin 8 → Bool :=
  bitVecToHolWordBits (word8 value)

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits (.var 1 : CrepExpHOL 8)) =
      some (.word (word8Bits 7)) := by
  simpa [exactCrepProjection, exactCrepLocals, word8Bits,
    holWordLabToCrepSourceWordLab, bitVecToHolWordBits_ofNat,
    FUPDATE, FEMPTY, FLOOKUP] using
      (evalCrepSourceProjection_var exactCrepLocals exactCrepGlobals exactCrepCode
        exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
        (word8 12) (word8 13) natCrepRuntimeFfiState 1)

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepSimpExpHOLToSourceBits (.var 1 : CrepExpHOL 8)) =
  evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits (.var 1 : CrepExpHOL 8)) := by
  exact crepSimpExpCorrect1SourceProjection_var
    (fun pair => pair.2) exactCrepLocals exactCrepGlobals exactCrepCode
    exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
    (word8 12) (word8 13) (HolWordLab.word (word8 7)) 1
    (by
      simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
        crepExpOfHOL, mapCrepExpWord,
        crepSourceEvalStateOfHOLFields, exactCrepLocals,
        holWordLabToCrepSourceWordLab, FUPDATE, FEMPTY,
        FLOOKUP])

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepSimpExpHOLToSourceBits (.const (word8 5) : CrepExpHOL 8)) =
  evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits (.const (word8 5) : CrepExpHOL 8)) := by
  exact crepSimpExpCorrect1SourceProjection_const
    (fun pair => pair.2) exactCrepLocals exactCrepGlobals exactCrepCode
    exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
    (word8 12) (word8 13) (HolWordLab.word (word8 5)) (word8 5)
    (by
      simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
        crepExpOfHOL, mapCrepExpWord,
        crepSourceEvalStateOfHOLFields, exactCrepLocals,
        holWordLabToCrepSourceWordLab, FUPDATE, FEMPTY,
        FLOOKUP])

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepSimpExpHOLToSourceBits
      (.load (.const (word8 3)) : CrepExpHOL 8)) =
  evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits
      (.load (.const (word8 3)) : CrepExpHOL 8)) := by
  exact crepSimpExpCorrect1SourceProjection_load
    (fun pair => pair.2) exactCrepLocals exactCrepGlobals exactCrepCode
    exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
    (word8 12) (word8 13) (.const (word8 3))
    (HolWordLab.word (word8 9))
    (by
      simp [evalCrepHolFiniteWordSourceExpWordLab,
        evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
        crepExpOfHOL, mapCrepExpWord, crepSourceEvalStateOfHOLFields,
        exactCrepMemory, exactCrepMemaddrs, word8,
        holWordBitsToBitVec_bitVecToHolWordBits])
    (by
      intro _ hAddress
      have hAddressOriginal :
          evalCrepHolFiniteWordSourceExpWordLab
            (instFinHolFiniteDimension (width := 8)) exactCrepProjection
            (crepExpHOLToSourceBits
              (.const (word8 3) : CrepExpHOL 8)) ≠ none := by
        simp [evalCrepHolFiniteWordSourceExpWordLab,
          evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
          crepExpOfHOL, mapCrepExpWord, word8]
      exact crepSimpExpCorrect1SourceProjection_const
        (fun pair => pair.2) exactCrepLocals exactCrepGlobals exactCrepCode
        exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
        (word8 12) (word8 13) (HolWordLab.word (word8 3)) (word8 3)
        (by
          simp [evalCrepHolFiniteWordSourceExpWordLab,
            evalCrepHolFiniteWordSourceExp, crepExpHOLToSourceBits,
            crepExpOfHOL, mapCrepExpWord,
            crepSourceEvalStateOfHOLFields, exactCrepMemory, exactCrepMemaddrs,
            word8]))

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits (.load (.const (word8 3)) : CrepExpHOL 8)) =
      some (.word (word8Bits 9)) := by
  have hAddress := evalCrepSourceProjection_const exactCrepLocals exactCrepGlobals
    exactCrepCode exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs
    0 false exactCrepFfi (word8 12) (word8 13) natCrepRuntimeFfiState (word8 3)
  have hAddress : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 8)) exactCrepProjection
      (crepExpHOLToSourceBits (.const (word8 3) : CrepExpHOL 8)) =
        some (bitVecToHolWordBits (word8 3)) := by
    simpa [exactCrepProjection, evalCrepHolFiniteWordSourceExpWordLab] using hAddress
  have hAddressRaw : evalCrepHolFiniteWordSourceExp
      (instFinHolFiniteDimension (width := 8)) exactCrepProjection
      (crepExpHOLToSourceBits (.const (word8 3) : CrepExpHOL 8)) =
        some (word8Bits 3) := by
    simpa [word8Bits] using hAddress
  have hLoad := evalCrepSourceProjection_load exactCrepLocals exactCrepGlobals
    exactCrepCode exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs
    0 false exactCrepFfi (word8 12) (word8 13) (word8 3)
    natCrepRuntimeFfiState (.const (word8 3)) hAddressRaw
  simpa [exactCrepProjection, exactCrepMemory, exactCrepMemaddrs, word8Bits,
    holWordLabToCrepSourceWordLab, bitVecToHolWordBits_ofNat] using hLoad

example : evalCrepHolFiniteWordSourceExpWordLab
    (instFinHolFiniteDimension (width := 8)) exactCrepProjection
    (crepExpHOLToSourceBits (.loadGlob (4 : BitVec 5) : CrepExpHOL 8)) =
      some (.word (word8Bits 11)) := by
  simpa [exactCrepProjection, exactCrepGlobals, word8Bits,
    holWordLabToCrepSourceWordLab, bitVecToHolWordBits_ofNat,
    FUPDATE, FEMPTY, FLOOKUP] using
      (evalCrepSourceProjection_loadGlob exactCrepLocals exactCrepGlobals exactCrepCode
        exactCrepMemory exactCrepMemaddrs exactCrepShMemaddrs 0 false exactCrepFfi
        (word8 12) (word8 13) natCrepRuntimeFfiState (4 : BitVec 5))

/- HOL crep_eval_probe: const, local hit/miss, word load hit/miss, and global
   hit return the corresponding Word word_lab values or NONE. -/
#guard (evalCrepRuntimeExp probeState (.const (word8 5))).map PanWordLab.word ==
  some (.word (word8 5))
#guard (evalCrepRuntimeExp probeState (.var 1)).map PanWordLab.word ==
  some (.word (word8 7))
#guard (evalCrepRuntimeExp probeState (.var 2)).map PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState (.load (.const (word8 3)))).map PanWordLab.word ==
  some (.word (word8 9))
#guard (evalCrepRuntimeExp probeState (.load (.const (word8 8)))).map PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState (.loadGlob (4 : BitVec 5))).map PanWordLab.word ==
  some (.word (word8 11))
#guard (evalCrepRuntimeExp probeState (.loadGlob (8 : BitVec 5))).map PanWordLab.word == none
/- HOL crep_arith_eval_mul_const_probe: the general multiplier case leaves
   Crepop Mul [Var 1; Const 3w], which evaluates to Word 21w. -/
#guard (evalCrepRuntimeExp probeState
    (.crepOp .mul [.var 1, .const (word8 3)])).map PanWordLab.word ==
  some (.word (word8 21))
#guard (evalCrepRuntimeExp probeState (.crepOp .mul [.const (word8 4)])).map
    PanWordLab.word == none
#guard (evalCrepRuntimeExp probeState .baseAddr).map PanWordLab.word ==
  some (.word (word8 12))
#guard (evalCrepRuntimeExp probeState .topAddr).map PanWordLab.word ==
  some (.word (word8 13))

example : (evalCrepRuntimeExp probeState (.var 1)).map PanWordLab.word =
    some (.word (word8 7)) :=
  evalCrepRuntimeExp_var_wordLab probeState 1

example : (evalCrepRuntimeExp probeState (.load (.const (word8 3)))).map
    PanWordLab.word = some (.word (word8 9)) := by
  rw [evalCrepRuntimeExp_load_wordLab]
  simp [evalCrepRuntimeExp, probeState, word8]

end Flapjack.Test.CrepEvalConstructorParity
