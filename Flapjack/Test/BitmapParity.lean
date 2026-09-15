import Flapjack.RiscV.WordToStack

/-! Oracle-backed parity tests for the write-bitmap port of CakeML's
    `write_bitmap` (word_to_stackScript.sml:240-244).  The frame carries
    `f = stack_var_count + 1` slots while the bitmap covers the `f' = f - 1`
    stack-variable slots: a variable stored at frame address `slot` sets bit
    `slot - 1`, the membership list closes with the explicit `T` terminator,
    and full chunks carry the terminator in their top bit
    (`word_list`, :231-235).  The expected words below are the values
    `bits_to_word`/`word_list` produce for the same live sets. -/

open Flapjack
open Flapjack.RiscV

/-- One live variable at frame address 5 in an 8-slot frame: bit 4 plus the
    terminator at bit 7. -/
example :
    wordStackLiveBitmapFromLocations
      ({ locations := [(9, WordLocation.stack 5)],
         scratch := 28, stackBase := 25 } : WordStackConfig) 8 64 [9] =
      [2 ^ 4 + 2 ^ 7] := by
  native_decide

/-- The register-derived builder agrees with the location-derived one: with
    `registerCount = 22`, word name 48 has `name = 8 - 2 - (24 - 22) = 4`. -/
example : wordStackLiveBitmap 22 8 64 [48] = [2 ^ 4 + 2 ^ 7] := by
  native_decide

/-- Boundary `f' = 63`: the 63 membership bits plus the terminator exceed
    the 63-bit chunk, so the frame emits two words — the full chunk carries
    the terminator at bit 63 and the trailing `[T]` folds to `1`. -/
example :
    wordStackLiveBitmapFromLocations
      ({ locations := [(9, WordLocation.stack 5)],
         scratch := 28, stackBase := 25 } : WordStackConfig) 64 64 [9] =
      [2 ^ 63 + 2 ^ 4, 1] := by
  native_decide

example : wordStackLiveBitmap 22 64 64 [160] = [2 ^ 63 + 2 ^ 4, 1] := by
  native_decide

/-- A register-resident live value contributes no membership bit; only the
    terminator word is emitted. -/
example :
    wordStackLiveBitmapFromLocations
      ({ locations := [(7, WordLocation.register 10)],
         scratch := 28, stackBase := 25 } : WordStackConfig) 8 64 [7] =
      [2 ^ 7] := by
  native_decide
