import Flapjack.Parser.Basic

namespace Flapjack.Test.ParserExtractSumParity

open Flapjack.Parser

/-! Direct parity for `parser/panPEGScript.sml:102`, `extract_sum_def`. -/

#guard P.extractSum (Sum.inl (7 : Nat)) == 7
#guard P.extractSum (Sum.inr (9 : Nat)) == 9

end Flapjack.Test.ParserExtractSumParity
