import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack

open RiscV

def pipelineDiagnosticsConfig : WordStackConfig :=
  { locations := [(0, .register 5), (1, .register 6),
      (2, .register 7), (3, .register 8)]
    scratch := 31
    stackBase := 10 }

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(17, [], (.alloc 0 ([], []) : WordProg (RiscV.Word 64)))] =
        .error { sectionId := 17, path := [], feature := .alloc } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

example :
    RiscV.pipelineWordFunctionsToStackChecked (width := 64)
      [(23, [], ((.seq .skip (.storeConsts 0 1 2 3 [])) :
        WordProg (RiscV.Word 64)))] =
        .error { sectionId := 23, path := [1], feature := .storeConsts } := by
  simp [RiscV.pipelineWordFunctionsToStackChecked,
    RiscV.wordStackIdentityConfig, RiscV.wordToStackProgWordChecked,
    RiscV.wordToStackProgNatChecked, RiscV.wordToStackProgNat,
    RiscV.wordProgFirstUnsupported, RiscV.wordProgToNat]

end Flapjack
