import Flapjack.Compiler.Backend.Backend

namespace Flapjack.Test.BackendConfigAttachBitmaps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.Backend
open Flapjack.Basis.Pure.MlString

/-! Kernel regression for generic payloads, ordered repeated section names,
missing-name fallback and preservation of every untouched configuration field.
The String byte payload and Bool bitmap payload are arbitrary HOL type
instantiations; neither is a mlstring representation. No standalone HOL original. -/
example (config : Config) (lab : LabToTarget.Config) :
    (attachBitmaps (sptFromAList [(1, ofString "picked")]) config true
      (some ("arbitrary-byte-payload", { lab with
        secPosLen := [(1, 4, 8), (9, 2, 5), (1, 7, 3)] }))).map
        (fun result => (result.1, result.2.1, result.2.2.symbols,
          result.2.2.sourceConf, result.2.2.closConf, result.2.2.bvlConf,
          result.2.2.dataConf, result.2.2.wordToWordConf, result.2.2.wordConf,
          result.2.2.stackConf, result.2.2.tapConf, result.2.2.exported)) =
      some ("arbitrary-byte-payload", true,
        [(ofString "picked", 4, 8),
         (ofString "NOTFOUND", 2, 5),
         (ofString "picked", 7, 3)],
        config.sourceConf, config.closConf, config.bvlConf, config.dataConf,
        config.wordToWordConf, config.wordConf, config.stackConf, config.tapConf,
        config.exported) := by
  simp [attachBitmaps, lookupAny, sptFromAList, sptInsert, sptLookup]

end Flapjack.Test.BackendConfigAttachBitmaps
