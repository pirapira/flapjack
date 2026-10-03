import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack

/-- Source BVL stub count, including the final namespace-alignment dummy. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "bvl_num_stubs_def"]
def bvlNumStubs : Nat := dataNumStubs + 9 + 1

/-- Source number of interleaved BVL-to-BVI namespaces. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "bvl_to_bvi_namespaces_def"]
def bvlToBviNamespaces : Nat := 4

@[hol "cakeml/compiler/backend/backend_commonScript.sml" "bvl_num_stub_MOD"]
theorem bvlNumStubMod : bvlNumStubs % bvlToBviNamespaces = 0 := by
  decide

end Flapjack
