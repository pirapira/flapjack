import Flapjack.Static

/-!
# `panLang$is_wf_flds` and `panLang$is_wf_ctxt` parity

The executable definitions are `Flapjack.isWfFields` and
`Flapjack.isWfContext` in `Flapjack/Static.lean`.  The expected values below
are checked-in direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_wf_fields_context_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:148-160`.

The context cases exercise Pancake's suffix scope rule: an earlier structure
may refer to a later structure, but a structure may not refer to itself after
its declaration has been removed from the suffix.  Duplicate names are also
rejected by `is_wf_ctxt`.
-/

namespace Flapjack.Test.PanLangWfFieldsContextParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:148-160 (is_wf_flds_def, is_wf_ctxt_def)"

def pairContext : StructContext :=
  [("Pair", { fields := [("left", .one), ("right", .one)], size := 2 })]

def forwardContext : StructContext :=
  [("Outer", { fields := [("inner", .named "Inner")], size := 1 }),
   ("Inner", { fields := [("value", .one)], size := 1 })]

def duplicateContext : StructContext :=
  [("Dup", { fields := [], size := 0 }), ("Dup", { fields := [], size := 0 })]

def selfReferenceContext : StructContext :=
  [("Self", { fields := [("value", .named "Self")], size := 1 })]

def parityGuard : Bool :=
  isWfFields [] [] &&
  isWfFields pairContext [("left", .one), ("right", .one)] &&
  !(isWfFields pairContext [("missing", .named "Missing")]) &&
  isWfContext forwardContext &&
  !(isWfContext duplicateContext) &&
  !(isWfContext selfReferenceContext)

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:148-160 (is_wf_flds_def, is_wf_ctxt_def)"
#eval parityGuard
#guard parityGuard

end Flapjack.Test.PanLangWfFieldsContextParity
