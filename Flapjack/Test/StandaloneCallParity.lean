import Flapjack.Pancake.PanToCrep.Compile

/-! Oracle-backed parity tests for the standalone and assigned call forms of
    `pan_to_crep` (`pan_to_crepScript.sml:220-262`).  A standalone
    value-returning call declares its return temporaries up front as zero
    constants (`nested_decs rts (REPLICATE (LENGTH rts) (Const 0w))`), an
    assigned call whose destination is dropped by `wrap_rt` becomes a tail
    call, and a known handler on such a destination keeps only the handler
    (`Call (SOME ([], SOME (neid, handler)))`). -/

namespace Flapjack

def standalonePairContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1]))],
    functions := [("f", ([], .comb [.one, .one]))], exceptions := [],
    maxVar := 1, bytesInWord := 1 }

def unknownCalleeContext : CompileContext Nat :=
  { vars := [], functions := [], exceptions := [], maxVar := 1,
    bytesInWord := 1 }

def handlerContext : CompileContext Nat :=
  { vars := [("pair", (.comb [.one, .one], [0, 1])),
      ("v", (.one, []))],
    functions := [("f", ([], .comb [.one, .one]))],
    exceptions := [("E", 9)], maxVar := 1, bytesInWord := 8 }

/-- A standalone call to a two-word function declares locals 2 and 3 as
    zero before the call (`rts = GENLIST (vmax + SUC x) 2`). -/
example :
    compileProg standalonePairContext (.call (some (none, none)) "f" []) =
      .dec 2 (.const 0)
        (.dec 3 (.const 0) (.call (some ([2, 3], none)) "f" [])) := by
  simp [compileProg, compileArgs, functionReturnNames, allocatedNames,
    standalonePairContext, lookupInfo, Shape.shapeSize, nestedDecs,
    List.range, List.range.loop]

/-- A standalone call to an unknown callee has no return temporaries, so no
    declarations are emitted. -/
example :
    compileProg unknownCalleeContext (.call (some (none, none)) "g" []) =
      .call (some ([], none)) "g" [] := by
  simp [compileProg, compileArgs, functionReturnNames, unknownCalleeContext,
    lookupInfo, nestedDecs]

/-- An assigned call to an unknown local destination is a tail call. -/
example :
    compileProg standalonePairContext
      (.call (some (some (.local, "missing"), none)) "f" []) =
      .call none "f" [] := by
  simp [compileProg, compileArgs, callDestinationNames,
    wrapRt, standalonePairContext, lookupInfo]

/-- Cake ignores the source kind tag here: a known global-tagged destination
    uses the same `wrap_rt (FLOOKUP ctxt.vars name)` result as a local tag. -/
example :
    compileProg standalonePairContext
      (.call (some (some (.global, "pair"), none)) "f" []) =
      .call (some ([0, 1], none)) "f" [] := by
  simp [compileProg, compileArgs, callDestinationNames, wrapRt,
    standalonePairContext, lookupInfo]

/-- An assigned call to a local whose shape `wrap_rt` drops (a one-word
    variable) is a tail call. -/
example :
    compileProg handlerContext
      (.call (some (some (.local, "v"), none)) "f" []) =
      .call none "f" [] := by
  simp [compileProg, compileArgs, callDestinationNames, wrapRt,
    handlerContext, lookupInfo]

/-- A known handler on an unknown destination keeps only the handler, and
    the handler setup loads the handler variable's slots from the global
    return area (`exp_hdl`), at word indices 0 and 1 even when
    `bytesInWord = 8`. -/
example :
    compileProg handlerContext
      (.call (some (some (.local, "missing"),
        some ("E", "pair", .skip))) "f" []) =
      .call (some ([], some (9,
        .seq (.seq (.assign 0 (.loadGlob 0))
          (.seq (.assign 1 (.loadGlob 1)) .skip)) .skip))) "f" [] := by
  simp [compileProg, compileArgs, callDestinationNames,
    wrapRt, expHdlFiniteMap, panMap2, loadGlobals, crepNestedSeq,
    handlerContext, lookupInfo]

end Flapjack
