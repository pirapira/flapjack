import Flapjack.CrepeGlobalStoreCorrectness

/-! A small non-word payload regression for the list-shaped global spill. -/

namespace Flapjack.Test.CrepeGlobalStoreCorrectness

theorem storeGlobals_three_words
    (state : CrepState Nat)
    (primitive : CrepPrimitiveHandler Nat)
    (ffi : CrepFfiHandler Nat)
    (sharedMem : CrepSharedMemHandler Nat)
    (hfirst : state.locals 1 = some 10)
    (hsecond : state.locals 2 = some 20)
    (hthird : state.locals 3 = some 30) :
    evalCrepFullProgState [] primitive ffi sharedMem 0 0 4 state
      (crepNestedSeq (storeGlobals 0 4
        [.var 1, .var 2, .var 3])) =
      some (.normal { state with
        globals := updateMemoryListAt state.globals 0 4 [10, 20, 30] }) := by
  apply evalCrepFullProgState_storeGlobals_vars
    (functions := []) (baseAddress := 0) (topAddress := 0)
    (address := 0) (stride := 4)
    (names := [1, 2, 3]) (values := [10, 20, 30])
  · rfl
  · simp [evalCrepFullExpsState, evalCrepFullExpState,
      hfirst, hsecond, hthird]

end Flapjack.Test.CrepeGlobalStoreCorrectness
