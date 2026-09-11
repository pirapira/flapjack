import Flapjack.CrepeCalleeParameterListRelation

/-!
Compiler metadata for functions whose formals are all scalar words.

The general parameter allocator is shape-directed.  This specialization makes
its recursive slot layout explicit, which is the compiler-side counterpart of
the word-valued callee-entry relation.
-/

namespace Flapjack

def compileWordParamVars : List VarName → Nat →
    InfoMap (Shape × List Nat) × List Nat × Nat
  | [], offset => ([], [], offset)
  | name :: names, offset =>
      let (restVars, restNames, nextOffset) := compileWordParamVars names (offset + 1)
      ((name, (.one, [offset])) :: restVars, offset :: restNames, nextOffset)

theorem compileParamVars_word_params
    (names : List VarName) (offset : Nat) :
    compileParamVars (names.map (fun name => (name, .one))) offset =
      compileWordParamVars names offset := by
  induction names generalizing offset with
  | nil => simp [compileParamVars, compileWordParamVars]
  | cons name names ih =>
      simp [compileParamVars, compileWordParamVars]
      rw [ih]
      simp

theorem compileWordParamVars_next_offset
    (names : List VarName) (offset : Nat) :
    (compileWordParamVars names offset).2.2 = offset + names.length := by
  induction names generalizing offset with
  | nil => simp [compileWordParamVars]
  | cons name names ih =>
      simp only [compileWordParamVars, List.length_cons]
      rw [ih]
      omega

end Flapjack
