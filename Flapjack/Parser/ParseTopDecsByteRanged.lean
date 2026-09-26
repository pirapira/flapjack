import Flapjack.Parser
import Flapjack.Parser.LocaliseByteRanged
import Flapjack.Pancake.PanToCrep.CompileProg

/-!
The executed parser boundary preserves byte-rangedness.

`parseTopDecs` is the function the compiler calls to turn Pancake source text
into declarations.  This module proves that every declaration it returns is
`DeclByteRanged`, by composing:

* the lexer token invariant (`pancakeLex_tokens_byteRanged`, re-exported by
  `safePancakeLex` on success),
* the grammar tree invariant (`gTopDecList_treesSafe` through `runGrammar`),
* the tree-to-declaration conversion (`convTopDecList_byteRanged`), and
* the localisation pass (`localiseDecls_byteRanged`).
-/

namespace Flapjack.Parser

open Flapjack
open Flapjack.Pancake.PanLang

theorem safePancakeLex_tokens_byteRanged {source : String} {toks : Toks}
    (h : safePancakeLex source = .ok toks) : ToksByteRanged toks := by
  unfold safePancakeLex at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact pancakeLex_tokens_byteRanged source
  · simp at h

theorem runGrammar_byteRanged {toks : Toks} (htoks : ToksByteRanged toks) {tree : ParseTree}
    (h : runGrammar gTopDecList toks = .ok tree) : ParseTreeByteRanged tree := by
  unfold runGrammar at h
  dsimp only at h
  split at h
  · rename_i tree0 final heq
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      exact ((gTopDecList_treesSafe (parseFuel toks.length)).1 (PState.ofToks toks)
        [tree0] final heq htoks).1 tree0 (by simp)
    · simp at h
  · simp at h
  · simp at h

theorem parseTopDecs_declByteRanged {width : Nat} (ofInt : Int → BitVec width)
    (source : String) (locations : Bool) (declarations : List (Decl (BitVec width)))
    (h : parseTopDecs ofInt source locations = .ok declarations) :
    ∀ d ∈ declarations, DeclByteRanged d := by
  unfold parseTopDecs at h
  split at h
  · simp at h
  · rename_i toks hlex
    split at h
    · simp at h
    · rename_i tree hrun
      split at h
      · simp at h
      · rename_i decls hconv
        simp only [Except.ok.injEq] at h
        subst h
        exact localiseDecls_byteRanged decls
          (convTopDecList_byteRanged ofInt locations (parseFuel toks.length) tree
            (runGrammar_byteRanged (safePancakeLex_tokens_byteRanged hlex) hrun) decls hconv)

/-! ### Routing the executed parser boundary through the exact carrier

`parseTopDecs` returns byte-ranged declarations (`parseTopDecs_declByteRanged`),
so the exact MLString-keyed `compile_prog` boundary
(`compileProgTopHOLOfExact`) applied to their `declToHOL` image equals the
production String-keyed `compileProgTopHOL`. This equality is NOT definitional:
it is kernel-proved by `compileProgTopHOLOfExact_declToHOL` using the
`DeclByteRanged` premise, i.e. propositional (not definitional) equality.
This is the kernel-checked bridge from the parser output to the exact carrier.
The production source entrypoints compose its premise through entry relocation,
`pan_simp`, struct compilation, and `compile_top`, then pass the resulting proof
to `compileProgTopHOLWithMetadataOfExact` in `compileFlapjackEntryCake`. The
source-shaped Crep output remains a documented carrier mismatch, so this
routing does not claim an exact HOL `compile_prog` theorem. Direct
original-Pancake parity evidence for the executed boundary is
`python3 scripts/check-parity-goldens.py` (wide_constants.pnk, parity
goldens=1, failures=0). -/
theorem parseTopDecs_routes_exactBoundary {width : Nat} [NeZero width]
    [BEq FunName] [LawfulBEq FunName] [LawfulHashable FunName]
    [OfNat (BitVec width) 0] [OfNat (BitVec width) 1]
    (ofInt : Int → BitVec width) (source : String) (locations : Bool)
    (declarations : List (Decl (BitVec width)))
    (h : parseTopDecs ofInt source locations = .ok declarations) :
    compileProgTopHOLOfExact (declarations.map declToHOL) =
      compileProgTopHOL declarations :=
  compileProgTopHOLOfExact_declToHOL declarations
    (parseTopDecs_declByteRanged ofInt source locations declarations h)

end Flapjack.Parser
