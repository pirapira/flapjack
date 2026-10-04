import Flapjack.HolRef
import Flapjack.Misc.Sptree
import Flapjack.Pancake.WordLang

/-!
# CakeML `word_depth`

Counterpart of `cakeml/compiler/backend/word_depthScript.sml`. This module ports
the acyclic call-graph representation and the static maximum-stack-depth
computation used by Pancake's `compile_prog_max`:

* `cakeml/compiler/backend/word_depthScript.sml:14-20` `call_tree`
  (`Leaf | Unknown | Const num call_tree | Call num call_tree |
   Branch call_tree call_tree`);
* `cakeml/compiler/backend/word_depthScript.sml:24-33` `max_depth`.

`max_depth` reads frame sizes through HOL `lookup` on a `num_map`
(`num spt`); the Lean carrier is the reviewed exact `Spt Nat` with
`Flapjack.sptLookup`, so both declarations are unqualified exact ports. The
`frame_sizes` argument is the only map, and it is the exact tree-map carrier,
not a `|->` finite map. `Option` is HOL `option` and `Nat` is HOL `num`.

The graph constructors and native WordLang traversal below implement the
remaining declarations in this source file. Full compile_prog_max and
source-to-target correctness remain separate obligations.
-/

namespace Flapjack.Compiler.Backend.WordDepth

open Flapjack (Spt sptLookup sptDelete sptSize sptMkBN sptMkBS WordLangProgHOL WordLangCutsetsHOL)

/-- HOL `OPTION_MAP2 f (SOME x) (SOME y) = SOME (f x y)`, otherwise `NONE`
    (`optionTheory`). Untagged Flapjack infrastructure. -/
def optionMap₂ {α β γ : Type} (f : α → β → γ) : Option α → Option β → Option γ
  | some x, some y => some (f x y)
  | _, _ => none

/-- Exact HOL `call_tree`
    (`cakeml/compiler/backend/word_depthScript.sml:14-20`):
    `Leaf | Unknown | Const num call_tree | Call num call_tree |
     Branch call_tree call_tree`. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "call_tree"]
inductive CallTree where
  | leaf : CallTree
  | unknown : CallTree
  | const (n : Nat) (t : CallTree) : CallTree
  | call (n : Nat) (t : CallTree) : CallTree
  | branch (t1 t2 : CallTree) : CallTree
  deriving DecidableEq, Repr

/-- Exact HOL `max_depth`
    (`cakeml/compiler/backend/word_depthScript.sml:24-33`):
    `max_depth frame_sizes Leaf = SOME 0`,
    `max_depth frame_sizes Unknown = NONE`,
    `max_depth frame_sizes (Const n t) = OPTION_MAP ((+) n) (max_depth frame_sizes t)`,
    `max_depth frame_sizes (Branch t1 t2) =
       OPTION_MAP2 MAX (max_depth frame_sizes t1) (max_depth frame_sizes t2)`,
    `max_depth frame_sizes (Call n t) =
       OPTION_MAP2 (+) (lookup n frame_sizes) (max_depth frame_sizes t)`.

    `frame_sizes` is HOL `num_map` (`num spt`), rendered by the exact
    `Spt Nat` carrier and `sptLookup`; a missing frame is `NONE`, so an
    unknown/cyclic `Call` propagates as `NONE` with no invented bound. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "max_depth_def"]
def maxDepth (frameSizes : Spt Nat) : CallTree → Option Nat
  | .leaf => some 0
  | .unknown => none
  | .const n t => (maxDepth frameSizes t).map (fun d => n + d)
  | .branch t1 t2 => optionMap₂ max (maxDepth frameSizes t1) (maxDepth frameSizes t2)
  | .call n t => optionMap₂ (· + ·) (sptLookup n frameSizes) (maxDepth frameSizes t)

/-- `sptSize` of a `mk_BN`-collapsed pair is bounded by the sum of the two
    children sizes.  Untagged Flapjack infrastructure used only for the
    `callGraph` termination measure. -/
private theorem sptSize_sptMkBN_le {α : Type} (a r : Spt α) :
    sptSize (sptMkBN a r) ≤ sptSize a + sptSize r := by
  cases a <;> cases r <;> simp [sptMkBN, sptSize]

/-- `sptSize` of a `mk_BS`-collapsed triple is bounded by the sum of the two
    children sizes plus one.  Untagged Flapjack infrastructure used only for
    the `callGraph` termination measure. -/
private theorem sptSize_sptMkBS_le {α : Type} (a r : Spt α) (v : α) :
    sptSize (sptMkBS a v r) ≤ sptSize a + sptSize r + 1 := by
  cases a <;> cases r <;> simp [sptMkBS, sptSize]

/-- Deleting a present key strictly decreases the spt size.  This untagged
    Flapjack termination lemma proves the strict inequality needed by the
    `callGraph` measure on the local tree implementation; it is not presented
    as a port of a HOL declaration. -/
private theorem sptSize_sptDelete_lt {α : Type} (t : Spt α) (k : Nat) (v : α)
    (h : sptLookup k t = some v) : sptSize (sptDelete k t) < sptSize t := by
  induction t generalizing k v with
  | ln => simp at h
  | ls x =>
      by_cases hk : k = 0
      · subst hk; simp [sptDelete, sptSize]
      · simp [sptLookup, hk] at h
  | bn l r ihl ihr =>
      by_cases hk : k = 0
      · simp [sptLookup, hk] at h
      · simp only [sptLookup, hk, if_false] at h
        by_cases he : k % 2 = 0
        · simp only [he, if_true] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_true]
          calc
            sptSize (sptMkBN (sptDelete ((k - 1) / 2) l) r)
                ≤ sptSize (sptDelete ((k - 1) / 2) l) + sptSize r :=
                  sptSize_sptMkBN_le _ _
            _ < sptSize l + sptSize r := by
                  have := ihl ((k - 1) / 2) v h; omega
        · simp only [he, if_false] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_false]
          calc
            sptSize (sptMkBN l (sptDelete ((k - 1) / 2) r))
                ≤ sptSize l + sptSize (sptDelete ((k - 1) / 2) r) :=
                  sptSize_sptMkBN_le _ _
            _ < sptSize l + sptSize r := by
                  have := ihr ((k - 1) / 2) v h; omega
  | bs l x r ihl ihr =>
      by_cases hk : k = 0
      · subst hk
        simp only [sptLookup, if_true] at h
        rw [sptDelete]
        simp only [if_true]
        simp [sptSize]
      · simp only [sptLookup, hk, if_false] at h
        by_cases he : k % 2 = 0
        · simp only [he, if_true] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_true]
          calc
            sptSize (sptMkBS (sptDelete ((k - 1) / 2) l) x r)
                ≤ sptSize (sptDelete ((k - 1) / 2) l) + sptSize r + 1 :=
                  sptSize_sptMkBS_le _ _ _
            _ < sptSize l + sptSize r + 1 := by
                  have := ihl ((k - 1) / 2) v h; omega
        · simp only [he, if_false] at h
          rw [sptDelete]
          simp only [hk, if_false, he, if_false]
          calc
            sptSize (sptMkBS l x (sptDelete ((k - 1) / 2) r))
                ≤ sptSize l + sptSize (sptDelete ((k - 1) / 2) r) + 1 :=
                  sptSize_sptMkBS_le _ _ _
            _ < sptSize l + sptSize r + 1 := by
                  have := ihr ((k - 1) / 2) v h; omega

/-- Exact HOL `mk_Branch`
    (`cakeml/compiler/backend/word_depthScript.sml:37-45`):
    `mk_Branch t1 t2` is `t1` when `t1 = t2`, `t2` when `t1 = Leaf`, `t1`
    when `t2 = Leaf`, `t1` when `t1 = Unknown`, `t2` when `t2 = Unknown`, and
    `Branch t1 t2` otherwise.  The nested `if` preserves HOL's clause order,
    including the `Unknown` absorptions after the `Leaf` cases. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "mk_Branch_def"]
def mkBranch (t1 t2 : CallTree) : CallTree :=
  if t1 = t2 then t1
  else if t1 = .leaf then t2
  else if t2 = .leaf then t1
  else if t1 = .unknown then t1
  else if t2 = .unknown then t2
  else .branch t1 t2

/-- Exact HOL `call_graph`
    (`cakeml/compiler/backend/word_depthScript.sml:47-86`).

    The program argument is HOL wordLang `prog`
    (`wordLangScript.sml:35-68`), rendered by the exact `WordLangProgHOL`
    carrier; the code map is the exact `Spt (Nat × prog)` tree map
    (`num_map = 'a spt`, not a `|->` finite map) and `lookup`/`delete`/`size`
    are `sptLookup`/`sptDelete`/`sptSize`.  Each clause is transcribed one for
    one: `Seq`/`If` combine with `mkBranch`; `Call` handles the `dest`
    `NONE`/`SOME`, the `MEM d ns ∧ ret = NONE` short-circuit, the
    `lookup`-miss `Unknown`, the tail (`ret = NONE`) `LENGTH ns < total` guard
    with the extended `ns` list, and the `ret = SOME` return case where
    `delete d funs` is used for the callee body and both the handler and return
    programs are walked; `MustTerminate`/`Loop` descend; `Alloc` gives
    `Call n Leaf`; `Install` gives `Unknown`; the default is `Leaf`.

    HOL terminates by the lexicographic measure
    `(size funs, total - LENGTH ns, prog_size (K 0) p)`
    (`word_depthScript.sml:81-86`).  Lean uses the same lexicographic structure
    `(sptSize funs, total - ns.length, sizeOf p)`; `sptSize_sptDelete_lt`
    justifies the `delete`-case decrease and `sizeOf` is Lean's structural size
    standing in for the datatype-package-generated `prog_size (K 0)` (the same
    stand-in the reviewed crepSem evaluator records).  The measure affects only
    termination, not the computed call tree.

    The word payload type is HOL's type-indexed `'a word` at positive
    dimension `dimindex (:α) ≥ 1`; Lean binds it as `{width : Nat}
    [NeZero width]` with the `(words_as_type_indexed_bitvec)` qualifier. This is
    a carrier translation only: no clause, quantifier, or side condition
    changes. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "call_graph_def" (words_as_type_indexed_bitvec)]
def callGraph {width : Nat} [NeZero width] :
    Spt (Nat × WordLangProgHOL (BitVec width)) → Nat → List Nat → Nat →
      WordLangProgHOL (BitVec width) → CallTree
  | funs, n, ns, total, .seq p1 p2 =>
      mkBranch (callGraph funs n ns total p1) (callGraph funs n ns total p2)
  | funs, n, ns, total, .ite _ _ _ p1 p2 =>
      mkBranch (callGraph funs n ns total p1) (callGraph funs n ns total p2)
  | funs, n, ns, total, .call ret dest _args handler =>
      match dest with
      | none => .unknown
      | some d =>
          if d ∈ ns ∧ ret = none then .leaf
          else
            match _hd : sptLookup d funs with
            | none => .unknown
            | some (_, body) =>
                match ret with
                | none =>
                    if ns.length < total then
                      mkBranch (.call d .leaf)
                        (callGraph funs d (d :: ns) total body)
                    else .leaf
                | some (_, _, retProg, _, _) =>
                    let newFuns := sptDelete d funs
                    match handler with
                    | none =>
                        .branch (.call n (.call d .leaf))
                          (mkBranch (.call n (callGraph newFuns d [d] total body))
                                    (callGraph funs n ns total retProg))
                    | some (_, p, _, _) =>
                        .branch (.call n (.const 3 (.call d .leaf)))
                          (mkBranch (.call n (.const 3
                              (callGraph newFuns d [d] total body)))
                          (mkBranch (callGraph funs n ns total p)
                                    (callGraph funs n ns total retProg)))
  | funs, n, ns, total, .mustTerminate p => callGraph funs n ns total p
  | _, n, _, _, .alloc _ _ => .call n .leaf
  | _, _, _, _, .install _ _ _ _ _ => .unknown
  | funs, n, ns, total, .loop _ body _ => callGraph funs n ns total body
  | _, _, _, _, _ => .leaf
termination_by funs _ ns total p => (sptSize funs, total - ns.length, sizeOf p)
decreasing_by
  all_goals
    first
      | apply Prod.Lex.left
        exact sptSize_sptDelete_lt _ _ _ _hd
      | apply Prod.Lex.right
        apply Prod.Lex.left
        simp only [List.length_cons]; omega
      | apply Prod.Lex.right
        apply Prod.Lex.right
        decreasing_trivial

/-- Exact HOL `full_call_graph`
    (`cakeml/compiler/backend/word_depthScript.sml:88-94`):
    `full_call_graph n funs` is `Unknown` when `n` is absent from `funs`, and
    otherwise `Branch (Call n Leaf) (call_graph funs n [n] (size funs) prog)`
    for the looked-up program `prog`.

    As with `callGraph`, HOL's `prog` is type-indexed over `'a word` at positive
    `dimindex (:α)`; Lean binds `{width : Nat} [NeZero width]` and carries the
    `(words_as_type_indexed_bitvec)` qualifier for that carrier translation
    only. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "full_call_graph_def" (words_as_type_indexed_bitvec)]
def fullCallGraph {width : Nat} [NeZero width] (n : Nat)
    (funs : Spt (Nat × WordLangProgHOL (BitVec width))) : CallTree :=
  match sptLookup n funs with
  | none => .unknown
  | some (_, prog) =>
      .branch (.call n .leaf) (callGraph funs n [n] (sptSize funs) prog)

/-- Exact HOL `max_depth_graphs`
    (`cakeml/compiler/backend/word_depthScript.sml:96-105`):
    `max_depth_graphs ss [] all funs all_funs = SOME 0`, and for `n :: ns` it
    is `NONE` when `n` is absent from `all_funs`, otherwise the `OPTION_MAP2
    MAX` of `lookup n ss`, of `max_depth ss (call_graph funs n all (size
    all_funs) body)`, and of the recursive `max_depth_graphs` over `ns`.
    `ss` is the frame-size `num_map` (`Spt Nat`) and `all`/`all_funs` carry the
    starting list of names and the full code map. The metadata in `funs`
    is HOL num, whereas `all_funs` has a separately quantified arbitrary
    metadata carrier. `Metadata : Type` preserves that original beta binder
    without equality, inhabitance or successful-search premises. Both maps
    retain the same word-program dimension.

    As with `callGraph`, the wordLang programs are over HOL's type-indexed
    `'a word` at positive `dimindex (:α)`; Lean binds `{width : Nat}
    [NeZero width]` and carries the `(words_as_type_indexed_bitvec)` qualifier
    for that carrier translation only. -/
@[hol "cakeml/compiler/backend/word_depthScript.sml" "max_depth_graphs_def" (words_as_type_indexed_bitvec)]
def maxDepthGraphs {width : Nat} [NeZero width] {Metadata : Type} :
    Spt Nat → List Nat → List Nat →
      Spt (Nat × WordLangProgHOL (BitVec width)) →
      Spt (Metadata × WordLangProgHOL (BitVec width)) → Option Nat
  | _, [], _, _, _ => some 0
  | ss, n :: ns, all, funs, allFuns =>
      match sptLookup n allFuns with
      | none => none
      | some (_, body) =>
          optionMap₂ max (sptLookup n ss)
            (optionMap₂ max (maxDepth ss (callGraph funs n all (sptSize allFuns) body))
                           (maxDepthGraphs ss ns all funs allFuns))
termination_by _ ns _ _ _ => ns.length

end Flapjack.Compiler.Backend.WordDepth
