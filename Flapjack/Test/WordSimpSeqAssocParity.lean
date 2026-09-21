import Flapjack.RiscV.WordSimp

/-!
# `Seq_assoc` reassociation is unchanged by the single-walk form

Cake's `Seq_assoc` (`word_simpScript.sml:21-38`) threads the accumulated left
prefix through its recursion and so visits every node once.  The port used to
recurse into both halves of a `Seq` and then re-run `wordSimpSeqItems` over
the two already reassociated results, which walks the processed spine again
at every `Seq` node.  These guards pin the single-walk form to the shape the
re-walking form produced.
-/

namespace Flapjack.RiscV

/-! The previous, re-walking definition, kept as the oracle.  It uses the
    same structural fuel as the optimized implementation so call metadata is
    included in the Cake `Seq_assoc` boundary as well. -/
def wordSimpSeqAssocRewalkFuel : Nat → WordProg Nat → WordProg Nat
  | 0, program => program
  | fuel + 1, .seq first second =>
      let first := wordSimpSeqAssocRewalkFuel fuel first
      let second := wordSimpSeqAssocRewalkFuel fuel second
      wordSimpLeftSeq (wordSimpSeqItems first ++ wordSimpSeqItems second)
  | fuel + 1, .ite operator condition right thenBranch elseBranch =>
      .ite operator condition right
        (wordSimpSeqAssocRewalkFuel fuel thenBranch)
        (wordSimpSeqAssocRewalkFuel fuel elseBranch)
  | fuel + 1, .call returns target arguments handler =>
      let returns := returns.map (fun metadata =>
        let (names, cutsets, returnProgram, firstLabel, secondLabel) := metadata
        (names, cutsets, wordSimpSeqAssocRewalkFuel fuel returnProgram,
          firstLabel, secondLabel))
      let handler := handler.map (fun metadata =>
        let (exception, handlerProgram, firstLabel, secondLabel) := metadata
        (exception, wordSimpSeqAssocRewalkFuel fuel handlerProgram,
          firstLabel, secondLabel))
      .call returns target arguments handler
  | fuel + 1, .loop liveIn body liveOut =>
      .loop liveIn (wordSimpSeqAssocRewalkFuel fuel body) liveOut
  | fuel + 1, .mustTerminate body =>
      .mustTerminate (wordSimpSeqAssocRewalkFuel fuel body)
  | _, program => program
termination_by fuel _ => fuel

def wordSimpSeqAssocRewalk (program : WordProg Nat) : WordProg Nat :=
  wordSimpSeqAssocRewalkFuel (wordSimpProgFuel program + 1) program

private def tick : WordProg Nat := .tick
private def a : WordProg Nat := .assign 1 (.const 1)
private def b : WordProg Nat := .assign 2 (.const 2)
private def c : WordProg Nat := .assign 3 (.const 3)
private def s : WordProg Nat := .skip

/-- Right-associated spines are the shape the source lowering produces and
    the shape the re-walk was quadratic on. -/
private def rightSpine : Nat → WordProg Nat
  | 0 => tick
  | n + 1 => .seq (.assign n (.const n)) (rightSpine n)

private def leftSpine : Nat → WordProg Nat
  | 0 => tick
  | n + 1 => .seq (leftSpine n) (.assign n (.const n))

/-- Cases that exercise leading, interior and trailing `Skip`s, both spine
    orientations, and the three constructors the pass descends into. -/
private def cases : List (WordProg Nat) :=
  [ s, a, .seq a b, .seq s a, .seq a s, .seq s s, .seq (.seq s s) s,
    .seq (.seq a b) c, .seq a (.seq b c),
    .seq (.seq s a) (.seq s b),
    .seq s (.seq s (.seq s a)),
    .seq (.seq a s) (.seq s b),
    .ite .equal 1 (.imm 0) (.seq s (.seq a b)) (.seq (.seq s s) c),
    .loop [1] (.seq s (.seq a (.seq s b))) [2],
    .mustTerminate (.seq (.seq s a) s),
    .seq (.ite .less 1 (.reg 2) (.seq s a) s) (.seq s (.loop [] (.seq s b) [])),
    /- a `Call` body is left alone by both forms; keep that pinned too -/
    .seq s (.call (some ([1], ([2], [3]), .seq s (.seq a b), 4, 5)) (some 6) [7] none),
    rightSpine 8, leftSpine 8,
    .seq (rightSpine 4) (leftSpine 4),
    .seq s (.seq (rightSpine 3) (.seq s (leftSpine 3))) ]

/-- `WordProg` carries only `Repr`, so compare the printed terms. -/
private def sameProg (left right : WordProg Nat) : Bool :=
  reprStr left == reprStr right

def wordSimpSeqAssocMatchesRewalk : Bool :=
  cases.all fun program =>
    sameProg (wordSimpSeqAssoc program) (wordSimpSeqAssocRewalk program)

#guard wordSimpSeqAssocMatchesRewalk

/-! The spine really is reassociated to the left.  A `Skip` is dropped when
    it leads its own reassociated subtree, and retained otherwise. -/
#guard sameProg (wordSimpSeqAssoc (.seq a (.seq b c))) (.seq (.seq a b) c)
#guard sameProg (wordSimpSeqAssoc (.seq s (.seq a b))) (.seq a b)
#guard sameProg (wordSimpSeqAssoc (.seq a (.seq s b))) (.seq a b)
#guard sameProg (wordSimpSeqAssoc (.seq (.seq a s) b)) (.seq (.seq a s) b)
#guard sameProg (wordSimpSeqAssoc (.seq s s : WordProg Nat)) (.skip)

/-- `wordSimpLeftSeqItems` is `wordSimpSeqItems ∘ wordSimpLeftSeq`. -/
def wordSimpLeftSeqItemsAgrees : Bool :=
  let lists : List (List (WordProg Nat)) :=
    [[], [s], [a], [s, s], [s, a], [a, s], [s, a, s, b], [a, b, c], [s, s, a]]
  lists.all fun items =>
    (wordSimpLeftSeqItems items).map reprStr ==
      (wordSimpSeqItems (wordSimpLeftSeq items)).map reprStr

#guard wordSimpLeftSeqItemsAgrees

/- Cake's `const_fp_loop` applies `const_fp_exp` to a Store address but does
   not materialize or select the address (`word_simpScript.sml:319-320`).
   This pins the source-to-Word boundary that precedes the separate
   `word_inst$inst_select` Store offset rule. -/
def wordSimpStoreAddressPreserved : Bool :=
  let program : WordProg (BitVec 64) :=
    .store (.op .add [.var 13, .const (BitVec.ofNat 64 8)]) 10
  reprStr (wordConstFp program) == reprStr program

#guard wordSimpStoreAddressPreserved

end Flapjack.RiscV
