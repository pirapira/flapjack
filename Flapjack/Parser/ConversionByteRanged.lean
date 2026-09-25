import Flapjack.Parser.ByteRanged
import Flapjack.Parser.Conversion

/-!
Byte-rangedness of the concrete parse tree and of the first conversion step.

`Flapjack/Parser/ByteRanged.lean` proves the executed lexer only ever produces
token names whose characters are bytes (`< 256`). This module starts lifting
that invariant into the conversion phase: it defines `ParseTreeByteRanged`
(every leaf token is byte-ranged) and shows the identifier-reading conversion
helpers `convIdent` and `convFfiIdent` only return byte-ranged strings from such
a tree.

This is the first, primitive slice of bead `flapjack-pxn.18.3.5.8.7.1.1.1`; the
remaining lift is the recursive conversion family (`convParams`, `convShape`,
the `convExp`/`convProg` mutual block, `convTopDec`/`convTopDecList`) and the
grammar invariant that `parseTopDecs` produces byte-ranged trees.
-/

namespace Flapjack.Parser

/-- Every leaf token of the tree is name-byte-ranged. -/
def ParseTreeByteRanged : ParseTree → Prop
  | .lf token _ => TokenNameByteRanged token
  | .nd _ children _ => ∀ child ∈ children, ParseTreeByteRanged child

theorem parseTreeByteRanged_lf {token : Token} {locs : Locs}
    (h : TokenNameByteRanged token) : ParseTreeByteRanged (.lf token locs) := by
  simpa [ParseTreeByteRanged] using h

theorem parseTreeByteRanged_nd_apply {nonterminal : Nonterminal} {children : List ParseTree}
    {locs : Locs} {child : ParseTree} (h : ParseTreeByteRanged (.nd nonterminal children locs))
    (hmem : child ∈ children) : ParseTreeByteRanged child := by
  have h' : ∀ child ∈ children, ParseTreeByteRanged child := by
    simpa [ParseTreeByteRanged] using h
  exact h' child hmem

/-- A byte-ranged tree's `destTok` is name-byte-ranged. -/
theorem destTok_byteRanged {tree : ParseTree} {token : Token}
    (ht : ParseTreeByteRanged tree) (h : tree.destTok = some token) :
    TokenNameByteRanged token := by
  cases tree with
  | lf tok locs =>
      simp only [ParseTree.destTok, Option.some.injEq] at h
      subst h
      simpa [ParseTreeByteRanged] using ht
  | nd nonterminal children locs =>
      simp [ParseTree.destTok] at h

/-- `conv_ident` returns a byte-ranged string from a byte-ranged tree. -/
theorem convIdent_byteRanged {tree : ParseTree} {name : String}
    (ht : ParseTreeByteRanged tree) (h : convIdent tree = some name) :
    StringByteRanged name := by
  cases tree with
  | lf token locs =>
      simp only [convIdent, ParseTree.destTok] at h
      cases token <;> simp_all [ParseTreeByteRanged, TokenNameByteRanged]
  | nd nonterminal children locs =>
      simp [convIdent, ParseTree.destTok] at h

/-- `conv_ffi_ident` returns a byte-ranged string from a byte-ranged tree. -/
theorem convFfiIdent_byteRanged {tree : ParseTree} {name : String}
    (ht : ParseTreeByteRanged tree) (h : convFfiIdent tree = some name) :
    StringByteRanged name := by
  cases tree with
  | lf token locs =>
      simp only [convFfiIdent, ParseTree.destTok] at h
      cases token <;> simp_all [ParseTreeByteRanged, TokenNameByteRanged]
  | nd nonterminal children locs =>
      simp [convFfiIdent, ParseTree.destTok] at h

end Flapjack.Parser
