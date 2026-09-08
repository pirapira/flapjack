import Flapjack.Parser.Basic

/-!
The concrete parse tree.

Ports `panPEG`'s `pancakeNT` and the `(token, pancakeNT, locs) parsetree` the
grammar produces, so that the conversion into the Flapjack AST can be a
faithful port of `panPtreeConversion` rather than something folded into the
grammar.

Constructor names follow upstream with the `NT` suffix dropped, except where
that would collide with a Lean keyword: `IfNT` is `ifNT`, `WhileNT` is
`whileNT`, `FunNT` is `funNT`, `ThrowNT` is `throwNT` and `ReturnNT` is
`returnNT`.

What matters for the conversion is *which* tokens reach the tree. Upstream
distinguishes `consume_tok`, which contributes no child, from `keep_tok`,
which contributes a leaf, and `try_default s t`, which contributes a leaf of
`t` when `s` fails. `conv_*` then matches on child counts, so those choices
are part of the grammar's contract and are reproduced exactly.
-/

namespace Flapjack.Parser

/-- `panPEG$pancakeNT`. -/
inductive Nonterminal where
  | topDecList | structName | fieldNameList
  | funNT | prog | block | stmt | exp
  | dec | globalDec | assign | store | storeByte | store32
  | ifNT | whileNT | call | ret | handle
  | extCall | throwNT | returnNT
  | decCall | retCall
  | argList
  | paramList
  | eBoolAnd | eEq | eCmp
  | eLoad | eLoadByte | eLoad32
  | eXor | eOr | eAnd
  | eShift | eAdd | eMul | eNot | eField | eBase
  | rawStruct | nmdStruct | nmdFieldList | nmdField
  | shapedIdent | shape | shapeComb
  | eqOps | cmpOps | shiftOps | addOps | mulOps
  | sharedLoad | sharedLoadByte | sharedLoad16 | sharedLoad32
  | sharedStore | sharedStoreByte | sharedStore16 | sharedStore32
  | exnDec
  deriving DecidableEq, Repr, Inhabited

/-- A parse tree: `Lf` carries a token, `Nd` a nonterminal and its children. -/
inductive ParseTree where
  | lf (token : Token) (locs : Locs)
  | nd (nonterminal : Nonterminal) (children : List ParseTree) (locs : Locs)
  deriving Repr, Inhabited

namespace ParseTree

def locs : ParseTree → Locs
  | .lf _ locs => locs
  | .nd _ _ locs => locs

/-- `destTOK ∘ destLf`: the token of a leaf. -/
def destTok : ParseTree → Option Token
  | .lf token _ => some token
  | .nd .. => none

/-- `tokcheck`. -/
def tokcheck (tree : ParseTree) (expected : Token) : Bool :=
  match destTok tree with
  | some actual => actual == expected
  | none => false

/-- `argsNT`: the children of a node, when it is the expected nonterminal. -/
def argsNT (tree : ParseTree) (expected : Nonterminal) : Option (List ParseTree) :=
  match tree with
  | .nd nonterminal children _ => if nonterminal == expected then some children else none
  | .lf .. => none

/-- `isNT`. -/
def isNT (tree : ParseTree) (expected : Nonterminal) : Bool :=
  match tree with
  | .nd nonterminal _ _ => nonterminal == expected
  | .lf .. => false

end ParseTree

namespace P

/--
A rule's result. `panPEG` expressions return a *list* of trees, not one: a
`consume_tok` contributes none, `keep_tok` one, and `ProgNT`'s final
`consume_tok RCurT` alternative contributes none at all. `conv_*` matches on
those counts, so the distinction is part of the grammar's contract.
-/
abbrev Trees := List ParseTree

/-- `consume_tok`: accept a token and contribute no child. -/
def consume (expected : Token) (described : String) : P Trees := do
  P.expect expected described
  pure []

/-- `consume_kw`. -/
def consumeKw (keyword : Keyword) (described : String) : P Trees :=
  consume (.keywordT keyword) described

/-- `keep_tok`: accept a token and contribute it as a leaf. -/
def keepTok (accept : Token → Bool) (described : String) : P Trees := fun s =>
  match s.toks with
  | (token, locs) :: rest =>
      if accept token then (some [.lf token locs], { s with toks := rest })
      else P.fail s!"Failed to see expected token: {described}" s
  | [] => P.fail s!"Failed to see expected token; saw EOF instead: {described}" s

/-- `keep_tok` for one specific token. -/
def keepExact (expected : Token) (described : String) : P Trees :=
  keepTok (fun token => token == expected) described

/-- `keep_kw`. -/
def keepKw (keyword : Keyword) (described : String) : P Trees :=
  keepExact (.keywordT keyword) described

/-- `keep_ident`. -/
def keepIdent : P Trees :=
  keepTok (fun token => match token with | .identT _ => true | _ => false) "an identifier"

/-- `keep_ffi_ident`. -/
def keepFfiIdent : P Trees :=
  keepTok (fun token => match token with | .foreignIdent _ => true | _ => false)
    "a foreign identifier"

/-- `keep_int`. -/
def keepInt : P Trees :=
  keepTok (fun token => match token with | .intT _ => true | _ => false)
    "an integer literal"

/-- `keep_nat`. -/
def keepNat : P Trees :=
  keepTok (fun token => match token with | .intT value => 0 ≤ value | _ => false)
    "a non-negative integer literal"

/-- `keep_annot`. -/
def keepAnnot : P Trees :=
  keepTok (fun token => match token with | .annotCommentT _ => true | _ => false)
    "an annotation comment"

/-- The `empty $ mkleaf (t, unknown_loc)` half of `try_default`. -/
def defaultLeaf (token : Token) : P Trees :=
  pure [.lf token unknownLoc]

/-- `try_default s t`. -/
def tryDefault (p : P Trees) (token : Token) : P Trees :=
  p <|> defaultLeaf token

/-- `try s`: `s`, or nothing. -/
def tryRule (p : P Trees) : P Trees :=
  p <|> pure []

/--
`mksubtree`: wrap a rule's trees in one node. The node's range comes from the
tokens the rule consumed, which is upstream's `ptree_list_loc` whenever the
children cover the rule.
-/
def subtree (nonterminal : Nonterminal) (p : P Trees) : P Trees := fun s =>
  match spanned p s with
  | (some (children, locs), s') => (some [.nd nonterminal children locs], s')
  | (none, s') => (none, s')

end P

end Flapjack.Parser
