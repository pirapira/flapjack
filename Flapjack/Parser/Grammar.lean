import Flapjack.Parser.ParseTree

/-!
The `panPEG` grammar, producing parse trees.

One function per rule, in `panPEG`'s order, with the same ordered choices.
`consume`/`keep` follow upstream exactly, because `conv_*` matches on how many
children a node has.

Recursion is structural on a fuel bound rather than on the token list: the
chain from `ExpNT` down to `EBaseNT` descends sixteen levels without consuming
anything. `parseFuel` seeds it far above what the grammar can use, and
exhaustion reports its own message so it cannot be read as a syntax error.
-/

namespace Flapjack.Parser

/-- Fuel for the grammar: enough for the deepest chain each token can start. -/
def parseFuel (tokenCount : Nat) : Nat := 40 * tokenCount + 64

def fuelExhausted : String :=
  "Parser exceeded its step bound; this is a parser limit, not a syntax error"

namespace P

/-- A node with no children, as in `empty $ mksubtree ParamListNT []`. -/
def emptyNode (nonterminal : Nonterminal) : P Trees :=
  pure [.nd nonterminal [] unknownLoc]

/-- `rpt s FLAT`: repeat while it succeeds, concatenating. Each iteration must
consume a token, so recursion on the remaining count terminates. -/
def rpt (p : P Trees) : Nat → P Trees
  | 0 => pure []
  | steps + 1 => do
      match ← optional' p with
      | none => pure []
      | some trees =>
          let rest ← rpt p steps
          pure (trees ++ rest)

/-- `rpt` seeded from the tokens still to come. -/
def rptHere (p : P Trees) : P Trees := fun s => rpt p s.toks.length s

end P

open P

mutual

/-- `ShapeNT`. -/
def gShape : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      keepInt
      <|> (do
        let open' ← consume .lCurT "{"
        let inner ← gShapeComb fuel
        let close ← consume .rCurT "}"
        pure (open' ++ inner ++ close))
      <|> keepIdent

/-- `ShapeCombNT`. -/
def gShapeComb : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .shapeComb (do
      let first ← gShape fuel
      let rest ← rptHere (do
        let _ ← consume .commaT ","
        gShape fuel)
      pure (first ++ rest))

/-- `ShapedIdentNT`: two children, a shape and a name. The shape is a
`DefaultShT` leaf when omitted. -/
def gShapedIdent : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        let shape ← gShape fuel
        let name ← keepIdent
        pure (shape ++ name))
      <|> (do
        let shape ← defaultLeaf .defaultShT
        let name ← keepIdent
        pure (shape ++ name))

end

/-- `ParamListNT` and `FieldNameListNT` share this shape. -/
def gShapedIdentList (nonterminal : Nonterminal) (fuel : Nat) : P Trees :=
  subtree nonterminal (do
    let first ← gShapedIdent fuel
    let rest ← rptHere (do
      let _ ← consume .commaT ","
      gShapedIdent fuel)
    pure (first ++ rest))

/-- `EqOpsNT`. -/
def gEqOps : P Trees := keepExact .eqT "==" <|> keepExact .neqT "!="

/-- `CmpOpsNT`. -/
def gCmpOps : P Trees :=
  keepExact .lessT "<" <|> keepExact .geqT ">=" <|> keepExact .greaterT ">"
  <|> keepExact .leqT "<=" <|> keepExact .lowerT "<+" <|> keepExact .higherT ">+"
  <|> keepExact .higheqT ">=+" <|> keepExact .loweqT "<=+"

/-- `ShiftOpsNT`. -/
def gShiftOps : P Trees :=
  keepExact .lslT "<<" <|> keepExact .lsrT ">>>" <|> keepExact .asrT ">>"
  <|> keepExact .rorT "#>>"

/-- `AddOpsNT`. -/
def gAddOps : P Trees := keepExact .plusT "+" <|> keepExact .minusT "-"

/-- `MulOpsNT`. -/
def gMulOps : P Trees := keepExact .starT "*"

mutual

/-- `ExpNT`. -/
def gExp : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .exp (do
      let first ← gEBoolAnd fuel
      let rest ← rptHere (do
        let _ ← consume .boolOrT "||"
        gEBoolAnd fuel)
      pure (first ++ rest))

/-- `EBoolAndNT`. -/
def gEBoolAnd : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eBoolAnd (do
      let first ← gEEq fuel
      let rest ← rptHere (do
        let _ ← consume .boolAndT "&&"
        gEEq fuel)
      pure (first ++ rest))

/-- `EEqNT`. -/
def gEEq : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eEq (do
      let first ← gECmp fuel
      let rest ← tryRule (do
        let op ← gEqOps
        let right ← gECmp fuel
        pure (op ++ right))
      pure (first ++ rest))

/-- `ECmpNT`. -/
def gECmp : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eCmp (do
      let first ← gELoad fuel
      let rest ← tryRule (do
        let op ← gCmpOps
        let right ← gELoad fuel
        pure (op ++ right))
      pure (first ++ rest))

/-- `ELoadNT`. -/
def gELoad : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      subtree .eLoad (do
        let _ ← consumeKw .ldsK "lds"
        let shape ← gShape fuel
        let address ← gELoadByte fuel
        pure (shape ++ address))
      <|> gELoadByte fuel

/-- `ELoadByteNT`. -/
def gELoadByte : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      subtree .eLoadByte (do
        let _ ← consumeKw .ld8K "ld8"
        gELoad32 fuel)
      <|> gELoad32 fuel

/-- `ELoad32NT`. -/
def gELoad32 : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      subtree .eLoad32 (do
        let _ ← consumeKw .ld32K "ld32"
        gEOr fuel)
      <|> gEOr fuel

/-- `EOrNT`. -/
def gEOr : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eOr (do
      let first ← gEXor fuel
      let rest ← rptHere (do
        let op ← keepExact .orT "|"
        let next ← gEXor fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `EXorNT`. -/
def gEXor : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eXor (do
      let first ← gEAnd fuel
      let rest ← rptHere (do
        let op ← keepExact .xorT "^"
        let next ← gEAnd fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `EAndNT`. -/
def gEAnd : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eAnd (do
      let first ← gEShift fuel
      let rest ← rptHere (do
        let op ← keepExact .andT "&"
        let next ← gEShift fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `EShiftNT`. -/
def gEShift : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eShift (do
      let first ← gEAdd fuel
      let rest ← rptHere (do
        let op ← gShiftOps
        let next ← gEAdd fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `EAddNT`. -/
def gEAdd : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eAdd (do
      let first ← gEMul fuel
      let rest ← rptHere (do
        let op ← gAddOps
        let next ← gEMul fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `EMulNT`. -/
def gEMul : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eMul (do
      let first ← gENot fuel
      let rest ← rptHere (do
        let op ← gMulOps
        let next ← gENot fuel
        pure (op ++ next))
      pure (first ++ rest))

/-- `ENotNT`. -/
def gENot : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eNot (do
      let negated ← tryRule (keepExact .notT "!")
      let operand ← gEField fuel
      pure (negated ++ operand))

/-- `EFieldNT`. -/
def gEField : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .eField (do
      let base ← gEBase fuel
      let rest ← rptHere (do
        let _ ← consume .dotT "."
        keepNat <|> keepIdent)
      pure (base ++ rest))

/-- `EBaseNT`. -/
def gEBase : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        let _ ← consume .lParT "("
        let inner ← gExp fuel
        let _ ← consume .rParT ")"
        pure inner)
      <|> keepKw .trueK "true"
      <|> keepKw .falseK "false"
      <|> gRawStruct fuel
      <|> gNmdStruct fuel
      <|> keepKw .baseK "@base"
      <|> keepKw .biwK "@biw"
      <|> keepKw .topK "@top"
      <|> keepInt
      <|> keepIdent

/-- `RawStructNT`. -/
def gRawStruct : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .rawStruct (do
      let _ ← consume .lessT "<"
      let fields ← gArgList fuel
      let _ ← consume .greaterT ">"
      pure fields)

/-- `NmdStructNT`. -/
def gNmdStruct : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .nmdStruct (do
      let name ← keepIdent
      let _ ← consume .lessT "<"
      let fields ← gNmdFieldList fuel
      let _ ← consume .greaterT ">"
      pure (name ++ fields))

/-- `NmdFieldListNT`. -/
def gNmdFieldList : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .nmdFieldList (do
      let first ← gNmdField fuel
      let rest ← rptHere (do
        let _ ← consume .commaT ","
        gNmdField fuel)
      pure (first ++ rest))

/-- `NmdFieldNT`. -/
def gNmdField : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .nmdField (do
      let name ← keepIdent
      let _ ← consume .assignT "="
      let value ← gExp fuel
      pure (name ++ value))

/-- `ArgListNT`. -/
def gArgList : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .argList (do
      let first ← gExp fuel
      let rest ← rptHere (do
        let _ ← consume .commaT ","
        gExp fuel)
      pure (first ++ rest))

end

/-- `StoreNT`, `StoreByteNT`, `Store32NT`: the same shape, three keywords. -/
def gStoreForm (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : P Trees :=
  subtree nonterminal (do
    let _ ← consumeKw keyword described
    let address ← gExp fuel
    let _ ← consume .commaT ","
    let value ← gExp fuel
    pure (address ++ value))

/-- `SharedLoad*NT`: `!` then the sized keyword, a name, and an address. -/
def gSharedLoad (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : P Trees :=
  subtree nonterminal (do
    let _ ← consume .notT "!"
    let _ ← consumeKw keyword described
    let name ← keepIdent
    let _ ← consume .commaT ","
    let address ← gExp fuel
    pure (name ++ address))

/-- `SharedStore*NT`: `!` then the sized keyword, an address, and a value. -/
def gSharedStore (nonterminal : Nonterminal) (keyword : Keyword) (described : String)
    (fuel : Nat) : P Trees :=
  subtree nonterminal (do
    let _ ← consume .notT "!"
    let _ ← consumeKw keyword described
    let address ← gExp fuel
    let _ ← consume .commaT ","
    let value ← gExp fuel
    pure (address ++ value))

/-- `RetNT`. -/
def gRet : P Trees :=
  subtree .ret (do
    let name ← keepIdent
    let _ ← consume .assignT "="
    pure name)

/-- `AssignNT`. -/
def gAssign (fuel : Nat) : P Trees :=
  subtree .assign (do
    let name ← keepIdent
    let _ ← consume .assignT "="
    let value ← gExp fuel
    pure (name ++ value))

/-- `ExtCallNT`. -/
def gExtCall (fuel : Nat) : P Trees :=
  subtree .extCall (do
    let name ← keepFfiIdent
    let _ ← consume .lParT "("
    let configuration ← gExp fuel
    let _ ← consume .commaT ","
    let configurationLength ← gExp fuel
    let _ ← consume .commaT ","
    let array ← gExp fuel
    let _ ← consume .commaT ","
    let arrayLength ← gExp fuel
    let _ ← consume .rParT ")"
    pure (name ++ configuration ++ configurationLength ++ array ++ arrayLength))

/-- `ThrowNT`. -/
def gThrow (fuel : Nat) : P Trees :=
  subtree .throwNT (do
    let _ ← consumeKw .throwK "throw"
    let exception ← keepIdent
    let value ← gExp fuel
    pure (exception ++ value))

/-- `ReturnNT`. -/
def gReturn (fuel : Nat) : P Trees :=
  subtree .returnNT (do
    let _ ← consumeKw .retK "return"
    gExp fuel)

/--
`RetCallNT`.

Unreachable in practice: `StmtNT` tries `CallNT` first, which matches
everything this would, and `conv_Prog` has no case for it. Ported for
completeness so the rule set matches `panPEG`.
-/
def gRetCall (fuel : Nat) : P Trees :=
  subtree .retCall (do
    let _ ← consumeKw .retK "return"
    let name ← keepIdent
    let _ ← consume .lParT "("
    let args ← tryRule (gArgList fuel)
    let _ ← consume .rParT ")"
    pure (name ++ args))

/-- `CallNT`. -/
def gCall (fuel : Nat) : P Trees :=
  subtree .call (do
    let ret ← tryDefault (keepKw .retK "return" <|> gRet) .notT
    let name ← keepIdent
    let _ ← consume .lParT "("
    let args ← tryDefault (gArgList fuel) .notT
    let _ ← consume .rParT ")"
    pure (ret ++ name ++ args))

/-- `ExnDecNT`. -/
def gExnDec (fuel : Nat) : P Trees :=
  subtree .exnDec (do
    let _ ← consumeKw .exceptionK "exception"
    let exception ← keepIdent
    let _ ← consume .colonT ":"
    let shape ← gShape fuel
    let _ ← consume .semiT ";"
    pure (exception ++ shape))

/-- `StructNameNT`. -/
def gStructName (fuel : Nat) : P Trees :=
  subtree .structName (do
    let _ ← consumeKw .namedK "struct"
    let name ← keepIdent
    let _ ← consume .lCurT "{"
    let fields ← gShapedIdentList .fieldNameList fuel
    let _ ← consume .rCurT "}"
    pure (name ++ fields))

/-- `DecNT` and `GlobalDecNT`: the same shape, different nonterminal. -/
def gDecForm (nonterminal : Nonterminal) (fuel : Nat) : P Trees :=
  subtree nonterminal (do
    let _ ← consumeKw .varK "var"
    let shapedName ← gShapedIdent fuel
    let _ ← consume .assignT "="
    let value ← gExp fuel
    let _ ← consume .semiT ";"
    pure (shapedName ++ value))

/-- `DecCallNT`. -/
def gDecCallHead (fuel : Nat) : P Trees :=
  subtree .decCall (do
    let _ ← consumeKw .varK "var"
    let shapedName ← gShapedIdent fuel
    let _ ← consume .assignT "="
    let function ← keepIdent
    let _ ← consume .lParT "("
    let args ← tryRule (gArgList fuel)
    let _ ← consume .rParT ")"
    let _ ← consume .semiT ";"
    pure (shapedName ++ function ++ args))

mutual

/-- `ProgNT`. Note the second and third alternatives wrap in `DecCallNT` and
`DecNT`, not `ProgNT`, and the last contributes no tree at all. -/
def gProg : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      subtree .prog (do
        let block ← gBlock fuel
        let rest ← gProg fuel
        pure (block ++ rest))
      <|> subtree .decCall (do
        let declaration ← gDecCallHead fuel
        let body ← gTryProg fuel
        pure (declaration ++ body))
      <|> subtree .dec (do
        let declaration ← gDecForm .dec fuel
        let body ← gTryProg fuel
        pure (declaration ++ body))
      <|> subtree .prog (do
        let annotation ← keepAnnot
        let rest ← gProg fuel
        pure (annotation ++ rest))
      <|> subtree .prog (do
        let statement ← gStmt fuel
        let _ ← consume .semiT ";"
        let rest ← gProg fuel
        pure (statement ++ rest))
      <|> consume .rCurT "}"

/-- `try_ProgNT`: a closing brace becomes an explicit `Skip`. -/
def gTryProg : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      subtree .prog (do
        let _ ← consume .rCurT "}"
        defaultLeaf (.keywordT .skipK))
      <|> gProg fuel

/-- `BlockNT`. -/
def gBlock : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => gHandle fuel <|> gIf fuel <|> gWhile fuel

/-- `HandleNT`. -/
def gHandle : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .handle (do
      let _ ← consumeKw .tryK "try"
      let ret ← tryDefault gRet .notT
      let function ← keepIdent
      let _ ← consume .lParT "("
      let args ← tryDefault (gArgList fuel) .notT
      let _ ← consume .rParT ")"
      let _ ← consumeKw .catchK "catch"
      let exception ← keepIdent
      let _ ← consume .arrowT "=>"
      let bound ← keepIdent
      let _ ← consume .lCurT "{"
      let handler ← gTryProg fuel
      pure (ret ++ function ++ args ++ exception ++ bound ++ handler))

/-- `IfNT`. -/
def gIf : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .ifNT (do
      let _ ← consumeKw .ifK "if"
      let condition ← gExp fuel
      let _ ← consume .lCurT "{"
      let thenBranch ← gTryProg fuel
      let elseBranch ← tryDefault (do
        let _ ← consumeKw .elseK "else"
        let _ ← consume .lCurT "{"
        gTryProg fuel) (.keywordT .skipK)
      pure (condition ++ thenBranch ++ elseBranch))

/-- `WhileNT`. -/
def gWhile : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .whileNT (do
      let _ ← consumeKw .whileK "while"
      let condition ← gExp fuel
      let _ ← consume .lCurT "{"
      let body ← gTryProg fuel
      pure (condition ++ body))

/-- `StmtNT`, in `panPEG`'s order. -/
def gStmt : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      keepKw .skipK "skip"
      <|> gCall fuel
      <|> gAssign fuel
      <|> gStoreForm .store .stK "st" fuel
      <|> gStoreForm .storeByte .st8K "st8" fuel
      <|> gStoreForm .store32 .st32K "st32" fuel
      <|> gSharedLoad .sharedLoadByte .ld8K "ld8" fuel
      <|> gSharedLoad .sharedLoad16 .ld16K "ld16" fuel
      <|> gSharedLoad .sharedLoad32 .ld32K "ld32" fuel
      <|> gSharedLoad .sharedLoad .ldwK "ldw" fuel
      <|> gSharedStore .sharedStoreByte .st8K "st8" fuel
      <|> gSharedStore .sharedStore16 .st16K "st16" fuel
      <|> gSharedStore .sharedStore32 .st32K "st32" fuel
      <|> gSharedStore .sharedStore .stwK "stw" fuel
      <|> keepKw .brK "break"
      <|> keepKw .contK "continue"
      <|> gExtCall fuel
      <|> gThrow fuel
      <|> gRetCall fuel
      <|> gReturn fuel
      <|> keepKw .ticK "tick"
      <|> (do
        let _ ← consume .lCurT "{"
        gTryProg fuel)

/-- `FunNT`: six children -- inline, export, shape, name, params, body. -/
def gFun : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 => subtree .funNT (do
      let inline ← tryDefault (keepKw .inlineK "inline") .noinlineT
      let exported ← tryDefault (keepKw .exportK "export") .staticT
      let _ ← consumeKw .funK "fun"
      let shapedName ← gShapedIdent fuel
      let _ ← consume .lParT "("
      let params ← gShapedIdentList .paramList fuel <|> emptyNode .paramList
      let _ ← consume .rParT ")"
      let _ ← consume .lCurT "{"
      let body ← gTryProg fuel
      pure (inline ++ exported ++ shapedName ++ params ++ body))

/-- `TopDecListNT`: items until end of input. -/
def gTopDecList : Nat → P Trees
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        if ← P.atEnd then subtree .topDecList (pure []) else P.fail "Expected end of input")
      <|> subtree .topDecList (do
        let item ← gFun fuel
        let rest ← gTopDecList fuel
        pure (item ++ rest))
      <|> subtree .topDecList (do
        let item ← gDecForm .globalDec fuel
        let rest ← gTopDecList fuel
        pure (item ++ rest))
      <|> subtree .topDecList (do
        let item ← gExnDec fuel
        let rest ← gTopDecList fuel
        pure (item ++ rest))
      <|> subtree .topDecList (do
        let item ← gStructName fuel
        let rest ← gTopDecList fuel
        pure (item ++ rest))
      <|> subtree .topDecList (do
        let item ← keepAnnot
        let rest ← gTopDecList fuel
        pure (item ++ rest))

end

end Flapjack.Parser
