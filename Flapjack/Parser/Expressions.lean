import Flapjack.Language
import Flapjack.Parser.Basic

/-!
Shape and expression grammar.

One function per `panPEG` nonterminal, in the same precedence order, building
the AST that `panPtreeConversion`'s `conv_Shape` and `conv_Exp` would have
built from the parse tree.

Every optional or repeated piece wraps its operator *and* its operand in a
single backtracking attempt, mirroring `panPEG`'s `try` and `rpt`, which apply
to a whole `seql`. Wrapping only the operator would let `<a, b>` consume its
closing `>` as a comparison and then fail with no way back.

The mutual block recurses structurally on a fuel bound rather than on the
token list: the precedence chain from `ExpNT` down to `EBaseNT` descends
sixteen levels without consuming anything, so the token count alone is not a
decreasing measure. `parseFuel` seeds it well above what any input needs, and
exhausting it reports its own message so it can never be mistaken for a
syntax error.
-/

namespace Flapjack.Parser

open Flapjack

/-- Fuel for the recursive-descent grammar: enough for the deepest chain each
token can start. -/
def parseFuel (tokenCount : Nat) : Nat := 40 * tokenCount + 64

def fuelExhausted : String :=
  "Parser exceeded its step bound; this is a parser limit, not a syntax error"

/-- `panLang$shape_val`: the zero value of a shape. -/
def shapeVal (ofInt : Int → α) : Shape → Exp α
  | .one => .const (ofInt 0)
  | .named _ => .const (ofInt 0)
  | .comb shapes => .rStruct (shapeVals ofInt shapes)
where
  shapeVals (ofInt : Int → α) : List Shape → List (Exp α)
    | [] => []
    | shape :: shapes => shapeVal ofInt shape :: shapeVals ofInt shapes

/-- `ShapeNT` with `conv_Shape`: a positive literal `n` becomes `n` copies of
`One`, braces a combination, and an identifier a named struct. -/
def parseShape : Nat → P Shape
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        let value ← P.intLit
        if value < 1 then P.fail "A shape literal must be at least 1"
        else if value == 1 then pure .one
        else pure (.comb (List.replicate value.toNat .one)))
      <|> (do
        P.expect .lCurT "{"
        let shapes ← P.sepByComma (parseShape fuel)
        P.expect .rCurT "}"
        pure (.comb shapes))
      <|> (do
        let name ← P.ident
        pure (.named name))

/-- `ShapedIdentNT`: an optional shape before the name, defaulting to `One`. -/
def parseShapedIdent (fuel : Nat) : P (VarName × Shape) :=
  (do
    let shape ← parseShape fuel
    let name ← P.ident
    pure (name, shape))
  <|> (do
    let name ← P.ident
    pure (name, .one))

/-- `ParamListNT` and `FieldNameListNT` share this shape. -/
def parseParamList (fuel : Nat) : P (List (VarName × Shape)) :=
  P.sepByComma (parseShapedIdent fuel)

def addOpOfToken : Token → Option BinOp
  | .plusT => some .add
  | .minusT => some .sub
  | _ => none

def shiftOfToken : Token → Option Shift
  | .lslT => some .lsl
  | .lsrT => some .lsr
  | .asrT => some .asr
  | .rorT => some .ror
  | _ => none

/--
`conv_cmp`. The flag says whether the operands are swapped: Pancake has no
`Greater`, so `a > b` is `Less` applied to `b, a`.
-/
def cmpOfToken : Token → Option (Cmp × Bool)
  | .eqT => some (.equal, false)
  | .neqT => some (.notEqual, false)
  | .lessT => some (.less, false)
  | .geqT => some (.notLess, false)
  | .greaterT => some (.less, true)
  | .leqT => some (.notLess, true)
  | .lowerT => some (.lower, false)
  | .higherT => some (.lower, true)
  | .higheqT => some (.notLower, false)
  | .loweqT => some (.notLower, true)
  | _ => none

/-- `EqOpsNT`. -/
def eqOpOfToken : Token → Option (Cmp × Bool)
  | .eqT => cmpOfToken .eqT
  | .neqT => cmpOfToken .neqT
  | _ => none

/-- `CmpOpsNT`: the ordering comparisons, which exclude `==` and `!=`. -/
def cmpOpOfToken : Token → Option (Cmp × Bool)
  | .eqT => none
  | .neqT => none
  | other => cmpOfToken other

/-- Accept one of the given operator tokens. -/
def operator (classify : Token → Option β) (described : String) : P β := fun s =>
  match s.toks with
  | (token, _) :: rest =>
      match classify token with
      | some value => (some value, { s with toks := rest })
      | none => P.fail s!"Failed to see expected token: {described}" s
  | [] => P.fail s!"Failed to see expected token; saw EOF instead: {described}" s

/-- `isSubOp`: subtraction takes exactly two operands, so it never flattens. -/
def isSubOp : Exp α → Bool
  | .op .sub [_, _] => true
  | _ => false

/--
`conv_binaryExps`: a run of the same operator flattens into one `Op` node,
except that subtraction nests because it is binary.
-/
def foldBinary (acc : Exp α) : List (BinOp × Exp α) → Exp α
  | [] => acc
  | (op, operand) :: rest =>
      let combined :=
        match acc with
        | .op bop args =>
            if bop != op || isSubOp acc then Exp.op op [acc, operand]
            else Exp.op bop (args ++ [operand])
        | _ => Exp.op op [acc, operand]
      foldBinary combined rest

/-- `conv_panops`: multiplication always nests to the left. -/
def foldPan (acc : Exp α) : List (PanOp × Exp α) → Exp α
  | [] => acc
  | (op, operand) :: rest => foldPan (Exp.panOp op [acc, operand]) rest

/-- `conv_shifts`. -/
def foldShift (acc : Exp α) : List (Shift × Exp α) → Exp α
  | [] => acc
  | (op, operand) :: rest => foldShift (Exp.shift op acc operand) rest

/-- A field accessor: `.0` selects positionally, `.name` by name. -/
inductive Accessor where
  | index (value : Nat)
  | field (name : FieldName)
  deriving DecidableEq, Repr

/-- `conv_Exp`'s `EFieldNT` fold, left-associative. -/
def foldAccessors (acc : Exp α) : List Accessor → Exp α
  | [] => acc
  | .index value :: rest => foldAccessors (Exp.rField value acc) rest
  | .field name :: rest => foldAccessors (Exp.nField name acc) rest

mutual

/-- `ExpNT`: boolean `||`. -/
def parseExp (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEBoolAnd ofInt fuel
      let rest ← parseBoolOrTail ofInt fuel
      match rest with
      | [] => pure first
      | _ => pure (.cmp .notEqual (.const (ofInt 0)) (.op .or (first :: rest)))

def parseBoolOrTail (ofInt : Int → α) : Nat → P (List (Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .boolOrT "||"
          parseEBoolAnd ofInt fuel) with
      | none => pure []
      | some next =>
          let rest ← parseBoolOrTail ofInt fuel
          pure (next :: rest)

/-- `EBoolAndNT`: boolean `&&`, comparing each operand against zero. -/
def parseEBoolAnd (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEEq ofInt fuel
      let rest ← parseBoolAndTail ofInt fuel
      match rest with
      | [] => pure first
      | _ =>
          pure (.op .and
            ((first :: rest).map (fun operand => .cmp .notEqual (.const (ofInt 0)) operand)))

def parseBoolAndTail (ofInt : Int → α) : Nat → P (List (Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .boolAndT "&&"
          parseEEq ofInt fuel) with
      | none => pure []
      | some next =>
          let rest ← parseBoolAndTail ofInt fuel
          pure (next :: rest)

/-- `EEqNT`: at most one `==` or `!=`. -/
def parseEEq (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let left ← parseECmp ofInt fuel
      match ← P.optional' (do
          let (op, swapped) ← operator eqOpOfToken "== or !="
          let right ← parseECmp ofInt fuel
          pure (op, swapped, right)) with
      | none => pure left
      | some (op, swapped, right) =>
          pure (if swapped then .cmp op right left else .cmp op left right)

/-- `ECmpNT`: at most one ordering comparison. -/
def parseECmp (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let left ← parseELoad ofInt fuel
      match ← P.optional' (do
          let (op, swapped) ← operator cmpOpOfToken "a comparison operator"
          let right ← parseELoad ofInt fuel
          pure (op, swapped, right)) with
      | none => pure left
      | some (op, swapped, right) =>
          pure (if swapped then .cmp op right left else .cmp op left right)

/-- `ELoadNT`: `lds <shape> <address>`. -/
def parseELoad (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        P.expectKw .ldsK "lds"
        let shape ← parseShape fuel
        let address ← parseELoadByte ofInt fuel
        pure (.load shape address))
      <|> parseELoadByte ofInt fuel

/-- `ELoadByteNT`: `ld8 <address>`. -/
def parseELoadByte (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        P.expectKw .ld8K "ld8"
        let address ← parseELoad32 ofInt fuel
        pure (.loadByte address))
      <|> parseELoad32 ofInt fuel

/-- `ELoad32NT`: `ld32 <address>`. -/
def parseELoad32 (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        P.expectKw .ld32K "ld32"
        let address ← parseEOr ofInt fuel
        pure (.load32 address))
      <|> parseEOr ofInt fuel

/-- `EOrNT`: bitwise `|`. -/
def parseEOr (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEXor ofInt fuel
      let rest ← parseOrTail ofInt fuel
      pure (foldBinary first rest)

def parseOrTail (ofInt : Int → α) : Nat → P (List (BinOp × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .orT "|"
          let next ← parseEXor ofInt fuel
          pure (BinOp.or, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseOrTail ofInt fuel
          pure (entry :: rest)

/-- `EXorNT`: bitwise `^`. -/
def parseEXor (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEAnd ofInt fuel
      let rest ← parseXorTail ofInt fuel
      pure (foldBinary first rest)

def parseXorTail (ofInt : Int → α) : Nat → P (List (BinOp × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .xorT "^"
          let next ← parseEAnd ofInt fuel
          pure (BinOp.xor, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseXorTail ofInt fuel
          pure (entry :: rest)

/-- `EAndNT`: bitwise `&`. -/
def parseEAnd (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEShift ofInt fuel
      let rest ← parseAndTail ofInt fuel
      pure (foldBinary first rest)

def parseAndTail (ofInt : Int → α) : Nat → P (List (BinOp × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .andT "&"
          let next ← parseEShift ofInt fuel
          pure (BinOp.and, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseAndTail ofInt fuel
          pure (entry :: rest)

/-- `EShiftNT`. -/
def parseEShift (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEAdd ofInt fuel
      let rest ← parseShiftTail ofInt fuel
      pure (foldShift first rest)

def parseShiftTail (ofInt : Int → α) : Nat → P (List (Shift × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          let op ← operator shiftOfToken "a shift operator"
          let next ← parseEAdd ofInt fuel
          pure (op, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseShiftTail ofInt fuel
          pure (entry :: rest)

/-- `EAddNT`. -/
def parseEAdd (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseEMul ofInt fuel
      let rest ← parseAddTail ofInt fuel
      pure (foldBinary first rest)

def parseAddTail (ofInt : Int → α) : Nat → P (List (BinOp × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          let op ← operator addOpOfToken "+ or -"
          let next ← parseEMul ofInt fuel
          pure (op, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseAddTail ofInt fuel
          pure (entry :: rest)

/-- `EMulNT`. -/
def parseEMul (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseENot ofInt fuel
      let rest ← parseMulTail ofInt fuel
      pure (foldPan first rest)

def parseMulTail (ofInt : Int → α) : Nat → P (List (PanOp × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .starT "*"
          let next ← parseENot ofInt fuel
          pure (PanOp.mul, next)) with
      | none => pure []
      | some entry =>
          let rest ← parseMulTail ofInt fuel
          pure (entry :: rest)

/-- `ENotNT`: `!e` is `e == 0`. -/
def parseENot (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let negated ← P.optional' (P.expect .notT "!")
      let operand ← parseEField ofInt fuel
      match negated with
      | none => pure operand
      | some _ => pure (.cmp .equal (.const (ofInt 0)) operand)

/-- `EFieldNT`: a chain of `.index` and `.name` accessors. -/
def parseEField (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let base ← parseEBase ofInt fuel
      let accessors ← parseAccessorTail fuel
      pure (foldAccessors base accessors)

def parseAccessorTail : Nat → P (List Accessor)
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .dotT "."
          (do let value ← P.natLit; pure (Accessor.index value))
          <|> (do let name ← P.ident; pure (Accessor.field name))) with
      | none => pure []
      | some accessor =>
          let rest ← parseAccessorTail fuel
          pure (accessor :: rest)

/-- `EBaseNT`, in `panPEG`'s order. Bare identifiers become `Global` here and
are reclassified by the localisation pass, exactly as upstream does. -/
def parseEBase (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        P.expect .lParT "("
        let inner ← parseExp ofInt fuel
        P.expect .rParT ")"
        pure inner)
      <|> (do P.expectKw .trueK "true"; pure (.const (ofInt 1)))
      <|> (do P.expectKw .falseK "false"; pure (.const (ofInt 0)))
      <|> parseRawStruct ofInt fuel
      <|> parseNmdStruct ofInt fuel
      <|> (do P.expectKw .baseK "@base"; pure .baseAddr)
      <|> (do P.expectKw .biwK "@biw"; pure .bytesInWord)
      <|> (do P.expectKw .topK "@top"; pure .topAddr)
      <|> (do let value ← P.intLit; pure (.const (ofInt value)))
      <|> (do let name ← P.ident; pure (.var .global name))

/-- `RawStructNT`: `<e, ...>`. -/
def parseRawStruct (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      P.expect .lessT "<"
      let fields ← parseArgList ofInt fuel
      P.expect .greaterT ">"
      pure (.rStruct fields)

/-- `NmdStructNT`: `name<field = e, ...>`. -/
def parseNmdStruct (ofInt : Int → α) : Nat → P (Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let name ← P.ident
      P.expect .lessT "<"
      let fields ← parseFieldList ofInt fuel
      P.expect .greaterT ">"
      pure (.nStruct name fields)

/-- `NmdFieldListNT`. -/
def parseFieldList (ofInt : Int → α) : Nat → P (List (FieldName × Exp α))
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseField ofInt fuel
      let rest ← parseFieldListTail ofInt fuel
      pure (first :: rest)

def parseFieldListTail (ofInt : Int → α) : Nat → P (List (FieldName × Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .commaT ","
          parseField ofInt fuel) with
      | none => pure []
      | some next =>
          let rest ← parseFieldListTail ofInt fuel
          pure (next :: rest)

/-- `NmdFieldNT`: `name = e`. -/
def parseField (ofInt : Int → α) : Nat → P (FieldName × Exp α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let name ← P.ident
      P.expect .assignT "="
      let value ← parseExp ofInt fuel
      pure (name, value)

/-- `ArgListNT`. -/
def parseArgList (ofInt : Int → α) : Nat → P (List (Exp α))
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let first ← parseExp ofInt fuel
      let rest ← parseArgListTail ofInt fuel
      pure (first :: rest)

def parseArgListTail (ofInt : Int → α) : Nat → P (List (Exp α))
  | 0 => pure []
  | fuel + 1 => do
      match ← P.optional' (do
          P.expect .commaT ","
          parseExp ofInt fuel) with
      | none => pure []
      | some next =>
          let rest ← parseArgListTail ofInt fuel
          pure (next :: rest)

end

end Flapjack.Parser
