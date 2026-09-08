import Flapjack.Parser.Expressions

/-!
Statement and declaration grammar.

Mirrors `panPEG`'s `ProgNT`, `StmtNT`, `BlockNT` and the top-level
`TopDecListNT`, building what `conv_Prog`, `conv_NonRecStmt` and
`conv_TopDec` would build.

`parseProg` returns `Option (Prog α)` because upstream distinguishes two
cases that matter: `ProgNT` matching a bare `}` contributes no node at all,
so the statement before it is *not* followed by a `Skip`, whereas
`try_ProgNT` turns the same `}` into an explicit `Skip`. `none` here is the
first case and `parseTryProg` supplies the `Skip` for the second.
-/

namespace Flapjack.Parser

open Flapjack

/-- `is_add_with_carry`: this name is a primitive rather than a call. -/
def addWithCarryName : String := "__add_with_carry__"

/-- `DecNT` and `GlobalDecNT` share their syntax; only their context differs. -/
def parseDecBody (ofInt : Int → α) (fuel : Nat) : P (VarName × Shape × Exp α) := do
  P.expectKw .varK "var"
  let (name, shape) ← parseShapedIdent fuel
  P.expect .assignT "="
  let value ← parseExp ofInt fuel
  P.expect .semiT ";"
  pure (name, shape, value)

/-- `DecCallNT`: `var <shape> x = f(args);`. -/
def parseDecCallBody (ofInt : Int → α) (fuel : Nat) :
    P (VarName × Shape × FunName × List (Exp α)) := do
  P.expectKw .varK "var"
  let (name, shape) ← parseShapedIdent fuel
  P.expect .assignT "="
  let function ← P.ident
  P.expect .lParT "("
  let args ← P.optional' (parseArgList ofInt fuel)
  P.expect .rParT ")"
  P.expect .semiT ";"
  pure (name, shape, function, args.getD [])

/-- `ExnDecNT`: `exception e : <shape>;`. -/
def parseExnDec (fuel : Nat) : P (ExceptionId × Shape) := do
  P.expectKw .exceptionK "exception"
  let exception ← P.ident
  P.expect .colonT ":"
  let shape ← parseShape fuel
  P.expect .semiT ";"
  pure (exception, shape)

/-- `StructNameNT`: `struct name { <shape> field, ... }`. -/
def parseStructName (fuel : Nat) : P (StructName × List (FieldName × Shape)) := do
  P.expectKw .namedK "struct"
  let name ← P.ident
  P.expect .lCurT "{"
  let fields ← parseParamList fuel
  P.expect .rCurT "}"
  pure (name, fields)

/--
`conv_Ret`. The two layers of `Option` are upstream's: the outer one says
whether control returns to this function at all, the inner one whether the
result is bound to a variable.
-/
def parseRetPrefix : P (Option (Option (VarKind × VarName))) :=
  (do P.expectKw .retK "ret"; pure none)
  <|> (do
    let name ← P.ident
    P.expect .assignT "="
    pure (some (some (.global, name))))
  <|> pure (some none)

/-- `RetNT` alone, as used by `HandleNT`, which has no tail-call form. -/
def parseHandleRet : P (Option (VarKind × VarName)) :=
  (do
    let name ← P.ident
    P.expect .assignT "="
    pure (some (.global, name)))
  <|> pure none

/-- `conv_Prog`'s `DecCallNT` case: `__add_with_carry__` becomes a primitive
applied inside a declaration of the same variable. -/
def buildDecCall (ofInt : Int → α) (name : VarName) (shape : Shape)
    (function : FunName) (args : List (Exp α)) (body : Prog α) : Prog α :=
  if function == addWithCarryName then
    .dec name shape (shapeVal ofInt shape) (.seq (.primitive name .addCarry args) body)
  else
    .decCall name shape function args body

/-- `conv_Prog`'s `CallNT` case, including the `__add_with_carry__` form. -/
def buildCall (ret : Option (Option (VarKind × VarName))) (function : FunName)
    (args : List (Exp α)) : P (Prog α) :=
  if function == addWithCarryName then
    match ret with
    | some (some (_, name)) => pure (.primitive name .addCarry args)
    | _ => P.fail s!"{addWithCarryName} needs a variable to assign its result to"
  else
    pure (.call (ret.map (fun target => (target, none))) function args)

/-- The shared-memory load sizes, mirroring `SharedLoad*NT`. -/
def sharedLoadForms : List (Keyword × String × OpSize) :=
  [(.ld8K, "ld8", .op8), (.ld16K, "ld16", .op16), (.ld32K, "ld32", .op32), (.ldwK, "ldw", .opW)]

/-- The shared-memory store sizes, mirroring `SharedStore*NT`. -/
def sharedStoreForms : List (Keyword × String × OpSize) :=
  [(.st8K, "st8", .op8), (.st16K, "st16", .op16), (.st32K, "st32", .op32), (.stwK, "stw", .opW)]

/--
`add_locs_annot`: wrap a statement in its source range, as `conv_Prog` does
for every statement it builds. Off unless `PState.locations` is set, since
upstream emits these unconditionally and they roughly double the tree.
-/
def withLocs (p : P (Prog α)) : P (Prog α) := fun s =>
  if s.locations then
    match P.spanned p s with
    | (some (program, locs), s') =>
        (some (.seq (.annot locationTag (locsComment locs)) program), s')
    | (none, s') => (none, s')
  else
    p s

/-- Sequence a statement with whatever followed it, where `none` means the
program ended at a `}` and so contributes no trailing `Skip`. -/
def appendProg (statement : Prog α) : Option (Prog α) → Prog α
  | none => statement
  | some rest => .seq statement rest

mutual

/-- `ProgNT`: a sequence of statements terminated by `}`. -/
def parseProg (ofInt : Int → α) : Nat → P (Option (Prog α))
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do
        let block ← withLocs (parseBlock ofInt fuel)
        let rest ← parseProg ofInt fuel
        pure (some (appendProg block rest)))
      <|> (do
        let declaration ← withLocs (do
          let (name, shape, function, args) ← parseDecCallBody ofInt fuel
          let body ← parseTryProg ofInt fuel
          pure (buildDecCall ofInt name shape function args body))
        pure (some declaration))
      <|> (do
        let declaration ← withLocs (do
          let (name, shape, value) ← parseDecBody ofInt fuel
          let body ← parseTryProg ofInt fuel
          pure (.dec name shape value body))
        pure (some declaration))
      <|> (do
        let annotation ← withLocs (do
          let text ← P.annotLit
          pure (.annot "@" text))
        let rest ← parseProg ofInt fuel
        pure (some (appendProg annotation rest)))
      <|> (do
        let statement ← parseStmt ofInt fuel
        P.expect .semiT ";"
        let rest ← parseProg ofInt fuel
        pure (some (appendProg statement rest)))
      <|> (do
        P.expect .rCurT "}"
        pure none)

/-- `try_ProgNT`: an empty body becomes `Skip`. -/
def parseTryProg (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      match ← parseProg ofInt fuel with
      | none => pure .skip
      | some body => pure body

/-- `BlockNT`: the statements that carry a nested program and take no `;`. -/
def parseBlock (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      parseHandle ofInt fuel <|> parseIf ofInt fuel <|> parseWhile ofInt fuel

/-- `HandleNT`: `try [x =] f(args) catch e => v { ... }`. -/
def parseHandle (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      P.expectKw .tryK "try"
      let ret ← parseHandleRet
      let function ← P.ident
      P.expect .lParT "("
      let args ← P.optional' (parseArgList ofInt fuel)
      P.expect .rParT ")"
      P.expectKw .catchK "catch"
      let exception ← P.ident
      P.expect .arrowT "=>"
      let bound ← P.ident
      P.expect .lCurT "{"
      let handler ← parseTryProg ofInt fuel
      pure (.call (some (ret, some (exception, bound, handler))) function (args.getD []))

/-- `IfNT`. A missing `else` becomes `Skip`, as `try_default` does upstream. -/
def parseIf (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      P.expectKw .ifK "if"
      let condition ← parseExp ofInt fuel
      P.expect .lCurT "{"
      let thenBranch ← parseTryProg ofInt fuel
      let elseBranch ← P.optional' (do
        P.expectKw .elseK "else"
        P.expect .lCurT "{"
        parseTryProg ofInt fuel)
      pure (.ite condition thenBranch (elseBranch.getD .skip))

/-- `WhileNT`. -/
def parseWhile (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      P.expectKw .whileK "while"
      let condition ← parseExp ofInt fuel
      P.expect .lCurT "{"
      let body ← parseTryProg ofInt fuel
      pure (.while condition body)

/--
`StmtNT`, in `panPEG`'s order.

The `{ ... }` form is not location-annotated: `conv_Prog` reaches it as a
`ProgNT` node, which it folds into a `Seq` without calling `add_locs_annot`.
Every other form arrives as a leaf or a `conv_NonRecStmt` node and is
annotated.
-/
def parseStmt (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      withLocs (parseSimpleStmt ofInt fuel)
      <|> (do
        P.expect .lCurT "{"
        parseTryProg ofInt fuel)

/-- Everything in `StmtNT` except the `{ ... }` block form. -/
def parseSimpleStmt (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 =>
      (do P.expectKw .skipK "skip"; pure .skip)
      <|> parseCall ofInt fuel
      <|> (do
        let name ← P.ident
        P.expect .assignT "="
        let value ← parseExp ofInt fuel
        pure (.assign .global name value))
      <|> parseStore ofInt .stK "st" (fun address value => .store address value) fuel
      <|> parseStore ofInt .st8K "st8" (fun address value => .storeByte address value) fuel
      <|> parseStore ofInt .st32K "st32" (fun address value => .store32 address value) fuel
      <|> parseSharedLoads ofInt sharedLoadForms fuel
      <|> parseSharedStores ofInt sharedStoreForms fuel
      <|> (do P.expectKw .brK "break"; pure .break)
      <|> (do P.expectKw .contK "continue"; pure .continue)
      <|> parseExtCall ofInt fuel
      <|> (do
        P.expectKw .throwK "throw"
        let exception ← P.ident
        let value ← parseExp ofInt fuel
        pure (.raise exception value))
      <|> (do
        P.expectKw .retK "return"
        let value ← parseExp ofInt fuel
        pure (.return value))
      <|> (do P.expectKw .ticK "tick"; pure .tick)

/-- `StoreNT`, `StoreByteNT` and `Store32NT`. -/
def parseStore (ofInt : Int → α) (keyword : Keyword) (described : String)
    (build : Exp α → Exp α → Prog α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      P.expectKw keyword described
      let address ← parseExp ofInt fuel
      P.expect .commaT ","
      let value ← parseExp ofInt fuel
      pure (build address value)

/-- `SharedLoad*NT`: `!ldw x, addr` and its sized variants. -/
def parseSharedLoads (ofInt : Int → α) : List (Keyword × String × OpSize) → Nat → P (Prog α)
  | [], _ => P.fail "Expected a shared-memory load"
  | (keyword, described, size) :: forms, fuel =>
      match fuel with
      | 0 => P.fail fuelExhausted
      | fuel + 1 =>
          (do
            P.expect .notT "!"
            P.expectKw keyword described
            let name ← P.ident
            P.expect .commaT ","
            let address ← parseExp ofInt fuel
            pure (.shMemLoad size .global name address))
          <|> parseSharedLoads ofInt forms (fuel + 1)

/-- `SharedStore*NT`: `!stw addr, val` and its sized variants. -/
def parseSharedStores (ofInt : Int → α) : List (Keyword × String × OpSize) → Nat → P (Prog α)
  | [], _ => P.fail "Expected a shared-memory store"
  | (keyword, described, size) :: forms, fuel =>
      match fuel with
      | 0 => P.fail fuelExhausted
      | fuel + 1 =>
          (do
            P.expect .notT "!"
            P.expectKw keyword described
            let address ← parseExp ofInt fuel
            P.expect .commaT ","
            let value ← parseExp ofInt fuel
            pure (.shMemStore size address value))
          <|> parseSharedStores ofInt forms (fuel + 1)

/-- `ExtCallNT`: `@name(conf, confLen, array, arrayLen)`. -/
def parseExtCall (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let function ← P.ffiIdent
      P.expect .lParT "("
      let configuration ← parseExp ofInt fuel
      P.expect .commaT ","
      let configurationLength ← parseExp ofInt fuel
      P.expect .commaT ","
      let array ← parseExp ofInt fuel
      P.expect .commaT ","
      let arrayLength ← parseExp ofInt fuel
      P.expect .rParT ")"
      pure (.extCall function configuration configurationLength array arrayLength)

/-- `CallNT`: `[ret | x =] f(args)`. -/
def parseCall (ofInt : Int → α) : Nat → P (Prog α)
  | 0 => P.fail fuelExhausted
  | fuel + 1 => do
      let ret ← parseRetPrefix
      let function ← P.ident
      P.expect .lParT "("
      let args ← P.optional' (parseArgList ofInt fuel)
      P.expect .rParT ")"
      buildCall ret function (args.getD [])

end

end Flapjack.Parser
