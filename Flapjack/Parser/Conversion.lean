import Flapjack.Language
import Flapjack.Parser.Grammar

/-!
Parse tree to Flapjack AST.

A port of `panPtreeConversion`, one function per `conv_*` definition, reading
the trees `Flapjack/Parser/Grammar.lean` produces.

Every function returns `Option`, as upstream does: a shape that the grammar
cannot produce converts to `none` rather than being silently repaired.

`fuel` bounds the walk, matching the grammar's treatment. It is seeded from
the token count, which bounds tree depth, so it cannot run out on a tree the
grammar built; running out yields `none`, never a wrong AST.
-/

namespace Flapjack.Parser

open Flapjack

/-- `conv_int`. -/
def convInt (tree : ParseTree) : Option Int :=
  match tree.destTok with
  | some (.intT value) => some value
  | _ => none

/-- `conv_nat`. -/
def convNat (tree : ParseTree) : Option Nat :=
  match convInt tree with
  | some value => if 0 ≤ value then some value.toNat else none
  | none => none

/-- `conv_const`, with `i2w` supplied by the caller. -/
def convConst (ofInt : Int → α) (tree : ParseTree) : Option (Exp α) :=
  (convInt tree).map (fun value => .const (ofInt value))

/-- `conv_ident`. -/
def convIdent (tree : ParseTree) : Option String :=
  match tree.destTok with
  | some (.identT name) => some name
  | _ => none

/-- `conv_ffi_ident`. -/
def convFfiIdent (tree : ParseTree) : Option String :=
  match tree.destTok with
  | some (.foreignIdent name) => some name
  | _ => none

/-- `conv_var`: every bare identifier starts `Global`. -/
def convVar (tree : ParseTree) : Option (Exp α) :=
  (convIdent tree).map (Exp.var .global)

/-- `conv_binop`, accepting either an `AddOpsNT` node or a bare leaf. -/
def convBinop (tree : ParseTree) : Option BinOp :=
  match tree with
  | .nd .addOps [leaf] _ => convBinop leaf
  | _ =>
      if tree.tokcheck .plusT then some .add
      else if tree.tokcheck .minusT then some .sub
      else if tree.tokcheck .andT then some .and
      else if tree.tokcheck .orT then some .or
      else if tree.tokcheck .xorT then some .xor
      else none

/-- `conv_panop`. -/
def convPanop (tree : ParseTree) : Option PanOp :=
  match tree with
  | .nd .mulOps [leaf] _ => convPanop leaf
  | _ => if tree.tokcheck .starT then some .mul else none

/-- `conv_shift`. -/
def convShift (tree : ParseTree) : Option Shift :=
  match tree with
  | .nd .shiftOps [leaf] _ => convShift leaf
  | _ =>
      if tree.tokcheck .lslT then some .lsl
      else if tree.tokcheck .lsrT then some .lsr
      else if tree.tokcheck .asrT then some .asr
      else if tree.tokcheck .rorT then some .ror
      else none

/-- `conv_cmp`. The flag says the operands are swapped. -/
def convCmp (tree : ParseTree) : Option (Cmp × Bool) :=
  match tree with
  | .nd .cmpOps [leaf] _ => convCmp leaf
  | .nd .eqOps [leaf] _ => convCmp leaf
  | _ =>
      if tree.tokcheck .eqT then some (.equal, false)
      else if tree.tokcheck .neqT then some (.notEqual, false)
      else if tree.tokcheck .lessT then some (.less, false)
      else if tree.tokcheck .geqT then some (.notLess, false)
      else if tree.tokcheck .greaterT then some (.less, true)
      else if tree.tokcheck .leqT then some (.notLess, true)
      else if tree.tokcheck .lowerT then some (.lower, false)
      else if tree.tokcheck .higherT then some (.lower, true)
      else if tree.tokcheck .higheqT then some (.notLower, false)
      else if tree.tokcheck .loweqT then some (.notLower, true)
      else none

/-- `conv_default_shape`. -/
def convDefaultShape (tree : ParseTree) : Option Shape :=
  match tree.destTok with
  | some .defaultShT => some .one
  | _ => none

/-- `conv_Shape`. A literal `n` means `n` copies of `One`. -/
def convShape : Nat → ParseTree → Option Shape
  | 0, _ => none
  | fuel + 1, tree =>
      match convDefaultShape tree with
      | some shape => some shape
      | none =>
          match convInt tree with
          | some value =>
              if value < 1 then none
              else if value == 1 then some .one
              else some (.comb (List.replicate value.toNat .one))
          | none =>
              match convIdent tree with
              | some name => some (.named name)
              | none =>
                  match tree.argsNT .shapeComb with
                  | some children => (convShapeList fuel children).map Shape.comb
                  | none => none
where
  convShapeList : Nat → List ParseTree → Option (List Shape)
    | _, [] => some []
    | fuel, tree :: trees => do
        let shape ← convShape fuel tree
        let shapes ← convShapeList fuel trees
        pure (shape :: shapes)

/-- `conv_params`: a flat shape/name sequence, as `ShapedIdentNT` produces. -/
def convParams (fuel : Nat) : List ParseTree → Option (List (VarName × Shape))
  | [] => some []
  | shapeTree :: nameTree :: rest => do
      let shape ← convShape fuel shapeTree
      let name ← convIdent nameTree
      let params ← convParams fuel rest
      pure ((name, shape) :: params)
  | _ => none

/-- `isSubOp`: subtraction is binary, so it never flattens. -/
def isSubOp : Exp α → Bool
  | .op .sub [_, _] => true
  | _ => false

/-- `conv_inline`. -/
def convInline (tree : ParseTree) : Option Bool :=
  match tree.destTok with
  | some (.keywordT .inlineK) => some true
  | some .noinlineT => some false
  | _ => none

/-- `conv_export`. -/
def convExport (tree : ParseTree) : Option Bool :=
  match tree.destTok with
  | some (.keywordT .exportK) => some true
  | some .staticT => some false
  | _ => none

/-- `dest_annot_tok`. -/
def destAnnotTok (tree : ParseTree) : Option String :=
  match tree.destTok with
  | some (.annotCommentT text) => some text
  | _ => none

mutual

/-- `conv_Exp`. -/
def convExp (ofInt : Int → α) : Nat → ParseTree → Option (Exp α)
  | 0, _ => none
  | fuel + 1, .nd nonterminal children _ =>
      match nonterminal, children with
      | .eField, [] => none
      | .eField, base :: accessors =>
          match convExp ofInt fuel base with
          | none => none
          | some value => convAccessors ofInt fuel accessors value
      | .rawStruct, [args] => (convArgList ofInt fuel args).map Exp.rStruct
      | .nmdStruct, [nameTree, fieldsTree] => do
          let name ← convIdent nameTree
          let fields ← convFieldList ofInt fuel fieldsTree
          pure (.nStruct name fields)
      | .eNot, [operand] => convExp ofInt fuel operand
      | .eNot, [_, operand] =>
          (convExp ofInt fuel operand).map (Exp.cmp .equal (.const (ofInt 0)))
      | .eLoadByte, [address] => (convExp ofInt fuel address).map Exp.loadByte
      | .eLoad32, [address] => (convExp ofInt fuel address).map Exp.load32
      | .eLoad, [shapeTree, address] => do
          let shape ← convShape fuel shapeTree
          let value ← convExp ofInt fuel address
          pure (.load shape value)
      | .eCmp, [operand] => convExp ofInt fuel operand
      | .eCmp, [left, opTree, right] => convComparison ofInt fuel left opTree right
      | .eEq, [operand] => convExp ofInt fuel operand
      | .eEq, [left, opTree, right] => convComparison ofInt fuel left opTree right
      | .exp, [operand] => convExp ofInt fuel operand
      | .exp, operands => do
          let values ← convExpList ofInt fuel operands
          pure (.cmp .notEqual (.const (ofInt 0)) (.op .or values))
      | .eBoolAnd, [operand] => convExp ofInt fuel operand
      | .eBoolAnd, operands => do
          let values ← convExpList ofInt fuel operands
          pure (.op .and
            (values.map (fun value => .cmp .notEqual (.const (ofInt 0)) value)))
      | .eShift, first :: rest =>
          match convExp ofInt fuel first with
          | none => none
          | some value => convShifts ofInt fuel rest value
      | .eOr, first :: rest
      | .eXor, first :: rest
      | .eAnd, first :: rest
      | .eAdd, first :: rest =>
          match convExp ofInt fuel first with
          | none => none
          | some value => convBinaryExps ofInt fuel rest value
      | .eMul, first :: rest =>
          match convExp ofInt fuel first with
          | none => none
          | some value => convPanops ofInt fuel rest value
      | _, _ => none
  | _ + 1, tree =>
      if tree.tokcheck (.keywordT .baseK) then some .baseAddr
      else if tree.tokcheck (.keywordT .topK) then some .topAddr
      else if tree.tokcheck (.keywordT .biwK) then some .bytesInWord
      else if tree.tokcheck (.keywordT .trueK) then some (.const (ofInt 1))
      else if tree.tokcheck (.keywordT .falseK) then some (.const (ofInt 0))
      else match convConst ofInt tree with
        | some value => some value
        | none => convVar tree

/-- The shared body of `ECmpNT` and `EEqNT`, which swap operands for the
comparisons Pancake states the other way round. -/
def convComparison (ofInt : Int → α) (fuel : Nat)
    (leftTree opTree rightTree : ParseTree) : Option (Exp α) := do
  let left ← convExp ofInt fuel leftTree
  let (op, swapped) ← convCmp opTree
  let right ← convExp ofInt fuel rightTree
  pure (if swapped then .cmp op right left else .cmp op left right)

def convExpList (ofInt : Int → α) : Nat → List ParseTree → Option (List (Exp α))
  | _, [] => some []
  | fuel, tree :: trees => do
      let value ← convExp ofInt fuel tree
      let values ← convExpList ofInt fuel trees
      pure (value :: values)

/-- `conv_ArgList`: a `NotT` leaf stands for an absent argument list. -/
def convArgList (ofInt : Int → α) : Nat → ParseTree → Option (List (Exp α))
  | 0, _ => none
  | fuel + 1, tree =>
      if tree.tokcheck .notT then some []
      else
        match tree.argsNT .argList with
        | some (first :: rest) => convExpList ofInt fuel (first :: rest)
        | _ => none

/-- `conv_FieldList`. -/
def convFieldList (ofInt : Int → α) : Nat → ParseTree → Option (List (FieldName × Exp α))
  | 0, _ => none
  | fuel + 1, tree =>
      match tree.argsNT .nmdFieldList with
      | some (first :: rest) => convFields ofInt fuel (first :: rest)
      | _ => none

def convFields (ofInt : Int → α) : Nat → List ParseTree → Option (List (FieldName × Exp α))
  | _, [] => some []
  | fuel, tree :: trees => do
      let field ← convField ofInt fuel tree
      let fields ← convFields ofInt fuel trees
      pure (field :: fields)

/-- `conv_Field`. -/
def convField (ofInt : Int → α) : Nat → ParseTree → Option (FieldName × Exp α)
  | 0, _ => none
  | fuel + 1, tree =>
      match tree.argsNT .nmdField with
      | some [nameTree, valueTree] => do
          let name ← convIdent nameTree
          let value ← convExp ofInt fuel valueTree
          pure (name, value)
      | _ => none

/-- `conv_Exp`'s `EFieldNT` fold. -/
def convAccessors (ofInt : Int → α) : Nat → List ParseTree → Exp α → Option (Exp α)
  | _, [], acc => some acc
  | fuel, tree :: trees, acc =>
      match convNat tree with
      | some index => convAccessors ofInt fuel trees (.rField index acc)
      | none =>
          match convIdent tree with
          | some name => convAccessors ofInt fuel trees (.nField name acc)
          | none => none

/-- `conv_binaryExps`: a run of one operator flattens, except subtraction. -/
def convBinaryExps (ofInt : Int → α) : Nat → List ParseTree → Exp α → Option (Exp α)
  | _, [], acc => some acc
  | fuel, opTree :: operandTree :: rest, acc => do
      let op ← convBinop opTree
      let operand ← convExp ofInt fuel operandTree
      let combined :=
        match acc with
        | .op bop args =>
            if bop != op || isSubOp acc then Exp.op op [acc, operand]
            else Exp.op bop (args ++ [operand])
        | _ => Exp.op op [acc, operand]
      convBinaryExps ofInt fuel rest combined
  | _, _, _ => none

/-- `conv_panops`. -/
def convPanops (ofInt : Int → α) : Nat → List ParseTree → Exp α → Option (Exp α)
  | _, [], acc => some acc
  | fuel, opTree :: operandTree :: rest, acc => do
      let op ← convPanop opTree
      let operand ← convExp ofInt fuel operandTree
      convPanops ofInt fuel rest (.panOp op [acc, operand])
  | _, _, _ => none

/-- `conv_shifts`. -/
def convShifts (ofInt : Int → α) : Nat → List ParseTree → Exp α → Option (Exp α)
  | _, [], acc => some acc
  | fuel, opTree :: operandTree :: rest, acc => do
      let op ← convShift opTree
      let operand ← convExp ofInt fuel operandTree
      convShifts ofInt fuel rest (.shift op acc operand)
  | _, _, _ => none

end

/-- `panLang$shape_val`: the zero value of a shape. -/
def shapeVal (ofInt : Int → α) : Shape → Exp α
  | .one => .const (ofInt 0)
  | .named _ => .const (ofInt 0)
  | .comb shapes => .rStruct (shapeVals ofInt shapes)
where
  shapeVals (ofInt : Int → α) : List Shape → List (Exp α)
    | [] => []
    | shape :: shapes => shapeVal ofInt shape :: shapeVals ofInt shapes

/-- `is_add_with_carry`. -/
def addWithCarryName : String := "__add_with_carry__"

/-- `add_locs_annot`, applied only when asked for. -/
def addLocsAnnot (locations : Bool) (tree : ParseTree) (program : Prog α) : Prog α :=
  if locations then .seq (.annot locationTag (locsComment tree.locs)) program else program

/-- `conv_NonRecStmt`: the statements that carry no nested program. -/
def convNonRecStmt (ofInt : Int → α) (fuel : Nat) (tree : ParseTree) : Option (Prog α) :=
  match tree with
  | .nd nonterminal children _ =>
      match nonterminal, children with
      | .assign, [nameTree, valueTree] => do
          let name ← convIdent nameTree
          let value ← convExp ofInt fuel valueTree
          pure (.assign .global name value)
      | .store, [addressTree, valueTree] => do
          let address ← convExp ofInt fuel addressTree
          let value ← convExp ofInt fuel valueTree
          pure (.store address value)
      | .storeByte, [addressTree, valueTree] => do
          let address ← convExp ofInt fuel addressTree
          let value ← convExp ofInt fuel valueTree
          pure (.storeByte address value)
      | .store32, [addressTree, valueTree] => do
          let address ← convExp ofInt fuel addressTree
          let value ← convExp ofInt fuel valueTree
          pure (.store32 address value)
      | .sharedLoad, [nameTree, addressTree] => convSharedLoad ofInt fuel .opW nameTree addressTree
      | .sharedLoadByte, [nameTree, addressTree] =>
          convSharedLoad ofInt fuel .op8 nameTree addressTree
      | .sharedLoad16, [nameTree, addressTree] =>
          convSharedLoad ofInt fuel .op16 nameTree addressTree
      | .sharedLoad32, [nameTree, addressTree] =>
          convSharedLoad ofInt fuel .op32 nameTree addressTree
      | .sharedStore, [addressTree, valueTree] =>
          convSharedStore ofInt fuel .opW addressTree valueTree
      | .sharedStoreByte, [addressTree, valueTree] =>
          convSharedStore ofInt fuel .op8 addressTree valueTree
      | .sharedStore16, [addressTree, valueTree] =>
          convSharedStore ofInt fuel .op16 addressTree valueTree
      | .sharedStore32, [addressTree, valueTree] =>
          convSharedStore ofInt fuel .op32 addressTree valueTree
      | .extCall, [nameTree, configurationTree, configurationLengthTree,
                   arrayTree, arrayLengthTree] => do
          let name ← convFfiIdent nameTree
          let configuration ← convExp ofInt fuel configurationTree
          let configurationLength ← convExp ofInt fuel configurationLengthTree
          let array ← convExp ofInt fuel arrayTree
          let arrayLength ← convExp ofInt fuel arrayLengthTree
          pure (.extCall name configuration configurationLength array arrayLength)
      | .throwNT, [exceptionTree, valueTree] => do
          let exception ← convIdent exceptionTree
          let value ← convExp ofInt fuel valueTree
          pure (.raise exception value)
      | .returnNT, [valueTree] => (convExp ofInt fuel valueTree).map Prog.return
      | _, _ => none
  | leaf =>
      if leaf.tokcheck (.keywordT .skipK) then some .skip
      else if leaf.tokcheck (.keywordT .brK) then some .break
      else if leaf.tokcheck (.keywordT .contK) then some .continue
      else if leaf.tokcheck (.keywordT .ticK) then some .tick
      else (destAnnotTok leaf).map (Prog.annot "@")
where
  convSharedLoad (ofInt : Int → α) (fuel : Nat) (size : OpSize)
      (nameTree addressTree : ParseTree) : Option (Prog α) := do
    let name ← convIdent nameTree
    let address ← convExp ofInt fuel addressTree
    pure (.shMemLoad size .global name address)
  convSharedStore (ofInt : Int → α) (fuel : Nat) (size : OpSize)
      (addressTree valueTree : ParseTree) : Option (Prog α) := do
    let address ← convExp ofInt fuel addressTree
    let value ← convExp ofInt fuel valueTree
    pure (.shMemStore size address value)

/-- `conv_Dec` and `conv_GlobalDec`: the same shape, different nonterminal. -/
def convDecForm (ofInt : Int → α) (fuel : Nat) (nonterminal : Nonterminal)
    (tree : ParseTree) : Option (Shape × VarName × Exp α) :=
  match tree.argsNT nonterminal with
  | some [shapeTree, nameTree, valueTree] => do
      let shape ← convShape fuel shapeTree
      let name ← convIdent nameTree
      let value ← convExp ofInt fuel valueTree
      pure (shape, name, value)
  | _ => none

/-- `conv_ExnDec`. -/
def convExnDec (fuel : Nat) (tree : ParseTree) : Option (ExceptionId × Shape) :=
  match tree.argsNT .exnDec with
  | some [exceptionTree, shapeTree] => do
      let exception ← convIdent exceptionTree
      let shape ← convShape fuel shapeTree
      pure (exception, shape)
  | _ => none

/-- `conv_DecCall`. -/
def convDecCall (ofInt : Int → α) (fuel : Nat) (tree : ParseTree) :
    Option (Shape × VarName × FunName × List (Exp α)) :=
  match tree.argsNT .decCall with
  | some (shapeTree :: nameTree :: functionTree :: rest) => do
      let shape ← convShape fuel shapeTree
      let name ← convIdent nameTree
      let function ← convIdent functionTree
      let args ← match rest with
        | [] => some []
        | argsTree :: _ => convArgList ofInt fuel argsTree
      pure (shape, name, function, args)
  | _ => none

/--
`conv_Ret`. The outer `Option` says whether control returns to this function
at all, the inner whether the result is bound to a variable.
-/
def convRet (tree : ParseTree) : Option (Option (Option (VarKind × VarName))) :=
  if tree.tokcheck (.keywordT .retK) then some none
  else if tree.tokcheck .notT then some (some none)
  else
    match tree.argsNT .ret with
    | some [nameTree] => do
        let name ← convIdent nameTree
        pure (some (some (.global, name)))
    | _ => none

/-- `conv_FieldNameList`. -/
def convFieldNameList (fuel : Nat) (tree : ParseTree) : Option (List (FieldName × Shape)) :=
  match tree.argsNT .fieldNameList with
  | some children => convParams fuel children
  | none => none

/-- `conv_StructName`. -/
def convStructName (fuel : Nat) (tree : ParseTree) :
    Option (StructName × List (FieldName × Shape)) :=
  match tree.argsNT .structName with
  | some [nameTree, fieldsTree] => do
      let name ← convIdent nameTree
      let fields ← convFieldNameList fuel fieldsTree
      pure (name, fields)
  | _ => none

mutual

/-- `conv_Prog`. -/
def convProg (ofInt : Int → α) (locations : Bool) : Nat → ParseTree → Option (Prog α)
  | 0, _ => none
  | fuel + 1, tree =>
      match tree with
      | .nd nonterminal children _ =>
          match nonterminal, children with
          | .dec, [declarationTree, bodyTree] => do
              let (shape, name, value) ← convDecForm ofInt fuel .dec declarationTree
              let body ← convProg ofInt locations fuel bodyTree
              pure (addLocsAnnot locations tree (.dec name shape value body))
          | .ifNT, [conditionTree, thenTree, elseTree] => do
              let condition ← convExp ofInt fuel conditionTree
              let thenBranch ← convProg ofInt locations fuel thenTree
              let elseBranch ← convProg ofInt locations fuel elseTree
              pure (addLocsAnnot locations tree (.ite condition thenBranch elseBranch))
          | .whileNT, [conditionTree, bodyTree] => do
              let condition ← convExp ofInt fuel conditionTree
              let body ← convProg ofInt locations fuel bodyTree
              pure (addLocsAnnot locations tree (.while condition body))
          | .decCall, [declarationTree, bodyTree] => do
              let (shape, name, function, args) ← convDecCall ofInt fuel declarationTree
              let body ← convProg ofInt locations fuel bodyTree
              if function == addWithCarryName then
                pure (addLocsAnnot locations tree
                  (.dec name shape (shapeVal ofInt shape)
                    (.seq (.primitive name .addCarry args) body)))
              else
                pure (addLocsAnnot locations tree (.decCall name shape function args body))
          | .handle, [retTree, functionTree, argsTree, exceptionTree, boundTree, bodyTree] => do
              let ret ← convRet retTree
              let target ← ret
              let function ← convIdent functionTree
              let args ← convArgList ofInt fuel argsTree
              let exception ← convIdent exceptionTree
              let bound ← convIdent boundTree
              let handler ← convProg ofInt locations fuel bodyTree
              pure (addLocsAnnot locations tree
                (.call (some (target, some (exception, bound, handler))) function args))
          | .call, [retTree, functionTree, argsTree] => do
              let ret ← convRet retTree
              let function ← convIdent functionTree
              let args ← convArgList ofInt fuel argsTree
              if function == addWithCarryName then
                match ret with
                | some (some (_, name)) =>
                    pure (addLocsAnnot locations tree (.primitive name .addCarry args))
                | _ => none
              else
                pure (addLocsAnnot locations tree
                  (.call (ret.map (fun target => (target, none))) function args))
          | .prog, first :: rest => convProgSeq ofInt locations fuel (first :: rest)
          | _, _ =>
              (convNonRecStmt ofInt fuel tree).map (addLocsAnnot locations tree)
      | leaf => (convNonRecStmt ofInt fuel leaf).map (addLocsAnnot locations leaf)

/-- `ProgNT`'s fold: every child in sequence, nested to the right. -/
def convProgSeq (ofInt : Int → α) (locations : Bool) :
    Nat → List ParseTree → Option (Prog α)
  | _, [] => none
  | fuel, [tree] => convProg ofInt locations fuel tree
  | fuel, tree :: trees => do
      let first ← convProg ofInt locations fuel tree
      let rest ← convProgSeq ofInt locations fuel trees
      pure (.seq first rest)

end

/-- `conv_TopDec`. -/
def convTopDec (ofInt : Int → α) (locations : Bool) (fuel : Nat) (tree : ParseTree) :
    Option (Decl α) :=
  match tree.argsNT .funNT with
  | some [inlineTree, exportTree, shapeTree, nameTree, paramsTree, bodyTree] => do
      let params ← match paramsTree.argsNT .paramList with
        | some children => convParams fuel children
        | none => none
      let body ← convProg ofInt locations fuel bodyTree
      let name ← convIdent nameTree
      let inline ← convInline inlineTree
      let exported ← convExport exportTree
      let returnShape ← convShape fuel shapeTree
      pure (.function { name := name, inline := inline, exported := exported,
                        params := params, body := body, returnShape := returnShape })
  | _ =>
      match convDecForm ofInt fuel .globalDec tree with
      | some (shape, name, value) => some (.decl shape name value)
      | none =>
          match convStructName fuel tree with
          | some (name, fields) => some (.name name fields)
          | none =>
              match convExnDec fuel tree with
              | some (exception, shape) => some (.exnDecl exception shape)
              | none => none

/-- `conv_TopDecList`: annotation comments are dropped rather than converted. -/
def convTopDecList (ofInt : Int → α) (locations : Bool) :
    Nat → ParseTree → Option (List (Decl α))
  | 0, _ => none
  | fuel + 1, tree =>
      match tree.argsNT .topDecList with
      | some [] => some []
      | some [itemTree, restTree] =>
          match destAnnotTok itemTree with
          | some _ => convTopDecList ofInt locations fuel restTree
          | none => do
              let declaration ← convTopDec ofInt locations fuel itemTree
              let rest ← convTopDecList ofInt locations fuel restTree
              pure (declaration :: rest)
      | _ => none

end Flapjack.Parser
