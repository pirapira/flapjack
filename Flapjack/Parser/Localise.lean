import Flapjack.Language

/-!
The localisation pass.

The grammar cannot tell a local from a global: both are just an identifier,
so `conv_Exp` marks every variable `Global` and this pass reclassifies the
ones that turn out to be bound. A name is local inside the scope of the
`var` that introduced it, a `DecCall` that binds it, a handler's exception
variable, or a function parameter. Ports `localise_exp`, `localise_prog` and
`localise_topdecs`.

Two divergences from upstream, both of which look like constructors added
after the pass was written rather than deliberate choices:

* `localise_exp` has no `Load32` case, so `ld32 x` leaves `x` marked
  `Global` even where `x` is local. Handled here.
* `localise_prog` has no `Store32` case, so neither operand of `st32` is
  localised. Handled here.

`collect_globals` is not ported: upstream defines it but `localise_topdecs`
starts from an empty scope and never calls it.
-/

namespace Flapjack.Parser

open Flapjack

/-- A variable is local exactly when it is in scope. -/
def localiseKind (scope : List VarName) (kind : VarKind) (name : VarName) : VarKind :=
  if scope.contains name then .local else kind

def localiseTarget (scope : List VarName) :
    Option (VarKind × VarName) → Option (VarKind × VarName)
  | none => none
  | some (kind, name) => some (localiseKind scope kind name, name)

/-- `localise_exp`. -/
def localiseExp (scope : List VarName) : Exp α → Exp α
  | .const value => .const value
  | .var kind name => .var (localiseKind scope kind name) name
  | .rStruct fields => .rStruct (localiseExps scope fields)
  | .rField index value => .rField index (localiseExp scope value)
  | .nStruct name fields => .nStruct name (localiseFields scope fields)
  | .nField name value => .nField name (localiseExp scope value)
  | .load shape address => .load shape (localiseExp scope address)
  | .load32 address => .load32 (localiseExp scope address)
  | .loadByte address => .loadByte (localiseExp scope address)
  | .op operator args => .op operator (localiseExps scope args)
  | .panOp operator args => .panOp operator (localiseExps scope args)
  | .cmp operator left right => .cmp operator (localiseExp scope left) (localiseExp scope right)
  | .shift operator left right =>
      .shift operator (localiseExp scope left) (localiseExp scope right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
  | .bytesInWord => .bytesInWord

termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  localiseExps (scope : List VarName) : List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        localiseExp scope expression :: localiseExps scope expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  localiseFields (scope : List VarName) :
      List (FieldName × Exp α) → List (FieldName × Exp α)
    | [] => []
    | (name, expression) :: fields =>
        (name, localiseExp scope expression) :: localiseFields scope fields
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

/-- `localise_prog`. -/
def localiseProg (scope : List VarName) : Prog α → Prog α
  | .skip => .skip
  | .dec name shape value body =>
      .dec name shape (localiseExp scope value) (localiseProg (name :: scope) body)
  | .assign kind name value =>
      .assign (localiseKind scope kind name) name (localiseExp scope value)
  | .primitive name operator args =>
      .primitive name operator (localiseExpList scope args)
  | .store address value => .store (localiseExp scope address) (localiseExp scope value)
  | .store32 address value => .store32 (localiseExp scope address) (localiseExp scope value)
  | .storeByte address value =>
      .storeByte (localiseExp scope address) (localiseExp scope value)
  | .seq first second => .seq (localiseProg scope first) (localiseProg scope second)
  | .ite condition thenBranch elseBranch =>
      .ite (localiseExp scope condition)
        (localiseProg scope thenBranch) (localiseProg scope elseBranch)
  | .while condition body => .while (localiseExp scope condition) (localiseProg scope body)
  | .break => .break
  | .continue => .continue
  | .call none name args => .call none name (localiseExpList scope args)
  | .call (some (target, none)) name args =>
      .call (some (localiseTarget scope target, none)) name (localiseExpList scope args)
  | .call (some (target, some (exception, bound, handler))) name args =>
      .call (some (localiseTarget scope target,
          some (exception, bound, localiseProg (bound :: scope) handler)))
        name (localiseExpList scope args)
  | .decCall name shape function args body =>
      .decCall name shape function (localiseExpList scope args)
        (localiseProg (name :: scope) body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (localiseExp scope configuration)
        (localiseExp scope configurationLength) (localiseExp scope array)
        (localiseExp scope arrayLength)
  | .raise exception value => .raise exception (localiseExp scope value)
  | .return value => .return (localiseExp scope value)
  | .shMemLoad size kind name address =>
      .shMemLoad size (localiseKind scope kind name) name (localiseExp scope address)
  | .shMemStore size address value =>
      .shMemStore size (localiseExp scope address) (localiseExp scope value)
  | .tick => .tick
  | .annot tag text => .annot tag text

termination_by program => sizeOf program
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial
where
  localiseExpList (scope : List VarName) : List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        localiseExp scope expression :: localiseExpList scope expressions

/-- `localise_topdec`: a function body starts in the scope of its parameters. -/
def localiseDecl : Decl α → Decl α
  | .function declaration =>
      .function { declaration with
        body := localiseProg (declaration.params.map Prod.fst) declaration.body }
  | other => other

/-- `localise_topdecs`. -/
def localiseDecls (declarations : List (Decl α)) : List (Decl α) :=
  declarations.map localiseDecl

end Flapjack.Parser
