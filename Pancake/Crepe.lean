import Pancake.Language

/-!
The Crepe intermediate language.

Crepe is Pancake after structured locals have been flattened into word-sized
locals. This mirrors `cakeml/pancake/crepLangScript.sml`; target-specific word
operations remain abstract in the polymorphic value type.
-/

namespace Pancake

inductive CrepOp where
  | mul
  deriving DecidableEq, Repr

inductive CrepExp (α : Type u) where
  | const (value : α)
  | var (name : Nat)
  | load (address : CrepExp α)
  | load32 (address : CrepExp α)
  | loadByte (address : CrepExp α)
  | loadGlob (address : α)
  | op (operator : BinOp) (args : List (CrepExp α))
  | crepOp (operator : CrepOp) (args : List (CrepExp α))
  | cmp (operator : Cmp) (left right : CrepExp α)
  | shift (operator : Shift) (left right : CrepExp α)
  | baseAddr
  | topAddr
  deriving Repr

inductive CrepMemOp where
  | load
  | load8
  | load16
  | load32
  | store
  | store8
  | store16
  | store32
  deriving DecidableEq, Repr

inductive CrepProg (α : Type u) where
  | skip
  | dec (name : Nat) (value : CrepExp α) (body : CrepProg α)
  | assign (name : Nat) (value : CrepExp α)
  | primitive (names : List Nat) (operator : PrimOp) (args : List Nat)
  | store (address value : CrepExp α)
  | store32 (address value : CrepExp α)
  | storeByte (address value : CrepExp α)
  | storeGlob (address : α) (value : CrepExp α)
  | seq (first second : CrepProg α)
  | ite (condition : CrepExp α) (thenBranch elseBranch : CrepProg α)
  | while (condition : CrepExp α) (body : CrepProg α)
  | break (label : Nat)
  | continue (label : Nat)
  | call (returnInfo : Option (List Nat × Option (α × CrepProg α)))
      (name : FunName) (args : List (CrepExp α))
  | extCall (function : FunName) (configuration configurationLength array arrayLength : Nat)
  | raise (exception : α)
  | return (values : List (CrepExp α))
  | shMem (operator : CrepMemOp) (name : Nat) (address : CrepExp α)
  | tick
  deriving Repr

def loadShape [BEq α] [OfNat α 0] [Add α]
    (address stride : α) (count : Nat) (value : CrepExp α) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 =>
      let loaded := if address == 0 then .load value else .load (.op .add [value, .const address])
      loaded :: loadShape (address + stride) stride count value

def crepNestedSeq : List (CrepProg α) → CrepProg α
  | [] => .skip
  | statement :: statements => .seq statement (crepNestedSeq statements)

def stores [BEq α] [OfNat α 0] [Add α]
    (address : CrepExp α) : List (CrepExp α) → α → α → List (CrepProg α)
  | [], _, _ => []
  | value :: values, offset, stride =>
      let destination := if offset == 0 then address else .op .add [address, .const offset]
      .store destination value :: stores address values (offset + stride) stride

def nestedDecs : List Nat → List (CrepExp α) → CrepProg α → CrepProg α
  | [], [], body => body
  | name :: names, value :: values, body => .dec name value (nestedDecs names values body)
  | _, _, _ => .skip

def storeGlobals [Add α] (address stride : α) : List (CrepExp α) → List (CrepProg α)
  | [] => []
  | value :: values => .storeGlob address value :: storeGlobals (address + stride) stride values

def loadGlobals [Add α] (address stride : α) (count : Nat) : List (CrepExp α) :=
  match count with
  | 0 => []
  | count + 1 => .loadGlob address :: loadGlobals (address + stride) stride count

def assignRet [OfNat α 0] [Add α] (wordStride : α) (names : List Nat) : CrepProg α :=
  crepNestedSeq (names.zipWith (fun name value => .assign name value)
    (loadGlobals (0 : α) wordStride names.length))

end Pancake
