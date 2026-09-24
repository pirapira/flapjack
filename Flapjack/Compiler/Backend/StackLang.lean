import Flapjack.HolRef

/-!
# Faithful Cake StackLang syntax

This module records the generic `store_name` and `prog` datatype shapes from
`cakeml/compiler/backend/stackLangScript.sml`. It is kept separate from
`Flapjack.Stack.StackProg`, whose executable fields intentionally use Flapjack
representations such as `Nat` registers, `FunName`, and RISC-V word
instructions. The generic carriers below preserve the HOL datatype boundary
without claiming that the existing executable AST is already related to it.
The word-independent program combinator `list_Seq` is ported over this carrier.
-/

namespace Flapjack.Compiler.Backend.StackLang

/-- HOL `stackLang$store_name`; `Temp` carries exactly a 5-bit word. -/
inductive StoreName where
  | nextFree
  | endOfHeap
  | triggerGC
  | heapLength
  | progStart
  | bitmapBase
  | currHeap
  | otherHeap
  | allocSize
  | globals
  | globReal
  | handler
  | genStart
  | codeBuffer
  | codeBufferEnd
  | bitmapBuffer
  | bitmapBufferEnd
  | temp (value : BitVec 5)
  deriving Repr

/-- HOL `stackLang$prog`, with its imported HOL carrier types explicit.

The target of `Call` is `num + num`, represented by `Sum Nat Nat`; the two
optional continuations retain their distinct tuple arities. -/
inductive Prog (Inst Cmp RegImm Binop Memop Addr MlString : Type) where
  | skip
  | inst (instruction : Inst)
  | get (destination : Nat) (store : StoreName)
  | set (store : StoreName) (source : Nat)
  | opCurrHeap (operator : Binop) (destination source : Nat)
  | call (returnHandler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString ×
        Nat × Nat × Nat))
      (target : Sum Nat Nat)
      (handler : Option (Prog Inst Cmp RegImm Binop Memop Addr MlString ×
        Nat × Nat))
  | seq (first second : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | ite (operator : Cmp) (condition : Nat) (right : RegImm)
      (thenBranch elseBranch : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | loop (body : Prog Inst Cmp RegImm Binop Memop Addr MlString)
  | jumpLower (left right target : Nat)
  | alloc (words : Nat)
  | storeConsts (source bitmap : Nat) (stub : Option Nat)
  | raise (exception : Nat)
  | ret (value : Nat)
  | break (label : Nat)
  | continue (label : Nat)
  | ffi (function : MlString) (configuration configurationLength array arrayLength returnAddress : Nat)
  | tick
  | locValue (destination label entry : Nat)
  | install (codeBuffer codeLength dataBuffer dataLength returnAddress : Nat)
  | shMemOp (operator : Memop) (register : Nat) (address : Addr)
  | codeBufferWrite (address value : Nat)
  | dataBufferWrite (address value : Nat)
  | rawCall (target : Nat)
  | stackAlloc (words : Nat)
  | stackFree (words : Nat)
  | stackStore (offset register : Nat)
  | stackStoreAny (register offsetRegister : Nat)
  | stackLoad (offset register : Nat)
  | stackLoadAny (register offsetRegister : Nat)
  | stackGetSize (register : Nat)
  | stackSetSize (register : Nat)
  | bitmapLoad (destination address : Nat)
  | halt (register : Nat)
  deriving Repr

/-- Exact port of HOL `list_Seq_def`
    (`cakeml/compiler/backend/stackLangScript.sml:86`):

```
(list_Seq [] = Skip) /\
(list_Seq [x] = x) /\
(list_Seq (x::y::xs) = Seq x (list_Seq (y::xs)))
```

    `list_Seq` builds the right-associated `Seq` chain of a program list, the
    canonical stackLang combinator used by the Word-to-Stack stubs and
    `compile_prog`.  HOL `list_Seq` is polymorphic in the word type `'a` and
    touches only the word-independent `Skip`/`Seq` constructors, whose fields are
    the program itself; the Lean definition is correspondingly polymorphic in the
    carrier's type parameters (`Inst`/`Cmp`/`RegImm`/`Binop`/`Memop`/`Addr`/
    `MlString`) and uses none of them.  The word-indexed constructors
    (`inst`/`ite`/`shMemOp`) are not involved. -/
@[hol "cakeml/compiler/backend/stackLangScript.sml" "list_Seq_def"]
def listSeq {Inst Cmp RegImm Binop Memop Addr MlString : Type} :
    List (Prog Inst Cmp RegImm Binop Memop Addr MlString) →
      Prog Inst Cmp RegImm Binop Memop Addr MlString
  | [] => .skip
  | [x] => x
  | x :: y :: xs => .seq x (listSeq (y :: xs))

end Flapjack.Compiler.Backend.StackLang
