import Flapjack.Display

namespace Flapjack.Test.DisplayParity

open Flapjack

def sameDisplay (actual expected : DisplayExpr) : Bool :=
  reprStr actual == reprStr expected

/-! Direct oracle guards for `pan_passesScript.sml:112-181`:
`opsize_to_display_def`, `insert_es_def`, `varkind_to_str_def`,
`primop_to_display_def`, and `dest_annot_def`. -/

def opSizeOracle : Bool :=
  sameDisplay (opSizeToDisplay .op8) (.string "byte") &&
    sameDisplay (opSizeToDisplay .op16) (.string "word16") &&
    sameDisplay (opSizeToDisplay .opW) (.string "word") &&
    sameDisplay (opSizeToDisplay .op32) (.string "word32")

def insertEsOracle : Bool :=
  sameDisplay (insertDisplayExpressions (.string "Op") [.string "x"])
      (.item none "Op" [.string "x"]) &&
    sameDisplay (insertDisplayExpressions (.tuple []) [.string "x"]) (.tuple [])

def varKindOracle : Bool :=
  varKindToDisplayString .global == "global" &&
    varKindToDisplayString .local == "local"

def primOpOracle : Bool :=
  sameDisplay (primOpToDisplay .addCarry) (.string "AddCarry")

def destAnnotOracle : Bool :=
  destAnnot (.annot "tag" "text" : Prog Nat) == some ("tag", "text") &&
    destAnnot (.skip : Prog Nat) == none

/-! Direct oracle guards for `pan_exp_to_display_def` in
    `pan_passesScript.sml:135-175`.  The expected words use Cake's
    `word_to_display_def` spelling (`0x` plus upper-case, unpadded hex). -/
def panExpConstOracle : Bool :=
  sameDisplay
    (panExpToDisplay (α := BitVec 64) (.const (BitVec.ofNat 64 255)))
    (.item none "Const" [.string "0xFF"])

def panExpVarOracle : Bool :=
  sameDisplay (panExpToDisplay (.var .global "g" : Exp (BitVec 64)))
    (.item none "Var" [.string "global", .string "g"])

def panExpLoadOracle : Bool :=
  sameDisplay
    (panExpToDisplay
      (.load (.comb [.one, .named "Pair"])
        (.op .add [.var .local "x", .const (BitVec.ofNat 64 1)])))
    (.item none "MemLoad"
      [.string "{1,Pair}",
       .item none "Add"
         [.item none "Var" [.string "local", .string "x"],
          .item none "Const" [.string "0x1"]]])

def panExpNamedStructOracle : Bool :=
  sameDisplay
    (panExpToDisplay
      (.nStruct "Pair" [("left", .const (BitVec.ofNat 64 2)),
                         ("right", .var .local "y")]))
    (.item none "NamedStruct"
      [.string "Pair",
       .tuple [.string "left", .string ":=",
         .item none "Const" [.string "0x2"]],
       .tuple [.string "right", .string ":=",
         .item none "Var" [.string "local", .string "y"]]])

def panExpShiftOracle : Bool :=
  let word : BitVec 64 := BitVec.ofNat 64 255
  sameDisplay
    (panExpToDisplay
      (.shift .ror (.cmp .equal (.const word) (.const (BitVec.ofNat 64 0)))
        (.const (BitVec.ofNat 64 3))))
    (.item none "Ror"
      [.item none "Equal"
         [.item none "Const" [.string "0xFF"],
          .item none "Const" [.string "0x0"]],
       .item none "Const" [.string "0x3"]])

def panExpOracle : Bool :=
  panExpConstOracle && panExpVarOracle && panExpLoadOracle &&
    panExpNamedStructOracle && panExpShiftOracle

#guard opSizeOracle
#guard insertEsOracle
#guard varKindOracle
#guard primOpOracle
#guard destAnnotOracle
#guard panExpOracle

end Flapjack.Test.DisplayParity
