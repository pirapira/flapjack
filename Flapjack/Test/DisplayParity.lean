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

/-! Direct oracle guards for `loop_exp_to_display_def` in
    `pan_passesScript.sml:508-530`. -/
def loopExpConstOracle : Bool :=
  sameDisplay
    (loopExpToDisplay (α := BitVec 64) (.const (BitVec.ofNat 64 255)))
    (.item none "Const" [.string "0xFF"])

def loopExpLookupOracle : Bool :=
  sameDisplay
    (loopExpToDisplay (α := BitVec 64) (.lookup (BitVec.ofNat 64 32)))
    (.item none "Lookup" [.string "0x20"])

def loopExpNestedOracle : Bool :=
  sameDisplay
    (loopExpToDisplay
      (.op .add [.var 3, .const (BitVec.ofNat 64 1)] : LoopExp (BitVec 64)))
    (.item none "Op"
      [.string "Add",
       .item none "Var" [.string "3"],
       .item none "Const" [.string "0x1"]])

def loopExpLoadOracle : Bool :=
  sameDisplay
    (loopExpToDisplay
      (.load (.op .xor [.var 2, .const (BitVec.ofNat 64 4)]) :
        LoopExp (BitVec 64)))
    (.item none "MemLoad"
      [.item none "Op"
        [.string "Xor",
         .item none "Var" [.string "2"],
         .item none "Const" [.string "0x4"]]])

def loopExpShiftOracle : Bool :=
  sameDisplay
    (loopExpToDisplay
      (.shift .ror (.const (BitVec.ofNat 64 255)) (.var 1) :
        LoopExp (BitVec 64)))
    (.item none "Shift"
      [.string "Ror",
       .item none "Const" [.string "0xFF"],
       .item none "Var" [.string "1"]])

def loopExpOracle : Bool :=
  loopExpConstOracle && loopExpLookupOracle && loopExpNestedOracle &&
    loopExpLoadOracle && loopExpShiftOracle

/-! Direct oracle guards for `loop_prog_to_display_def` and its handler
    equation in `pan_passesScript.sml:549-631`. -/
def loopProgCoreOracle : Bool :=
  sameDisplay
      (loopProgToDisplay [] (.skip : LoopProg Nat))
      (.string "skip") &&
    sameDisplay
      (loopProgToDisplay []
        (.arith (.longDiv 1 2 3 4 5) : LoopProg Nat))
      (.item none "long_div"
        [.string "1", .string "2", .string "3", .string "4", .string "5"]) &&
    sameDisplay
      (loopProgToDisplay []
        (.assign 3 (.const (BitVec.ofNat 64 7)) : LoopProg (BitVec 64)))
      (.tuple [.string "3", .string ":=",
        .item none "Const" [.string "0x7"]])

def loopProgSeqOracle : Bool :=
  sameDisplay
    (loopProgToDisplay []
      (.seq .skip (.assign 1 (.const 2)) : LoopProg Nat))
    (.list [.string "seq", .string "skip",
      .tuple [.string "1", .string ":=",
        .item none "Const" [.string "0x2"]]])

def loopProgMemoryOracle : Bool :=
  sameDisplay
    (loopProgToDisplay []
      (.shMem .store8 4 (.const (BitVec.ofNat 64 9)) : LoopProg (BitVec 64)))
    (.tuple [.string "share_mem", .string "Store8", .string "4",
      .item none "Const" [.string "0x9"]]) &&
    sameDisplay
      (loopProgToDisplay []
        (.locValue 7 3 : LoopProg Nat))
      (.item none "loc_value" [.string "7", .string "3"])

def loopProgControlOracle : Bool :=
  sameDisplay
    (loopProgToDisplay []
      (.ite .equal 1 (.imm (BitVec.ofNat 64 0)) .skip .fail [] :
        LoopProg (BitVec 64)))
    (.item none "if"
      [.tuple [.string "Equal", .string "1",
        .item none "Imm" [.string "0x0"]],
       .string "skip", .string "fail", .string "{}"])

def loopProgCallOracle : Bool :=
  sameDisplay
    (loopProgToDisplay [(7, "callee")]
      (.call (some ([4], [2])) (some 7) [1, 2]
        (some (9, .skip, .return [3], [4])) : LoopProg Nat))
    (.tuple [.list [.string "4"], .string ":=",
      .item none "call"
        [.string "callee@7",
         .list [.string "1", .string "2"],
         .string "{2}",
         .item none "handler"
           [.tuple [.string "9", .string "skip",
             .item none "return" [.string "3"], .string "{4}"]]]])

def loopProgOracle : Bool :=
  loopProgCoreOracle && loopProgSeqOracle && loopProgMemoryOracle &&
    loopProgControlOracle && loopProgCallOracle

def loopFunOracle : Bool :=
  sameDisplay
    (loopFunToDisplay [(7, "callee")]
      ((7, [1, 2], .assign 3 (.const (BitVec.ofNat 64 7))) :
        Nat × List Nat × LoopProg (BitVec 64)))
    (.tuple [.string "func", .string "callee@7",
      .tuple [.string "1", .string "2"],
      .tuple [.string "3", .string ":=",
        .item none "Const" [.string "0x7"]]])

def loopToStrsOracle : Bool :=
  loopToStrs [(7, "callee")]
    [((7, [1, 2], .assign 3 (.const (BitVec.ofNat 64 7))) :
        Nat × List Nat × LoopProg (BitVec 64))] ==
    ["(", "func", " ", "callee@7", " ", "(", "1", " ", "2", ")", " ",
     "(", "3", " ", ":=", " ", "(", "Const", " ", "0x7", ")", ")", ")",
     "\n\n"]

#guard opSizeOracle
#guard insertEsOracle
#guard varKindOracle
#guard primOpOracle
#guard destAnnotOracle
#guard panExpOracle
#guard loopExpOracle
#guard loopProgOracle
#guard loopFunOracle
#guard loopToStrsOracle

end Flapjack.Test.DisplayParity
