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

/-! Direct oracle guards for `pan_prog_to_display_def` in
    `pan_passesScript.sml:203-300`, including sequence flattening, annotation
    escaping, calls, handlers, and declaration calls. -/
def panProgBasicOracle : Bool :=
  sameDisplay (panProgToDisplay (.skip : Prog (BitVec 64))) (.string "skip") &&
    sameDisplay
      (panProgToDisplay
        (.shMemLoad .opW .global "g" (.const (BitVec.ofNat 64 8))))
      (.item none "shared_mem_load"
        [.string "word", .string "global", .string "g",
         .item none "Const" [.string "0x8"]]) &&
    sameDisplay
      (panProgToDisplay
        (.store32 (.const (BitVec.ofNat 64 0)) (.const (BitVec.ofNat 64 1))))
      (.tuple [.string "mem", .item none "Const" [.string "0x0"],
        .string ":=", .string "32bit", .item none "Const" [.string "0x1"]])

def panProgSequenceOracle : Bool :=
  let program : Prog (BitVec 64) :=
    .seq (.seq .skip .tick) (.assign .local "x" (.const (BitVec.ofNat 64 7)))
  sameDisplay (panProgToDisplay program)
    (.list [.string "seq", .string "skip", .string "tick",
      .tuple [.string "local", .string "x", .string ":=",
        .item none "Const" [.string "0x7"]]])

def panProgAnnotationOracle : Bool :=
  sameDisplay
    (panProgToDisplay (.annot "a\n" "b\"" : Prog (BitVec 64)))
    (.item none "annot" [.string "\"a\\n\"", .string "\"b\\\"\""])

def panProgCallOracle : Bool :=
  sameDisplay
      (panProgToDisplay
        (.call none "f" [.const (BitVec.ofNat 64 1)] : Prog (BitVec 64)))
      (.item none "tail_call"
        [.string "f", .tuple [.item none "Const" [.string "0x1"]]]) &&
    sameDisplay
      (panProgToDisplay
        (.call (some (none, some ("E", "h", .return (.const (BitVec.ofNat 64 2)))))
          "f" [] : Prog (BitVec 64)))
      (.item none "call"
        [.string "f", .tuple [],
         .item none "handler"
           [.tuple [.string "E", .string "h",
             .item none "return" [.item none "Const" [.string "0x2"]]]]]) &&
    sameDisplay
      (panProgToDisplay
        (.call (some (some (.local, "r"), none)) "f" [] : Prog (BitVec 64)))
      (.tuple [.string "r", .string ":=",
        .item none "call"
          [.string "f", .tuple [], .string "no_handler"]])

def panProgDeclCallOracle : Bool :=
  sameDisplay
    (panProgToDisplay
      (.decCall "r" .one "f" [.const (BitVec.ofNat 64 3)] .skip : Prog (BitVec 64)))
    (.item none "dec"
      [.tuple [.string "1", .string "r", .string ":=",
        .item none "call"
          [.string "f", .tuple [.item none "Const" [.string "0x3"]]]],
       .string "skip"])

def panProgOracle : Bool :=
  panProgBasicOracle && panProgSequenceOracle && panProgAnnotationOracle &&
    panProgCallOracle && panProgDeclCallOracle

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

#guard opSizeOracle
#guard insertEsOracle
#guard varKindOracle
#guard primOpOracle
#guard destAnnotOracle
#guard panExpOracle
#guard panProgOracle
#guard loopExpOracle

end Flapjack.Test.DisplayParity
