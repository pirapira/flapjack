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

/-! Direct oracle guards for `crep_exp_to_display_def` in
    `pan_passesScript.sml:348-372`. -/
def crepExpOracle : Bool :=
  sameDisplay
      (crepExpToDisplay (α := BitVec 64) (.const (BitVec.ofNat 64 255)))
      (.item none "Const" [.string "0xFF"]) &&
    sameDisplay
      (crepExpToDisplay (α := BitVec 64) (.loadGlob (BitVec.ofNat 5 5)))
      (.item none "LoadGlob" [.string "0x5"]) &&
    sameDisplay
      (crepExpToDisplay (.var 7 : CrepExp (BitVec 64)))
      (.item none "Var" [.string "7"]) &&
    sameDisplay
      (crepExpToDisplay
        (.load32 (.op .add [.var 1, .const (BitVec.ofNat 64 4)]) :
          CrepExp (BitVec 64)))
      (.item none "MemLoad32"
        [.item none "Add"
          [.item none "Var" [.string "1"],
           .item none "Const" [.string "0x4"]]]) &&
    sameDisplay
      (crepExpToDisplay
        ((.crepOp .mul [.var 2, .const (BitVec.ofNat 64 3)]) :
          CrepExp (BitVec 64)))
      (.item none "Mul"
        [.item none "Var" [.string "2"],
         .item none "Const" [.string "0x3"]]) &&
    sameDisplay
      (crepExpToDisplay
        (.shift .ror (.cmp .equal (.var 0) (.const (BitVec.ofNat 64 0)))
          (.const (BitVec.ofNat 64 1)) : CrepExp (BitVec 64)))
      (.item none "Ror"
        [.item none "Equal"
          [.item none "Var" [.string "0"],
           .item none "Const" [.string "0x0"]],
         .item none "Const" [.string "0x1"]])

/-! Direct oracle guards for `crep_prog_to_display_def` in
    `pan_passesScript.sml:394-489`.  These cover every source constructor
    family, including sequence flattening and both call/handler forms. -/
def crepProgOracle : Bool :=
  sameDisplay
      (crepProgToDisplay (.skip : CrepProg (BitVec 64)))
      (.string "skip") &&
    sameDisplay
      (crepProgToDisplay
        (.shMem .load8 3 (.const (BitVec.ofNat 64 4)) :
          CrepProg (BitVec 64)))
      (.item none "shared_mem"
        [.string "load", .string "byte", .string "3",
         .item none "Const" [.string "0x4"]]) &&
    sameDisplay
      (crepProgToDisplay
        (.extCall "ffi" 1 2 3 4 : CrepProg (BitVec 64)))
      (.item none "ext_call"
        [.string "ffi", .string "1", .string "2", .string "3", .string "4"]) &&
    sameDisplay
      (crepProgToDisplay
        (.storeGlob (BitVec.ofNat 5 5) (.var 0) : CrepProg (BitVec 64)))
      (.item none "store_glob"
        [.string "0x5", .item none "Var" [.string "0"]]) &&
    sameDisplay
      (crepProgToDisplay
        (.ite (.var 0) (.assign 1 (.const (BitVec.ofNat 64 2))) .skip :
          CrepProg (BitVec 64)))
      (.item none "if"
        [.item none "Var" [.string "0"],
         .tuple [.string "1", .string ":=", .item none "Const" [.string "0x2"]],
         .string "skip"]) &&
    sameDisplay
      (crepProgToDisplay
        (.dec 2 (.const (BitVec.ofNat 64 5))
          (.while (.var 2) (.storeByte (.var 0) (.var 2))) :
          CrepProg (BitVec 64)))
      (.item none "dec"
        [.tuple [.string "2", .string ":=", .item none "Const" [.string "0x5"]],
         .item none "while"
           [.item none "Var" [.string "2"],
            .tuple [.string "mem", .item none "Var" [.string "0"], .string ":=",
              .string "byte", .item none "Var" [.string "2"]]]]) &&
    sameDisplay
      (crepProgToDisplay
        (.primitive [1, 2] .addCarry [3, 4] : CrepProg (BitVec 64)))
      (.tuple [.tuple [.string "1", .string "2"], .string ":=",
        .item none "AddCarry" [.string "3", .string "4"]]) &&
    sameDisplay
      (crepProgToDisplay
        (.store (.var 0) (.const (BitVec.ofNat 64 1)) : CrepProg (BitVec 64)))
      (.tuple [.string "mem", .item none "Var" [.string "0"], .string ":=",
        .item none "Const" [.string "0x1"]]) &&
    sameDisplay
      (crepProgToDisplay
        (.store32 (.var 0) (.const (BitVec.ofNat 64 1)) : CrepProg (BitVec 64)))
      (.tuple [.string "mem", .item none "Var" [.string "0"], .string ":=",
        .string "32bit", .item none "Const" [.string "0x1"]]) &&
    sameDisplay
      (crepProgToDisplay (.tick : CrepProg (BitVec 64))) (.string "tick") &&
    sameDisplay
      (crepProgToDisplay (.break 4 : CrepProg (BitVec 64)))
      (.item none "break" [.string "4"]) &&
    sameDisplay
      (crepProgToDisplay (.continue 5 : CrepProg (BitVec 64)))
      (.item none "continue" [.string "5"]) &&
    sameDisplay
      (crepProgToDisplay
        (.return [.const (BitVec.ofNat 64 6), .var 1] : CrepProg (BitVec 64)))
      (.item none "return"
        [.item none "Const" [.string "0x6"], .item none "Var" [.string "1"]]) &&
    sameDisplay
      (crepProgToDisplay (.raise (BitVec.ofNat 64 7) : CrepProg (BitVec 64)))
      (.item none "raise" [.string "0x7"]) &&
    sameDisplay
      (crepProgToDisplay
        (.seq (.seq .skip .tick) (.assign 0 (.const (BitVec.ofNat 64 8))) :
          CrepProg (BitVec 64)))
      (.list [.string "seq", .string "skip", .string "tick",
        .tuple [.string "0", .string ":=", .item none "Const" [.string "0x8"]]]) &&
    sameDisplay
      (crepProgToDisplay
        (.call none "f" [.const (BitVec.ofNat 64 9)] : CrepProg (BitVec 64)))
      (.item none "tail_call"
        [.string "f", .tuple [.item none "Const" [.string "0x9"]]]) &&
    sameDisplay
      (crepProgToDisplay
        (.call (some ([], none)) "f" [] : CrepProg (BitVec 64)))
      (.item none "call" [.string "f", .tuple [], .string "no_handler"]) &&
    sameDisplay
      (crepProgToDisplay
        (.call (some ([2], some ((BitVec.ofNat 64 10), .skip))) "f" [] :
          CrepProg (BitVec 64)))
      (.tuple [.tuple [.string "2"], .string ":=",
        .item none "call"
          [.string "f", .tuple [],
           .item none "handler"
           [.tuple [.string "0xA", .string "skip"]]]])

/-! Direct oracle guard for `crep_fun_to_display_def` in
    `pan_passesScript.sml:492-499`. -/
def crepFunOracle : Bool :=
  sameDisplay
    (crepFunToDisplay "f" [2, 3]
      (.return [.var 2, .const (BitVec.ofNat 64 7)] : CrepProg (BitVec 64)))
    (.tuple [.string "func", .string "f",
      .tuple [.string "2", .string "3"],
      .item none "return"
        [.item none "Var" [.string "2"],
         .item none "Const" [.string "0x7"]]])

def crepToStrsOracle : Bool :=
  crepToStrs
    [(("f", [2, 3],
      .return [.var 2, .const (BitVec.ofNat 64 7)]) :
        FunName × List Nat × CrepProg (BitVec 64))] ==
    ["(", "func", " ", "f", " ", "(", "2", " ", "3", ")", " ",
     "(", "return", " ", "(", "Var", " ", "2", ")", " ", "(", "Const", " ",
     "0x7", ")", ")", ")", "\n\n"]

/-! Direct oracle guard for `pan_to_strs_def` in
    `pan_passesScript.sml:340-346`. -/
def panToStrsOracle : Bool :=
  panToStrs
    [(.decl .one "g" (.const (BitVec.ofNat 64 5)) : Decl (BitVec 64))] ==
    ["(", "global", " ", "1", " ", "g", " ", ":=", " ", "(", "Const", " ",
     "0x5", ")", ")", "\n\n"]

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

/-! Direct oracle guards for `pan_fun_to_display_def` in
    `pan_passesScript.sml:311-330`. -/
def panFunOracle : Bool :=
  sameDisplay
      (panFunToDisplay
        (.function
          { name := "f", inline := false, exported := true,
            params := [("x", .one), ("pair", .comb [.one, .one])],
            body := .return (.var .local "x"), returnShape := .one } :
          Decl (BitVec 64)))
      (.tuple [.string "func", .string "1", .string "f",
        .tuple [.tuple [.string "x", .string ":", .string "1"],
          .tuple [.string "pair", .string ":", .string "{1,1}"]],
        .item none "return" [.item none "Var" [.string "local", .string "x"]]]) &&
    sameDisplay
      (panFunToDisplay
        (.decl .one "g" (.const (BitVec.ofNat 64 5)) : Decl (BitVec 64)))
      (.tuple [.string "global", .string "1", .string "g", .string ":=",
        .item none "Const" [.string "0x5"]]) &&
    sameDisplay
      (panFunToDisplay
        (.name "Pair" [("left", .one), ("right", .named "Word")] :
          Decl (BitVec 64)))
      (.tuple [.string "struct", .string "Pair",
        .tuple [.tuple [.string "left", .string ":", .string "1"],
          .tuple [.string "right", .string ":", .string "Word"]]]) &&
    sameDisplay
      (panFunToDisplay
        (.exnDecl "E" (.comb [.one, .one]) : Decl (BitVec 64)))
      (.tuple [.string "exception", .string "E", .string ":", .string "{1,1}"])

def anyPanProgOracle : Bool :=
  let panProgram : List (Decl (BitVec 64)) :=
    [.decl Shape.one "g" (.const (BitVec.ofNat 64 7))]
  let crepProgram : List (FunName × List Nat × CrepProg (BitVec 64)) :=
    [("c", [], .skip)]
  let loopProgram : List (Nat × List Nat × LoopProg (BitVec 64)) :=
    [(0, [], .skip)]
  anyPanProgPp (.pan panProgram) == panToStrs panProgram &&
    anyPanProgPp (.crep crepProgram) == crepToStrs crepProgram &&
    anyPanProgPp (.loop loopProgram []) == loopToStrs [] loopProgram &&
    anyPanProgPp (.cake ["backend", "stage"] : AnyPanProg (BitVec 64)) ==
      ["backend", "stage"]

/-! Direct oracle guards for `loop_exp_to_display_def` in
    `pan_passesScript.sml:508-530`. -/
def loopExpConstOracle : Bool :=
  sameDisplay
    (loopExpToDisplay (α := BitVec 64) (.const (BitVec.ofNat 64 255)))
    (.item none "Const" [.string "0xFF"])

def loopExpLookupOracle : Bool :=
  sameDisplay
    (loopExpToDisplay (α := BitVec 64) (.lookup (BitVec.ofNat 5 5)))
    (.item none "Lookup" [.string "0x5"])

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
#guard crepExpOracle
#guard crepProgOracle
#guard crepFunOracle
#guard crepToStrsOracle
#guard panToStrsOracle
#guard panProgOracle
#guard anyPanProgOracle
#guard loopExpOracle
#guard panFunOracle
#guard loopProgOracle
#guard loopFunOracle
#guard loopToStrsOracle

end Flapjack.Test.DisplayParity
