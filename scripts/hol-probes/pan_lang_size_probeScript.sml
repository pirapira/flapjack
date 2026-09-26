(* Direct HOL oracle for the *generated* datatype size functions of panLang.

   HOL's `Datatype` command generates `shape_size`/`shape1_size` and
   `exp_size`/`exp1_size`/`exp2_size`/`exp3_size` for
   cakeml/pancake/panLangScript.sml:35-39 (`shape`) and :53-69 (`exp`).  These
   are not textual source declarations (`Definition`/`Theorem`), so
   `scripts/check-hol-refs.py` cannot resolve them and the Lean ports cannot
   carry an `@[hol]` tag.  `Theorem MEM_IMP_shape_size`
   (panLangScript.sml:131-137) and `Theorem MEM_IMP_exp_size`
   (panLangScript.sml:198-208) are stated over them, so their exact equations
   are pinned here.

   This probe loads only HOL's standard library and defines local replicas with
   the same constructor arities and field types as the CakeML datatypes
   (`mlstring = implode (char list)`, `shape`, `panop`, `varkind`, `binop`,
   `cmp`, `shift`, and the polymorphic `exp`).  `char_size` is HOL's registered
   `char_size (c:char) = 0` (HOL/src/string/stringScript.sml:179); `w2n` is the
   registered size of `'a word`; `num`'s size is the identity.  No CakeML
   theory is loaded, so running it does not touch the read-only submodule.

   Regenerate from a scratch directory (the script calls `new_theory`, which
   writes theory files into the current directory):

     /home/zksecurity/HOL/bin/hol run \
       scripts/hol-probes/pan_lang_size_probeScript.sml

   The `print_thm` output is captured in `pan_lang_size_probe.out`. *)

load "bossLib";
load "stringTheory";
load "wordsTheory";
open bossLib HolKernel Parse boolLib;

val _ = new_theory "pan_lang_size_probe";

Datatype:
  mlstring = implode (char list)
End

Datatype:
  shape = One | Comb (shape list) | Named mlstring
End

Datatype:
  panop = Mul
End

Datatype:
  varkind = Local | Global
End

Datatype:
  binop = Add | Sub | And | Or | Xor
End

Datatype:
  cmp = Equal | Lower | Less | Test | NotEqual | NotLower | NotLess | NotTest
End

Datatype:
  shift = Lsl | Lsr | Asr | Ror
End

Datatype:
  exp = Const ('a word)
      | Var varkind mlstring
      | RStruct (exp list)
      | RField num exp
      | NStruct mlstring ((mlstring # exp) list)
      | NField mlstring exp
      | Load shape exp
      | Load32 exp
      | LoadByte exp
      | Op binop (exp list)
      | Panop panop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp exp
      | BaseAddr
      | TopAddr
      | BytesInWord
End

fun show name th = (print (name ^ " : "); print_thm th; print "\n");

val _ = show "mlstring_size_def" (fetch "-" "mlstring_size_def");
val _ = show "shape_size_def" (fetch "-" "shape_size_def");
val _ = show "exp_size_def" (fetch "-" "exp_size_def");
val _ = print "DONE\n";
