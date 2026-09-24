(*
  Direct HOL oracle for CakeML backend `wordConvs$extract_labels`.

  `extract_labels` collects the handler label pairs a `wordLang$prog` mentions:
  the `Call` return/handler labels, descending into the return-handler and
  handler bodies, plus `MustTerminate`, `Seq`, `Loop`, and `If` bodies, and no
  labels for every other constructor.  With no `Call` return metadata the
  result is empty even when a handler is present.

  Reference: cakeml/compiler/backend/semantics/wordConvsScript.sml:440-459.
*)
load "bossLib";
load "preamble";
load "wordConvsTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open wordConvsTheory;
open wordLangTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val skip = ``wordLang$Skip : (8 word) wordLang$prog``;

val callNone = ``wordLang$Call NONE NONE [] NONE : (8 word) wordLang$prog``;

val callRet = ``wordLang$Call (SOME ([1], (sptree$LN : num_set, sptree$LN : num_set),
    (wordLang$Skip : (8 word) wordLang$prog), 10, 11)) NONE [] NONE :
    (8 word) wordLang$prog``;

val callBoth = ``wordLang$Call (SOME ([1], (sptree$LN : num_set, sptree$LN : num_set),
    (wordLang$Skip : (8 word) wordLang$prog), 10, 11)) NONE []
    (SOME (2, (wordLang$Skip : (8 word) wordLang$prog), 20, 21)) :
    (8 word) wordLang$prog``;

val () = print_eval "el_inst" ``extract_labels (wordLang$Inst (asm$Skip : (8 word) asm$inst))``;
val () = print_eval "el_call_none" ``extract_labels ^callNone``;
val () = print_eval "el_call_ret" ``extract_labels ^callRet``;
val () = print_eval "el_call_both" ``extract_labels ^callBoth``;
val () = print_eval "el_handler_only" ``extract_labels
  (wordLang$Call NONE NONE [] (SOME (2, ^callRet, 20, 21)))``;
val () = print_eval "el_must_terminate" ``extract_labels (wordLang$MustTerminate ^callBoth)``;
val () = print_eval "el_seq" ``extract_labels (wordLang$Seq ^callBoth ^skip)``;
val () = print_eval "el_loop" ``extract_labels
  (wordLang$Loop (sptree$LN : num_set) ^callBoth (sptree$LN : num_set))``;
val () = print_eval "el_if" ``extract_labels
  (wordLang$If asm$Equal 0 (asm$Reg 1) ^callBoth ^skip)``;
val () = print_eval "el_nested" ``extract_labels
  (wordLang$Call (SOME ([1], (sptree$LN : num_set, sptree$LN : num_set), ^callBoth, 10, 11))
    NONE [] (SOME (2, ^callRet, 20, 21)))``;