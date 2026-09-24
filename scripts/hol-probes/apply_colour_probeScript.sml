(* Direct HOL-EVAL observations for CakeML total_colour and apply_colour.
   References: word_allocScript.sml:1592-1599, 632-674. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_allocTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val colour = ``sptree$fromAList [(1n,7n); (3n,9n)]``;
val _ = print_eval "total_colour_alloc"
  ``total_colour ^colour 1``;
val _ = print_eval "total_colour_physical"
  ``total_colour ^colour 2``;
val _ = print_eval "total_colour_stack_default"
  ``total_colour ^colour 7``;

val _ = print_eval "apply_colour_assign"
  ``apply_colour (total_colour ^colour)
      (wordLang$Assign 1 (wordLang$Var 3 : 64 word wordLang$exp))``;

val alias_colour = ``\n:num. if n = 0n then 0n else 1n``;
val _ = print_eval "apply_colour_alias_assign"
  ``apply_colour ^alias_colour
      (wordLang$Assign 2 (wordLang$Var 1 : 64 word wordLang$exp))``;

val binary_alias_colour =
  ``\n:num. if n = 2 then 1 else if n = 3 then 2 else n``;
val _ = print_eval "apply_colour_alias_add"
  ``apply_colour ^binary_alias_colour
      (wordLang$Assign 2
        (wordLang$Op Add
          [wordLang$Var 1; wordLang$Var 3] : 64 word wordLang$exp))``;

val _ = print_eval "apply_colour_return_raise"
  ``apply_colour (total_colour ^colour)
      (wordLang$Seq
        (wordLang$Return 1 [3; 5])
        (wordLang$Raise 7) : 64 wordLang$prog)``;

val _ = print_eval "apply_colour_call_handler"
  ``apply_colour (total_colour ^colour)
      (wordLang$Call
        (SOME ([1], (insert 3 () LN, insert 5 () LN),
          wordLang$Return 1 [3], 10, 11))
        (SOME 12) [1; 3]
        (SOME (7, wordLang$Raise 3, 13, 14)) : 64 wordLang$prog)``;

val _ = print_eval "apply_colour_loop_live"
  ``apply_colour (total_colour ^colour)
      (wordLang$Loop (insert 1 () (insert 7 () LN))
        (wordLang$Assign 1 (wordLang$Var 3))
        (insert 3 () LN) : 64 wordLang$prog)``;

val _ = print_eval "apply_colour_alias_const"
  ``apply_colour ^alias_colour
      (wordLang$Assign 2 (wordLang$Const 5w : 64 word wordLang$exp))``;
