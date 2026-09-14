(* Direct HOL-EVAL fixture for word_alloc$get_stack_only.
   Reference: cakeml/compiler/backend/word_allocScript.sml:1741-1789. *)
load "bossLib";
load "preamble";
load "word_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

val _ = print_eval "skip"
  ``word_alloc$get_stack_only
      (wordLang$Skip : 64 wordLang$prog)``;

(* A move chain whose second element writes an allocatable variable (9)
   from a stack variable (7): 9 becomes forced-stack. *)
val _ = print_eval "move_chain"
  ``word_alloc$get_stack_only
      (wordLang$Move 1 [(9,9); (7,9)] : 64 wordLang$prog)``;

(* The same move shape but sourced from a physical register (2): the
   target stays allocatable. *)
val _ = print_eval "move_from_reg"
  ``word_alloc$get_stack_only
      (wordLang$Move 1 [(9,9); (2,9)] : 64 wordLang$prog)``;

(* Sequences thread the (ts,fs) state right-to-left: the second move's
   forced-stack target must remain visible. *)
val _ = print_eval "seq_moves"
  ``word_alloc$get_stack_only
      (wordLang$Seq
        (wordLang$Move 1 [(13,13); (2,13)] : 64 wordLang$prog)
        (wordLang$Move 1 [(9,9); (7,9)] : 64 wordLang$prog))``;

(* Branches merge the two arms' forced-stack sets. *)
val _ = print_eval "if_merge"
  ``word_alloc$get_stack_only
      (wordLang$If NotEqual 2 (Reg 3)
        (wordLang$Move 1 [(9,9); (7,9)] : 64 wordLang$prog)
        (wordLang$Move 1 [(19,19); (7,19)] : 64 wordLang$prog))``;

(* Both arms contributing (21 = 4*5+1 is allocatable). *)
val _ = print_eval "if_merge_alloc"
  ``word_alloc$get_stack_only
      (wordLang$If NotEqual 2 (Reg 3)
        (wordLang$Move 1 [(9,9); (7,9)] : 64 wordLang$prog)
        (wordLang$Move 1 [(21,21); (7,21)] : 64 wordLang$prog))``;

(* Call with a return continuation and an exception handler: both are
   analysed and merged. *)
val _ = print_eval "call_merge"
  ``word_alloc$get_stack_only
      (wordLang$Call
        (SOME ([9], (LN, LN), wordLang$Move 1 [(9,9); (7,9)], 0, 1))
        (SOME 5) [2]
        (SOME (11, wordLang$Move 1 [(19,19); (7,19)], 0, 2)))``;

(* Tail calls (no return tuple) leave the state untouched. *)
val _ = print_eval "call_tail"
  ``word_alloc$get_stack_only
      (wordLang$Call NONE (SOME 5) [0; 2] NONE)``;

(* A plain assignment is a clash-tree leaf: its written and read names
   are removed from the temporaries set. *)
val _ = print_eval "assign_leaf"
  ``word_alloc$get_stack_only
      (wordLang$Assign 9 (wordLang$Const 7w : 64 word wordLang$exp))``;
