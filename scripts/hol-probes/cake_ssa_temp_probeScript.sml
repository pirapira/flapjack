(*
  Direct HOL-EVAL probes for the CakeML allocator's SSA/CC temporary numbering
  and frame-slot boundary (bead flapjack-pxn.8.5.14.1.3.1.3).

  Sources (cakeml/compiler/backend/word_allocScript.sml):
    even_list             line 38
    list_next_var_rename  line 47
    setup_ssa             line 1808
    limit_var             line 1816
    full_ssa_cc_trans     line 1822
    ssa_cc_trans          line 347

  limit_var sets the fresh-name base; setup_ssa renames the n incoming
  parameter registers to the next available even names and returns the
  Move1 prologue; full_ssa_cc_trans composes them and runs the SSA/CC
  renaming.  The temporary slots that eventually occupy frame words are
  numbered from this base, so these observations anchor the frame-occupancy
  port to the original.
*)
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
    print_term (rconc th);
    print "\n"
  end

(* Two small 64-bit Word programs. *)
val _ = print_eval "limit_skip" ``limit_var (Skip:64 wordLang$prog)``
val _ = print_eval "limit_two_assigns"
  ``limit_var (Seq (Assign 0 (Const (0w:64 word)))
    (Assign 2 (Var 0)):64 wordLang$prog)``

(* setup_ssa returns (Move1 prologue, renamed-name map, next fresh name). *)
val _ = print_eval "setup_two_empty"
  ``setup_ssa 2 5 (Skip:64 wordLang$prog)``
val _ = print_eval "setup_two_next"
  ``setup_ssa 2 (limit_var (Seq (Assign 0 (Const (0w:64 word)))
    (Assign 2 (Var 0)):64 wordLang$prog))
    (Seq (Assign 0 (Const (0w:64 word))) (Assign 2 (Var 0)):64 wordLang$prog)``

(* full_ssa_cc_trans: the composed prologue + renamed program. *)
val _ = print_eval "full_two_assigns"
  ``full_ssa_cc_trans 2 (Seq (Assign 0 (Const (0w:64 word)))
    (Assign 2 (Var 0)):64 wordLang$prog)``
val _ = print_eval "full_skip"
  ``full_ssa_cc_trans 2 (Skip:64 wordLang$prog)``