(*
  Direct HOL-EVAL observations for the CakeML word_inst normalization and
  instruction-selection boundary (immediate-operand parity slice).

  Sources (cakeml/compiler/backend):
    word_instScript.sml: pull_ops, convert_sub, optimize_consts, reduce_const,
      pull_exp, flatten_exp, inst_select (line 383)

  The probe evaluates the original definitions directly; the Lean tests
  Flapjack/Test/WordInstNormalizeParity.lean and
  Flapjack/Test/RiscVAbiParity.lean consume the checked-in .out.
*)
load "bossLib";
load "preamble";
load "word_instTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open word_instTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

(* pull_exp: reverses the operand list (pull_ops conses). *)
val _ = print_eval "pull_two_vars"
  ``pull_exp ((Op Add [Var (2:num); Var (4:num)]) : 64 wordLang$exp)``
val _ = print_eval "pull_t_plus_1"
  ``pull_exp ((Op Add [Var (7:num); Const (1w:64 word)]) : 64 wordLang$exp)``

(* flatten_exp: head goes last. *)
val _ = print_eval "flat_two_vars"
  ``flatten_exp ((Op Add [Var (2:num); Var (4:num)]) : 64 wordLang$exp)``
val _ = print_eval "flat_pulled_two_vars"
  ``flatten_exp (pull_exp ((Op Add [Var (2:num); Var (4:num)]) : 64 wordLang$exp))``

(* The full normalization pair used by inst_select. *)
val _ = print_eval "norm_two_vars"
  ``(flatten_exp o pull_exp) ((Op Add [Var (2:num); Var (4:num)]) : 64 wordLang$exp)``
val _ = print_eval "norm_t_plus_1"
  ``(flatten_exp o pull_exp) ((Op Add [Var (7:num); Const (1w:64 word)]) : 64 wordLang$exp)``
val _ = print_eval "norm_1_plus_t"
  ``(flatten_exp o pull_exp) ((Op Add [Const (1w:64 word); Var (7:num)]) : 64 wordLang$exp)``
val _ = print_eval "norm_x_minus_8"
  ``(flatten_exp o pull_exp) ((Op Sub [Var (7:num); Const (8w:64 word)]) : 64 wordLang$exp)``
val _ = print_eval "norm_nested_add"
  ``(flatten_exp o pull_exp)
      ((Op Add [Var (1:num); Op Add [Var (2:num); Const (3w:64 word)]]) : 64 wordLang$exp)``
val _ = print_eval "norm_nested_add_consts"
  ``(flatten_exp o pull_exp)
      ((Op Add [Op Add []; Op Or []]) : 64 wordLang$exp)``

(* inst_select: operand materialization order for a two-variable Add. *)
val wi_config = ``((
   <| ISA := RISC_V; encode := ARB; big_endian := F; code_alignment := 0;
      link_reg := SOME 1; avoid_regs := [0;2;3;4;31]; reg_count := 32;
      fp_reg_count := 0; two_reg_arith := F; valid_imm := ARB;
      addr_offset := ARB; hw_offset := ARB; byte_offset := ARB;
      jump_offset := ARB; cjump_offset := ARB; loc_offset := ARB |>) : 64 asm_config)``
val _ = print_eval "inst_assign_two_vars"
  ``inst_select ^wi_config 6
      ((Assign 5 (Op Add [Var (2:num); Var (4:num)])) : 64 wordLang$prog)``
val _ = print_eval "inst_assign_t_plus_1"
  ``inst_select ^wi_config 6
      ((Assign 5 (Op Add [Var (2:num); Const (1w:64 word)])) : 64 wordLang$prog)``

(* convert_sub / optimize_consts / reduce_const direct values. *)
val _ = print_eval "convert_sub_const"
  ``convert_sub ([Op Sub [Var (7:num); Const (8w:64 word)]] : 64 wordLang$exp list)``
val _ = print_eval "optimize_consts_two_consts"
  ``optimize_consts Add
      ([Const (1w:64 word); Const (2w:64 word); Var (3:num)] : 64 wordLang$exp list)``
val _ = print_eval "optimize_consts_zero_add"
  ``optimize_consts Add ([Const (0w:64 word); Var (3:num)] : 64 wordLang$exp list)``
val _ = print_eval "reduce_const_add_zero_tail"
  ``reduce_const Add (0w:64 word) ([Var (3:num)] : 64 wordLang$exp list)``

(* Order diagnostics for pull_ops itself. *)
val _ = print_eval "pullops_two_vars"
  ``pull_ops Add ([Var (2:num); Var (4:num)] : 64 wordLang$exp list) []``
val _ = print_eval "pullops_three_vars"
  ``pull_ops Add ([Var (1:num); Var (2:num); Var (3:num)] : 64 wordLang$exp list) []``
val _ = print_eval "pull_three_vars"
  ``pull_exp ((Op Add [Var (1:num); Var (2:num); Var (3:num)]) : 64 wordLang$exp)``
val _ = print_eval "pull_four_vars"
  ``pull_exp ((Op Add [Var (1:num); Var (2:num); Var (3:num); Var (4:num)]) : 64 wordLang$exp)``
val _ = print_eval "pull_const_middle"
  ``pull_exp ((Op Add [Var (1:num); Const (5w:64 word); Var (3:num)]) : 64 wordLang$exp)``
val _ = print_eval "norm_const_middle"
  ``(flatten_exp o pull_exp)
      ((Op Add [Var (1:num); Const (5w:64 word); Var (3:num)]) : 64 wordLang$exp)``
val _ = print_eval "inst_assign_const_middle"
  ``inst_select ^wi_config 6
      ((Assign 5 (Op Add [Var (1:num); Const (5w:64 word); Var (3:num)])) : 64 wordLang$prog)``

(* resolve the pull_exp/pull_ops composition order *)
val _ = print_eval "opt_two_vars_rev"
  ``optimize_consts Add ([Var (4:num); Var (2:num)] : 64 wordLang$exp list)``
val _ = print_eval "opt_three_vars_rev"
  ``optimize_consts Add ([Var (3:num); Var (2:num); Var (1:num)] : 64 wordLang$exp list)``
val _ = print_eval "pull_two_vars_again"
  ``pull_exp ((Op Add [Var (2:num); Var (4:num)]) : 64 wordLang$exp)``
