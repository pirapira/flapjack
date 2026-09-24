(* Direct HOL-EVAL summary oracle for the local flatten quotation in
   cakeml/compiler/backend/stack_to_labScript.sml. *)
load "bossLib";
load "preamble";
load "stack_to_labTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open stack_to_labTheory;

fun print_eval label q =
  let val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end;

val tail_seq = ``stackLang$Seq stackLang$Tick (stackLang$Inst (asm$Skip))``;
val both_skip = ``stackLang$If Equal 1 (Reg 2) stackLang$Skip stackLang$Skip``;
val then_skip = ``stackLang$If Equal 1 (Reg 2) stackLang$Skip stackLang$Tick``;
val else_skip = ``stackLang$If Equal 1 (Reg 2) stackLang$Tick stackLang$Skip``;
val then_terminates = ``stackLang$If Equal 1 (Reg 2) (stackLang$Halt 0) stackLang$Tick``;
val else_terminates = ``stackLang$If Equal 1 (Reg 2) stackLang$Tick (stackLang$Halt 0)``;
val both_live = ``stackLang$If Equal 1 (Reg 2) stackLang$Tick
  (stackLang$Inst (asm$Skip))``;
val loop_if = ``stackLang$Loop
  (stackLang$If Equal 1 (Reg 2) stackLang$Tick stackLang$Tick)``;
val return_call = ``stackLang$Call
  (SOME (stackLang$Tick, 4, 5, 6)) (INR 7) NONE``;
val handled_call = ``stackLang$Call
  (SOME (stackLang$Tick, 4, 5, 6)) (INR 7)
  (SOME (stackLang$Halt 0, 8, 9))``;

val _ = print_eval "flat_skip" ``let (xs, done, next) = flatten F stackLang$Skip 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_tick" ``let (xs, done, next) = flatten F stackLang$Tick 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_inst" ``let (xs, done, next) = flatten F (stackLang$Inst (asm$Skip)) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_halt" ``let (xs, done, next) = flatten F (stackLang$Halt 0) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_seq_tail" ``let (xs, done, next) = flatten T ^tail_seq 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_seq_not_tail" ``let (xs, done, next) = flatten F ^tail_seq 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_both_skip" ``let (xs, done, next) = flatten F ^both_skip 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_then_skip" ``let (xs, done, next) = flatten F ^then_skip 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_else_skip" ``let (xs, done, next) = flatten F ^else_skip 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_then_terminates" ``let (xs, done, next) = flatten F ^then_terminates 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_else_terminates" ``let (xs, done, next) = flatten F ^else_terminates 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_if_both_live" ``let (xs, done, next) = flatten F ^both_live 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_loop_if" ``let (xs, done, next) = flatten F ^loop_if 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_raise" ``let (xs, done, next) = flatten F (stackLang$Raise 4) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_return" ``let (xs, done, next) = flatten F (stackLang$Return 5) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_break" ``let (xs, done, next) = flatten F (stackLang$Break 1) 3 2 [] [4; 9] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_continue" ``let (xs, done, next) = flatten F (stackLang$Continue 0) 3 2 [6] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_raw_call" ``let (xs, done, next) = flatten F (stackLang$RawCall 11) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_call_none_label" ``let (xs, done, next) = flatten F (stackLang$Call NONE (INL 11) NONE) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_call_none_reg" ``let (xs, done, next) = flatten F (stackLang$Call NONE (INR 4) NONE) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_call_return" ``let (xs, done, next) = flatten F ^return_call 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_call_handler" ``let (xs, done, next) = flatten F ^handled_call 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_jump_lower" ``let (xs, done, next) = flatten F (stackLang$JumpLower 1 2 12) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_ffi" ``let (xs, done, next) = flatten F (stackLang$FFI (strlit "ffi") 0 0 0 0 4) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_loc_value" ``let (xs, done, next) = flatten F (stackLang$LocValue 1 2 3) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_install" ``let (xs, done, next) = flatten F (stackLang$Install 0 0 0 0 4) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_shared_memory" ``let (xs, done, next) = flatten F (stackLang$ShMemOp Load 2 (Addr 3 0w)) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_code_buffer_write" ``let (xs, done, next) = flatten F (stackLang$CodeBufferWrite 1 2) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "flat_default" ``let (xs, done, next) = flatten F (stackLang$DataBufferWrite 1 2) 3 2 [] [] in (LENGTH (misc$append xs), done, next)``;
val _ = print_eval "section_skip" ``stack_to_lab$prog_to_section (3, stackLang$Skip)``;
val _ = print_eval "section_seq" ``stack_to_lab$prog_to_section
  (3, stackLang$Seq stackLang$Tick (stackLang$Inst (asm$Skip)))``;
val _ = print_eval "section_if" ``stack_to_lab$prog_to_section
  (3, stackLang$If Equal 1 (Reg 2) stackLang$Tick stackLang$Tick)``;
