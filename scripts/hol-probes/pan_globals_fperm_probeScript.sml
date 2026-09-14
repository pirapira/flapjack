(* Direct HOL-EVAL fixture for pan_globals$fperm_def. *)
load "bossLib";
load "preamble";
load "pan_globalsTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val _ = print_eval "recursive_control"
  ``pan_globals$fperm «foo» «bar»
      (panLang$Seq
        (panLang$If (panLang$Const 0w)
          (panLang$Call NONE «foo» [])
          (panLang$While (panLang$Const 1w)
            (panLang$Dec «x» panLang$One (panLang$Const 2w)
              (panLang$Call NONE «foo» []))))
        (panLang$Assign panLang$Local «x» (panLang$Const 3w)))``;
val _ = print_eval "handler"
  ``pan_globals$fperm «foo» «bar»
      (panLang$Call (SOME (NONE,
        SOME («E», «exn», panLang$Call NONE «foo» []))) «worker» [])``;
val _ = print_eval "deccall"
  ``pan_globals$fperm «foo» «bar»
      (panLang$DecCall «x» panLang$One «bar» [] panLang$Skip)``;
val _ = print_eval "unchanged"
  ``pan_globals$fperm «foo» «bar»
      (panLang$Return (panLang$Const 9w))``;
