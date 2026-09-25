(* Probe: exact HOL word_to_stack handler-argument/caller helpers.

   Bead flapjack-pxn.18.5.15.3.19.  Source:
   cakeml/compiler/backend/word_to_stackScript.sml
     StackHandlerArgs_def (:350), PushHandler_def (:355), PopHandler_def (:378).

   Oracle provenance: read-only prebuilt checkout /home/zksecurity/flapjack2/cakeml,
   cakeml submodule HEAD 857f0d98da8f8a3580f23338e697809308ede,
   word_to_stackScript.sml sha256 prefix 3b487de8259affbf.
*)
load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val shaF = ``((StackHandlerArgs F (INL 4 : (num, num) sum) 7 (2,7,9)
              = StackArgs (INL 4 : (num, num) sum) 7 (2,10,12)) : bool)``;
val shaT = ``((StackHandlerArgs T (INR 4 : (num, num) sum) 7 (2,7,9)
              = StackArgs (INR 4 : (num, num) sum) 7 (2,12,14)) : bool)``;
val phF_top = ``((case PushHandler F 1 2 (3,4,5) of Seq _ _ => T | _ => F) : bool)``;
val phT_top = ``((case PushHandler T 1 2 (3,4,5) of Seq _ _ => T | _ => F) : bool)``;
val phF_eq = ``((PushHandler F 1 2 (3,4,5)
   = Seq (StackAlloc 3)
      (Seq (Inst (Const 3 1w))
        (Seq (StackStore 3 0)
          (Seq (LocValue 3 1 2)
            (Seq (StackStore 3 1)
              (Seq (Get 3 Handler)
                (Seq (StackStore 3 2)
                  (Seq Skip
                    (Seq (StackGetSize 3) (Set Handler 3)))))))))) : bool)``;
val pop_eq = ``((PopHandler F (1,2,3) Skip
   = Seq (StackLoad 1 2)
      (Seq (Set Handler 1) (Seq (StackFree 3) Skip))) : bool)``;

print_eval "shaF" shaF;
print_eval "shaT" shaT;
print_eval "phF_top" phF_top;
print_eval "phT_top" phT_top;
print_eval "phF_eq" phF_eq;
print_eval "pop_eq" pop_eq;
