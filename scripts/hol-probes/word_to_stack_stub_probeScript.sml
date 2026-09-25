(* Probe: exact HOL word_to_stack perf_call_prefix/perf_call_suffix and
   raise_stub/store_consts_stub bodies.

   Bead flapjack-pxn.18.5.15.3.21.  Source:
   cakeml/compiler/backend/word_to_stackScript.sml perf_call_prefix_def (:319),
   perf_call_suffix_def (:336), raise_stub_def (:557), store_consts_stub_def
   (:578).

   Oracle provenance: read-only prebuilt checkout /home/zksecurity/flapjack2/cakeml,
   cakeml submodule HEAD 857f0d98da8f8a3580f2333897e0e, word_to_stackScript.sml
   sha256 prefix 3b487de8259affbf.
*)
load "bossLib";
load "preamble";
load "word_to_stackTheory";
open bossLib HolKernel Parse preamble word_to_stackTheory;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

val pcp_eq = ``(((perf_call_prefix 1 2 3 : 64 stackLang$prog)
               = (stackLang$list_Seq [
                   LocValue 3 1 2;
                   Inst (Mem Store 3 (Addr perf_rsp (-8w)));
                   Inst (Mem Store perf_rbp (Addr perf_rsp (-16w)));
                   Inst (Arith (Binop Sub perf_rsp perf_rsp (Imm 16w)));
                   Inst (Arith (Binop Or perf_rbp perf_rsp (Reg perf_rsp)))]
                 : 64 stackLang$prog)) : bool)``;
val pcs_eq = ``(((perf_call_suffix : 64 stackLang$prog)
               = (stackLang$list_Seq [
                   Inst (Mem Load perf_rbp (Addr perf_rsp 0w));
                   Inst (Arith (Binop Add perf_rsp perf_rsp (Imm 16w)))]
                 : 64 stackLang$prog)) : bool)``;
val rs_eq_f = ``(((raise_stub F 3 : 64 stackLang$prog)
               = (Seq (Get 3 Handler)
                   (Seq (StackSetSize 3)
                     (Seq Skip
                       (Seq (StackLoad 3 2)
                         (Seq (Set Handler 3)
                           (Seq (StackLoad 3 1)
                             (Seq (StackFree 3) (Raise 3)))))))
                 : 64 stackLang$prog)) : bool)``;
val rs_eq_t = ``(((raise_stub T 3 : 64 stackLang$prog)
               = (Seq (Get 3 Handler)
                   (Seq (StackSetSize 3)
                     (Seq (stackLang$list_Seq [
                             StackLoad 3 3;
                             Inst (Arith (Binop Or perf_rsp 3 (Reg 3)));
                             StackLoad 3 4;
                             Inst (Arith (Binop Or perf_rbp 3 (Reg 3)))])
                       (Seq (StackLoad 3 2)
                         (Seq (Set Handler 3)
                           (Seq (StackLoad 3 1)
                             (Seq (StackFree 5) (Raise 3)))))))
                 : 64 stackLang$prog)) : bool)``;
val scs_eq = ``(((store_consts_stub 3 : 64 stackLang$prog)
               = (Seq (StoreConsts 3 4 NONE) (Return 0)
                 : 64 stackLang$prog)) : bool)``;
val pcp_top = ``(((perf_call_prefix 1 2 3 : 64 stackLang$prog) = Skip) : bool)``;

val () = print_eval "pcp_eq" pcp_eq;
val () = print_eval "pcs_eq" pcs_eq;
val () = print_eval "rs_eq_f" rs_eq_f;
val () = print_eval "rs_eq_t" rs_eq_t;
val () = print_eval "scs_eq" scs_eq;
val () = print_eval "pcp_top" pcp_top;
