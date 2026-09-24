load "bossLib";
load "preamble";
load "stackLangTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in (print (label ^ "="); print_term (rconc th); print "\n") end;

(* Direct HOL EVAL over the `stackLang$prog` datatype
   (cakeml/compiler/backend/stackLangScript.sml:27-66):

     prog = Skip | Inst ('a inst) | Get num store_name | Set store_name num |
       OpCurrHeap binop num num |
       Call ((prog#num#num#num) option) (num+num) ((prog#num#num) option) |
       Seq prog prog | If cmp num ('a reg_imm) prog prog | Loop prog |
       JumpLower num num num | Alloc num | StoreConsts num num (num option) |
       Raise num | Return num | Break num | Continue num |
       FFI mlstring num num num num num | Tick | LocValue num num num |
       Install num num num num num | ShMemOp memop num ('a addr) |
       CodeBufferWrite num num | DataBufferWrite num num | RawCall num |
       StackAlloc num | StackFree num | StackStore num num |
       StackStoreAny num num | StackLoad num num | StackLoadAny num num |
       StackGetSize num | StackSetSize num | BitmapLoad num num | Halt num

   The declaration is parameterised by a SINGLE shared word type 'a, and its
   FFI field is `mlstring = implode string` (string = char list).  The Lean
   counterpart `Flapjack.Compiler.Encoders.Asm.HolProg width` instantiates the
   generic `StackLang.Prog` with the exact width-indexed asm carriers plus the
   faithful `MlString` carrier (Flapjack/Compiler/Backend/MlString.lean), so it
   shares the one word dimension.  The rows below pin the FFI field and
   representative constructor shapes/fields at the HOL numeral word type 64.

   Provenance: generated from the Flapjack checkout with the coordinator-approved
   read-only prebuilt CakeML/HOL object directory as oracle input, without
   editing that checkout.  `stackLangTheory` is prebuilt in flapjack2/3/4/6:

     CAKEML=/home/zksecurity/flapjack2/cakeml \
       HOL_PROBE_ONLY=stack_lang_prog_carrier_probeScript.sml \
       scripts/hol-probes/regenerate.sh

   Both checkouts are at cakeml submodule HEAD
   857f0d98da8f8a3580f34423338e697809308ede. *)

val _ = print_eval "pg_skip" ``(stackLang$Skip : 64 stackLang$prog)``;
val _ = print_eval "pg_seq"
  ``(stackLang$Seq stackLang$Skip stackLang$Skip : 64 stackLang$prog)``;
val _ = print_eval "pg_inst"
  ``(case (stackLang$Inst (asm$Const 3 (5w : 64 word)) : 64 stackLang$prog) of
       stackLang$Inst (asm$Const r v) => r + w2n v | _ => 0)``;
val _ = print_eval "pg_get"
  ``(case (stackLang$Get 7 (stackLang$Temp (3w : 5 word)) : 64 stackLang$prog) of
       stackLang$Get n _ => n | _ => 0)``;
val _ = print_eval "pg_stackalloc"
  ``(case (stackLang$StackAlloc 4 : 64 stackLang$prog) of
       stackLang$StackAlloc n => n | _ => 0)``;
val _ = print_eval "pg_shmem"
  ``(case (stackLang$ShMemOp asm$Load 3 (asm$Addr 4 (5w : 64 word)) : 64 stackLang$prog) of
       stackLang$ShMemOp _ r (asm$Addr b off) => r + b + w2n off | _ => 0)``;
val _ = print_eval "pg_ffi_len"
  ``(case (stackLang$FFI (strlit [CHR 65; CHR 66]) 1 2 3 4 5 : 64 stackLang$prog) of
       stackLang$FFI s _ _ _ _ _ => LENGTH (explode s) | _ => 0)``;
val _ = print_eval "pg_ffi_explode"
  ``(case (stackLang$FFI (strlit [CHR 65; CHR 66]) 1 2 3 4 5 : 64 stackLang$prog) of
       stackLang$FFI s _ _ _ _ _ => explode s | _ => [])``;
val _ = print_eval "pg_ffi_eq"
  ``((stackLang$FFI (strlit [CHR 65; CHR 66]) 1 2 3 4 5 : 64 stackLang$prog) =
     (stackLang$FFI (strlit [CHR 65; CHR 66]) 1 2 3 4 5 : 64 stackLang$prog))``;