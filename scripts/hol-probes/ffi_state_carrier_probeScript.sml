load "preamble";
load "ffiTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open ffiTheory;

fun print_eval label q =
  (print label; print "="; print_term (rconc (EVAL q)); print "\n");

(* Small constructions over an 8-bit word carrier and a `num` host state. *)
val osucc = ``\(n:ffiname) (s:num) (c:8 word list) (b:8 word list).
  Oracle_return (s + 1) b``;
val obad = ``\(n:ffiname) (s:num) (c:8 word list) (b:8 word list).
  Oracle_return s (b ++ b)``;
val ofin = ``\(n:ffiname) (s:num) (c:8 word list) (b:8 word list).
  (Oracle_final FFI_diverged : num oracle_result)``;

val st = ``initial_ffi_state ^osucc (0:num)``;

val conf = ``([7w;8w] : 8 word list)``;
val one = ``([1w] : 8 word list)``;

val _ = print_eval "ffi_outcome_failed" ``FFI_failed : ffi_outcome``;
val _ = print_eval "shmem_mappedRead" ``MappedRead : shmem_op``;
val _ = print_eval "ffi_name_extcall" ``ExtCall «f» : ffiname``;
val _ = print_eval "oracle_final_diverged" ``Oracle_final FFI_diverged : num oracle_result``;
val _ = print_eval "initial_state_host" ``(^st).ffi_state``;
val _ = print_eval "initial_state_events" ``(^st).io_events``;
val _ = print_eval "io_event_sizes"
  ``(case (IO_event (ExtCall «f») (^conf) [(1w,2w)] : io_event) of
       IO_event _ out inp => (LENGTH out, LENGTH inp))``;
val _ = print_eval "call_identity"
  ``(case call_FFI ^st (ExtCall «») (^conf) (^one) of
       FFI_return st' bs => (st'.ffi_state = 0) /\ (bs = ^one)
     | FFI_final _ => F)``;
val _ = print_eval "call_ok_host"
  ``(case call_FFI ^st (ExtCall «f») (^conf) (^one) of
       FFI_return st' _ => st'.ffi_state | FFI_final _ => 99)``;
val _ = print_eval "call_ok_events"
  ``(case call_FFI ^st (ExtCall «f») (^conf) (^one) of
       FFI_return st' _ => LENGTH st'.io_events | FFI_final _ => 0)``;
val _ = print_eval "call_ok_bytes"
  ``(case call_FFI ^st (ExtCall «f») (^conf) (^one) of
       FFI_return _ bs => bs | FFI_final _ => [])``;
val _ = print_eval "call_length_failure"
  ``(case call_FFI (initial_ffi_state ^obad (0:num)) (ExtCall «f») (^conf) (^one) of
       FFI_return _ _ => F
     | FFI_final (Final_event _ _ _ oc) => oc = FFI_failed)``;
val _ = print_eval "call_final_event"
  ``(case call_FFI (initial_ffi_state ^ofin (0:num)) (ExtCall «f») (^conf) (^one) of
       FFI_return _ _ => F
     | FFI_final (Final_event _ _ _ oc) => oc = FFI_diverged)``;
val _ = print_eval "shmem_mappedWrite" ``MappedWrite : shmem_op``;
val _ = print_eval "call_shmem_ok_host"
  ``(case call_FFI ^st (SharedMem MappedRead) (^conf) (^one) of
       FFI_return st' _ => st'.ffi_state | FFI_final _ => 99)``;
val _ = print_eval "call_shmem_ok_events"
  ``(case call_FFI ^st (SharedMem MappedRead) (^conf) (^one) of
       FFI_return st' _ => LENGTH st'.io_events | FFI_final _ => 0)``;
val _ = print_eval "call_shmem_ok_bytes"
  ``(case call_FFI ^st (SharedMem MappedRead) (^conf) (^one) of
       FFI_return _ bs => bs | FFI_final _ => [])``;
val _ = print_eval "call_shmem_length_failure"
  ``(case call_FFI (initial_ffi_state ^obad (0:num)) (SharedMem MappedWrite) (^conf) (^one) of
       FFI_return _ _ => F
     | FFI_final (Final_event _ _ _ oc) => oc = FFI_failed)``;
val _ = print_eval "call_shmem_final_event"
  ``(case call_FFI (initial_ffi_state ^ofin (0:num)) (SharedMem MappedRead) (^conf) (^one) of
       FFI_return _ _ => F
     | FFI_final (Final_event _ _ _ oc) => oc = FFI_diverged)``;
