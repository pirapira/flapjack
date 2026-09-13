(*
  Original Pancake panSem FFI-boundary probe for the source fixture
  `@foo(1,2,3,4); return 0;`.  The oracle returns the mutable bytes unchanged,
  so the checked observation is the original semantic I/O event rather than a
  Lean-side host reimplementation.

  Reference: cakeml/pancake/semantics/panSemScript.sml:716-730
  (ExtCall evaluation) and cakeml/semantics/ffi/ffiScript.sml:64-77
  (call_FFI/event construction).
*)
load "bossLib";
load "preamble";
load "../semantics/panSemTheory";
open bossLib;
open HolKernel Parse;
open preamble;
open panSemTheory;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print_term (rconc th);
    print "\n"
  end

val ffi =
  ``<| oracle := (λname. λst. λconf. λbytes.
        case name of
        | ffi$ExtCall «foo» => ffi$Oracle_return st bytes
        | _ => ffi$Oracle_final ffi$FFI_failed);
      ffi_state := ();
      io_events := [] |>``

val s = ``(s:((8),unit) panSem$state)``;
val source_state =
  ``(^s with <| clock := 20;
      memory := ((1w:8 word) =+ panSem$Word (1w:8 word))
        (((2w:8 word) =+ panSem$Word (2w:8 word))
          (((3w:8 word) =+ panSem$Word (3w:8 word))
            (((4w:8 word) =+ panSem$Word (4w:8 word))
              (((5w:8 word) =+ panSem$Word (5w:8 word))
                (((6w:8 word) =+ panSem$Word (6w:8 word))
                  (λa : 8 word. panSem$Word (0w:8 word)))))));
      memaddrs := {1w; 2w; 3w; 4w; 5w; 6w};
      ffi := ^ffi |>)``

val _ = print_eval "ffi_foo_event"
  ``(SND (panSem$evaluate
      (panLang$Seq
        (panLang$ExtCall «foo»
          (panLang$Const (1w:8 word))
          (panLang$Const (2w:8 word))
          (panLang$Const (3w:8 word))
          (panLang$Const (4w:8 word)))
        (panLang$Return (panLang$Const (0w:8 word))),
       ^source_state))).ffi.io_events``
