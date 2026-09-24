load "bossLib";
load "preamble";
load "listTheory";
load "mlstringTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let val th = EVAL q in
    (print (label ^ "="); print_term (rconc th); print "\n")
  end;

(* HOL `map_map2_fst` (crep_to_loopProofScript.sml:3799): projecting FST of the
   pointwise MAP2 wrapper recovers the first list when the lengths agree. *)
val _ = print_eval "mm2_pair_eq"
  (``MAP FST
      (MAP2 (λx (n,p,b). (x, GENLIST I (LENGTH p), (λ(p:num list) (b:mlstring). T) p b))
        ([1;2]:num list)
        ([(0,[],«a»); (1,[7;8],«b»)] : (num # num list # mlstring) list))
      = [1;2]``);

val _ = print_eval "mm2_empty"
  (``MAP FST
      (MAP2 (λx (n,p,b). (x, GENLIST I (LENGTH p), (λ(p:num list) (b:mlstring). T) p b))
        ([]:num list)
        ([] : (num # num list # mlstring) list))
      = []``);
