(* Direct HOL-EVAL fixture for reg_alloc$reg_alloc (the full IRC colouring)
   on tiny clash trees, alg = 2 (IRC), no moves, no forced pairs.
   Reference: cakeml/compiler/backend/reg_alloc/reg_allocScript.sml reg_alloc_def. *)
load "bossLib";
load "preamble";
load "reg_allocTheory";
open bossLib;
open HolKernel Parse;
open preamble;

fun print_eval label q =
  let
    val th = EVAL q
  in
    print (label ^ "=");
    print (term_to_string (rconc th));
    print "\n"
  end

(* Two clashing nodes 1 and 3, no stack-only vars, 4 available colours.
   Expected: both nodes coloured from 0..3 with distinct colours. *)
val _ = print_eval "ra_delta_pair"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE :num sptree$num_map option) 4 []
      (reg_alloc$Delta [1] [3]) [] LN``;

(* No clashes at all: every node free to take colour 0. *)
val _ = print_eval "ra_delta_free"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE :num sptree$num_map option) 4 []
      (reg_alloc$Delta [1] [2]) [] LN``;

(* A three-node clique via three deltas sharing names. *)
val _ = print_eval "ra_delta_triangle"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE :num sptree$num_map option) 4 []
      (reg_alloc$Seq (reg_alloc$Delta [1] [3])
         (reg_alloc$Seq (reg_alloc$Delta [3] [5])
            (reg_alloc$Delta [5] [1]))) [] LN``;

(* A stack-only node 7 (4n+3) with a move target: stack-only nodes must not
   consume a colour. *)
val _ = print_eval "ra_stack_only"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE :num sptree$num_map option) 4 []
      (reg_alloc$Delta [7] [1;3]) [] (insert 7 () LN)``;
