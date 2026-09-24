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
val _ = print_eval "ra_moves_coalesce"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4
      [(1,(1:num,5:num))] (reg_alloc$Delta [1] [5;3]) [] LN``;
(* Simple allocation intentionally ignores move preferences before the
   worklist is initialized; keep its full colouring distinct from IRC. *)
val _ = print_eval "ra_simple_moves"
  ``reg_alloc$reg_alloc reg_alloc$Simple (NONE:num sptree$num_map option) 4
      [(1,(1:num,5:num))] (reg_alloc$Delta [1] [5;3]) [] LN``;
(* A fixed physical-register endpoint exercises do_coalesce_real's fixed-x
   branch: x=2 must not receive a degree increment when y=5 is coalesced. *)
val _ = print_eval "ra_fixed_coalesce"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4
      [(1,(2:num,5:num))] (reg_alloc$Delta [2] [5;3]) [] LN``;
val _ = print_eval "ra_moves_self_filtered"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4
      [(1,(1:num,1:num))] (reg_alloc$Delta [1] [5;3]) [] LN``;
val _ = print_eval "ra_forced_edge"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4
      [] (reg_alloc$Delta [1] [5;3]) [(1,5)] LN``;
(* `do_reg_alloc` rebuilds the source move-partner table with
   `moves_to_sp`, then applies `resort_moves` before biased preferences. *)
val _ = print_eval "moves_to_sp_resort"
  ``reg_alloc$resort_moves
      (reg_alloc$moves_to_sp
        [(1:num,(2:num,5:num));(2,(2,7));(3,(2,11))] LN)``;
val _ = print_eval "ra_order_seq"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4 []
      (reg_alloc$Seq (reg_alloc$Delta [9] []) (reg_alloc$Delta [13] [])) [] LN``;
val _ = print_eval "ra_order_clique"
  ``reg_alloc$reg_alloc reg_alloc$IRC (NONE:num sptree$num_map option) 4 []
      (reg_alloc$Delta [9;13] []) [] LN``;
(* A non-NONE source-keyed spill-cost table exercises the cost-sensitive
   do_spill path: with k=1, the middle-cost clique node is selected first. *)
val _ = print_eval "ra_spill_cost"
  ``reg_alloc$reg_alloc reg_alloc$IRC
      (SOME (fromAList [(1,1);(5,100);(9,1)]) : num sptree$num_map option) 1 []
      (reg_alloc$Delta [1;5;9] []) [] LN``;

(* The proof-side node-field accessor is EL under an explicit list bound. *)
val _ = print_eval "node_list_empty_length"
  ``LENGTH ([] : num list) = 0``;
val _ = print_eval "node_list_first"
  ``EL 0 ([7; 11; 13] : num list)``;
val _ = print_eval "node_list_last"
  ``EL 2 ([7; 11; 13] : num list)``;
val _ = print_eval "node_list_last_in_range"
  ``2 < LENGTH ([7; 11; 13] : num list)``;
val _ = print_eval "node_list_out_of_range"
  ``3 < LENGTH ([7; 11; 13] : num list)``;
val _ = print_eval "node_list_lupdate_same"
  ``EL 1 (LUPDATE 99 1 ([7; 11; 13] : num list)) = 99``;
val _ = print_eval "node_list_lupdate_other"
  ``EL 0 (LUPDATE 99 1 ([7; 11; 13] : num list)) = 7``;
val _ = print_eval "node_list_lupdate_length"
  ``LENGTH (LUPDATE 99 1 ([7; 11; 13] : num list)) = 3``;
val _ = print_eval "node_list_lupdate_outside"
  ``LUPDATE 99 3 ([7; 11; 13] : num list) = [7; 11; 13]``;
