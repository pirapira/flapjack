import Flapjack.Parser

/-!
The Pancake static-checker examples, as a parser corpus.

`cakeml/pancake/static_checker/panStaticExamplesScript.sml` exists to exercise
the static checker, but it asserts `check_parse_success` on every example
first -- its own comment is "All examples should parse" -- which makes it a
much larger parser corpus than the concrete-syntax file: 276 programs against
38, covering shapes, structs, exceptions, shared memory, calls and handlers in
combinations the concrete examples do not reach.

The examples are here rather than in `Flapjack/Test/Parser.lean` to keep that
file readable; it holds the hand-written structural checks. Only *parsing* is
asserted. Whether Flapjack's own `staticCheck` agrees with upstream's verdict
on each program is a question about `Flapjack/Static.lean`, not about the
parser, so it is not asserted here.
-/

namespace Flapjack.Test.ParserStaticExamples

open Flapjack Flapjack.Parser

abbrev ofI : Int → Int := fun value => value

def accepts (source : String) : Bool :=
  (parseTopDecs ofI source).toOption.isSome

def rejects (source : String) : Bool :=
  (parseTopDecs ofI source).toOption.isNone

/-! ### Programs upstream marks `check_parse_success` -/


-- ex_arg_main
#guard accepts "\n  fun 1 main (1 a) {\n    return 1;\n  }\n"
-- ex_export_main
#guard accepts "\n  export fun 1 main () {\n    return 1;\n  }\n"
-- ex_export_4_arg
#guard accepts "\n  export fun 1 f (1 a, 1 b, 1 c, 1 d, 1 e) {\n    return 1;\n  }\n"
-- ex_empty_fun
#guard accepts "\n  fun 1 f () {}\n"
-- ex_no_ret_fun
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    x = 1;\n  }\n"
-- ex_while_ret_fun
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      return 1;\n    }\n  }\n"
-- ex_half_if_ret_fun
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    if true {\n      return 1;\n    } else {\n      x = 1;\n    }\n  }\n"
-- ex_full_if_ret_fun
#guard accepts "\n  fun 1 f () {\n    if true {\n      return 1;\n    } else {\n      return 1;\n    }\n  }\n"
-- ex_rogue_break
#guard accepts "\n  fun 1 f () {\n    break;\n    return 1;\n  }\n"
-- ex_rogue_continue
#guard accepts "\n  fun 1 f () {\n    continue;\n    return 1;\n  }\n"
-- ex_func_correct_num_args
#guard accepts "\n  fun 1 f () {\n    g(1, 2, 3);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b, 1 c) {\n    return 1;\n  }\n"
-- ex_func_no_args
#guard accepts "\n  fun 1 f () {\n    g();\n    return 1;\n  }\n  fun 1 g (1 a, 1 b, 1 c) {\n    return 1;\n  }\n"
-- ex_func_missing_args
#guard accepts "\n  fun 1 f () {\n    g(1);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b, 1 c) {\n    return 1;\n  }\n"
-- ex_func_extra_args
#guard accepts "\n  fun 1 f () {\n    g(1, 2, 3, 4);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b, 1 c) {\n    return 1;\n  }\n"
-- ex_stmt_after_ret
#guard accepts "\n  fun 1 f () {\n    return 1;\n    skip;\n  }\n"
-- ex_stmt_after_retcall
#guard accepts "\n  fun 1 f () {\n    return f();\n    skip;\n  }\n"
-- ex_stmt_after_raise
#guard accepts "\n  exception Err : 1;\n\n  fun 1 f () {\n    throw Err 1;\n    skip;\n  }\n"
-- ex_annot_after_ret
#guard accepts "\n  fun 1 f () {\n    return 1;\n    /@ annot @/\n  }\n"
-- ex_stmt_after_annot_after_ret
#guard accepts "\n  fun 1 f () {\n    return 1;\n    /@ annot @/\n    skip;\n  }\n"
-- ex_stmt_after_inner_ret
#guard accepts "\n  fun 1 f () {\n    {\n      var 1 x = 12;\n      return x;\n    };\n    skip;\n  }\n"
-- ex_stmt_after_always_ret
#guard accepts "\n  fun 1 f () {\n    if true {\n      return 1;\n    } else {\n      return 1;\n    }\n    skip;\n  }\n"
-- ex_stmt_after_maybe_ret
#guard accepts "\n  fun 1 f () {\n    if true {\n      return 1;\n    } else {\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_loop_ret
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      return 1;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_brk
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      break;\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_cont
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      continue;\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_inner_brk
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      {\n        var 1 x = 0;\n        break;\n      };\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_always_brk
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      if true {\n        break;\n      } else {\n        break;\n      }\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_stmt_after_maybe_brk
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      if true {\n        break;\n      } else {\n        skip;\n      }\n      break;\n    }\n    return 1;\n  }\n"
-- ex_maybe_stmt_after_always_brk
#guard accepts "\n  fun 1 f () {\n    while (1) {\n      if true {\n        break;\n        skip;\n      } else {\n        break;\n      }\n    }\n    return 1;\n  }\n"
-- ex_local_word_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 x = lds 1 0;\n    st 0, x;\n\n    return 1;\n  }\n"
-- ex_local_byte_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 x = ld8 0;\n    st8 0, x;\n\n    return 1;\n  }\n"
-- ex_local_word_based
#guard accepts "\n  fun 1 f () {\n    var 1 x = lds 1 @base;\n    st @base, x;\n\n    return 1;\n  }\n"
-- ex_local_byte_based
#guard accepts "\n  fun 1 f () {\n    var 1 x = ld8 @base;\n    st8 @base, x;\n\n    return 1;\n  }\n"
-- ex_local_word_field_notbased
#guard accepts "\n  fun 1 f () {\n    var 2 x = <0, 0>;\n    var 1 y = lds 1 x.0;\n    st x.0, y;\n\n    return 1;\n  }\n"
-- ex_local_word_field_based
#guard accepts "\n  fun 1 f () {\n    var 2 x = <@base, 0>;\n    var 1 y = lds 1 x.0;\n    st x.0, y;\n\n    return 1;\n  }\n"
-- ex_local_word_arg
#guard accepts "\n  fun 1 f (1 a) {\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_local
#guard accepts "\n  fun 1 f () {\n    var 1 a = (lds 1 @base);\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_shared
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    !ldw a, 0;\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_always_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = @base;\n    } else {\n      a = @base;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_else_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = 0;\n    } else {\n      a = @base;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_based_while_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = @base;\n    while (1) {\n      a = @base;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_notbased_while_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    while (1) {\n      a = @base;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_always_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = 0;\n    } else {\n      a = 0;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_else_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = @base;\n    } else {\n      a = 0;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_notbased_while_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    while (1) {\n      a = 0;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_local_word_based_while_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = @base;\n    while (1) {\n      a = 0;\n    }\n\n    var 1 x = lds 1 a;\n    st a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    !ldw x, 0;\n    !stw 0, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_based
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    !ldw x, @base;\n    !stw @base, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_field_notbased
#guard accepts "\n  fun 1 f () {\n    var 2 x = <0, 0>;\n    var 1 y = 0;\n    !ldw y, x.0;\n    !stw x.0, y;\n\n    return 1;\n  }\n"
-- ex_shared_word_field_based
#guard accepts "\n  fun 1 f () {\n    var 2 x = <@base, 0>;\n    var 1 y = 0;\n    !ldw y, x.0;\n    !stw x.0, y;\n\n    return 1;\n  }\n"
-- ex_shared_word_arg
#guard accepts "\n  fun 1 f (1 a) {\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_local
#guard accepts "\n  fun 1 f () {\n    var 1 a = (lds 1 @base);\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_shared
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    !ldw a, 0;\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_always_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = @base;\n    } else {\n      a = @base;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_else_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = 0;\n    } else {\n      a = @base;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_based_while_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = @base;\n    while (1) {\n      a = @base;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_notbased_while_based
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    while (1) {\n      a = @base;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_always_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = 0;\n    } else {\n      a = 0;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_else_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    if (1) {\n      a = @base;\n    } else {\n      a = 0;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_notbased_while_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = 0;\n    while (1) {\n      a = 0;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_shared_word_based_while_notbased
#guard accepts "\n  fun 1 f () {\n    var 1 a = @base;\n    while (1) {\n      a = 0;\n    }\n\n    var 1 x = 0;\n    !ldw x, a;\n    !stw a, x;\n\n    return 1;\n  }\n"
-- ex_undefined_fun_standalone
#guard accepts "\n  fun 1 f () {\n    foo();\n    return 1;\n  }\n"
-- ex_undefined_fun_dec
#guard accepts "\n  fun 1 f () {\n    var 1 x = foo();\n    return 1;\n  }\n"
-- ex_undefined_fun_assign
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    x = foo();\n    return 1;\n  }\n"
-- ex_undefined_fun_tail
#guard accepts "\n  fun 1 f () {\n    return foo();\n  }\n"
-- ex_undefined_struct_field
#guard accepts "\n  struct first_struct {\n    second_struct s\n  }\n\n  struct second_struct {\n    1 x\n  }\n"
-- ex_defined_struct_field
#guard accepts "\n  struct first_struct {\n    1 x\n  }\n\n  struct second_struct {\n    first_struct s\n  }\n"
-- ex_undefined_struct_param
#guard accepts "\n  fun 1 f (my_struct a) {\n    return 1;\n  }\n"
-- ex_undefined_struct_return
#guard accepts "\n  fun my_struct f (1 a) {\n    return 1;\n  }\n"
-- ex_undefined_struct_local
#guard accepts "\n  fun 1 f (1 a) {\n    var my_struct x = 1;\n    return 1;\n  }\n"
-- ex_undefined_struct_global
#guard accepts "\n  var my_struct x = 1;\n"
-- ex_undefined_struct_load
#guard accepts "\n  fun 1 f (1 a) {\n    return lds my_struct @base;\n  }\n"
-- ex_undefined_struct_constant
#guard accepts "\n  fun 1 f (1 a) {\n    return my_struct <value = 1>;\n  }\n"
-- ex_func_global_order
#guard accepts "\n  var my_struct x = my_struct <value = 1>;\n\n  fun my_struct f (my_struct a) {\n    var my_struct y = x;\n    y = lds my_struct @base;\n    return a;\n  }\n\n  struct my_struct {\n    1 value\n  }\n"
-- ex_undefined_var
#guard accepts "\n  fun 1 f () {\n    return x;\n  }\n"
-- ex_self_referential_global
#guard accepts "\n  var 1 x = x;\n"
-- ex_well_scoped_globals
#guard accepts "\n  var 1 x = 1;\n  var 1 y = x;\n  var 1 z = x + y;\n"
-- ex_global_function_order
#guard accepts "\n  fun 1 f() { return x; }\n  var 1 x = 1;\n"
-- ex_redefined_fun
#guard accepts "\n  fun 1 f () {\n    return 1;\n  }\n  fun 1 f () {\n    return 1;\n  }\n"
-- ex_repeat_params
#guard accepts "\n  fun 1 f (1 a, 1 b, 1 c, 1 a) {\n    return 1;\n  }\n"
-- ex_redefined_struct
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct my_struct {\n    1 other_value\n  }\n"
-- ex_repeat_field
#guard accepts "\n  struct my_struct {\n    1 value,\n    1 other_value,\n    1 value\n  }\n"
-- ex_redefined_var_dec_dec
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    var 1 x = 0;\n    return 1;\n  }\n"
-- ex_redefined_var_dec_deccall
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    var 1 x = f();\n    return 1;\n  }\n"
-- ex_redefined_var_deccall_dec
#guard accepts "\n  fun 1 f () {\n    var 1 x = f();\n    var 1 x = 0;\n    return 1;\n  }\n"
-- ex_redefined_var_deccall_deccall
#guard accepts "\n  fun 1 f () {\n    var 1 x = f();\n    var 1 x = f();\n    return 1;\n  }\n"
-- ex_redefined_global_var
#guard accepts "\n  var 1 x = 1;\n  var 1 x = 1;\n"
-- ex_redefined_global_var_locally
#guard accepts "\n  var 1 x = 1;\n  fun 1 f() {\n    var 1 x = 1;\n    return x;\n  }\n"
-- ex_redefined_global_var_deccall
#guard accepts "\n  var 1 x = 1;\n  fun 1 f() {\n    var 1 x = f();\n    return x;\n  }\n"
-- ex_local_decl_word_match
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    return 1;\n  }\n"
-- ex_local_decl_word_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var 1 x = <1>;\n    return 1;\n  }\n"
-- ex_local_decl_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_decl_rstruct_match
#guard accepts "\n  fun 1 f () {\n    var {1} x = <1>;\n    return 1;\n  }\n"
-- ex_local_decl_rstruct_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var {1} x = 1;\n    return 1;\n  }\n"
-- ex_local_decl_rstruct_mismatch_2
#guard accepts "\n  fun 1 f () {\n    var {1} x = <1, 1>;\n    return 1;\n  }\n"
-- ex_local_decl_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var {1} x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_decl_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_decl_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = 1;\n    return 1;\n  }\n"
-- ex_local_decl_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = <1>;\n    return 1;\n  }\n"
-- ex_local_decl_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = My_Struct <value = 1>;\n    return 1;\n  }\n"
-- ex_global_decl_word_match
#guard accepts "\n  var 1 x = 1;\n"
-- ex_global_decl_word_mismatch_1
#guard accepts "\n  var 1 x = <1>;\n"
-- ex_global_decl_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  var 1 x = my_struct <value = 1>;\n"
-- ex_global_decl_rstruct_match
#guard accepts "\n  var {1} x = <1>;\n"
-- ex_global_decl_rstruct_mismatch_1
#guard accepts "\n  var {1} x = 1;\n"
-- ex_global_decl_rstruct_mismatch_2
#guard accepts "\n  var {1} x = <1, 1>;\n"
-- ex_global_decl_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  var {1} x = my_struct <value = 1>;\n"
-- ex_global_decl_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  var my_struct x = my_struct <value = 1>;\n"
-- ex_global_decl_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  var my_struct x = 1;\n"
-- ex_global_decl_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  var my_struct x = <1>;\n"
-- ex_global_decl_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  var my_struct x = My_Struct <value = 1>;\n"
-- ex_local_asgn_word_match
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    x = 1;\n    return 1;\n  }\n"
-- ex_local_asgn_word_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    x = <1>;\n    return 1;\n  }\n"
-- ex_local_asgn_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 0;\n    x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_asgn_rstruct_match
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    x = <1>;\n    return 1;\n  }\n"
-- ex_local_asgn_rstruct_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    x = 1;\n    return 1;\n  }\n"
-- ex_local_asgn_rstruct_mismatch_2
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    x = <1, 1>;\n    return 1;\n  }\n"
-- ex_local_asgn_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var {1} x = <0>;\n    x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_asgn_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct < value = 0 >;\n    x = my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_asgn_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct < value = 0 >;\n    x = 1;\n    return 1;\n  }\n"
-- ex_local_asgn_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct < value = 0 >;\n    x = <1>;\n    return 1;\n  }\n"
-- ex_local_asgn_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct < value = 0 >;\n    x = My_Struct <value = 1>;\n    return 1;\n  }\n"
-- ex_func_arg_word_match
#guard accepts "\n  fun 1 f () {\n    g(1, 1);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b) {\n    return 1;\n  }\n"
-- ex_func_arg_word_mismatch_1
#guard accepts "\n  fun 1 f () {\n    g(1, <1>);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b) {\n    return 1;\n  }\n"
-- ex_func_arg_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, my_struct <value = 1>);\n    return 1;\n  }\n  fun 1 g (1 a, 1 b) {\n    return 1;\n  }\n"
-- ex_func_arg_rstruct_match
#guard accepts "\n  fun 1 f () {\n    g(1, <1>);\n    return 1;\n  }\n  fun 1 g (1 a, {1} b) {\n    return 1;\n  }\n"
-- ex_func_arg_rstruct_mismatch_1
#guard accepts "\n  fun 1 f () {\n    g(1, 1);\n    return 1;\n  }\n  fun 1 g (1 a, {1} b) {\n    return 1;\n  }\n"
-- ex_func_arg_rstruct_mismatch_2
#guard accepts "\n  fun 1 f () {\n    g(1, <1, 1>);\n    return 1;\n  }\n  fun 1 g (1 a, {1} b) {\n    return 1;\n  }\n"
-- ex_func_arg_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, my_struct <value = 1>);\n    return 1;\n  }\n  fun 1 g (1 a, {1} b) {\n    return 1;\n  }\n"
-- ex_func_arg_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, my_struct <value = 1>);\n    return 1;\n  }\n  fun 1 g (1 a, my_struct b) {\n    return 1;\n  }\n"
-- ex_func_arg_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, 1);\n    return 1;\n  }\n  fun 1 g (1 a, my_struct b) {\n    return 1;\n  }\n"
-- ex_func_arg_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, <1>);\n    return 1;\n  }\n  fun 1 g (1 a, my_struct b) {\n    return 1;\n  }\n"
-- ex_func_arg_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    g(1, My_Struct <value = 1>);\n    return 1;\n  }\n  fun 1 g (1 a, my_struct b) {\n    return 1;\n  }\n"
-- ex_func_ret_word_match
#guard accepts "\n  fun 1 f () {\n    return 1;\n  }\n"
-- ex_func_ret_word_mismatch_1
#guard accepts "\n  fun 1 f () {\n    return <1>;\n  }\n"
-- ex_func_ret_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1>;\n  }\n"
-- ex_func_ret_rstruct_match
#guard accepts "\n  fun {1} f () {\n    return <1>;\n  }\n"
-- ex_func_ret_rstruct_mismatch_1
#guard accepts "\n  fun {1} f () {\n    return 1;\n  }\n"
-- ex_func_ret_rstruct_mismatch_2
#guard accepts "\n  fun {1} f () {\n    return <1, 1>;\n  }\n"
-- ex_func_ret_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun {1} f () {\n    return my_struct <value = 1>;\n  }\n"
-- ex_func_ret_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun my_struct f () {\n    return my_struct <value = 1>;\n  }\n"
-- ex_func_ret_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun my_struct f () {\n    return 1;\n  }\n"
-- ex_func_ret_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun my_struct f () {\n    return <1>;\n  }\n"
-- ex_func_ret_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun my_struct f () {\n    return My_Struct <value = 1>;\n  }\n"
-- ex_field_val_word_match
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <x = 1, y = 1>;\n"
-- ex_field_val_word_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <x = 1, y = <1> >;\n"
-- ex_field_val_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  struct other_struct {\n    1 value\n  }\n\n  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;\n"
-- ex_field_val_rstruct_match
#guard accepts "\n  struct my_struct {\n    1 x,\n    {1} y\n  }\n\n  var my_struct s = my_struct <x = 1, y = <1> >;\n"
-- ex_field_val_rstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 x,\n    {1} y\n  }\n\n  var my_struct s = my_struct <x = 1, y = 1>;\n"
-- ex_field_val_rstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 x,\n    {1} y\n  }\n\n  var my_struct s = my_struct <x = 1, y = <1, 1> >;\n"
-- ex_field_val_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 x,\n    {1} y\n  }\n\n  struct other_struct {\n    1 value\n  }\n\n  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;\n"
-- ex_field_val_nstruct_match
#guard accepts "\n  struct your_struct {\n    1 value\n  }\n\n  struct my_struct {\n    1 x,\n    your_struct y\n  }\n\n  var my_struct s = my_struct <x = 1, y = your_struct <value = 1> >;\n"
-- ex_field_val_nstruct_mismatch_1
#guard accepts "\n  struct your_struct {\n    1 value\n  }\n\n  struct my_struct {\n    1 x,\n    your_struct y\n  }\n\n  var my_struct s = my_struct <x = 1, y = 1>;\n"
-- ex_field_val_nstruct_mismatch_2
#guard accepts "\n  struct your_struct {\n    1 value\n  }\n\n  struct my_struct {\n    1 x,\n    your_struct y\n  }\n\n  var my_struct s = my_struct <x = 1, y = <1> >;\n"
-- ex_field_val_nstruct_mismatch_3
#guard accepts "\n  struct your_struct {\n    1 value\n  }\n\n  struct my_struct {\n    1 x,\n    your_struct y\n  }\n\n  struct other_struct {\n    1 value\n  }\n\n  var my_struct s = my_struct <x = 1, y = other_struct <value = 1> >;\n"
-- ex_struct_field_missing
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <x = 1>;\n"
-- ex_struct_field_extra
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <x = 1, y = 1, z = 1>;\n"
-- ex_struct_field_duplicate
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <x = 1, y = 1, x = 1>;\n"
-- ex_struct_field_reordered
#guard accepts "\n  struct my_struct {\n    1 x,\n    1 y\n  }\n\n  var my_struct s = my_struct <y = 1, x = 1>;\n"
-- ex_local_lds_word_match
#guard accepts "\n  fun 1 f () {\n    var 1 x = lds 1 @base;\n    return 1;\n  }\n"
-- ex_local_lds_word_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var {1} x = lds 1 @base;\n    return 1;\n  }\n"
-- ex_local_lds_word_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = lds 1 @base;\n    return 1;\n  }\n"
-- ex_local_lds_rstruct_match
#guard accepts "\n  fun 1 f () {\n    var {1} x = lds {1} @base;\n    return 1;\n  }\n"
-- ex_local_lds_rstruct_mismatch_1
#guard accepts "\n  fun 1 f () {\n    var 1 x = lds {1} @base;\n    return 1;\n  }\n"
-- ex_local_lds_rstruct_mismatch_2
#guard accepts "\n  fun 1 f () {\n    var 2 x = lds {1} @base;\n    return 1;\n  }\n"
-- ex_local_lds_rstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = lds {1} @base;\n    return 1;\n  }\n"
-- ex_local_lds_nstruct_match
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = lds my_struct @base;\n    return 1;\n  }\n"
-- ex_local_lds_nstruct_mismatch_1
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = lds my_struct @base;\n    return 1;\n  }\n"
-- ex_local_lds_nstruct_mismatch_2
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var {1} x = lds my_struct @base;\n    return 1;\n  }\n"
-- ex_local_lds_nstruct_mismatch_3
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var My_Struct x = lds my_struct @base;\n    return 1;\n  }\n"
-- ex_local_ld8_word_dest
#guard accepts "\n  fun 1 f () {\n    var 1 x = ld8 @base;\n    return 1;\n  }\n"
-- ex_local_ld8_rstruct_dest
#guard accepts "\n  fun 1 f () {\n    var {1} x = ld8 @base;\n    return 1;\n  }\n"
-- ex_local_ld8_nstruct_dest
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = ld8 @base;\n    return 1;\n  }\n"
-- ex_shared_ldw_word_dest
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    !ldw x, 0;\n    return 1;\n  }\n"
-- ex_shared_ldw_rstruct_dest
#guard accepts "\n  fun 1 f () {\n    var {1} x = <1>;\n    !ldw x, 0;\n    return 1;\n  }\n"
-- ex_shared_ldw_nstruct_dest
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 1>;\n    !ldw x, 0;\n    return 1;\n  }\n"
-- ex_shared_stw_word_src
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    !stw 0, x;\n    return 1;\n  }\n"
-- ex_shared_stw_rstruct_src
#guard accepts "\n  fun 1 f () {\n    var {1} x = <1>;\n    !stw 0, x;\n    return 1;\n  }\n"
-- ex_shared_stw_nstruct_src
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 1>;\n    !stw 0, x;\n    return 1;\n  }\n"
-- ex_main_rstruct_ret
#guard accepts "\n  fun {1} main () {\n    return <1>;\n  }\n"
-- ex_main_nstruct_ret
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun my_struct main () {\n    return my_struct <value = 1>;\n  }\n"
-- ex_ffi_rstruct_lit_arg
#guard accepts "\n  fun 1 f () {\n    @g(1, 2, 3, <4>);\n    return 1;\n  }\n"
-- ex_ffi_rstruct_var_arg
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    @g(1, x, 3, 4);\n    return 1;\n  }\n"
-- ex_ffi_nstruct_lit_arg
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    @g(1, 2, 3, my_struct <value = 4>);\n    return 1;\n  }\n"
-- ex_ffi_nstruct_var_arg
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 0>;\n    @g(1, x, 3, 4);\n    return 1;\n  }\n"
-- ex_export_rstruct_arg
#guard accepts "\n  export fun 1 f ({1} a) {\n    return 1;\n  }\n"
-- ex_export_nstruct_arg
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  export fun 1 f (my_struct a) {\n    return 1;\n  }\n"
-- ex_export_rstruct_ret
#guard accepts "\n  export fun {1} f () {\n    return <1>;\n  }\n"
-- ex_export_nstruct_ret
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  export fun my_struct f () {\n    return my_struct <value = 1>;\n  }\n"
-- ex_local_load_rstruct_addr
#guard accepts "\n  fun 1 f () {\n    var 1 x = lds 1 <1>;\n    return 1;\n  }\n"
-- ex_local_load_nstruct_addr
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = lds 1 my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_local_store_rstruct_addr
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    st <1>, x;\n    return 1;\n  }\n"
-- ex_local_store_nstruct_addr
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 1;\n    st my_struct <value = 1>, x;\n    return 1;\n  }\n"
-- ex_shared_load_rstruct_addr
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    !ldw x, <1>;\n    return 1;\n  }\n"
-- ex_shared_load_nstruct_addr
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 1;\n    !ldw x, my_struct <value = 1>;\n    return 1;\n  }\n"
-- ex_shared_store_rstruct_addr
#guard accepts "\n  fun 1 f () {\n    var 1 x = 1;\n    !stw <1>, x;\n    return 1;\n  }\n"
-- ex_shared_store_nstruct_addr
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 1;\n    !stw my_struct <value = 1>, x;\n    return 1;\n  }\n"
-- ex_add_one_rstruct_operand
#guard accepts "\n  fun 1 f () {\n    return 1 + <2>;\n  }\n"
-- ex_add_all_rstruct_operands
#guard accepts "\n  fun 1 f () {\n    return <1> + <2, 3>;\n  }\n"
-- ex_add_one_nstruct_operand
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return 1 + my_struct <value = 2>;\n  }\n"
-- ex_add_all_nstruct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> + My_Struct <value = 3>;\n  }\n"
-- ex_add_both_struct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> + <2, 3>;\n  }\n"
-- ex_mult_one_rstruct_operand
#guard accepts "\n  fun 1 f () {\n    return 1 * <2>;\n  }\n"
-- ex_mult_all_rstruct_operands
#guard accepts "\n  fun 1 f () {\n    return <1> * <2, 3>;\n  }\n"
-- ex_mult_one_nstruct_operand
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return 1 * my_struct <value = 2>;\n  }\n"
-- ex_mult_all_nstruct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> * My_Struct <value = 3>;\n  }\n"
-- ex_mult_both_struct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> * <2, 3>;\n  }\n"
-- ex_shift_rstruct_operand
#guard accepts "\n  fun 1 f () {\n    return <1> << 2;\n  }\n"
-- ex_shift_nstruct_operand
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> << 2;\n  }\n"
-- ex_cmp_word_rstruct_operands
#guard accepts "\n  fun 1 f () {\n    return 0 == <1>;\n  }\n"
-- ex_cmp_word_nstruct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return 0 == my_struct <value = 1>;\n  }\n"
-- ex_cmp_rstruct_nstruct_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return <1> == my_struct <value = 1>;\n  }\n"
-- ex_cmp_diff_rstructs_operands
#guard accepts "\n  fun 1 f () {\n    return <1> == <2, 3>;\n  }\n"
-- ex_cmp_diff_nstructs_operands
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct My_Struct {\n    1 value\n  }\n\n  fun 1 f () {\n    return my_struct <value = 1> == My_Struct <value = 1>;\n  }\n"
-- ex_if_cond_rstruct
#guard accepts "\n  fun 1 f () {\n    if <1> {\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_if_cond_nstruct
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    if my_struct <value = 1> {\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_while_cond_rstruct
#guard accepts "\n  fun 1 f () {\n    while <1> {\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_while_cond_nstruct
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    while my_struct <value = 1> {\n      skip;\n    }\n    return 1;\n  }\n"
-- ex_valid_rstruct_lit_index
#guard accepts "\n  fun 1 f () {\n    var 1 x = <0>.0;\n    return 1;\n  }\n"
-- ex_valid_rstruct_var_index
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    var 1 y = x.0;\n    return 1;\n  }\n"
-- ex_invalid_rstruct_lit_index
#guard accepts "\n  fun 1 f () {\n    var 1 x = <0>.5;\n    return 1;\n  }\n"
-- ex_invalid_rstruct_var_index
#guard accepts "\n  fun 1 f () {\n    var {1} x = <0>;\n    var 1 y = x.5;\n    return 1;\n  }\n"
-- ex_invalid_word_lit_index
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0.5;\n    return 1;\n  }\n"
-- ex_invalid_word_var_index
#guard accepts "\n  fun 1 f () {\n    var 1 x = 0;\n    var 1 y = x.5;\n    return 1;\n  }\n"
-- ex_invalid_nstruct_lit_index
#guard accepts "\n  struct my_struct {\n    1 value0,\n    1 value1,\n    1 value2,\n    1 value3,\n    1 value4,\n    1 value5\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <\n      value0 = 1,\n      value1 = 1,\n      value2 = 1,\n      value3 = 1,\n      value4 = 1,\n      value5 = 1\n    >.5;\n    return 1;\n  }\n"
-- ex_invalid_nstruct_var_index
#guard accepts "\n  struct my_struct {\n    1 value0,\n    1 value1,\n    1 value2,\n    1 value3,\n    1 value4,\n    1 value5\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <\n      value0 = 1,\n      value1 = 1,\n      value2 = 1,\n      value3 = 1,\n      value4 = 1,\n      value5 = 1\n    >;\n    var 1 y = x.5;\n    return 1;\n  }\n"
-- ex_valid_nstruct_lit_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = my_struct <value = 0>.value;\n    return 1;\n  }\n"
-- ex_valid_nstruct_var_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 0>;\n    var 1 y = x.value;\n    return 1;\n  }\n"
-- ex_invalid_rstruct_lit_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = <0>.value;\n    return 1;\n  }\n"
-- ex_invalid_rstruct_var_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var {1} x = <0>;\n    var 1 y = x.value;\n    return 1;\n  }\n"
-- ex_invalid_word_lit_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 0.value;\n    return 1;\n  }\n"
-- ex_invalid_word_var_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun 1 f () {\n    var 1 x = 0;\n    var 1 y = x.value;\n    return 1;\n  }\n"
-- ex_invalid_nstruct_lit_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct your_struct {\n    1 Value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 1>.Value;\n    return 1;\n  }\n"
-- ex_invalid_nstruct_var_field
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  struct your_struct {\n    1 Value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = 1>;\n    var 1 y = x.Value;\n    return 1;\n  }\n"
-- ex_big_rstruct_var
#guard accepts "\n  fun 1 f () {\n    var 33 x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;\n    return 1;\n  }\n"
-- ex_big_nstruct_var
#guard accepts "\n  struct my_struct {\n    33 value\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <value = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;\n    return 1;\n  }\n"
-- ex_big_nstruct_split_var
#guard accepts "\n  struct my_struct {\n    11 x,\n    22 y\n  }\n\n  fun 1 f () {\n    var my_struct x = my_struct <x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>, y = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;\n    return 1;\n  }\n"
-- ex_big_rstruct_func_ret
#guard accepts "\n  fun 33 f () {\n    return <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>;\n  }\n"
-- ex_big_nstruct_func_ret
#guard accepts "\n  struct my_struct {\n    33 value\n  }\n\n  fun my_struct f () {\n    return my_struct <value = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;\n  }\n"
-- ex_big_nstruct_split_func_ret
#guard accepts "\n  struct my_struct {\n    11 x,\n    22 y\n  }\n\n  fun my_struct f () {\n    return my_struct <x = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0>, y = <0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0> >;\n  }\n"
-- ex_default_all_good
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_local_decl
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = <0>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_global_decl
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = <1>;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_local_deccall
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = bar();\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n  fun {1} bar() {\n    return <0>;\n  }\n"
-- ex_default_bad_rstruct_local_assign
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    x = <1>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_global_assign
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    n = <1>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_local_assigncall
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    x = bar();\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n  fun {1} bar() {\n    return <0>;\n  }\n"
-- ex_default_bad_rstruct_arg
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = foo(<0>);\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_rstruct_return
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = 2>;\n    return <n + a + x>;\n  }\n"
-- ex_default_bad_rstruct_field
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = <2> >;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_local_decl
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = my_struct <value = 0>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_global_decl
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = my_struct <value = 1>;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_local_deccall
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = bar();\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n  fun my_struct bar() {\n    return my_struct <value = 0>;\n  }\n"
-- ex_default_bad_nstruct_local_assign
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    x = my_struct <value = 1>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_global_assign
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    n = my_struct <value = 1>;\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_local_assigncall
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    x = bar();\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n  fun my_struct bar() {\n    return my_struct <value = 0>;\n  }\n"
-- ex_default_bad_nstruct_arg
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = foo(my_struct <value = 0>);\n    var my_struct y = my_struct <value = 2>;\n    return n + a + x;\n  }\n"
-- ex_default_bad_nstruct_return
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = 2>;\n    return my_struct <value = n + a + x>;\n  }\n"
-- ex_default_bad_nstruct_field
#guard accepts "\n  struct my_struct {\n    value\n  }\n  var n = 1;\n  fun foo(a) {\n    var x = 0;\n    var my_struct y = my_struct <value = my_struct <value = 2> >;\n    return n + a + x;\n  }\n"
-- ex_addcarry_ok
#guard accepts "\n  fun {1,1} f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var {1,1} r = __add_with_carry__(a, b, c);\n    r = __add_with_carry__(a, b, c);\n    return r;\n  }\n"
-- ex_addcarry_bad_shape_dec
#guard accepts "\n  fun 1 f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var 1 r = __add_with_carry__(a, b, c);\n    return r;\n  }\n"
-- ex_addcarry_bad_shape_assign
#guard accepts "\n  fun 1 f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var 1 r = 0;\n    r = __add_with_carry__(a, b, c);\n    return r;\n  }\n"
-- ex_addcarry_bad_nstruct_dec
#guard accepts "\n  struct my_struct {\n    1 first,\n    1 second\n  }\n\n  fun my_struct f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var my_struct r = __add_with_carry__(a, b, c);\n    return r;\n  }\n"
-- ex_addcarry_bad_nstruct_assign
#guard accepts "\n  struct my_struct {\n    1 first,\n    1 second\n  }\n\n  fun my_struct f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var my_struct r = my_struct <first = 0, second = 0>;\n    r = __add_with_carry__(a, b, c);\n    return r;\n  }\n"
-- ex_addcarry_arity_low
#guard accepts "\n  fun {1,1} f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var {1,1} r = __add_with_carry__(a, b);\n    return r;\n  }\n"
-- ex_addcarry_arity_high
#guard accepts "\n  fun {1,1} f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    var 1 d = 0;\n    var {1,1} r = __add_with_carry__(a, b, c, d);\n    return r;\n  }\n"
-- ex_addcarry_global_dest
#guard accepts "\n  var {1,1} n = <0, 0>;\n  fun 1 f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    n = __add_with_carry__(a, b, c);\n    return 0;\n  }\n"
-- ex_addcarry_first_rstruct_operand
#guard accepts "\n  fun {1,1} f () {\n    var 1 b = 2;\n    var 1 c = 0;\n    var {1,1} r = __add_with_carry__(<1>, b, c);\n    return r;\n  }\n"
-- ex_addcarry_middle_rstruct_operand
#guard accepts "\n  fun {1,1} f () {\n    var 1 a = 1;\n    var 1 c = 0;\n    var {1,1} r = __add_with_carry__(a, <2>, c);\n    return r;\n  }\n"
-- ex_addcarry_nstruct_operand
#guard accepts "\n  struct my_struct {\n    1 value\n  }\n\n  fun {1,1} f () {\n    var 1 b = 2;\n    var 1 c = 0;\n    var {1,1} r = __add_with_carry__(my_struct <value = 1>, b, c);\n    return r;\n  }\n"
-- ex_not_field
#guard accepts "\n  fun 1 f(2 x) {\n    return !x.0;\n  }\n"
-- ex_exception_shape_mismatch
#guard accepts "\n  exception Err : {1,1};\n\n  fun 1 f () {\n    throw Err 1;\n  }\n"
-- ex_exception_shape_mismatch2
#guard accepts "\n  exception Err : {1,1};\n\n  fun 1 f () {\n    var 1 x = 0;\n    try f()\n    catch Err => x {\n      x = x + 1;\n    }\n    return 0;\n  }\n"
-- ex_undeclared_exception
#guard accepts "\n  fun 1 f () {\n    throw Err 1;\n  }\n"

/-! ### Programs upstream marks `check_parse_failure` -/

-- ex_addcarry_standalone
#guard rejects "\n  fun 1 f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    __add_with_carry__(a, b, c);\n    return 0;\n  }\n"
-- ex_addcarry_tail
#guard rejects "\n  fun {1,1} f () {\n    var 1 a = 1;\n    var 1 b = 2;\n    var 1 c = 0;\n    return __add_with_carry__(a, b, c);\n  }\n"

end Flapjack.Test.ParserStaticExamples
