# Soundness status

Flapjack is an in-progress Lean 4 port of the CakeML Pancake compiler. This
document records what the current repository does and does not establish. It
is deliberately conservative: a theorem that elaborates and a compiler path
that runs are not, by themselves, evidence that the port is equivalent to the
HOL development or ready for production use.

## Scope

The intended target is Pancake source compiled to RISC-V. Backends other than
RISC-V are out of scope. The CakeML checkout in `cakeml` is the reference for
the ASTs, pass ordering, semantics, compiler, and correctness theorem. The
current source-facing command is documented in the repository README and is
implemented by `Flapjack.CompileMain`.

## What is currently checked

- Lean checks the definitions and proof terms that are present in the tree.
- The repository builds with `lake build Flapjack.lean`.
- `lake test` runs executable regression tests for selected parser, lowering,
  linked-image, and RISC-V encoding cases.
- Selected pass-local theorems cover small source, allocation, Stack, and
  RISC-V fragments. Their statements have not received an independent
  correspondence review against HOL.
- The source-facing compiler reports parse, static-check, entry-point, and
  lowering failures instead of silently treating every unsupported construct as
  compiled code. The default CLI artifact is Pancake-compatible RISC-V
  assembly; `--hex` is an explicitly named compatibility mode for the historical
  raw byte line.

These checks establish useful local properties of the covered fragments. They
do not establish whole-compiler equivalence.

## HOL-to-Lean trust boundary

Similarity to HOL artifacts does not establish equivalence. HOL-to-Lean
equivalence proofs are out of scope; `@[hol]` tags record reviewed provenance,
not equivalence certificates. Lean proofs establish results only about the
Lean definitions in their statements. Those definitions, statements, and their
implications must be evaluated independently of the HOL artifacts; HOL's
assurance does not automatically transfer to Flapjack.

The translation of HOL's choice operators is also an external assumption.
`holOptionSome` and `buildLprefixLub` use Lean's classical choice; in particular,
no cross-language agreement is established for choices on non-chain prefix
families. These already-present definitions do not add a new Lean trust root,
but kernel-checked wrapper theorems do not resolve this translation assumption.

## Explicit limitations

The following are open review or verification obligations:

1. Compiler-correctness theorem porting is in progress.
2. The RISC-V semantics in Flapjack have not been proven equivalent to a Lean
   extraction of the authoritative Sail RISC-V model.
3. Compiler behavior has not been tested extensively against the original
   Pancake compiler. The executable parity suite and differential fuzzer cover
   only a small corpus and do not establish equivalence for arbitrary input.
   This limitation applies to internal and intermediate regression tests as
   well: a test that compares two Lean definitions is not evidence of Pancake
   equivalence. New porting tests must use an original CakeML executable run
   or an original HOL EVAL/probe, and record the exact source definition,
   fixture, comparison boundary, and regeneration command.
4. The compiler does not yet cover every Pancake construct or emit the same
   complete runtime/ELF artifacts as CakeML. The current command emits a
   Pancake-shaped checked RV64I assembly image for its supported source subset;
   `--hex` is the raw-byte compatibility view.
5. Proof work remains for the full source-to-target simulation, runtime image,
   collector/frame-machine behavior, calls and FFI in all configurations, and
   the complete Pancake correctness theorem.
6. Passing `lake build`, `lake test`, or CI proves only the checked repository
   state and selected regressions. It does not review the mathematical
   adequacy of the specifications or prove untested source programs compile
   identically to CakeML.
8. HOL's floating-point library specifies rounding over real numbers. The
   current Lean binary64 arithmetic rendering uses `Rat` for finite float
   values and rational operation inputs. Lean proves its computable
   round-to-nearest-even algorithm agrees with the Lean choice-based
   specification for every rational input, but the correspondence between
   that rational rendering and HOL's real-number specification is a
   source-reviewed external assumption, not a kernel-checked cross-prover
   theorem. The value-component theorems do not establish flag equivalence;
   NaN payload choice remains unspecified. HOL `real_to_float` and
   `real_to_fp64` accept arbitrary reals. The executed path renders them
   only for rational inputs (`holRealToFloat`, `holRealToFp64`); the
   general-real `real_to_float` over Mathlib `ℝ` is `holRealToFloatR`, and
   `holRealToFloatR_ratCast` proves that at every rational argument it equals
   the executed `holRealToFloat` (likewise `round`, `float_round` and
   `float_round_with_flags`, in `Flapjack/Misc/BinaryIeeeSqrt/RealCarrier.lean`).
   The one wordSem
   use, `int_to_fp64`, applies them to integers, which are in scope. The
   WordSem and StackSem `FPSqrt`/`FPToInt`/`FPFromInt` instruction clauses
   are proved equal, with no premise, to the same clauses over the tagged
   Mathlib-real `fp64_sqrt`, `fp64_to_int` and `real_to_fp64` ports
   (`WordSem/Inst/RealSqrtAgreement.lean`, `WordSem/Inst/RealConvertAgreement.lean`,
   `StackSem/FpRegisterInstructions/RealAgreement.lean`). Likewise the executed
   `float_add`/`float_sub`/`float_mul`/`float_div`/`float_mul_add`/`float_compare`
   and their generated fp64 lifts and comparisons are proved equal, for every mode
   and input, to literal Mathlib-real transcriptions
   (`Misc/BinaryIeeeArith/RealCarrier.lean`, `Misc/MachineIeee/ArithReal.lean`), so
   no executed binary64 operation relies on an unproved `Rat`-versus-real step; the
   reading of Mathlib `ℝ` as HOL `real` remains the standard carrier assumption.
   Irrational square-root rounding
   is not covered by these rational-input theorems, and is handled
   separately below.

   `float_sqrt` rounds the real `sqrt r` of a nonnegative rational `r`.
   `Flapjack/Misc/BinaryIeeeSqrt.lean` replaces each HOL comparison against
   `s = sqrt r` with an exact rational criterion:
   - `s ≤ q` iff `0 ≤ q ∧ r ≤ q²`;
   - `s < q` iff `0 < q ∧ r < q²`;
   - `q ≤ s` iff `q ≤ 0 ∨ q² ≤ r`;
   - `q < s` iff `q < 0 ∨ q² < r`;
   - `q = s` iff `0 ≤ q ∧ q² = r`;
   - `|A − s| ≤ |B − s|` iff `A = B`, or `A < B ∧ s ≤ (A+B)/2`, or
     `B < A ∧ (A+B)/2 ≤ s`;
   - `|s| = s`.

   `Misc/BinaryIeeeSqrt/RealAgreement.lean` now kernel-checks the rational-cut
   comparisons against Mathlib's `Real.sqrt`, including distance comparisons,
   and `Misc/BinaryIeeeSqrt/RealCarrier.lean` (with `Misc/MachineIeee/SqrtReal.lean`
   for `fp64_sqrt`) kernel-checks that the executed
   cut `float_sqrt`/`fp64_sqrt` equal literal transcriptions of HOL `round`,
   `float_round`, `float_round_with_flags` and `float_sqrt` over Mathlib `ℝ`
   (with `Real.sqrt`, HOL `abs` and all flag tests kept), for every rounding
   mode and input.
   The agreement of that Lean real specification with HOL's
   real specification remains an external assurance assumption. The fixed
   binary64 `holFp64SqrtR` wrapper has a source-reviewed `@[hol]` tag with
   the conservative IEEE real-representation qualifier; the generic
   zero-width-capable real helpers remain untagged. Consumer agreement proofs
   cover the actual unary evaluator and native WordSem sqrt instruction,
   including missing-register failure. These kernel equalities remove the
   cut-comparison proof gap without proving cross-assistant real equivalence. Lean proves that the
   computable binary64 sqrt equals the cut specification for every rational
   `r ≥ 0` (`holFloatRoundSqrt_rte_fp64`).

   HOL's rounding specification (`float_round_with_flags`, `float_round`,
   `round`, `closest_such`, `is_closest`, `threshold`) inspects its real
   argument only through order, equality and absolute-difference comparisons
   with rationals, including the flag computations, and its rounded value does
   not depend on HOL's choice operator. So the rational and rational-cut
   renderings are a representation of HOL's reals rather than a different
   specification. Every tagged declaration that uses them directly carries
   the `(reals_as_rational_cuts)` qualifier (AGENTS.md): the wordSem
   `inst_def` and the `fpSem` `fp_uop_comp_def`, `fp_bop_comp_def`,
   `fpfma_def`, `fp_cmp_comp_def` and `fp_cmp_def` renderings.
   Declarations stated over those, such as the wordSem `evaluate_def` and
   its theorems, record the inherited assumption in the theorem map
   (`inherits_reals_as_rational_cuts`, checked against a constant-closure
   export). That marker propagates the assumption only; it does not review
   the untagged definitions on the path. The qualifier is a reviewed
   representation, not an equivalence theorem, and does not remove the
   external assumption stated above.

   Every real value these renderings reach is rational except `sqrt r`:
   finite comparisons, the sum, difference, product and nonzero quotient of
   two float values, the fused `x * y + z`, `float_to_int`'s floor, ceiling
   and comparison with `1/2`, and `int_to_fp64` of an integer. Subnormal
   values are dyadic rationals, signed zeros and infinities are decided by
   sign bits and case splits without reals, the value-level `fp64_*`
   operations discard the flags, and no transcendental function is reached.
   NaN results are HOL's choice `float_some_qnan`, rendered by
   `Classical.epsilon` over the same predicate; their payload is unspecified
   in both systems, and this choice rendering is not covered by the
   qualifier.

## Stack bounds and liveness

Compiler correctness does not unconditionally preserve source liveness on a
finite-memory RISC-V machine. HOL's `pan_to_target_compile_semantics`
(`cakeml/pancake/proofs/pan_to_targetProofScript.sml`) gives a precise
source-behavior guarantee only when the statically computed `stack_max` is
known and strictly below the available stack limit. `compile_prog_max` computes
that bound from frame sizes and the call graph; an unknown bound (`NONE`)
does not satisfy the condition.

Otherwise, the theorem uses `extend_with_resource_limit'`: the target may
terminate with `Resource_limit_hit` after a prefix of the source's I/O trace,
even when the source would continue or terminate normally. In particular,
recursive Pancake programs whose stack usage cannot be statically bounded can
exhaust the target stack. The theorem is therefore not an exact liveness or
complete-trace preservation guarantee for such programs; it permits RISC-V
resource exhaustion. Recursion alone is not a proof of exhaustion, and a known
bound must also fit the configured stack. A faithful Lean port must retain
this distinction, not silently strengthen the theorem to exclude out-of-memory
behavior. Flapjack's assembled end-to-end theorem is still unfinished.

## Trust and reproducibility notes

The Lean kernel checks elaborated theorem statements and proof terms.
Elaboration adds implicit arguments, inferred types, and resolved notation
not explicit in the source; the resulting statement may differ from what
the author intended. Some existing concrete
regressions use `native_decide`; their locations are audited by
`scripts/check-native-decide.sh` and the allowlist. This is a repository
engineering policy and should not be confused with an independent review of
the theorem statements or a proof of semantic equivalence to HOL.

## Required next evidence for a stronger claim

Before describing Flapjack as a Pancake-equivalent compiler, the project needs
all of the following:

- an independently reviewed mapping of each ported theorem statement to its
  HOL counterpart;
- systematic RISC-V semantic comparison against the Sail model for the
  instructions and machine state used by the backend;
- differential tests over a substantially representative Pancake corpus,
  comparing parse results, intermediate programs, and final artifacts with
  documented name/label normalization;
- completed source-to-RISC-V and runtime-image correctness proofs for the
  supported RISC-V configuration; and
- explicit coverage/error behavior for every remaining unsupported construct.
