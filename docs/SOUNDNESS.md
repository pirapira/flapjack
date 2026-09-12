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
- Many pass-local correctness theorems cover selected source, Crepe, Loop,
  Word, Stack, and RISC-V fragments.
- The source-facing compiler reports parse, static-check, entry-point, and
  lowering failures instead of silently treating every unsupported construct as
  compiled code.

These checks establish useful local properties of the covered fragments. They
do not establish whole-compiler equivalence.

## Explicit limitations

The following are open review or verification obligations:

1. The theorem statements in the port have not yet been independently
   reviewed for adequacy against the corresponding Pancake/HOL statements.
   In particular, a true theorem about a weakened predicate can still be too
   weak to serve as the intended compiler-correctness theorem.
2. The RISC-V semantics in Flapjack have not yet been compared systematically
   with the Sail RISC-V model. The HOL reference model is available at
   `/home/zksecurity/HOL/examples/l3-machine-code/riscv/model/riscv.sml` in the
   development environment, but correspondence to Sail is not claimed here.
3. Compiler behavior has not been tested extensively against the original
   Pancake compiler. The current executable parity suite contains only a small
   set of CakeML-derived byte vectors and Lean pipeline goldens; it is not a
   differential test of the full Pancake corpus.
4. The compiler does not yet cover every Pancake construct or emit the same
   complete runtime/assembly/ELF artifacts as CakeML. The current command
   emits a checked raw RV64I byte list for its supported source subset.
5. Proof work remains for the full source-to-target simulation, runtime image,
   collector/frame-machine behavior, calls and FFI in all configurations, and
   the complete Pancake correctness theorem.
6. Passing `lake build`, `lake test`, or CI proves only the checked repository
   state and selected regressions. It does not review the mathematical
   adequacy of the specifications or prove untested source programs compile
   identically to CakeML.

## Trust and reproducibility notes

The normal Lean kernel checks theorem elaboration. Some existing concrete
regressions use `native_decide`; their locations are audited by
`scripts/check-native-decide.sh` and the allowlist. This is a repository
engineering policy and should not be confused with an independent review of
the theorem statements or a proof of semantic equivalence to HOL.

The authoritative reference sources remain under `cakeml/pancake`, including
`pan_to_targetScript.sml` and its proof files. When adding a parity fixture,
record the source program, the exact reference command/output boundary, and
any normalization of labels or names. A fixture that fails against CakeML is a
compiler-parity bug and must remain tracked as high-priority work until fixed
or its reference interpretation is corrected.

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
