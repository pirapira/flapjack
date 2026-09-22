#!/usr/bin/env python3
"""Check the original-Cake allocator witnesses for exact RISC-V bytes.

These fixtures exercise distinct allocator/frame shapes: dead-raise
allocation, colour permutation, returned-value allocation, 64-bit
register pressure, and a stack-allocation boundary.  Keep the list explicit
so a change in the checked original-Cake witnesses is reviewable.
The expected Cake stdout hashes are pinned in ``parity-small-corpus.json``.
Comparing Flapjack's complete assembly stdout with those hashes keeps this
check exact while avoiding a dependency on the ignored/local Cake executable
in clean CI checkouts.
"""

import hashlib
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
FLAPJACK = REPO_ROOT / ".lake" / "build" / "bin" / "flapjack-compile"
MANIFEST = REPO_ROOT / "scripts" / "parity-small-corpus.json"
FIXTURES = (
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00634_dead_raise.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f01266_raise_live_continuation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00097_ssa_unmapped_zero.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00103_fuzz_global_struct_loop.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00114_fuzz_global_pressure.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00278_fuzz_global_struct_handler.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00268_fuzz_high_pressure_handler.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00000_fuzz_global_pressure_20261015.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00002_fuzz_pressure_20261017.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00226_fuzz_nested_pressure_20261017.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00209_fuzz_global_pressure_20261018.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00413_fuzz_pressure_20261019.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "allocator_colour_permutation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00068_allocator_return.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "mul64x64_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "wide_call_arguments.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "wide_call_arity.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "stack_args_overflow_slots.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "secp256k1_recover.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "many_word_parameters.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1049_stack_alloc.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00014_loop_to_word_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "dec_temporary_cutset.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00068_throwminimal3.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00460_nested_handler_constant_fold.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00484_nested_and_store.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "process_message_negative_offset.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "store_offset_boundaries.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "spilled_load_offset.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "process_message_empty_catch.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "loop_body_condition_fuse.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "set_transient_storage_copy_class.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "wide_call_spilled_base.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "ready_last_argument_permutation.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "nested_shape_22_fields.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00228_copy_share_store.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "secp_accel_init_block.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "nested_handler_condition.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "secp_accel_modmul.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "nested_handler_comparison.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "and_comparison_handler.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00238_handler_const_or.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1039_handled_call_labels.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "ordinary_subword_offsets.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00017_nested_and_zero.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00091_nested_and_constants.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1025_frame_bitmap.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "gh1025_frame_bitmap_f00000.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00108_handler_spill_slot.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "allocator_frame_handler_min.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00028_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "divmnu_copy_loop.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "bn_divmnu_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "bitmap_calls.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "u256_mul_full.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "u256_mul_full_bitmap_wrap.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f84_frame_allocator.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "p8_frame_pressure.pnk",
    REPO_ROOT / "Flapjack" / "Test" / "OriginalPancake" / "f00217_fuzz_allocator_20260928.pnk",
)


def main() -> int:
    missing = [path for path in FIXTURES if not path.is_file()]
    if missing:
        for path in missing:
            print(f"missing allocator fixture: {path}", file=sys.stderr)
        return 2
    if not FLAPJACK.is_file():
        print(f"missing flapjack binary: {FLAPJACK}", file=sys.stderr)
        return 2
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    expected = {
        REPO_ROOT / fixture["path"]: fixture["cake_sha256"]
        for fixture in manifest["fixtures"]
    }
    failures = 0
    for path in FIXTURES:
        if path not in expected:
            print(f"missing pinned Cake hash: {path}", file=sys.stderr)
            failures += 1
            continue
        result = subprocess.run(
            [str(FLAPJACK), "--assembly", str(path)], capture_output=True
        )
        actual = hashlib.sha256(result.stdout).hexdigest()
        if result.returncode == 0 and actual == expected[path]:
            print(f"exact {path.name} sha256={actual}")
        else:
            print(
                f"MISMATCH {path.name} returncode={result.returncode} "
                f"cake={expected[path]} flapjack={actual}",
                file=sys.stderr,
            )
            failures += 1
    print(f"allocator fixtures={len(FIXTURES)} failures={failures}")
    return int(failures != 0)


if __name__ == "__main__":
    sys.exit(main())
