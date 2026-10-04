#!/usr/bin/env python3
"""Require the complete independent original divide guard set."""
from pathlib import Path
expected = {f"divide_{op}_{mode}_{case}_{rd}" for op in ("DIV","REM","DIVU","REMU","DIVW","REMW","DIVUW","REMUW") for mode in (0,2,3) for case in range(15) for rd in (0,1,2,7)}
expected |= {f"divide_symbolic_{op}_{prior}" for op in ("DIV","REM","DIVU","REMU","DIVW","REMW","DIVUW","REMUW") for prior in (0,1)}
# Explicit signed/zero-divisor/overflow captures of the original `dfn'DIV`
# equation: the actual 64-bit result word, not just a boolean sentinel.
# These pin truncation toward zero (word_quot) and the min/-1 overflow wrap.
expected_values = {
    "divide_value_DIV_neg7_pos2": "0xFFFFFFFFFFFFFFFDw",
    "divide_value_DIV_pos7_neg2": "0xFFFFFFFFFFFFFFFDw",
    "divide_value_DIV_neg7_neg2": "3w",
    "divide_value_DIV_zero_divisor": "0xFFFFFFFFFFFFFFFFw",
    "divide_value_DIV_min_neg1": "0x8000000000000000w",
    "divide_value_DIV_types": ":word5 # word5 # word5 -> riscv_state -> riscv_state",
}
rows = {}
for line in Path(__file__).with_name("l3_divide_probe.out").read_text().splitlines():
    if line.startswith("divide_") and not line.startswith("divide_definition_"):
        key, value = line.split("=", 1)
        if key in rows:
            raise SystemExit(f"duplicate original fixture: {key}")
        rows[key] = value
if set(rows) != expected | set(expected_values):
    raise SystemExit(f"fixture mismatch: missing {expected - set(rows)}, extra {set(rows) - expected - set(expected_values)}")
if any(rows[key] != "T" for key in expected):
    raise SystemExit("original equations did not all reduce to T")
for key, value in expected_values.items():
    if rows[key] != value:
        raise SystemExit(f"{key}: captured {rows[key]} != expected original {value}")
print(f"PASS {len(rows)} original divide captures ({len(expected_values)} explicit value rows)")
