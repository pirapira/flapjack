#!/usr/bin/env python3
"""Reviewed original register-comparison statement/capture drift checks.

These syntactic pins protect the reviewed full shapes and original hypothesis
captures. Lean checks the proofs; this does not establish HOL-to-Lean equivalence.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
LEAN = "Flapjack/RiscV/L3/Step/RegisterComparison.lean"
CHECKS = {'scripts/hol-probes/l3_step_register_comparison_probeScript.sml': 'ead66796b16c8052f78af8dcf6d4ad034944ec8eec3d292c9f6c8f8777097371', 'scripts/hol-probes/l3_step_register_comparison_probe.out': '1a076e9fba4e2a4310218ebef45e10e836d157ac569ca923716303c3c44ab9f4'}
STATEMENTS = {'dfnSlt': 'b1d04ef4e2720217916f57bbb56b58ce3655486ae44527a1e988b122bd7a1651', 'dfnSltU': 'f48d32557376081985196a7dcc4e23ea7b613048045e46b53c7dcbd9223d5121', 'dfnSltNop': '5764fd3abd84f2d4dc7710011e1af0dd3d59971b5f4242eeaad94babb400e801', 'dfnSltUNop': '8b653462f9fd34447a25a9d365c0cbdc165fe4fb5a5dfe4c7e5d8204513d1dc5'}
NAMES = {'dfnSlt': 'SLT', 'dfnSltU': 'SLTU', 'dfnSltNop': 'SLT_NOP', 'dfnSltUNop': 'SLTU_NOP'}

def check(root=ROOT):
    for name, expected in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError("original register-comparison capture drift: " + name)
    source = (root / LEAN).read_text()
    for name, expected in STATEMENTS.items():
        marker = "theorem " + name + " "
        if source.count(marker) != 1:
            raise ValueError("missing/duplicate original register-comparison theorem: " + name)
        signature = source.split(marker, 1)[1].split(" := by", 1)[0]
        if hashlib.sha256(" ".join(signature.split()).encode()).hexdigest() != expected:
            raise ValueError("full original register-comparison statement drift: " + name)
        tag = r'@\[hol\s+"HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml"\s+"' + NAMES[name] + r'"\]\s*theorem\s+' + name + r'\b'
        if not re.search(tag, source):
            raise ValueError("original register-comparison declaration reference drift: " + name)
    driver = (root / "scripts/hol-probes/regenerate.sh").read_text()
    commands = driver.replace(chr(92) + chr(10), " ").splitlines()
    registered = [c for c in commands if c.startswith("run_probe l3_step_register_comparison_probeScript.sml ")]
    if len(registered) != 1:
        raise ValueError("register-comparison probe must have one full registration")
    for name in NAMES.values():
        for suffix in ("_hypotheses", "_statement", "_gen", "_hypothesis_count"):
            if name.lower() + suffix not in registered[0]:
                raise ValueError("missing original register-comparison evidence row: " + name + suffix)
    return True

if __name__ == "__main__":
    check()
    print("All four full original SLT/SLTU equations and per-theorem hypothesis captures PASS")
