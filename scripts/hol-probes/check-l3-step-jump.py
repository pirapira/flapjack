#!/usr/bin/env python3
"""Reviewed original jump statement/capture drift checks.

These syntactic pins protect the reviewed full shapes and original hypothesis
captures. Lean checks the proofs; this does not establish HOL-to-Lean equivalence.
"""
from pathlib import Path
import hashlib
import re
ROOT = Path(__file__).resolve().parents[2]
LEAN = "Flapjack/RiscV/L3/Step/JumpStep.lean"
CHECKS = {'scripts/hol-probes/l3_step_jump_probeScript.sml': 'a475f46082f84125c366e7634de95661702b98f6097b10f24313d9591beb70fb', 'scripts/hol-probes/l3_step_jump_probe.out': '45e273694c4ba22e8bbeea1cc834d92a24e6feb344441a68ecff9b34f63151eb'}
STATEMENTS = {'dfnJal': 'a0499a0596fa042ae393308b6ffbb51db915547f903fc93c3eabe6ad60086ee7', 'dfnJalr': 'd4f4ffb6059cdc3d70cd2fcc8b08c6de8e8fbbec8f18731e0f53956f453d1e71', 'dfnJalNop': 'ed814b52d9c3291e31951462246af51ad3ae3bd28beea9fe3a57a066f1dad3db', 'dfnJalrNop': 'ce8dda84b688656079e0d2c9cf51cf7a3ba9e7f0b3a9734269cad1b5e393800b'}
NAMES = {'dfnJal': 'JAL', 'dfnJalr': 'JALR', 'dfnJalNop': 'JAL_NOP', 'dfnJalrNop': 'JALR_NOP'}

def check(root=ROOT):
    for name, expected in CHECKS.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != expected:
            raise ValueError("original jump capture drift: " + name)
    source = (root / LEAN).read_text()
    for name, expected in STATEMENTS.items():
        marker = "theorem " + name + " "
        if source.count(marker) != 1:
            raise ValueError("missing/duplicate original jump theorem: " + name)
        signature = source.split(marker, 1)[1].split(" := by", 1)[0]
        if hashlib.sha256(" ".join(signature.split()).encode()).hexdigest() != expected:
            raise ValueError("full original jump statement drift: " + name)
        tag = r'@\[hol\s+"HOL/examples/l3-machine-code/riscv/step/riscv_stepScript.sml"\s+"' + NAMES[name] + r'"\]\s*theorem\s+' + name + r'\b'
        if not re.search(tag, source):
            raise ValueError("original jump declaration reference drift: " + name)
    driver = (root / "scripts/hol-probes/regenerate.sh").read_text()
    commands = driver.replace(chr(92) + chr(10), " ").splitlines()
    registered = [c for c in commands if c.startswith("run_probe l3_step_jump_probeScript.sml ")]
    if len(registered) != 1:
        raise ValueError("jump probe must have one full registration")
    for name in NAMES.values():
        for suffix in ("_hypotheses", "_statement", "_gen", "_hypothesis_count"):
            if name.lower() + suffix not in registered[0]:
                raise ValueError("missing original jump evidence row: " + name + suffix)
    return True

if __name__ == "__main__":
    check()
    print("All four full original JAL/JALR equations and per-theorem hypothesis captures PASS")
