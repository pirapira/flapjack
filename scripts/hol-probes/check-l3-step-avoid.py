"""Reject drift in original HOL step state-lemma captures."""
from pathlib import Path
EXPECTED = [
    'avoid_statement=¬b ⇒ (if b then signalAddressException t u else s) = s',
    'avoid_signalAddressException_type=:ExceptionType # word64 -> riscv_state -> riscv_state',
    'avoid_source=HOL riscv_stepScript.sml avoid_signalAddressException (l.553-557): ~b ==> ((if b then signalAddressException t u else s) = s)',
    'update_pc_statement=update_pc v s = SOME (s with c_PC := s.c_PC⦇s.procID ↦ v⦈)',
    'update_pc_def_type=:word64 -> riscv_state -> riscv_state option',
    "update_pc_source=HOL riscv_stepScript.sml update_pc (l.662-663): saved from update_pc_def and write'PC_def",
]


def check(text):
    if text.splitlines() != EXPECTED:
        raise ValueError("original HOL step state-lemma capture differs from reviewed statements")


if __name__ == "__main__":
    check(Path(__file__).with_name("l3_step_avoid_probe.out").read_text())
    print("step_avoid: exact original HOL statements and types PASS")
