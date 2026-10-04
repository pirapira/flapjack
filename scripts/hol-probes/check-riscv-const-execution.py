#!/usr/bin/env python3
"""Pin actual native target iteration and full emitted-list execution shape.
Syntactic regression only; Lean checks proofs and source review is separate.
"""
from pathlib import Path
import hashlib
ROOT = Path(__file__).resolve().parents[2]
NAMES = ['projected_memory_eq', 'bytes_projection_transfer', 'encoded_bytes_of_region', 'const_native_execute', 'const_native_execute_projection', 'const_native_execute_frame', 'const_native_asserts2']
EXPECTED = '41a82aab66061059193b5786a6d0bf2eba2107c95633a072f44c863745ebea5f'

def check(root=ROOT):
    s = (root / 'Flapjack/RiscV/CorrectnessEncoding/ConstExecution.lean').read_text()
    parts = [s.split('noncomputable def constNativeExecute',1)[1].split('/--',1)[0]]
    parts += [s.split('theorem '+n+' ',1)[1].split(' := by',1)[0] for n in NAMES]
    if hashlib.sha256(''.join(parts).encode()).hexdigest() != EXPECTED:
        raise ValueError('actual native emitted-list execution/region/asserts2 shape drift')
    return True

if __name__ == '__main__':
    check()
    print('Actual native Const emitted-list execution/original asserts2 shape PASS')
