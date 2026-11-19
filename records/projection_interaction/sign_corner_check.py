"""無限素点の符号 P = R_{−1} は、角 φ_{N,M}(1) の上で A_M に入るか（数値。証明ではない）。2026-11-19。
P_M φ_{N,M}(1) ∈ A_M となる (N, M)（N ∣ M、M ≤ 36）を数え、N ∣ 12 と一致するかを見る。"""
import sys
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/projection_interaction')
from corner_check import A, in_span, divisors, iota
from interaction_check import Rmat
bad = []; n = 0
for M in range(2, 37):
    BM, _, _ = A(M); PM = Rmat(M, M - 1)
    for N in divisors(M):
        I = iota(N, M); Q = I @ I.conj().T
        inA = in_span(BM, PM @ Q); n += 1
        if inA != (12 % N == 0): bad.append((N, M, inA))
print(f'組 {n}、「P_M φ(1) ∈ A_M ⇔ N ∣ 12」の不一致 {bad}')
