"""PAG264 の各文の数値照合（証明ではない）：fsum_pull、pull_dind、cornerOp_dind、cornerOp_one_single、cornerOp_one（M/N は自然数の割り算）。"""
import math, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from corner_check import A, divisors, iota
bad = []; n = 0
for M in range(1, 31):
    BM, DM, EM = A(M)
    for N in divisors(M):
        BN, DN, EN = A(N); k = M // N
        P = iota(N, M) * np.sqrt(k)                     # π^*（正規化しない引き戻し）
        F = P.T.copy()                                   # π_*（繊維の和）
        phi = lambda S: (N / M) * P @ S @ F              # cornerOp
        ok = np.allclose(F @ P, k * np.eye(N))           # fsum_pull
        for s in DN:
            m = sum((DM[u] for u in DM if math.gcd(u, N) == s), np.zeros((M, M), dtype=complex))
            ok &= np.allclose(P @ np.diag(DN[s]), np.diag(m))                                       # pull_dind（関数として）
            ok &= np.allclose(phi(DN[s]), m @ phi(np.eye(N)))                                       # cornerOp_dind
        e0 = np.zeros(M); e0[0] = 1
        ok &= np.isclose((phi(np.eye(N)) @ e0)[0], N / M)                                          # cornerOp_one_single
        ok &= np.allclose(phi(np.eye(N)), sum(EM[s] for s in EM if s % (M // N) == 0))           # cornerOp_one
        n += 1
        if not ok: bad.append((N, M))
print(f'組 {n}、合わない組 {bad}')
