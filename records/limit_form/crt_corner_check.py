"""極限の具体形の問いの見込み（数値。証明ではない）。
(1) 角の写像は中国剰余定理の分解と両立するか：互いに素な a', b' で a | a', b | b' のとき、
    V_{a'b'} ≅ V_{a'} ⊗ V_{b'}（CRT）のもとで φ_{ab, a'b'} = φ_{a, a'} ⊗ φ_{b, b'}。
(2) 局所の単位 e_1 = φ_{1, q}(1)（q ∈ {2, 4, 8, 3, 9, 27, 5, 25}：p = 2, 3, 5、k ≤ 3、q ≤ 30。2026-11-20 に範囲を計算したものに合わせて直した。計算は変えていない）が、定数への射影 E^{(q)}_q と一致すること。
（2026-11-19 夜：照合の指摘で、途中で切れていたこの説明の文を完結させた。計算は変えていない。）
"""
import sys, math, itertools
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import A, iota, divisors

def corner(N, M):
    I = iota(N, M)
    return lambda S: I @ S @ I.conj().T

def crt_perm(a, b):
    """V_{ab} の基底 δ_x を V_a ⊗ V_b の基底 δ_{x mod a} ⊗ δ_{x mod b} に送る置換行列。"""
    n = a * b
    P = np.zeros((n, n))
    for x in range(n):
        P[(x % a) * b + (x % b), x] = 1
    return P

bad = []; n = 0
for (a1, b1) in [(2, 3), (4, 3), (2, 9), (4, 9), (8, 3), (3, 5), (9, 5), (4, 5), (2, 15)]:
    if math.gcd(a1, b1) != 1: continue
    for a in divisors(a1):
        for b in divisors(b1):
            Ba, Da, Ea = A(a); Bb, Db, Eb = A(b)
            P1 = crt_perm(a, b); P2 = crt_perm(a1, b1)
            ph = corner(a * b, a1 * b1); pa = corner(a, a1); pb = corner(b, b1)
            for i in range(Ba.shape[1]):
                for j in range(Bb.shape[1]):
                    Sa = Ba[:, i].reshape(a, a); Sb = Bb[:, j].reshape(b, b)
                    S = P1.T @ np.kron(Sa, Sb) @ P1
                    lhs = P2 @ ph(S) @ P2.T
                    rhs = np.kron(pa(Sa), pb(Sb))
                    n += 1
                    if not np.allclose(lhs, rhs): bad.append((a, b, a1, b1))
print(f'(1) CRT との両立：照合 {n} 回、合わない組 {sorted(set(bad))}')
bad2 = []
for p in [2, 3, 5]:
    for k in range(1, 4):
        q = p ** k
        if q > 30: continue
        BM, DM, EM = A(q)
        if not np.allclose(corner(1, q)(np.eye(1)), EM[q]): bad2.append(q)
print(f'(2) e_1 = φ_(1,q)(1) = E^(q)_q（定数への射影）：合わない q {bad2}')
