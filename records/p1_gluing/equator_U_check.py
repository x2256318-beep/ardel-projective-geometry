"""舞台 P¹ の赤道の絡み合い（Part 21、PAG25 の equator_intertwine_hat）と、貼り合わせ U の位相（Part 252、PAG256 の rootNum = 𝔀）の関係（数値。証明ではない）。2026-11-19 夜。

規約（PAG7・PAG25・PAG256 に合わせる）：e(t) = exp(2πi t/N)（stdAddChar）、τ(χ) = Σ_x χ(x) e(x)、J(χ1,χ2) = Σ_x χ1(x) χ2(1−x)、Ĵ = J/√N、
𝔀(χ) = τ(χ)/(i^a √N)（a = 0：χ(−1) = 1、a = 1：χ(−1) = −1）。
(1) χ1, χ2, χ1χ2 が法 N = p^K の原始指標のとき、conj(Ĵ)² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))² か。
(2) 1 乗の版 conj(Ĵ)² = 𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)) は成り立つか（成り立たない見込み）。
(3) 条件「U² が赤道で南の畳み込みを北の畳み込みに移す」を満たす位相 φ の集まり：r = (φ/𝔀)² が、原始指標の上で乗法的（χ1, χ2, χ1χ2 が原始的なとき r(χ1χ2) = r(χ1)r(χ2)）。
    そのような r が「ある単数 a で r(χ) = χ(a)」に限られるかを、線形の方程式（r の偏角）として次元で調べる。
"""
import cmath, math, itertools, sys
import numpy as np

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1]

def characters(N):
    U = units(N); n = len(U); idx = {u: i for i, u in enumerate(U)}
    rng = np.random.default_rng(1); c = rng.normal(size=n) + 1j * rng.normal(size=n)
    M = np.zeros((n, n), dtype=complex)
    for k, a in enumerate(U):
        for u in U: M[idx[u], idx[(a * u) % N]] += c[k]
    w, V = np.linalg.eig(M)
    return [{u: V[idx[u], j] / V[idx[1], j] for u in U} for j in range(n)]

def is_primitive(N, chi, p):
    if N == p: return any(abs(chi[u] - 1) > 1e-8 for u in chi)
    g = 1 + N // p
    return abs(chi[g % N] - 1) > 1e-8

def mul(c1, c2): return {u: c1[u] * c2[u] for u in c1}

def ev(N, chi, x): return chi.get(x % N, 0.0)

def tau(N, chi): return sum(chi[u] * cmath.exp(2j * math.pi * u / N) for u in chi)

def J(N, c1, c2): return sum(ev(N, c1, x) * ev(N, c2, 1 - x) for x in range(N))

def w(N, chi):
    a = 0 if abs(chi[N - 1] - 1) < 1e-8 else 1
    return tau(N, chi) / ((1j) ** a * math.sqrt(N))

def key(N, chi): return tuple(np.round([chi[u] for u in sorted(chi)], 6))

if __name__ == '__main__':
  for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (2, 3), (5, 2), (3, 3), (2, 4), (7, 2)]:
      N = p ** K
      chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
      pk = {key(N, c): i for i, c in enumerate(prim)}
      n1 = n2 = 0; bad1 = bad2 = 0; eqs = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              c12 = mul(c1, c2)
              if key(N, c12) not in pk: continue
              k = pk[key(N, c12)]
              Jh = J(N, c1, c2) / math.sqrt(N)
              lhs = np.conj(Jh) ** 2
              rhs2 = (w(N, c12) / (w(N, c1) * w(N, c2))) ** 2
              rhs1 = w(N, c12) / (w(N, c1) * w(N, c2))
              n1 += 1; bad1 += not np.isclose(lhs, rhs2); bad2 += np.isclose(lhs, rhs1)
              eqs.append((i, j, k))
      # (3) r の偏角 θ（r = e^{iθ}）について θ_i + θ_j − θ_k ≡ 0。解の空間の次元（実数の線形代数、2π の整数倍は無視）と、
      #     「θ(χ) = arg χ(a)」の族の次元（= 0：離散）を比べる代わりに、方程式の階数から自由度を出す。
      m = len(prim)
      A = np.zeros((len(eqs), m))
      for r_, (i, j, k) in enumerate(eqs):
          A[r_, i] += 1; A[r_, j] += 1; A[r_, k] -= 1
      rank = np.linalg.matrix_rank(A) if len(eqs) else 0
      print(f'N = {N}：原始指標 {m} 個、組 {n1}、(1) の不一致 {bad1}、(2) の一致 {bad2}、(3) 偏角の方程式の自由度 {m - rank}')
