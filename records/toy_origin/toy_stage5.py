#!/usr/bin/env python3
"""玩具の段 5：回転角 arg 𝔀(χ) の分解（numpy だけ）。

PAG261 `rootNum_listChar_formII`：互いに素な法 N_i の原始指標 χ_i の積 χ について
  𝔀(χ) = ε_∞(χ) · ∏_i (τ(χ_i)/√N_i) · ∏_i ∏_{j≠i} χ_j(N_i)。
角で書くと（mod 2π）
  θ(χ) = θ_∞ + Σ_i θ_i + Σ_{i≠j} arg χ_j(N_i)、θ_∞ = arg (−i)^a = −aπ/2（規約 T）、θ_i = arg τ(χ_i)/√N_i。
逆の規約（無限素点 i^a、有限素点の積 χ(−1)τ(χ)/√N）では無限と有限の分け方が変わるが、和は同じ。
"""
import cmath
import itertools
import math
import numpy as np

RNG = np.random.default_rng(20261127)
TWO_PI = 2 * math.pi


def units(N):
    return [u for u in range(1, N) if math.gcd(u, N) == 1]


def characters(N):
    U = units(N)
    idx = {u: i for i, u in enumerate(U)}
    m = len(U)
    A = np.zeros((m, m), dtype=complex)
    for g in U:
        Mg = np.zeros((m, m))
        for u in U:
            Mg[idx[(g * u) % N], idx[u]] = 1
        A += complex(RNG.normal(), RNG.normal()) * Mg
    _, V = np.linalg.eig(A)
    chars = []
    for k in range(m):
        v = V[:, k] / V[idx[1], k]
        chars.append({u: v[idx[u]] for u in U})
    return chars


def primitive(N, chi):
    for d in range(1, N):
        if N % d == 0 and all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0):
            return False
    return True


def value(chi, N, n):
    n %= N
    return chi.get(n, 0.0)


def tau(chi, N):
    return sum(chi[u] * cmath.exp(2j * math.pi * u / N) for u in chi)


def parity(chi, N):
    return 0 if abs(chi[N - 1] - 1) < 1e-8 else 1


def wrap(x):
    return (x + math.pi) % TWO_PI - math.pi


def main():
    out = []
    P = out.append
    P("# 段 5：回転角の分解（θ を π 単位で。和は mod 2）")
    P("  法の組        χ の成分のパリティ  θ_∞    Σθ_i    交差項  合計     arg𝔀(χ)  差（mod 2π）  逆規約の θ_∞ / 有限  実？")
    for mods in ([3, 5], [3, 7], [4, 5], [5, 7], [3, 5, 7], [4, 3, 5]):
        comps = [[c for c in characters(Ni) if primitive(Ni, c)] for Ni in mods]
        N = math.prod(mods)
        worst = 0.0
        rows = 0
        for combo in itertools.product(*comps):
            # 積の指標（自然数での値の積）
            chi = {u: complex(np.prod([value(c, Ni, u) for c, Ni in zip(combo, mods)])) for u in units(N)}
            a = parity(chi, N)
            th_inf = -a * math.pi / 2
            th_loc = sum(cmath.phase(tau(c, Ni) / math.sqrt(Ni)) for c, Ni in zip(combo, mods))
            cross = 0.0
            for i, Ni in enumerate(mods):
                for j, (cj, Nj) in enumerate(zip(combo, mods)):
                    if j != i:
                        cross += cmath.phase(value(cj, Nj, Ni))
            total = th_inf + th_loc + cross
            W = tau(chi, N) / ((1j) ** a * math.sqrt(N))
            d = abs(wrap(total - cmath.phase(W)))
            worst = max(worst, d)
            real = all(abs(chi[u].imag) < 1e-8 for u in chi)
            # 逆の規約：無限素点 i^a、有限素点 χ(−1)τ/√N
            th_inf2 = a * math.pi / 2
            fin2 = cmath.phase(((-1) ** a) * tau(chi, N) / math.sqrt(N))
            d2 = abs(wrap(th_inf2 + fin2 - cmath.phase(W)))
            worst = max(worst, d2)
            if rows < 4 or real:
                P(f"  {'·'.join(map(str, mods)):<13} {','.join(str(parity(c, Ni)) for c, Ni in zip(combo, mods)):<19} "
                  f"{th_inf/math.pi:+.3f}  {wrap(th_loc)/math.pi:+.3f}  {wrap(cross)/math.pi:+.3f}  {wrap(total)/math.pi:+.3f}   "
                  f"{cmath.phase(W)/math.pi:+.3f}   {d:.1e}       {th_inf2/math.pi:+.3f} / {fin2/math.pi:+.3f}         {'実' if real else ''}")
            rows += 1
        P(f"  {'·'.join(map(str, mods))}：原始指標 {rows} 個、分解の和と arg𝔀 の差の最大（両規約）{worst:.1e}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
