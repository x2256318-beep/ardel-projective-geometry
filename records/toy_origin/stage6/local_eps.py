#!/usr/bin/env python3
"""玩具の段 6：各素点の局所定数を、局所ゼータ積分（Tate の局所関数等式）から直接求める（numpy だけ）。

答えの式（E1・E2）を使わない独立の計算：
- 素点 p（法 N_i = p^e の原始指標 χ_i）：ℚ_p の関数を p^{−M}ℤ_p の上、p^{M}ℤ_p で不変なものとして格子 x_k = k/p^M で表す。
  dx は vol(ℤ_p) = 1、d^×x = dx/(|x|(1 − 1/p))（vol(ℤ_p^×) = 1）、ψ_p(x) = e^{+2πi{x}_p}（規約 T）。
  ω_p(p^v u) = w^v · ω_p|_units(u)、ω_p|_units = χ̄_i（ω_q(q) = χ(q) の正規化から）。w = ω_p(p) は入力。
  試験関数 f = 1_{ℤ_p^×}·χ_i（Z(f, ω, s) = 1）、f̂ を数値で求め、γ(1/2) = Z(f̂, ω^{−1}, 1/2)/Z(f, ω, 1/2)。
  ω_p は分岐しているので L 因子は 1 で、γ(1/2) = ε(1/2, ω_p, ψ_p)。
- 無限素点：f = x^a e^{−πx²}、ω_∞ = sgn^a、ψ_∞(x) = e^{−2πix}（規約 T）。f̂ を数値積分で求めて比をとる。
- w の与え方：(E3) w = ∏_{j≠i} χ_j(p_i)（主イデール p_i の上で ω = 1）と、比較のために共役 conj(E3)。
"""
import cmath
import itertools
import math
import numpy as np

RNG = np.random.default_rng(20261127)


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
    return [{u: V[idx[u], k] / V[idx[1], k] for u in U} for k in range(m)]


def primitive(N, chi):
    for d in range(1, N):
        if N % d == 0 and all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0):
            return False
    return True


def val(chi, N, n):
    return chi.get(n % N, 0.0)


def vp(n, p):
    if n == 0:
        return 10 ** 9
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def local_eps(p, e, chi_i, w, M=None):
    """局所ゼータ積分から ε(1/2, ω_p, ψ_p) を求める。chi_i は法 p^e の原始指標（dict）。"""
    if M is None:
        M = e + 2
    P = p ** M
    G = p ** (2 * M)
    # f = 1_{ℤ_p^×}·χ_i：格子 x = k/p^M、ℤ_p^× は v_p(k) = M（k = p^M u、u は p^M を法とする単数）
    # f̂(y) = ∫ f(x) ψ(xy) dx = Σ_{u mod p^M, 単数} χ_i(u) e^{2πi {u y}_p} p^{−M}
    us = [u for u in range(P) if u % p]
    fu = np.array([val(chi_i, p ** e, u) for u in us])
    us = np.array(us)
    Zfh = 0.0 + 0.0j
    for l in range(1, G):
        j = vp(l, p)
        v = j - M                       # y = l/p^M の付値
        if v > M - 1:
            continue
        # {u y}_p = ((u·l) mod p^M)/p^M（u は単数、y = l/p^M）
        ph = np.exp(2j * math.pi * ((us * l) % P) / P)
        fh = np.sum(fu * ph) * p ** (-M)
        if abs(fh) < 1e-14:
            continue
        # ω^{−1}(y) |y|^{1/2} d^×y：y = p^v u'、u' = l/p^j
        uprime = (l // p ** j)
        om = (w ** v) * np.conj(val(chi_i, p ** e, uprime))   # ω(y) = w^v χ̄_i(u')
        absy = p ** (-v)
        dmeas = p ** (-M) / (absy * (1 - 1 / p))             # d^×y の格子の 1 区画（l は p^{2M} を法とする代表）
        Zfh += fh * (1 / om) * absy ** 0.5 * dmeas
    return Zfh  # Z(f, ω, 1/2) = 1


def arch_eps(a):
    xs = np.linspace(-8, 8, 4001)
    dx = xs[1] - xs[0]
    f = xs ** a * np.exp(-math.pi * xs ** 2)
    ys = xs
    fh = np.array([np.sum(f * np.exp(-2j * math.pi * xs * y)) * dx for y in ys])
    sgn = np.sign(ys)
    w = np.abs(ys) ** 0.5 / np.where(ys == 0, 1, np.abs(ys))
    mask = ys != 0
    Zfh = np.sum((fh * (sgn ** a) * w)[mask]) * dx          # ω^{−1} = sgn^a
    Zf = np.sum(((f * (np.sign(xs) ** a)) * np.abs(xs) ** 0.5 / np.where(xs == 0, 1, np.abs(xs)))[mask]) * dx
    return Zfh / Zf


def main():
    out = []
    P_ = out.append
    P_("# 無限素点：ε(1/2, sgn^a, ψ_∞) を数値積分で（ψ_∞(x) = e^{−2πix}）")
    for a in (0, 1):
        e = arch_eps(a)
        P_(f"  a = {a}：{e.real:+.6f}{e.imag:+.6f}i   （(−i)^a = {((-1j) ** a).real:+.0f}{((-1j) ** a).imag:+.0f}i）")
    P_("# 素点：局所ゼータ積分の ε(1/2, ω_p, ψ_p) と E2 の式、大域の積と 𝔀(χ)")
    P_("  法の組   成分          w = E3 での |ε_p − E2| の最大   |ε_∞∏ε_p − 𝔀| の最大（E3）  同（w = conj E3）  |ε_p| − 1 の最大")
    for mods in ([3, 5], [3, 7], [4, 5], [5, 7], [8, 3], [9, 4], [3, 5, 7], [4, 3, 5]):
        comps = [[c for c in characters(Ni) if primitive(Ni, c)] for Ni in mods]
        N = math.prod(mods)
        wr = {"E3": 0.0, "conj": 0.0}
        werr = 0.0
        wnorm = 0.0
        count = 0
        for combo in itertools.product(*comps):
            chi = {u: complex(np.prod([val(c, Ni, u) for c, Ni in zip(combo, mods)])) for u in units(N)}
            a = 0 if abs(chi[N - 1] - 1) < 1e-8 else 1
            tau = sum(chi[u] * cmath.exp(2j * math.pi * u / N) for u in chi)
            W = tau / ((1j) ** a * math.sqrt(N))
            for mode in ("E3", "conj"):
                prod = (-1j) ** a
                for i, (ci, Ni) in enumerate(zip(combo, mods)):
                    p = min(d for d in range(2, Ni + 1) if Ni % d == 0)
                    e = round(math.log(Ni, p))
                    w = complex(np.prod([val(cj, Nj, p) for j, (cj, Nj) in enumerate(zip(combo, mods)) if j != i]))
                    if mode == "conj":
                        w = w.conjugate()
                    eps = local_eps(p, e, ci, w)
                    prod *= eps
                    if mode == "E3":
                        cross = complex(np.prod([val(cj, Nj, Ni) for j, (cj, Nj) in enumerate(zip(combo, mods)) if j != i]))
                        tau_i = sum(ci[u] * cmath.exp(2j * math.pi * u / Ni) for u in ci)
                        werr = max(werr, abs(eps - cross * tau_i / math.sqrt(Ni)))
                        wnorm = max(wnorm, abs(abs(eps) - 1))
                wr[mode] = max(wr[mode], abs(prod - W))
            count += 1
        P_(f"  {'·'.join(map(str, mods)):<8} {count:<3} 個        {werr:<28.1e} {wr['E3']:<28.1e} {wr['conj']:<17.2e} {wnorm:.1e}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
