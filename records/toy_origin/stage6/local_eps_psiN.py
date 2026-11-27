#!/usr/bin/env python3
"""段 6 の追加：加法指標を大域の ψ(·/N)（ℚ の上で自明）に替えたときの局所定数を、局所ゼータ積分で求める。

local_eps.py と同じ方法。素点 p_i で ψ_a(x) = ψ_p(a x)、a = 1/N。ψ_a に自己双対な測度 |a|_p^{1/2} dx を使う。
ほかの素点（不分岐の素数と ∞）では a は単数か正の数なので局所定数は変わらない（ω_∞(1/N) = 1）。
確かめること：ε(1/2, ω_{p_i}, ψ_a) = χ_i(N/N_i)·τ(χ_i)/√N_i（PAG261 の形 (I) の因子）と、積が 𝔀(χ)。
"""
import cmath, itertools, math, sys
import numpy as np
sys.path.insert(0, '.')
from local_eps import characters, primitive, val, vp, units


def local_eps_tw(p, e, chi_i, w, Nprime, M=None):
    if M is None:
        M = e + 2
    P = p ** M
    G = p ** (2 * M)
    K = p ** (M + e)
    inv = pow(Nprime, -1, K)
    us = np.array([u for u in range(P) if u % p])
    fu = np.array([val(chi_i, p ** e, int(u)) for u in us])
    Z = 0j
    for l in range(1, G):
        j = vp(l, p)
        v = j - M
        if v > M - 1:
            continue
        ph = np.exp(2j * math.pi * ((us * l * inv) % K) / K)   # ψ_p(u·y/N)、y = l/p^M
        fh = np.sum(fu * ph) * p ** (-M) * p ** (e / 2)      # 自己双対な測度 |1/N|_p^{1/2} dx
        if abs(fh) < 1e-14:
            continue
        om = (w ** v) * np.conj(val(chi_i, p ** e, l // p ** j))
        absy = p ** (-v)
        Z += fh / om * absy ** 0.5 * p ** (-M) / (absy * (1 - 1 / p))
    return Z


out = ["# 加法指標 ψ(·/N) での局所定数（局所ゼータ積分）"]
out.append("  法の組  成分  |ε_{p_i} − 形 (I) の因子| の最大  |ε_{p_i} − 形 (II) の因子| の最大  |ε_∞∏ε − 𝔀| の最大")
for mods in ([3, 5], [5, 7], [4, 3, 5]):
    comps = [[c for c in characters(Ni) if primitive(Ni, c)] for Ni in mods]
    N = math.prod(mods)
    e1 = e2 = eg = 0.0
    cnt = 0
    for combo in itertools.product(*comps):
        chi = {u: complex(np.prod([val(c, Ni, u) for c, Ni in zip(combo, mods)])) for u in units(N)}
        a = 0 if abs(chi[N - 1] - 1) < 1e-8 else 1
        W = sum(chi[u] * cmath.exp(2j * math.pi * u / N) for u in chi) / ((1j) ** a * math.sqrt(N))
        prod = (-1j) ** a
        for i, (ci, Ni) in enumerate(zip(combo, mods)):
            p = min(d for d in range(2, Ni + 1) if Ni % d == 0)
            e = round(math.log(Ni, p))
            w = complex(np.prod([val(cj, Nj, p) for j, (cj, Nj) in enumerate(zip(combo, mods)) if j != i]))
            eps = local_eps_tw(p, e, ci, w, N // Ni)
            prod *= eps
            tau_i = sum(ci[u] * cmath.exp(2j * math.pi * u / Ni) for u in ci)
            fI = val(ci, Ni, N // Ni) * tau_i / math.sqrt(Ni)
            fII = complex(np.prod([val(cj, Nj, Ni) for j, (cj, Nj) in enumerate(zip(combo, mods)) if j != i])) * tau_i / math.sqrt(Ni)
            e1 = max(e1, abs(eps - fI)); e2 = max(e2, abs(eps - fII))
        eg = max(eg, abs(prod - W)); cnt += 1
    out.append(f"  {'·'.join(map(str, mods)):<7} {cnt:<5} {e1:<32.1e} {e2:<34.2e} {eg:.1e}")
print("\n".join(out))
