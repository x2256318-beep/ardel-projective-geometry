#!/usr/bin/env python3
"""玩具の段 7：水準ごとの加法指標 ψ_N = e(·/N) の極限（numpy だけ）。

(a) ℚ/ℤ の上で e(x) = ∏_p ψ_p(x)、ψ_p(x) = e^{2πi{x}_p}（ランダムな有理数、負の数と p = 2 を含む）。
(b) 埋め込み ι_{N→M}(x) = (M/N)x に沿って ψ_M∘ι = ψ_N（両立）、還元 r_{M→N} に沿っては ψ_N∘r ≠ ψ_M。
(c) 水準 N の作用素 T_N = J∘H_N/√N を、導手 f の指標（水準 N で原始的でないものを含む）に作用させ、
    ⟨χ, T_N χ⟩/⟨χ, χ⟩ と W(χ_prim) = τ(χ_prim)/(i^a√f)、固有ベクトルからのずれ ‖T_Nχ − cχ‖/‖χ‖ を比べる
    （PAG258 `TopL_not_compat` の数値版）。
(d) 交差項：f = ∏ f_i で、1/f の p_i 成分は u_i/f_i（u_i ≡ (f/f_i)^{−1} mod f_i）。
    Σ_x χ_i(x) e(x u_i/f_i) = χ_i(f/f_i)·τ(χ_i) と、その積が τ(χ)。
(e) 盲検の問いテストが返した式（Montgomery–Vaughan 9.5・9.7・9.10 として）
    T_N χ = μ(N/f)·χ*(N/f)·√(f/N)·W(χ*)·χ（χ* は導手 f の原始指標、gcd(N/f, f) > 1 なら χ*(N/f) = 0）
    を N ≤ 60 のすべての非自明な指標で照合し、f < N で値が W(χ*) と一致する例を数える（盲検の後に追加）。
"""
import cmath
import itertools
import math
import numpy as np

RNG = np.random.default_rng(20261127)


def e(t):
    return cmath.exp(2j * math.pi * t)


def frac_p(a, b, p):
    """有理数 a/b の p 進の小数部分 {a/b}_p を (分子, 分母) で返す。"""
    k = 0
    while b % p == 0:
        b //= p
        k += 1
    if k == 0:
        return 0, 1
    pk = p ** k
    return (a * pow(b, -1, pk)) % pk, pk


def primes_upto(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = [False] * len(s[i * i::i])
    return [i for i in range(n + 1) if s[i]]


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


def conductor(N, chi):
    for d in sorted(d for d in range(1, N + 1) if N % d == 0):
        if all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0):
            return d
    return N


def prim_values(N, chi, f):
    """導手 f の原始指標の値（(ℤ/f)^× の上）。"""
    out = {}
    for u in units(f) if f > 1 else [0]:
        if f == 1:
            out[0] = 1.0
            continue
        # u に合同で N と互いに素な代表を探す
        x = u
        while math.gcd(x, N) != 1:
            x += f
        out[u] = chi[x % N]
    return out


def mobius(n):
    r, d = 1, 2
    while d * d <= n:
        if n % d == 0:
            n //= d
            if n % d == 0:
                return 0
            r = -r
        d += 1
    return -r if n > 1 else r


def main():
    out = []
    P = out.append
    # (a)
    worst = 0.0
    for _ in range(2000):
        b = int(RNG.integers(1, 5000))
        a = int(RNG.integers(-10 ** 6, 10 ** 6))
        prod = 1.0 + 0j
        # 分母の素因数をすべて拾う（最初の版は 200 以下の素数だけを拾い、大きな素因数の因子を落としていた）
        ps, bb, d = [], b, 2
        while d * d <= bb:
            if bb % d == 0:
                ps.append(d)
                while bb % d == 0:
                    bb //= d
            d += 1
        if bb > 1:
            ps.append(bb)
        for p in ps:
            if b % p == 0:
                n_, d_ = frac_p(a, b, p)
                prod *= e(n_ / d_)
        worst = max(worst, abs(prod - e(a / b)))
    P(f"# (a) e(x) = ∏_p ψ_p(x)：ランダムな有理数 2000 個（分母 < 5000、分子は負を含む）で差の最大 {worst:.1e}")
    # (b)
    P("# (b) 埋め込みと還元に沿った両立")
    for N, M in ((3, 6), (4, 12), (5, 15), (6, 36), (8, 24)):
        emb = max(abs(e(((M // N) * x % M) / M) - e(x / N)) for x in range(N))
        red = max(abs(e((x % N) / N) - e(x / M)) for x in range(M))
        P(f"  N = {N}, M = {M}：埋め込み ψ_M∘ι − ψ_N の最大 {emb:.1e}、還元 ψ_N∘r − ψ_M の最大 {red:.3f}")
    # (c)
    P("# (c) 水準 N の作用素 T_N = J∘H_N/√N と、導手の位相 W(χ_prim)")
    P("  N    導手 f  原始？  ⟨χ,T_Nχ⟩/⟨χ,χ⟩         W(χ_prim)               固有ベクトルからのずれ")
    for N in (8, 9, 12, 15, 16):
        U = units(N)
        idx = {u: i for i, u in enumerate(U)}
        m = len(U)
        T = np.zeros((m, m))
        for i, u in enumerate(U):
            uinv = pow(u, -1, N)
            for j, x in enumerate(U):
                th = 2 * math.pi * x * uinv / N
                T[i, j] = (math.cos(th) + math.sin(th)) / math.sqrt(N)
        shown = set()
        for chi in characters(N):
            f = conductor(N, chi)
            if f == 1:
                continue
            v = np.array([chi[u] for u in U])
            Tv = T @ v
            c = np.vdot(v, Tv) / np.vdot(v, v)
            dev = np.linalg.norm(Tv - c * v) / np.linalg.norm(v)
            pv = prim_values(N, chi, f)
            a = 0 if abs(pv[f - 1] - 1) < 1e-8 else 1
            tau = sum(pv[u] * e(u / f) for u in pv)
            W = tau / ((1j) ** a * math.sqrt(f))
            key = (f, round(c.real, 3), round(c.imag, 3))
            if key in shown:
                continue
            shown.add(key)
            P(f"  {N:<4} {f:<7} {'はい' if f == N else 'いいえ':<6} {c.real:+.4f}{c.imag:+.4f}i      {W.real:+.4f}{W.imag:+.4f}i      {dev:.3f}")
    # (d)
    P("# (d) 交差項と共通の点 1/f（1/f の p_i 成分 u_i/f_i、u_i ≡ (f/f_i)^{−1} mod f_i）")
    for mods in ([3, 5], [4, 7], [3, 5, 7], [8, 9]):
        f = math.prod(mods)
        comps = [[c for c in characters(fi) if conductor(fi, c) == fi] for fi in mods]
        w1 = w2 = 0.0
        cnt = 0
        for combo in itertools.product(*comps):
            chi = {u: complex(np.prod([c[u % fi] for c, fi in zip(combo, mods)])) for u in units(f)}
            tau = sum(chi[u] * e(u / f) for u in chi)
            prod = 1.0 + 0j
            for c, fi in zip(combo, mods):
                ui = pow(f // fi, -1, fi)
                g = sum(c[x] * e(x * ui / fi) for x in c)
                tau_i = sum(c[x] * e(x / fi) for x in c)
                w1 = max(w1, abs(g - c[(f // fi) % fi] * tau_i))
                prod *= g
            w2 = max(w2, abs(prod - tau))
            cnt += 1
        # 1/f の分解の確認：Σ u_i/f_i ≡ 1/f (mod 1)
        s = sum(pow(f // fi, -1, fi) * (f // fi) for fi in mods) % f
        P(f"  f = {'·'.join(map(str, mods))} = {f}：原始指標 {cnt} 個、|Σ_x χ_i(x)e(xu_i/f_i) − χ_i(f/f_i)τ(χ_i)| の最大 {w1:.1e}、"
          f"積と τ(χ) の差の最大 {w2:.1e}、Σ u_i(f/f_i) ≡ {s} (mod f)（1 なら Σ u_i/f_i ≡ 1/f）")
    # (e)
    P("# (e) 式 T_N χ = μ(N/f)·χ*(N/f)·√(f/N)·W(χ*)·χ の照合（N ≤ 60、非自明な指標すべて。盲検の後に追加）")
    tot = imp = hitW = 0
    werr = wdev = 0.0
    for N in range(3, 61):
        U = units(N)
        m = len(U)
        T = np.zeros((m, m))
        for i, u in enumerate(U):
            uinv = pow(u, -1, N)
            for j, x in enumerate(U):
                th = 2 * math.pi * x * uinv / N
                T[i, j] = (math.cos(th) + math.sin(th)) / math.sqrt(N)
        for chi in characters(N):
            f = conductor(N, chi)
            if f == 1:
                continue
            v = np.array([chi[u] for u in U])
            Tv = T @ v
            c = np.vdot(v, Tv) / np.vdot(v, v)
            wdev = max(wdev, np.linalg.norm(Tv - c * v) / np.linalg.norm(v))
            pv = prim_values(N, chi, f)
            a = 0 if abs(pv[f - 1] - 1) < 1e-8 else 1
            tau = sum(pv[u] * e(u / f) for u in pv)
            W = tau / ((1j) ** a * math.sqrt(f))
            k = N // f
            chik = pv[k % f] if math.gcd(k, f) == 1 else 0
            pred = mobius(k) * chik * math.sqrt(f / N) * W
            werr = max(werr, abs(c - pred))
            tot += 1
            if f < N:
                imp += 1
                if abs(c - W) < 1e-8:
                    hitW += 1
    P(f"  非自明な指標 {tot} 個（うち f < N は {imp} 個）：式との差の最大 {werr:.1e}、固有ベクトルからのずれの最大 {wdev:.1e}、"
      f"f < N で値が W(χ*) と一致した個数 {hitW}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
