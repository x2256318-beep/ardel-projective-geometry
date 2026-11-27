#!/usr/bin/env python3
"""玩具の段 8：極限の U_∞ を「加法の変換 A → 軌道からの読み出し → 反転 J → ε_∞」の合成として書く（numpy だけ）。

記号（依頼文 prompt_blind.md と同じ）：
  (A g)(t) = ∫_{Ẑ^×} g(x) e(xt) dx（正規化したハール測度）。t = v/n、g の水準 N のとき、(ℤ/lcm(N, n))^× の平均で計算する。
  O_n = 位数がちょうど n の点。R_n h (u) = h(u/n)。J g (u) = g(u^{−1})。ε_∞ = (−i)^a。
(a) 反転 J は引き戻しと可換（PAG267 `invG_comp_pullSys` の数値版）。
(b) A は水準によらない：水準 N の g と、その水準 M への引き戻しで A の値が一致する。
(c) 軌道ごとの値（文 M2）：(Aχ)(v/n) = [f | n]·μ(n/f)χ*(n/f)τ(χ*)χ̄(v)/φ(n)。台は n/f が平方因子なしで f と互いに素な n。
(d) T_N χ = ε_∞(φ(N)/√N) J R_N A χ をベクトルとして（固有値だけでなく）照合。T_N は Hartley 核から直接作る。
(e) 最小の軌道 O_f で読んだ ε_∞(φ(f)/√f) J R_f A χ と W(χ*)χ をベクトルとして照合（N ≤ 60）。
(f) 文 M4：Σ_n n^{−s} S_n χ（S_n = (φ(n)/√n) J R_n A、ガウス和は定義から直接計算）と f^{−s}(τ(χ*)/√f)/L(s+1/2, χ*)。
(g) 文 M5 の局所の分解：不分岐な p で Φ = 1_{ℤ_p^×}、Φ̂ の殻ごとの値と Tate の局所ゼータ積分
    Z(Φ̂, χ^{−1}, 1−s) = Σ_k Φ̂(殻 k)·χ̄(p)^k·p^{−k(1−s)}（d^×y は ℤ_p^× の測度 1）を、L(1−s, χ̄)/L(s, χ) と比べる。
    ℚ/ℤ で見える部分（ℤ_p を点 0 につぶし、殻 −1 だけを残したもの）がどう規格化すると 1/L になるかも出す。
"""
import cmath
import math
import numpy as np

RNG = np.random.default_rng(20261127)


def e(t):
    return cmath.exp(2j * math.pi * t)


def units(N):
    return [u for u in range(1, N + 1) if math.gcd(u, N) == 1] if N > 1 else [0]


def phi(n):
    return len(units(n)) if n > 1 else 1


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


def characters(N):
    """(ℤ/N)^× の指標を値の辞書で返す（乱数の線形結合の固有ベクトル）。"""
    U = units(N)
    if N <= 2:
        return [{u: 1.0 + 0j for u in U}]
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


def prim(N, chi, f):
    """導手 f の原始指標 χ* を関数（整数 → 値、f と互いに素でなければ 0）で返す。"""
    vals = {}
    for u in (units(f) if f > 1 else [0]):
        if f == 1:
            vals[0] = 1.0 + 0j
            continue
        x = u
        while math.gcd(x, N) != 1:
            x += f
        vals[u] = chi[x % N]

    def g(x):
        if f == 1:
            return 1.0 + 0j
        return vals[x % f] if math.gcd(x, f) == 1 else 0j
    return g


def A_val(g, N, v, n):
    """(A g)(v/n)：水準 N の関数 g（(ℤ/N)^× の上の辞書）を Ẑ^× の上の平均で。"""
    L = N * n // math.gcd(N, n)
    U = units(L)
    return sum(g[x % N if N > 1 else 0] * e(x * v / n) for x in U) / len(U)


def tau(chis, f):
    return sum(chis(x) * e(x / f) for x in range(f)) if f > 1 else 1.0 + 0j


def W_of(chis, f):
    if f == 1:
        return 1.0 + 0j
    a = 0 if abs(chis(f - 1) - 1) < 1e-8 else 1
    return tau(chis, f) / ((1j) ** a * math.sqrt(f)), a


def main():
    out = []
    P = out.append
    # (a)
    w = 0.0
    for N, M in ((3, 12), (4, 20), (5, 30), (8, 24), (9, 45)):
        g = {u: complex(RNG.normal(), RNG.normal()) for u in units(N)}
        pull = {u: g[u % N] for u in units(M)}
        Jpull = {u: pull[pow(u, -1, M)] for u in units(M)}
        Jg = {u: g[pow(u, -1, N)] for u in units(N)}
        pullJ = {u: Jg[u % N] for u in units(M)}
        w = max(w, max(abs(Jpull[u] - pullJ[u]) for u in units(M)))
    P(f"# (a) J と引き戻しの可換性：5 組（N ∣ M）でランダムな関数、差の最大 {w:.1e}")
    # (b)
    w = 0.0
    cnt = 0
    for N, M in ((3, 12), (4, 20), (5, 30), (8, 24)):
        g = {u: complex(RNG.normal(), RNG.normal()) for u in units(N)}
        pull = {u: g[u % N] for u in units(M)}
        for n in range(1, 41):
            for v in units(n):
                w = max(w, abs(A_val(g, N, v, n) - A_val(pull, M, v, n)))
                cnt += 1
    P(f"# (b) A の水準によらなさ：4 組の (N, M)、軌道 O_n（n ≤ 40）の点 {cnt} 個で、水準 N と M の計算の差の最大 {w:.1e}")
    # (c)
    w = 0.0
    supp_bad = 0
    nchi = 0
    for N in range(1, 31):
        for chi in characters(N):
            f = conductor(N, chi)
            chis = prim(N, chi, f)
            t = tau(chis, f)
            nchi += 1
            for n in range(1, 91):
                for v in units(n)[:3]:
                    val = A_val(chi, N, v, n)
                    if n % f != 0:
                        pred = 0
                    else:
                        k = n // f
                        cb = np.conj(chis(v)) if f > 1 else 1.0
                        pred = mobius(k) * chis(k) * t * cb / phi(n)
                    w = max(w, abs(val - pred))
                    nz = abs(val) > 1e-9
                    should = (n % f == 0) and mobius(n // f) != 0 and math.gcd(n // f, f) == 1
                    if nz != should:
                        supp_bad += 1
    P(f"# (c) 文 M2：N ≤ 30 の指標 {nchi} 個（自明指標と p = 2 を含む）、n ≤ 90 の各軌道の点 3 個まで：式との差の最大 {w:.1e}、"
      f"台の判定（n/f が平方因子なしで f と互いに素）の食い違い {supp_bad} 件")
    # (d)・(e)
    wd = we = 0.0
    nd = ne = 0
    for N in range(1, 61):
        U = units(N)
        for chi in characters(N):
            f = conductor(N, chi)
            chis = prim(N, chi, f)
            Wv, a = W_of(chis, f) if f > 1 else (1.0 + 0j, 0)
            eps = (-1j) ** a
            if N <= 40 and N > 1:
                # T_N をベクトルで
                TN = {}
                for u in U:
                    ui = pow(u, -1, N)
                    TN[u] = sum(chi[x] * (math.cos(2 * math.pi * x * ui / N) + math.sin(2 * math.pi * x * ui / N)) for x in U) / math.sqrt(N)
                rhs = {u: eps * phi(N) / math.sqrt(N) * A_val(chi, N, pow(u, -1, N), N) for u in U}
                wd = max(wd, max(abs(TN[u] - rhs[u]) for u in U))
                nd += 1
            # 最小の軌道 O_f で読む
            lhs = {u: eps * phi(f) / math.sqrt(f) * A_val(chi, N, (pow(u, -1, N) if N > 1 else 0) % f if f > 1 else 0, f) for u in U}
            we = max(we, max(abs(lhs[u] - Wv * chi[u]) for u in U))
            ne += 1
    P(f"# (d) T_N χ = ε_∞(φ(N)/√N)·J R_N A χ：2 ≤ N ≤ 40 の指標 {nd} 個、ベクトルの差の最大 {wd:.1e}")
    P(f"# (e) ε_∞(φ(f)/√f)·J R_f A χ = W(χ*)χ（最小の軌道 O_f で読む）：N ≤ 60 の指標 {ne} 個、ベクトルの差の最大 {we:.1e}")
    # (f)
    P("# (f) 文 M4：Σ_{n ≤ X} n^{−s}(S_n χ)(1) と f^{−s}(τ(χ*)/√f)/L(s+1/2, χ*)（ガウス和は定義から直接、L は n ≤ 2·10^6 の和）")
    X = 3000
    nn = np.arange(1, 2_000_001)
    for f in (3, 4, 5, 7, 8, 12, 15):
        for chi in characters(f):
            if conductor(f, chi) != f:
                continue
            chis = prim(f, chi, f)
            t = tau(chis, f)
            chiarr = np.array([chis(int(x)) for x in range(f)])
            for s in (2.0, 3.0, 2 + 3j):
                Lval = np.sum(chiarr[nn % f] * nn.astype(float) ** (-(s + 0.5)))
                part = 0j
                for n in range(f, X + 1, f):
                    x = np.arange(1, n + 1)
                    x = x[np.gcd(x, n) == 1]
                    tn = np.sum(chiarr[x % f] * np.exp(2j * np.pi * x / n))
                    part += n ** (-s) * tn / math.sqrt(n)
                pred = f ** (-s) * t / math.sqrt(f) / Lval
                P(f"  f = {f:<3} χ(−1) = {chis(f - 1).real:+.0f}  s = {s}：差 {abs(part - pred):.1e}（値 {pred.real:+.6f}{pred.imag:+.6f}i、"
                  f"打ち切りの見積り ~{(X / f) ** (-(s.real - 0.5)):.0e}）")
            break  # 導手ごとに 1 個
    # (g)
    P("# (g) 文 M5 の局所の分解（不分岐な p、Φ = 1_{ℤ_p^×}）")
    for p in (2, 3, 7):
        # Φ̂ の殻ごとの値を、離散化した p 進の積分で（x ∈ ℤ_p^× を mod p^K、y = p^k u）
        K = 6
        vals = {}
        for k in range(-3, 3):
            # y = p^k、x を mod p^K の単数で平均し、測度 (1 − 1/p) を掛ける
            xs = [x for x in range(p ** K) if x % p]
            if k >= 0:
                val = (1 - 1 / p)
            else:
                val = (1 - 1 / p) * sum(e(x * p ** (K + k) / p ** K) for x in xs) / len(xs)
            vals[k] = complex(val)
        chip = cmath.exp(1j * 0.7)  # 不分岐な指標の値 χ(p)、絶対値 1
        for s in (0.3 + 0.0j, 0.8 + 2.0j):
            full = sum((vals[k] if k < 0 else (1 - 1 / p)) * (np.conj(chip) ** k) * p ** (-k * (1 - s)) for k in range(-3, 200))
            Lcbar = 1 / (1 - np.conj(chip) * p ** (s - 1))
            Ls = 1 / (1 - chip * p ** (-s))
            vis = vals[0] + vals[-1] * np.conj(chip) ** (-1) * p ** (1 - s)
            P(f"  p = {p} s = {s}：Φ̂ の殻 −1・−2 の値 {vals[-1].real:+.4f}・{abs(vals[-2]):.1e}、"
              f"Z(Φ̂) と L(1−s,χ̄)/L(s,χ) の差 {abs(full - Lcbar / Ls):.1e}、"
              f"ℤ_p を点 0 につぶした部分 Φ̂(0) + 殻 −1 = {vis.real:+.4f}{vis.imag:+.4f}i、"
              f"1/L(s,χ) = {(1 / Ls).real:+.4f}{(1 / Ls).imag:+.4f}i、"
              f"(1 − 1/p)·(1 − χ(p)p^{{−s}}/(1 − 1/p)) との差 {abs(vis - ((1 - 1 / p) - chip * p ** (-s))):.1e}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
