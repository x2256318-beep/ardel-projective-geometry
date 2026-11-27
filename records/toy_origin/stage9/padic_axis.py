#!/usr/bin/env python3
"""玩具の段 9：素数 p の点の上の J_p∘F_p を、付値の軸（殻 S_k = p^kℤ_p^× の番号 k）の上の作用素として計算する（numpy・scipy）。

記号（依頼文 prompt_blind.md と同じ）：ψ_p(x) = e^{+2πi{x}_p}、dx は vol(ℤ_p) = 1、F_p g(y) = ∫ g(x)ψ_p(xy)dx、
(J_p g)(x) = |x|^{−1} g(1/x)。χ の成分の基底 g_k = χ(u(x))·1_{S_k}、正規化 ĝ_k = g_k/vol(S_k)^{1/2}、vol(S_k) = p^{−k}(1 − 1/p)。
F_p g_k(p^j) = p^{−k}∫_{ℤ_p^×} χ(u) ψ_p(p^{k+j}u) du は有限和で正確に計算できる（L = max(e, −(k+j), 1) として mod p^L の平均）。
(J_p F_p g_k)(p^m u) = p^m·χ(u)·F_p g_k(p^{−m})（F_p g_k は単数の上で χ̄ のように変わる）。
行列 M̃[m, k]（ĝ_k の像の ĝ_m の係数）= p^m F_p g_k(p^{−m})·(vol S_m / vol S_k)^{1/2}。

(a) 分岐（文 P1）：M̃ は m = k + e の対角線だけで、値は一定 τ(χ)/p^{e/2}（|·| = 1）。
(b) 不分岐（文 P2）：M̃ は m − k だけによる。M̃_d と予想 −p^{−1/2}（d = 1）、(1 − 1/p)p^{d/2}（d ≤ 0）、0（d ≥ 2）。
    記号 σ(z) = Σ_d M̃_d z^d と (1 − p^{−1/2}z)/(1 − p^{−1/2}z^{−1})、|σ| = 1。
(c) ユニタリ性：窓の内側の列の ℓ² ノルムと、列どうしの内積。
(d) 文 P2・P3 を Tate の局所ゼータ積分と独立に照合：Z(F_pΦ, ω^{−1}, 1−s)/Z(Φ, ω, s) を殻ごとの試験関数 Φ = g_k で直接の和として計算し、
    分岐なら τ(χ)/p^{e/2}·w^e·p^{−iet}（記号 ε z^e を z = w p^{−it} で読んだもの）、不分岐なら σ(w p^{−it}) と比べる（s = 1/2 + it）。
    ω_p は単数の上で χ̄、ω_p(p) = w（|w| = 1）。
(e) 文 P4：導手 f = ∏ p_i^{e_i} の χ = ∏χ_i で、w_i = ∏_{j≠i} χ_j(p_i)（積公式と ω_q(q) = χ(q) の正規化から）として
    ε_∞·∏_i (τ(χ_i)/p_i^{e_i/2})·w_i^{e_i} と 𝔀(χ) = τ(χ)/(i^a√f)。ε(s)/ε(1/2) の積が f^{1/2−s} であること。
(f) 文 P5：無限素点の γ_∞(1/2 + it) = (−i)^a Γ_ℝ(1/2 − it + a)/Γ_ℝ(1/2 + it + a)（ψ_∞(x) = e^{−2πix}）を
    直接の数値積分と閉じた式で照合し、位相の 2 階差分が 0 でない（t について線形でない）ことを、分岐する素数の位相（線形）と比べる。
"""
import cmath
import math
import numpy as np
from scipy.special import loggamma

RNG = np.random.default_rng(20261127)
STATS = {"short": 0, "exact_zero_checked": 0, "exact_zero_max": 0.0}


def e(t):
    return cmath.exp(2j * math.pi * t)


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


def chi_val(chi, pe, u):
    """χ（法 p^e の辞書。e = 0 なら自明）の u での値。"""
    if pe == 1:
        return 1.0 + 0j
    return chi.get(u % pe, 0j)


def Fg(p, e, chi, k, j):
    """F_p g_k(p^j)。"""
    pe = p ** e
    L = max(e, -(k + j), 1)
    PL = p ** L
    if L > max(e, 1) and PL > 200000:
        # 近道：L > max(e, 1) なら和は 0（原始的でない指標のガウス和）。p^L ≤ 2·10^5 の場合は正確に計算し、
        # その 0 を STATS で確かめる。
        STATS["short"] += 1
        return 0j
    us = np.array([u for u in range(PL) if u % p])
    cv = np.array([chi_val(chi, pe, int(u)) for u in us])
    if k + j >= 0:
        ph = np.ones(len(us))
    else:
        q = p ** (-(k + j))
        ph = np.exp(2j * math.pi * (us % q) / q)
    val = p ** (-k) * np.sum(cv * ph) / PL
    if L > max(e, 1):
        STATS["exact_zero_checked"] += 1
        STATS["exact_zero_max"] = max(STATS["exact_zero_max"], abs(val) * p ** k)
    return val


def vol(p, k):
    return p ** (-k) * (1 - 1 / p)


def Mtilde(p, e, chi, ks, ms):
    M = np.zeros((len(ms), len(ks)), dtype=complex)
    for b, k in enumerate(ks):
        for a, m in enumerate(ms):
            M[a, b] = p ** m * Fg(p, e, chi, k, -m) * math.sqrt(vol(p, m) / vol(p, k))
    return M


def tau(chi, pe):
    return sum(chi_val(chi, pe, u) * e(u / pe) for u in range(pe) if math.gcd(u, pe) == 1)


def zeta_ratio(p, e, chi, k, w, s, Kmax=90):
    """Z(F_p g_k, ω^{−1}, 1−s)/Z(g_k, ω, s)。ω は単数の上で χ̄、ω(p) = w。d^×x は vol(ℤ_p^×) = 1。"""
    # Z(g_k, ω, s) = ∫_{S_k} χ(u) ω(x)|x|^s d^×x = w^k p^{−ks}
    Zg = w ** k * p ** (-k * s)
    # F_p g_k は単数の上で χ̄：F g_k(p^j u) = χ̄(u) F g_k(p^j)。ω^{−1}(p^j u) = w^{−j} χ(u)。積は u によらない。
    Zf = 0j
    for j in range(-k - e - 2, Kmax):
        Zf += Fg(p, e, chi, k, j) * w ** (-j) * p ** (-j * (1 - s))
    return Zf / Zg


def main():
    out = []
    P = out.append
    # (a)
    P("# (a) 分岐（文 P1）：M̃ の台と値（窓 k, m ∈ [−6, 6]）")
    ks = list(range(-6, 7))
    ms = list(range(-12, 13))
    for p, e_ in ((2, 2), (2, 3), (3, 1), (3, 2), (5, 1), (7, 1)):
        pe = p ** e_
        chis = [c for c in characters(pe) if primitive(pe, c)]
        woff = wval = wnorm = 0.0
        for chi in chis:
            M = Mtilde(p, e_, chi, ks, ms)
            eps = tau(chi, pe) / p ** (e_ / 2)
            for b, k in enumerate(ks):
                for a, m in enumerate(ms):
                    if m == k + e_:
                        wval = max(wval, abs(M[a, b] - eps))
                    else:
                        woff = max(woff, abs(M[a, b]))
            wnorm = max(wnorm, abs(abs(eps) - 1))
        P(f"  p = {p} e = {e_}：原始指標 {len(chis)} 個、m = k + e での値と τ/p^(e/2) の差の最大 {wval:.1e}、"
          f"それ以外の成分の最大 {woff:.1e}、||ε| − 1| の最大 {wnorm:.1e}")
    # (b)・(c)
    P("# (b) 不分岐（文 P2）：M̃_d と予想、記号 σ(z)")
    for p in (2, 3, 5, 7):
        ks = list(range(-3, 4))
        ms = list(range(-70, 6))
        M = Mtilde(p, 0, {}, ks, ms)
        wtoep = wpred = 0.0
        Md = {}
        for b, k in enumerate(ks):
            for a, m in enumerate(ms):
                d = m - k
                if d not in Md:
                    Md[d] = M[a, b]
                wtoep = max(wtoep, abs(M[a, b] - Md[d]))
                pred = -p ** -0.5 if d == 1 else ((1 - 1 / p) * p ** (d / 2) if d <= 0 else 0)
                wpred = max(wpred, abs(M[a, b] - pred))
        ws = wu = 0.0
        for th in np.linspace(0, 2 * math.pi, 13)[:-1]:
            z = cmath.exp(1j * th)
            sig = sum(v * z ** d for d, v in Md.items() if d >= -60)
            form = (1 - p ** -0.5 * z) / (1 - p ** -0.5 / z)
            ws = max(ws, abs(sig - form))
            wu = max(wu, abs(abs(form) - 1))
        # (c) 列のノルムと内積（窓の内側）
        G = M.conj().T @ M
        wun = np.max(np.abs(G - np.eye(len(ks))))
        P(f"  p = {p}：M̃ が m − k だけによることのずれ {wtoep:.1e}、予想の値との差の最大 {wpred:.1e}、"
          f"σ(z) と閉じた式の差の最大（|z| = 1 の 12 点、d ≥ −60 で打ち切り）{ws:.1e}、||σ| − 1| の最大 {wu:.1e}、"
          f"(c) 列のグラム行列と単位行列の差の最大 {wun:.1e}")
    P("# (c) 分岐の場合のユニタリ性：上の (a) で各列は |ε| = 1 の成分 1 つだけ（列の直交は台が互いに違うことから）")
    # (d)
    P("# (d) Tate の局所ゼータ積分（殻ごとの試験関数 g_k、直接の和）と記号の読み（s = 1/2 + it）")
    for p, e_ in ((3, 0), (5, 0), (2, 0), (3, 1), (5, 1), (2, 2), (2, 3), (3, 2)):
        pe = p ** e_
        chis = [{}] if e_ == 0 else [c for c in characters(pe) if primitive(pe, c)][:2]
        wmax = wk = 0.0
        for chi in chis:
            for w in (cmath.exp(0.7j), cmath.exp(-2.1j)):
                for t in (0.0, 0.9, 3.3):
                    s = 0.5 + 1j * t
                    z = w * p ** (-1j * t)
                    if e_ == 0:
                        pred = (1 - p ** -0.5 * z) / (1 - p ** -0.5 / z)
                    else:
                        pred = tau(chi, pe) / p ** (e_ / 2) * z ** e_
                    vals = [zeta_ratio(p, e_, chi, k, w, s) for k in (-2, 0, 3)]
                    wmax = max(wmax, max(abs(v - pred) for v in vals))
                    wk = max(wk, max(abs(v - vals[0]) for v in vals))
        P(f"  p = {p} e = {e_}：Z(Fg_k)/Z(g_k) と記号の読みの差の最大 {wmax:.1e}、試験関数 k = −2, 0, 3 の間の差の最大 {wk:.1e}")
    # (e)
    P("# (e) 文 P4：ε_∞·∏_i (τ(χ_i)/p_i^(e_i/2))·w_i^(e_i)、w_i = ∏_{j≠i} χ_j(p_i)、と 𝔀(χ)")
    for mods in ([3, 5], [4, 7], [3, 5, 7], [8, 9], [4, 9, 5]):
        comps = [[c for c in characters(Ni) if primitive(Ni, c)] for Ni in mods]
        f = math.prod(mods)
        import itertools
        werr = 0.0
        cnt = 0
        for combo in itertools.product(*comps):
            chi = {u: complex(np.prod([c[u % Ni] for c, Ni in zip(combo, mods)])) for u in units(f)}
            a = 0 if abs(chi[f - 1] - 1) < 1e-8 else 1
            W = sum(chi[u] * e(u / f) for u in chi) / ((1j) ** a * math.sqrt(f))
            prod = (-1j) ** a
            for i, (ci, Ni) in enumerate(zip(combo, mods)):
                p = min(d for d in range(2, Ni + 1) if Ni % d == 0)
                ei = round(math.log(Ni, p))
                wi = complex(np.prod([cj[p % Nj] for j, (cj, Nj) in enumerate(zip(combo, mods)) if j != i]))
                prod *= tau(ci, Ni) / math.sqrt(Ni) * wi ** ei
            werr = max(werr, abs(prod - W))
            cnt += 1
        P(f"  f = {'·'.join(map(str, mods))} = {f}：指標 {cnt} 個、差の最大 {werr:.1e}（ε(s)/ε(1/2) の積 ∏ p_i^(e_i(1/2−s)) = f^(1/2−s) は指数の和 Σ e_i log p_i = log f）")
    # (f)
    P("# (f) 文 P5：無限素点の γ_∞(1/2+it) と、分岐する素数の位相")
    def Gr(w):
        return -0.5 * w * math.log(math.pi) + loggamma(w / 2)
    for a in (0, 1):
        # 直接の数値積分：∫_ℝ |x|^a e^{−πx²} |x|^{w} d^×x = 2∫_0^∞ x^{a+w} e^{−πx²} dx/x、x = e^u
        us_ = np.linspace(-30, 5, 200001)
        du = us_[1] - us_[0]
        werr = 0.0
        for t in (0.0, 1.0, 2.5, 4.0):
            s = 0.5 + 1j * t
            def I(wexp):
                return 2 * np.sum(np.exp(us_ * (a + wexp)) * np.exp(-math.pi * np.exp(2 * us_))) * du
            num = I(1 - s)   # Z(f̂, ω^{−1}, 1−s)：f̂ = (−i)^a y^a e^{−πy²}
            den = I(s)
            g_num = (-1j) ** a * num / den
            g_form = (-1j) ** a * np.exp(Gr(1 - s + a) - Gr(s + a))
            werr = max(werr, abs(g_num - g_form))
        ts = np.linspace(0, 20, 401)
        ph = np.unwrap(np.angle([(-1j) ** a * np.exp(Gr(0.5 - 1j * t + a) - Gr(0.5 + 1j * t + a)) for t in ts]))
        d2 = np.abs(np.diff(ph, 2)).max()
        mods_ = [abs((-1j) ** a * np.exp(Gr(0.5 - 1j * t + a) - Gr(0.5 + 1j * t + a))) for t in ts]
        P(f"  a = {a}：数値積分と閉じた式の差の最大（t = 0, 1, 2.5, 4）{werr:.1e}、|γ_∞| − 1 の最大 {max(abs(m - 1) for m in mods_):.1e}、"
          f"位相の 2 階差分の最大（t ∈ [0, 20]、刻み 0.05）{d2:.1e}")
    for p, e_ in ((3, 1), (2, 3)):
        ts = np.linspace(0, 20, 401)
        ph = np.unwrap(np.angle([p ** (-1j * e_ * t) for t in ts]))
        P(f"  分岐 p = {p} e = {e_}：位相の 2 階差分の最大 {np.abs(np.diff(ph, 2)).max():.1e}（線形、傾き −e log p = {-e_ * math.log(p):.4f}）")
    # (g) 盲検の後に追加：不分岐の記号 σ の値域（弧 |arg σ| ≤ 2 arcsin(p^{−1/2})）と、分岐の一般化固有ベクトルの向き
    P("# (g) 盲検の後に追加：不分岐の記号の値域と、分岐の一般化固有ベクトルの向き")
    for p in (2, 3, 5, 7):
        th = np.linspace(0, 2 * math.pi, 200001)
        z = np.exp(1j * th)
        sig = (1 - p ** -0.5 * z) / (1 - p ** -0.5 / z)
        P(f"  p = {p}：max |arg σ| = {np.abs(np.angle(sig)).max():.6f}、2 arcsin(p^(−1/2)) = {2 * math.asin(p ** -0.5):.6f}、巻き数 {round(np.sum(np.diff(np.unwrap(np.angle(sig)))) / (2 * math.pi))}")
    p, e_ = 3, 2
    chi = [c for c in characters(9) if primitive(9, c)][0]
    eps = tau(chi, 9) / 3
    ks = list(range(-8, 9))
    M = Mtilde(p, e_, chi, ks, ks)
    lam = 1j * eps
    for name, ratio in (("文の形 c̃_(k+e) = (λ/ε)c̃_k", lam / eps), ("盲検の形 c̃_(k+e) = (ε/λ)c̃_k", eps / lam)):
        c = np.zeros(len(ks), dtype=complex)
        for i, k in enumerate(ks):
            c[i] = ratio ** ((k + 8) // e_) if (k + 8) % e_ == 0 else 0.5 * ratio ** ((k + 8) // e_)
        r = M @ c - lam * c
        inner = np.abs(r[e_:-e_]).max()
        P(f"  p = 3 e = 2、λ = iε：{name} での |JF c̃ − λ c̃| の最大（窓の内側）{inner:.1e}")
    P(f"# 近道の記録：L > max(e, 1) の和を正確に計算して 0 を確かめた件数 {STATS['exact_zero_checked']}（p^k 倍の絶対値の最大 {STATS['exact_zero_max']:.1e}）、"
      f"p^L > 2·10^5 で近道（0 とおいた）件数 {STATS['short']}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
