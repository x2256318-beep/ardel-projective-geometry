#!/usr/bin/env python3
"""零点と解像度の読み（事前登録の数値）。numpy だけを使う（mpmath・scipy はこの環境にない）。

E0  零点の計算：Riemann–Siegel の Z(t)（C0 と C1 の補正項）で符号の変わり目を探し、二分法で詰める。
    既知の最初の 10 個の値と比べる。
E1  ψ(x) の打ち切った明示公式：零点を高さ T まで入れたときの誤差（素数冪の中点で測る）。T = 0 は主項だけ。
E2  Weil の明示公式の等式の確認：台が [−L, L] の試験関数（三角形の自己畳み込み）。
    素数の側は n ≤ e^L だけ。零点の側は計算した零点の和（打ち切りの誤差つき）。
E3  N(T) と主項 (T/2π)log(T/2πe) + 7/8 の差 S(T) の範囲。
E5  対照群：𝔽_5 上の楕円曲線 y² = x³ + x + 1。𝔽_5 と 𝔽_25 で点を数え、明示公式 N_n = q^n + 1 − α^n − ᾱ^n を確かめる。
    零点の虚部が 2π/log q の周期で並ぶこと（N(T) が T に比例すること）を書き出す。
"""
import math
import sys
import numpy as np

TWO_PI = 2 * math.pi


# ---------- E0：零点 ----------
def theta(t):
    return t / 2 * math.log(t / TWO_PI) - t / 2 - math.pi / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3)


def C0(p):
    return math.cos(TWO_PI * (p * p - p - 1 / 16)) / math.cos(TWO_PI * p)


def C1(p, h=1e-3):
    # C1 = −Ψ'''(p)/(96π²)、Ψ = C0。3 階の差分で近似する。
    d3 = (C0(p + 2 * h) - 2 * C0(p + h) + 2 * C0(p - h) - C0(p - 2 * h)) / (2 * h ** 3)
    return -d3 / (96 * math.pi ** 2)


def Z(t):
    a = math.sqrt(t / TWO_PI)
    N = int(a)
    p = a - N
    th = theta(t)
    s = 0.0
    for n in range(1, N + 1):
        s += math.cos(th - t * math.log(n)) / math.sqrt(n)
    R = (-1) ** (N - 1) * (t / TWO_PI) ** (-0.25) * (C0(p) + C1(p) * (t / TWO_PI) ** (-0.5))
    return 2 * s + R


def zeros_upto(T, step=0.02):
    zs = []
    t = 10.0
    f = Z(t)
    while t < T:
        t2 = t + step
        f2 = Z(t2)
        if f * f2 < 0:
            lo, hi, flo = t, t2, f
            for _ in range(50):
                mid = (lo + hi) / 2
                fm = Z(mid)
                if flo * fm <= 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            zs.append((lo + hi) / 2)
        t, f = t2, f2
    return np.array(zs)


KNOWN10 = [14.134725142, 21.022039639, 25.010857580, 30.424876126, 32.935061588,
           37.586178159, 40.918719012, 43.327073281, 48.005150881, 49.773832478]


def Nsmooth(T):
    return T / TWO_PI * math.log(T / (TWO_PI * math.e)) + 7 / 8


# ---------- 素数・Λ ----------
def mangoldt_table(M):
    lam = np.zeros(M + 1)
    sieve = np.ones(M + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, M + 1):
        if sieve[p]:
            sieve[p * p::p] = False
            q = p
            while q <= M:
                lam[q] = math.log(p)
                q *= p
    return lam


# ---------- E1 ----------
def psi_trunc(x, zs):
    # ψ_0(x) ≈ x − Σ_ρ x^ρ/ρ − log 2π − ½ log(1 − x^{−2})、ρ と ρ̄ を組にする
    s = x - math.log(TWO_PI) - 0.5 * math.log(1 - x ** -2)
    lx = math.log(x)
    for g in zs:
        rho = complex(0.5, g)
        s -= 2 * (np.exp(rho * lx) / rho).real
    return s


# ---------- E2 ----------
def digamma(z):
    # 漸化式で |z| を大きくしてから漸近展開
    res = 0j
    while abs(z) < 10:
        res -= 1 / z
        z += 1
    z2 = 1 / (z * z)
    res += np.log(z) - 1 / (2 * z) - z2 * (1 / 12 - z2 * (1 / 120 - z2 * (1 / 252 - z2 * (1 / 240 - z2 / 132))))
    return res


def make_test(L):
    # g = 三角形 Δ_{L/2} の自己畳み込み（台 [−L, L]）。Δ_a(u) = max(0, 1 − |u|/a)。
    a = L / 2

    def h(r):  # h(r) = ĝ(r) = (ĥΔ(r))²、ĥΔ(r) = a·(sin(ar/2)/(ar/2))²
        r = np.asarray(r, dtype=complex)
        x = a * r / 2
        with np.errstate(divide='ignore', invalid='ignore'):
            sinc = np.where(np.abs(x) < 1e-8, 1.0 + 0j, np.sin(x) / x)
        return (a * sinc ** 2) ** 2

    us = np.linspace(-L, L, 40001)
    du = us[1] - us[0]
    tri = np.maximum(0, 1 - np.abs(us) / a)
    gv = np.convolve(tri, tri, mode='same') * du

    def g(u):
        return np.interp(u, us, gv, left=0.0, right=0.0)

    return g, h


def explicit_formula_check(L, zs):
    g, h = make_test(L)
    lam = mangoldt_table(int(math.exp(L)) + 1)
    ns = np.nonzero(lam)[0]
    prime_side = -2 * np.sum(lam[ns] / np.sqrt(ns) * g(np.log(ns)))
    pole = 2 * h(0.5j).real   # h(i/2) + h(−i/2)
    rr = np.linspace(-400, 400, 160001)
    dr = rr[1] - rr[0]
    arch_int = np.sum(h(rr).real * np.array([digamma(complex(0.25, r / 2)).real for r in rr])) * dr / TWO_PI
    rhs = pole - g(0.0) * math.log(math.pi) + arch_int + prime_side
    lhs = 2 * np.sum(h(zs).real)  # ±γ の両方
    # 打ち切りの誤差の目安：|h(r)| ≤ a² (2/(a r/2))^4 を γ > Tmax の零点密度で積分
    a = L / 2
    Tm = zs[-1]
    tail = 2 * sum(a ** 2 * (4 / (a * t)) ** 4 * math.log(t / TWO_PI) / TWO_PI * 0.5 for t in np.arange(Tm, 20000, 0.5))
    n_used = int(len(ns))
    return dict(L=L, X=math.exp(L), n_prime_powers=n_used, lhs=lhs, rhs=rhs, diff=lhs - rhs, tail_bound=tail,
                pole=pole, arch=arch_int - g(0.0) * math.log(math.pi), prime=prime_side)


# ---------- E5 ----------
def count_F5():
    q = 5
    cnt = 1  # 無限遠点
    for x in range(q):
        for y in range(q):
            if (y * y - (x ** 3 + x + 1)) % q == 0:
                cnt += 1
    return cnt


def count_F25():
    # 𝔽_25 = 𝔽_5[i]/(i² − 2)、元は (u, v) ↦ u + v i
    q = 5

    def mul(a, b):
        return ((a[0] * b[0] + 2 * a[1] * b[1]) % q, (a[0] * b[1] + a[1] * b[0]) % q)

    def add(a, b):
        return ((a[0] + b[0]) % q, (a[1] + b[1]) % q)

    els = [(u, v) for u in range(q) for v in range(q)]
    sq = {}
    for y in els:
        s = mul(y, y)
        sq[s] = sq.get(s, 0) + 1
    cnt = 1
    for x in els:
        rhs = add(add(mul(mul(x, x), x), x), (1, 0))
        cnt += sq.get(rhs, 0)
    return cnt


def main():
    out = []
    P = out.append
    Tmax = float(sys.argv[1]) if len(sys.argv) > 1 else 300.0
    zs = zeros_upto(Tmax)
    P(f"# E0 零点：0 < γ < {Tmax:g} に {len(zs)} 個")
    err10 = max(abs(zs[i] - KNOWN10[i]) for i in range(10))
    P(f"  最初の 10 個と既知の値の差の最大：{err10:.2e}")
    P(f"  N({Tmax:g}) の主項 {Nsmooth(Tmax):.3f}（計算した個数 {len(zs)}）")

    # E3
    Ts = np.arange(15, Tmax, 0.05)
    S = np.array([np.searchsorted(zs, T) - Nsmooth(T) for T in Ts])
    P(f"# E3 S(T) = N(T) − 主項 の範囲（15 ≤ T < {Tmax:g}）：min {S.min():.3f}、max {S.max():.3f}、平均 {S.mean():.3f}")

    # E1
    M = 200
    lam = mangoldt_table(M)
    psi = np.cumsum(lam)
    pp = [n for n in range(2, M + 1) if lam[n] > 0]
    mids = [(pp[i] + pp[i + 1]) / 2 for i in range(len(pp) - 1)]
    P("# E1 ψ(x) の打ち切った明示公式（x は 2 ≤ x ≤ 200 の素数冪の中点、誤差は |式 − ψ(x)|）")
    P("  T      零点の数  平均誤差   最大誤差   跳びの見分け（x ≤ 100 の素数冪で、幅 0.6 の窓での式の増分から主項の増分 0.6 を引いた値が log p の半分を超えた割合）")
    for T in [0, 30, 60, 100, 200, Tmax]:
        zz = zs[zs < T]
        errs = [abs(psi_trunc(x, zz) - psi[int(x)]) for x in mids]
        ok = 0
        tot = 0
        for n in pp:
            if n > 100:
                break
            jump = psi_trunc(n + 0.3, zz) - psi_trunc(n - 0.3, zz) - 0.6  # 主項 x の増分 0.6 を引く
            tot += 1
            ok += jump > 0.5 * lam[n]
        P(f"  {T:<6g} {len(zz):<9d} {np.mean(errs):<10.3f} {np.max(errs):<10.3f} {ok}/{tot}")

    # E2
    P("# E2 Weil の明示公式の等式（台 [−L, L]、素数の側は n ≤ e^L）")
    for L in [math.log(10), math.log(50), math.log(200)]:
        r = explicit_formula_check(L, zs)
        P(f"  X = e^L = {r['X']:.0f}：素数冪 {r['n_prime_powers']} 個、左辺 {r['lhs']:.6f}、右辺 {r['rhs']:.6f}、"
          f"差 {r['diff']:.2e}（零点の打ち切りの目安 {r['tail_bound']:.1e}）、"
          f"内訳：極 {r['pole']:.4f}、無限素点 {r['arch']:.4f}、素数 {r['prime']:.4f}")
    P("  h の主峰の半値幅（r = 0 の峰が h(0)/2 になる r）：")
    for L in [math.log(10), math.log(50), math.log(200), math.log(1000)]:
        _, h = make_test(L)
        rr = np.linspace(0, 50, 50001)
        hv = h(rr).real
        r_half = rr[np.argmax(hv < hv[0] / 2)]
        P(f"    X = {math.exp(L):.0f}：r_half = {r_half:.3f}、2π/log X = {TWO_PI / L:.3f}、比 {r_half / (TWO_PI / L):.3f}")

    # E5
    q = 5
    N1 = count_F5()
    N2 = count_F25()
    a = q + 1 - N1
    alpha = complex(a / 2, math.sqrt(4 * q - a * a) / 2)
    N2_pred = q * q + 1 - 2 * (alpha ** 2).real
    th = math.atan2(alpha.imag, alpha.real)
    P("# E5 対照群：𝔽_5 上の y² = x³ + x + 1")
    P(f"  #E(𝔽_5) = {N1}、a = {a}、α = {alpha.real:.4f} + {alpha.imag:.4f}i（|α| = {abs(alpha):.4f}、√5 = {math.sqrt(5):.4f}）")
    P(f"  #E(𝔽_25) = {N2}、明示公式の予言 25 + 1 − (α² + ᾱ²) = {N2_pred:.6f}")
    P(f"  零点の虚部：γ = (±θ + 2πk)/log 5、θ = {th:.4f}、周期 2π/log 5 = {TWO_PI / math.log(q):.4f}"
      f" → N(T) = 2T·log5/(2π) + O(1)（log の因子なし）")
    print("\n".join(out))


if __name__ == '__main__':
    main()
