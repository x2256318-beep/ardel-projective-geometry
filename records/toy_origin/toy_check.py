#!/usr/bin/env python3
"""玩具「∞ と −∞ と 0 が射影でねじれて繋がる」の積み上げの数値（numpy だけ）。

T0（単数の座標なし）：基礎は q^ℤ（離散）、対数で ℤ。窓 M = 2L で両端を貼り合わせる：f(n + M) = U f(n)、|U| = 1。
  反転 (J f)(n) = f(−n)。
  T0.1 J が U の空間を保つのは U = ±1 のときだけ（J は U の空間を U⁻¹ の空間に写す）。
  T0.2 反転の固定点は n ≡ 0（加法の 0 ＝ 乗法の 1）と n ≡ L（貼り合わせの点：乗法の 0・∞ ＝ 加法の ∓∞）。
       U = +1：J で偶な関数は両方で自由、奇な関数は両方で 0。U = −1：偶な関数は ∞ で 0、奇な関数は 0 で 0。
  T0.3 平行移動 T f(n) = f(n + 1)（q 倍）の固有値は ζ^M = U。U = −1 では ζ = 1（不変なベクトル）がない。
T1（単数の座標 K = (ℤ/N)^× を足す）：f(k, n + M) = (U f(·, n))(k)、U は L²(K) のユニタリ。
  K の平行移動と可換 ⇔ U は指標で対角（U = Σ e^{iα_χ} P_χ）。反転 (k, n) ↦ (k⁻¹, −n) との両立 ⇔ α_χ̄ = −α_χ。
  A1 の位相 𝔀(χ) = τ(χ)/(i^a √N)（原始指標）を数値で：|𝔀| = 1、𝔀(χ̄) = conj 𝔀(χ)、実の原始指標で 𝔀 = 1。
  実化：χ と χ̄ の組は実の 2 次元の面になり、U はその面の回転（角 arg 𝔀(χ)）として働く。
"""
import cmath
import math
import numpy as np

RNG = np.random.default_rng(20261127)


def ring_basis(M):
    """窓 n ∈ {−L, …, L − 1}（M = 2L）。U の空間の元は窓の上の値で決まる。"""
    L = M // 2
    return list(range(-L, L))


def extend(vals, n, M, U):
    """窓の上の値 vals から f(n) を f(n + M) = U f(n) で求める。"""
    L = M // 2
    k, r = divmod(n + L, M)  # n = (r − L) + kM
    return vals[r] * (U ** k)


def J_maps_space(M, U, trials=20):
    """Jf(n) = f(−n) が再び f(n + M) = U f(n) を満たすか（ランダムな f で）。"""
    worst = 0.0
    for _ in range(trials):
        vals = RNG.normal(size=M) + 1j * RNG.normal(size=M)
        g = lambda n: extend(vals, -n, M, U)
        for n in range(-M, M):
            worst = max(worst, abs(g(n + M) - U * g(n)))
    return worst


def node_pattern(M, U):
    """J で偶・奇な関数の空間で、n = 0 と n = L の値が恒等的に 0 か。"""
    L = M // 2
    basis = ring_basis(M)
    # 窓の値ベクトル v に対し (Jv)(n) = f(−n) を窓に戻した線形写像
    Jm = np.zeros((M, M), dtype=complex)
    for i, n in enumerate(basis):
        for j in range(M):
            e = np.zeros(M, dtype=complex); e[j] = 1
            Jm[i, j] = extend(e, -n, M, U)
    out = {}
    for name, sgn in (("偶", 1), ("奇", -1)):
        P = (np.eye(M) + sgn * Jm) / 2
        # 固定点の値：n = 0 は窓の添字 L、n = L は f(L) = U f(−L)（窓の添字 0）
        v0 = np.abs(P[L, :]).max()
        vinf = np.abs(U * P[0, :]).max()
        out[name] = ("0 で" + ("自由" if v0 > 1e-12 else "0"), "∞ で" + ("自由" if vinf > 1e-12 else "0"),
                     int(round(np.trace(P).real)))
    return out


def T_spectrum(M, U):
    T = np.zeros((M, M), dtype=complex)
    basis = ring_basis(M)
    for i, n in enumerate(basis):
        for j in range(M):
            e = np.zeros(M, dtype=complex); e[j] = 1
            T[i, j] = extend(e, n + 1, M, U)
    ev = np.linalg.eigvals(T)
    return ev, np.min(np.abs(ev - 1))


# ---------- T1 ----------
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
    w, V = np.linalg.eig(A)
    chars = [V[:, k] / V[idx[1], k] for k in range(m)]
    return U, idx, chars


def primitive(N, U, idx, chi):
    for d in range(1, N):
        if N % d == 0 and all(abs(chi[idx[u]] - 1) < 1e-8 for u in U if (u - 1) % d == 0):
            return False
    return True


def a1_phases(N):
    U, idx, chars = characters(N)
    res = []
    for c in chars:
        if not primitive(N, U, idx, c):
            continue
        tau = sum(c[idx[u]] * cmath.exp(2j * math.pi * u / N) for u in U)
        a = 0 if abs(c[idx[N - 1]] - 1) < 1e-8 else 1
        W = tau / ((1j) ** a * math.sqrt(N))
        real = np.allclose(c.imag, 0, atol=1e-8)
        res.append((c, W, a, real))
    return U, idx, res


def main():
    out = []
    P = out.append
    P("# T0（単数の座標なし）")
    for M in (6, 8, 10):
        for name, U in (("U = +1", 1.0), ("U = −1", -1.0), ("U = e^{iπ/3}", cmath.exp(1j * math.pi / 3)), ("U = i", 1j)):
            err = J_maps_space(M, U)
            s = f"  M = {M:<3} {name:<12} J が U の空間を保つ：{'はい' if err < 1e-12 else 'いいえ'}（ずれの最大 {err:.1e}）"
            if err < 1e-12:
                np_ = node_pattern(M, U)
                ev, d1 = T_spectrum(M, U)
                s += f"；偶 {np_['偶'][0]}・{np_['偶'][1]}（次元 {np_['偶'][2]}）、奇 {np_['奇'][0]}・{np_['奇'][1]}（次元 {np_['奇'][2]}）；T の固有値と 1 の最小の距離 {d1:.3f}"
            P(s)
    P("  （M = 2L、窓 n ∈ {−L, …, L − 1}。∞ は貼り合わせの点 n ≡ L、0 は n ≡ 0）")

    P("# T1（単数の座標 K = (ℤ/N)^× を足す）：A1 の位相 𝔀(χ) = τ(χ)/(i^a √N) を原始指標で")
    P("  N    原始  実  |𝔀|−1 の最大  𝔀(χ̄)−conj𝔀(χ) の最大  実の原始指標の 𝔀  複素の組の角 arg𝔀/π（χ ごと、小さい方から）")
    for N in (1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 16, 20, 21):
        if N == 1:
            P("  1    （(ℤ/1)^× は自明群。指標は自明なものだけで、原始的とみなすとガウス和 1・𝔀 = 1（T0 の U = +1 に当たる）。数値の対象外）")
            continue
        U_, idx, res = a1_phases(N)
        if not res:
            P(f"  {N:<4} 0     —   （原始指標なし）")
            continue
        dn = max(abs(abs(W) - 1) for _, W, _, _ in res)
        dc = 0.0
        for c, W, a, r in res:
            cbar = c.conj()
            for c2, W2, _, _ in res:
                if np.allclose(c2, cbar, atol=1e-8):
                    dc = max(dc, abs(W2 - W.conjugate()))
        reals = [W for c, W, a, r in res if r]
        realstr = "・".join(f"{W.real:+.3f}{W.imag:+.3f}i" for W in reals) or "—"
        angs = sorted(cmath.phase(W) / math.pi for c, W, a, r in res if not r)
        P(f"  {N:<4} {len(res):<5} {len(reals):<3} {dn:<14.1e} {dc:<24.1e} {realstr:<17} {' '.join(f'{x:+.3f}' for x in angs) or '—'}")

    P("# T1 の実化：χ と χ̄ の組の上で U は実の 2 次元の回転（例 N = 5、13）")
    for N in (5, 13):
        U_, idx, res = a1_phases(N)
        m = len(U_)
        done = []
        for c, W, a, r in res:
            if r or any(np.allclose(c, d.conj(), atol=1e-8) for d in done):
                continue
            done.append(c)
            v = c / math.sqrt(m)
            Re, Im = np.sqrt(2) * v.real, np.sqrt(2) * v.imag
            Umat = W * np.outer(v, v.conj()) + W.conjugate() * np.outer(v.conj(), v)
            R = np.array([[Re @ (Umat @ Re), Re @ (Umat @ Im)], [Im @ (Umat @ Re), Im @ (Umat @ Im)]])
            ang = math.atan2(R[1, 0].real, R[0, 0].real) / math.pi
            P(f"  N = {N:<3} 組の行列（Re χ, Im χ の基底）= [[{R[0,0].real:+.4f}, {R[0,1].real:+.4f}], [{R[1,0].real:+.4f}, {R[1,1].real:+.4f}]]、"
              f"虚部の最大 {np.abs(R.imag).max():.1e}、回転角/π = {ang:+.4f}、arg𝔀/π = {cmath.phase(W)/math.pi:+.4f}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
