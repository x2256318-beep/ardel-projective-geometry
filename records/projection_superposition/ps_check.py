#!/usr/bin/env python3
"""「射影」の変換と重ね合わせ（事前登録の数値）。numpy だけを使う。

記号は PAG256（Part 252）に合わせる：e(t) = exp(2πi t/N)、cas(θ) = cos θ + sin θ、(H_N f)(y) = Σ_x f(x) cas(2π xy/N)、
(J g)(u) = g(u⁻¹)、W(χ) = τ(χ)/(i^a √N)、τ(χ) = Σ_x χ(x) e(x/N)。

C1  可換性：H_N と殻の射影 D_s、U（原始指標の空間の上の J H_N/√N）と D_s、U と単数の座標の射影 P_x の交換子のノルム。
    U を原始指標の基底で作ったもの（位相 W(χ)）と J H_N/√N を原始指標の空間に挟んだものの差（Part 252 の式の数値の確認）。
C2  （位相「逆規約の有限」は χ(−1)τ(χ)/√N：逆の規約で有限素点の局所定数の積に当たるもの。CLAUDE.md §1）
    重ね合わせの度合い：原始指標の空間の正規直交基底として「単数の座標に最も近い」基底（δ_y の射影を正規化したもの、
    素数の法では平均を引いた δ_y）を使い、U でその像がどれだけ単数の座標の上に広がるか（平坦さ φ·max p、
    エントロピー / log φ）。位相を (A1) W(χ)、(素朴) τ(χ)/√N、(自明) 1、(乱数) 一様な位相、で比べる。
C3  不確定性：単数の座標と指標は互いに偏りのない基底なので、エントロピーの和は log φ 以上（Maassen–Uffink）。
    位相を変えても指標の基底での分布は変わらない（数値で確認）。
C4  対照群：有限体 𝔽_9 = 𝔽_3[t]/(t² + 1) の乗法群（位数 8）の指標と、加法指標 ψ(a + bt) = e(2a/3)（トレース）での
    ガウス和の位相で、C2 と同じ量。
"""
import math
import cmath
import numpy as np

RNG = np.random.default_rng(20261126)


def units(N):
    return [u for u in range(1, N) if math.gcd(u, N) == 1]


def char_table(N):
    """(ℤ/N)^× の指標を、乗法の作用素の同時固有ベクトルとして数値で作る。行 = 指標、列 = 単数。"""
    U = units(N)
    idx = {u: i for i, u in enumerate(U)}
    m = len(U)
    A = np.zeros((m, m), dtype=complex)
    for g in U:
        Mg = np.zeros((m, m))
        for u in U:
            Mg[idx[(g * u) % N], idx[u]] = 1
        A += RNG.normal() * Mg + 1j * RNG.normal() * Mg
    w, V = np.linalg.eig(A)
    chars = []
    for k in range(m):
        v = V[:, k]
        v = v / v[idx[1]]  # χ(1) = 1
        chars.append(v)
    chars = np.array(chars)
    # 値を 1 の冪根に丸めて確認
    assert np.allclose(np.abs(chars), 1, atol=1e-8)
    return U, idx, chars


def is_primitive(N, U, idx, chi):
    for d in range(1, N):
        if N % d == 0:
            # 法 d で 1 に合同な単数で χ = 1 なら、χ は法 d から来る
            if all(abs(chi[idx[u]] - 1) < 1e-8 for u in U if (u - 1) % d == 0):
                return False
    return True


def setup(N):
    U, idx, chars = char_table(N)
    prim = [c for c in chars if is_primitive(N, U, idx, c)]
    m = len(U)
    e = lambda t: cmath.exp(2j * math.pi * t / N)
    data = []
    for c in prim:
        tau = sum(c[idx[u]] * e(u) for u in U)
        a = 0 if abs(c[idx[N - 1]] - 1) < 1e-8 else 1
        W = tau / ((1j) ** a * math.sqrt(N))
        data.append((c / math.sqrt(m), tau, a, W))
    return U, idx, data


def U_from_phases(data, phases):
    m = len(data[0][0])
    Umat = np.zeros((m, m), dtype=complex)
    for (v, _, _, _), w in zip(data, phases):
        Umat += w * np.outer(v, v.conj())
    return Umat


def JH_on_units(N, U, idx):
    m = len(U)
    M = np.zeros((m, m), dtype=complex)  # (J H f)(u) = Σ_x f(x) cas(2π x u⁻¹/N)、f は単数の上（他は 0）
    for i, u in enumerate(U):
        uinv = pow(u, -1, N)
        for j, x in enumerate(U):
            th = 2 * math.pi * x * uinv / N
            M[i, j] = math.cos(th) + math.sin(th)
    return M / math.sqrt(N)


def spread_stats(Umat, Pi, m):
    """基底：δ_y を原始指標の空間に射影して正規化したもの。像の分布の平坦さとエントロピー。"""
    flat, ent = [], []
    for y in range(m):
        b = Pi[:, y].copy()
        if np.linalg.norm(b) < 1e-12:
            continue
        b /= np.linalg.norm(b)
        v = Umat @ b
        p = np.abs(v) ** 2
        p /= p.sum()
        flat.append(m * p.max())
        pp = p[p > 1e-15]
        ent.append(-np.sum(pp * np.log(pp)) / math.log(m))
    return np.mean(flat), np.max(flat), np.mean(ent)


def main():
    out = []
    P = out.append
    P("# C1 可換性（交換子の作用素ノルム）と、Part 252 の式の数値の確認")
    for N in (7, 11, 13, 15, 16, 21):
        # ℂ^N の上の H_N と殻 D_s
        Hm = np.array([[math.cos(2 * math.pi * x * y / N) + math.sin(2 * math.pi * x * y / N) for x in range(N)] for y in range(N)])
        shells = sorted({math.gcd(x, N) for x in range(N)})
        cH = max(np.linalg.norm(Hm @ np.diag([1.0 if math.gcd(x, N) == s else 0 for x in range(N)])
                                - np.diag([1.0 if math.gcd(x, N) == s else 0 for x in range(N)]) @ Hm, 2) for s in shells)
        U_, idx, data = setup(N)
        m = len(U_)
        Ua1 = U_from_phases(data, [d[3] for d in data])
        Pi = U_from_phases(data, [1.0] * len(data))  # 原始指標の空間への射影
        JH = JH_on_units(N, U_, idx)
        diff = np.linalg.norm(Ua1 - Pi @ JH @ Pi, 2)
        # U を ℂ^N に（単数の外は 0 で）延ばし、殻 D_s との交換子
        emb = np.zeros((N, m))
        for i, u in enumerate(U_):
            emb[u, i] = 1
        UN = emb @ Ua1 @ emb.T
        cUD = max(np.linalg.norm(UN @ np.diag([1.0 if math.gcd(x, N) == s else 0 for x in range(N)])
                                 - np.diag([1.0 if math.gcd(x, N) == s else 0 for x in range(N)]) @ UN, 2) for s in shells)
        cUP = max(np.linalg.norm(Ua1 @ np.diag(np.eye(m)[i]) - np.diag(np.eye(m)[i]) @ Ua1, 2) for i in range(m))
        unit = np.linalg.norm(Ua1.conj().T @ Ua1 - Pi, 2)
        P(f"  N = {N:<3} 原始指標 {len(data):<3} ‖[H_N, D_s]‖max = {cH:.3f}   ‖[U, D_s]‖max = {cUD:.1e}   "
          f"‖[U, P_x]‖max = {cUP:.3f}   ‖U − Π(JH/√N)Π‖ = {diff:.1e}   ‖U*U − Π‖ = {unit:.1e}")

    P("# C2 重ね合わせの度合い（基底は δ_y の原始指標の空間への射影、像の分布：平坦さ m·max p の平均と最大、エントロピー/log m の平均）")
    P("  m は単数の個数。完全に平坦なら平坦さ 1、エントロピー比 1。")
    for N in (11, 13, 17, 19, 23, 29, 31, 15, 21):
        U_, idx, data = setup(N)
        m = len(U_)
        Pi = U_from_phases(data, [1.0] * len(data))
        rows = []
        for name, ph in [("A1", [d[3] for d in data]),
                         ("素朴", [d[1] / math.sqrt(N) for d in data]),
                         ("逆規約の有限", [(1 if d[2] == 0 else -1) * d[1] / math.sqrt(N) for d in data]),
                         ("自明", [1.0] * len(data))]:
            f_mean, f_max, e_mean = spread_stats(U_from_phases(data, ph), Pi, m)
            rows.append(f"{name}：{f_mean:.2f}/{f_max:.2f}/{e_mean:.3f}")
        fs, fm, es = [], [], []
        for _ in range(200):
            ph = np.exp(2j * math.pi * RNG.random(len(data)))
            a, b, c = spread_stats(U_from_phases(data, ph), Pi, m)
            fs.append(a); fm.append(b); es.append(c)
        rows.append(f"乱数（200 回の平均）：{np.mean(fs):.2f}/{np.mean(fm):.2f}/{np.mean(es):.3f}")
        P(f"  N = {N:<3} m = {m:<3} " + "  ".join(rows))

    P("# C3 指標の基底での分布は位相で変わらない（最大の差）と、エントロピーの和の下限 log m")
    for N in (13, 21):
        U_, idx, data = setup(N)
        m = len(U_)
        Pi = U_from_phases(data, [1.0] * len(data))
        Ua1 = U_from_phases(data, [d[3] for d in data])
        V = np.array([d[0] for d in data])  # 原始指標（正規化）
        worst = 0.0
        min_sum = 1e9
        for y in range(m):
            b = Pi[:, y].copy()
            b /= np.linalg.norm(b)
            p0 = np.abs(V.conj() @ b) ** 2
            p1 = np.abs(V.conj() @ (Ua1 @ b)) ** 2
            worst = max(worst, np.abs(p0 - p1).max())
            v = Ua1 @ b
            px = np.abs(v) ** 2; px /= px.sum()
            pc = p1 / p1.sum()
            Hx = -np.sum(px[px > 1e-15] * np.log(px[px > 1e-15]))
            Hc = -np.sum(pc[pc > 1e-15] * np.log(pc[pc > 1e-15]))
            min_sum = min(min_sum, Hx + Hc)
        P(f"  N = {N}：指標の基底の分布の差の最大 {worst:.1e}、エントロピーの和の最小 {min_sum:.3f}（log m = {math.log(m):.3f}）")

    # C4 対照群 𝔽_9
    P("# C4 対照群：𝔽_9 = 𝔽_3[t]/(t² + 1) の乗法群（位数 8）")
    # 元を (a, b) ↦ a + b t。生成元を探す
    def mul(x, y):
        a, b = x; c, d = y
        return ((a * c - b * d) % 3, (a * d + b * c) % 3)
    els = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
    gen = None
    for g in els:
        x, order = g, 1
        while x != (1, 0):
            x = mul(x, g); order += 1
        if order == 8:
            gen = g; break
    powers = [(1, 0)]
    for _ in range(7):
        powers.append(mul(powers[-1], gen))
    m = 8
    psi = lambda x: cmath.exp(2j * math.pi * (2 * x[0] % 3) / 3)
    data = []
    for k in range(1, 8):  # 自明でない指標 χ_k(gen^j) = exp(2πi kj/8)
        v = np.array([cmath.exp(2j * math.pi * k * j / 8) for j in range(8)])
        tau = sum(v[j] * psi(powers[j]) for j in range(8))
        data.append((v / math.sqrt(m), tau, None, tau / 3.0))
    Pi = U_from_phases(data, [1.0] * len(data))
    taus = [abs(d[1]) for d in data]
    rows = []
    for name, ph in [("ガウス和の位相 τ/3", [d[3] for d in data]), ("自明", [1.0] * 7)]:
        a, b, c = spread_stats(U_from_phases(data, ph), Pi, m)
        rows.append(f"{name}：{a:.2f}/{b:.2f}/{c:.3f}")
    fs, fm, es = [], [], []
    for _ in range(200):
        ph = np.exp(2j * math.pi * RNG.random(7))
        a, b, c = spread_stats(U_from_phases(data, ph), Pi, m)
        fs.append(a); fm.append(b); es.append(c)
    rows.append(f"乱数（200 回の平均）：{np.mean(fs):.2f}/{np.mean(fm):.2f}/{np.mean(es):.3f}")
    P(f"  |τ(χ)| = {min(taus):.6f}〜{max(taus):.6f}（√9 = 3）  " + "  ".join(rows))
    print("\n".join(out))


if __name__ == '__main__':
    main()
