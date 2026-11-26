#!/usr/bin/env python3
"""重ね合わせの言葉による解像度の読み（Q1・Q2）の事前登録の数値。numpy だけを使う。

計算の上の打ち切り：素数を P = (2, 3, 5, 7) に限り、指数を |e_p| ≤ E の箱に限る。
箱は計算のための打ち切りであり、解像度ではない（解像度のパラメータは未決定のまま）。

N1  L = Σ e_p log p の固有値：窓 [−1, 1] の中の個数、最大の隙間、最小の差（単純性の数値の確認）、
    幅 δ のビンのうち固有値を含む割合。
N2  L のまわりに集まった状態 c(e) ∝ exp(−L(e)²/(2σ²)) で、S の付値だけを測ったときに残る L の揺らぎ
    E[Var(L | e_S)]。
N3  もつれのエントロピー（素数の 2 分割）：集まった状態、基底ベクトル（積状態）、素数ごとの積の状態。
N4  対照群：関数体型（log p を (次数)·log 2 に置き換える、次数 1, 1, 2, 3）と、一般化素数型（乱数の対数）。
N5  δ-鎖の類の個数（窓 [−1, 1] の固有値、δ = 0.05）。
"""
import itertools
import math
import sys
import numpy as np

P = (2, 3, 5, 7)
LOGS_Q = np.log(np.array(P, dtype=float))


def box(E):
    r = np.arange(-E, E + 1)
    return np.array(list(itertools.product(r, repeat=len(P))))


def spectrum_stats(Lv, w=1.0, delta=0.05):
    x = np.sort(Lv[np.abs(Lv) <= w])
    gaps = np.diff(x)
    bins = np.arange(-w, w + 1e-12, delta)
    hit = np.histogram(x, bins=bins)[0] > 0
    # δ-鎖の類：隣り合う差が δ 以上のところで切れる
    clusters = 1 + int(np.sum(gaps >= delta)) if len(x) else 0
    return len(x), gaps.max() if len(gaps) else float('nan'), gaps.min() if len(gaps) else float('nan'), hit.mean(), clusters


def packet(Lv, sigma):
    c = np.exp(-Lv ** 2 / (2 * sigma ** 2))
    return c / np.linalg.norm(c)


def cond_var(E, Lv, c, S_idx):
    """E[Var(L | e_S)]（確率は |c|²）。"""
    pr = c ** 2
    ev = box(E)
    if len(S_idx) == 0:
        m = np.sum(pr * Lv)
        return float(np.sum(pr * (Lv - m) ** 2))
    keys = ev[:, S_idx]
    # キーごとにまとめる
    _, inv = np.unique(keys, axis=0, return_inverse=True)
    inv = inv.ravel()
    w = np.bincount(inv, weights=pr)
    m1 = np.bincount(inv, weights=pr * Lv)
    m2 = np.bincount(inv, weights=pr * Lv ** 2)
    ok = w > 0
    var_k = m2[ok] / w[ok] - (m1[ok] / w[ok]) ** 2
    return float(np.sum(w[ok] * np.maximum(var_k, 0)))


def ent_entropy(E, c, A_idx):
    n = 2 * E + 1
    k = len(P)
    T = c.reshape((n,) * k)
    B_idx = [i for i in range(k) if i not in A_idx]
    M = np.transpose(T, list(A_idx) + B_idx).reshape(n ** len(A_idx), -1)
    s = np.linalg.svd(M, compute_uv=False)
    p = s ** 2
    p = p[p > 1e-15]
    p = p / p.sum()
    return float(-np.sum(p * np.log2(p)))


def main():
    out = []
    Pr = out.append
    Pr(f"# 素数 {P}、指数の箱 |e_p| ≤ E（計算の打ち切り）")

    Pr("# N1 L のスペクトル（窓 [−1, 1]、δ = 0.05）")
    Pr("  系        E   窓の固有値の数  最大の隙間   最小の差     ビンの被覆  δ-鎖の類（N5）")
    rng = np.random.default_rng(20261126)
    beurling_logs = np.sort(rng.uniform(0.6, 2.2, size=len(P)))
    ff_logs = np.array([1, 1, 2, 3], dtype=float) * math.log(2)
    systems = [("ℚ", LOGS_Q), ("関数体型", ff_logs), ("一般化素数型", beurling_logs)]
    for name, logs in systems:
        for E in (2, 4, 6, 8):
            ev = box(E)
            Lv = ev @ logs
            n, gmax, gmin, cov, cl = spectrum_stats(Lv)
            Pr(f"  {name:<8} {E:<3} {n:<15d} {gmax:<11.4f} {gmin:<12.2e} {cov:<10.3f} {cl}")
    Pr(f"  一般化素数型の対数（乱数、シード 20261126）：{np.round(beurling_logs, 4).tolist()}")
    Pr("  注：関数体型の最小の差 0 は固有値の重複（同じ次数の和）を表す。")

    E = 6
    ev = box(E)
    Pr(f"# N2 S だけを測ったときに残る L の揺らぎ E[Var(L | e_S)]（ℚ、E = {E}）")
    for sigma in (0.1, 0.3):
        Lv = ev @ LOGS_Q
        c = packet(Lv, sigma)
        row = []
        for S in ([], [0], [0, 1], [0, 1, 2], [0, 1, 2, 3]):
            row.append(f"S={{{','.join(str(P[i]) for i in S)}}}: {cond_var(E, Lv, c, S):.4e}")
        Pr(f"  σ = {sigma}：" + "、".join(row))

    Pr(f"# N3 もつれのエントロピー（ビット、E = {E}）")
    for name, logs in systems:
        Lv = ev @ logs
        c = packet(Lv, 0.1)
        Pr(f"  {name}：集まった状態（σ = 0.1）  {{2}}|{{3,5,7}}: {ent_entropy(E, c, [0]):.3f}、"
           f"{{2,3}}|{{5,7}}: {ent_entropy(E, c, [0, 1]):.3f}")
    d = np.zeros(len(ev)); d[np.argmin(np.abs(ev @ LOGS_Q - math.log(6)))] = 1.0
    Pr(f"  基底ベクトル δ_6：{{2}}|{{3,5,7}}: {ent_entropy(E, d, [0]):.3f}")
    g = np.exp(-(ev.astype(float) ** 2).sum(axis=1) / 4.0); g /= np.linalg.norm(g)
    Pr(f"  素数ごとの積の状態 Π_p exp(−e_p²/4)：{{2}}|{{3,5,7}}: {ent_entropy(E, g, [0]):.3f}、"
       f"{{2,3}}|{{5,7}}: {ent_entropy(E, g, [0, 1]):.3f}")
    print("\n".join(out))


if __name__ == '__main__':
    main()
