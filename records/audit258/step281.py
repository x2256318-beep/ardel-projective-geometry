"""Part 258（方向βの前提）段階 2：N | M で、受容条件 1〜3 を満たす代数の写像 A_N → A_M があるかを数値で調べる。
数値の確認は証明ではない。

A_N：End(ℂ^{ℤ/N}) の中で D_s（空間の殻 gcd(N,x)=s の指示関数の掛け算）と E_s（フーリエ側で gcd(N,ξ)=s を残す射影）が生成する代数。
条件 1：代数準同型（単位元を保つ版／保たない版）。条件 2：φ(T) π^* = π^* T。条件 3（強い読み）：φ(D_s) ∈ span{D_t^M}、φ(E_s) ∈ span{E_t^M}。

強い読みでは、条件 2 から φ(D_s) = π^*(1_{S_s}) の掛け算に決まり、φ(E_s) はフーリエ側で V（N 周期の関数）の双対殻 t = (M/N)s'
では [s = s'] に決まる。V の外の双対殻 t の値は自由だが、E_s が互いに直交するべき等元なので、各 t を高々 1 つの s に割り当てる
（単位元を保つならちょうど 1 つ）。この有限の割り当てをすべて調べる。
"""
import itertools, math, sys
import numpy as np

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def gens(N):
    F = np.array([[np.exp(-2j * np.pi * k * x / N) for x in range(N)] for k in range(N)]) / np.sqrt(N)
    D = {s: np.diag([1.0 if math.gcd(N, x) == s else 0.0 for x in range(N)]).astype(complex) for s in divisors(N)}
    E = {s: F.conj().T @ np.diag([1.0 if math.gcd(N, k) == s else 0.0 for k in range(N)]) @ F for s in divisors(N)}
    return D, E, F

def rank(vs, tol=1e-8):
    if not vs: return 0
    return np.linalg.matrix_rank(np.array([v.ravel() for v in vs]), tol=tol)

def basis_words(G):
    """生成元の行列のリスト G から、A を張る語の基底（語は生成元の番号の列）。"""
    n = G[0].shape[0]
    I = np.eye(n, dtype=complex)
    B = [()]; Bm = [I]
    frontier = [()]
    while frontier:
        nf = []
        for w in frontier:
            Wm = Bm[B.index(w)]
            for gi, g in enumerate(G):
                cand = g @ Wm
                if rank(Bm + [cand]) > len(Bm):
                    B.append((gi,) + w); Bm.append(cand); nf.append((gi,) + w)
        frontier = nf
    return B, Bm

def coords(Bm, X):
    A = np.array([b.ravel() for b in Bm]).T
    c, *_ = np.linalg.lstsq(A, X.ravel(), rcond=None)
    return c, np.linalg.norm(A @ c - X.ravel())

def word_mat(w, G, n):
    X = np.eye(n, dtype=complex)
    for gi in reversed(w): X = G[gi] @ X
    return X

def is_hom(GN, GM, unital, tol=1e-7):
    """生成元の対応 GN[i] ↦ GM[i] が代数準同型に延びるか。"""
    n = GN[0].shape[0]; m = GM[0].shape[0]
    B, Bm = basis_words(GN)
    Phi = [word_mat(w, GM, m) for w in B]   # Φ(b) = 像の語
    if not unital:
        # 単位元を保たない場合：長さ 1 以上の語の張る空間で基底を取り直す（A_N は単位元を含むので、
        # 単位元が長さ 1 以上の語の線形結合で書けるなら全体になる）
        B, Bm = [], []
        frontier = []
        for gi, g in enumerate(GN):
            if rank(Bm + [g]) > len(Bm): B.append((gi,)); Bm.append(g); frontier.append((gi,))
        while frontier:
            nf = []
            for w in frontier:
                Wm = Bm[B.index(w)]
                for gi, g in enumerate(GN):
                    cand = g @ Wm
                    if rank(Bm + [cand]) > len(Bm):
                        B.append((gi,) + w); Bm.append(cand); nf.append((gi,) + w)
            frontier = nf
        Phi = [word_mat(w, GM, m) for w in B]
    def Phi_of(X):
        c, res = coords(Bm, X)
        if res > 1e-6: raise ValueError('not in A_N')
        return sum(ci * P for ci, P in zip(c, Phi))
    # 生成元の像が一致するか
    for g, h in zip(GN, GM):
        if np.linalg.norm(Phi_of(g) - h) > tol: return False, 'gen'
    # Φ(g b) = h Φ(b)
    for g, h in zip(GN, GM):
        for b, P in zip(Bm, Phi):
            if np.linalg.norm(Phi_of(g @ b) - h @ P) > tol: return False, 'mult'
    if unital:
        if np.linalg.norm(Phi_of(np.eye(n)) - np.eye(m)) > tol: return False, 'unit'
    return True, 'ok'

def pullback(N, M):
    P = np.zeros((M, N), dtype=complex)
    for y in range(M): P[y, y % N] = 1
    return P

def strong_candidates(N, M, unital):
    DN, EN, _ = gens(N); DM, EM, FM = gens(M)
    r = M // N
    # φ(D_s) は決まる
    phD = {s: sum((DM[t] for t in divisors(M) if math.gcd(N, t) == s), np.zeros((M, M), complex)) for s in divisors(N)}
    vt = {r * s: s for s in divisors(N)}               # V の双対殻 t = r·s → s
    free = [t for t in divisors(M) if t % r != 0]       # V の外の双対殻
    opts = list(divisors(N)) + ([] if unital else [None])
    res = []
    for assign in itertools.product(opts, repeat=len(free)):
        a = dict(zip(free, assign))
        phE = {}
        for s in divisors(N):
            X = np.zeros((M, M), complex)
            for t in divisors(M):
                if (t in vt and vt[t] == s) or (t in a and a[t] == s): X = X + EM[t]
            phE[s] = X
        GN = [DN[s] for s in divisors(N)] + [EN[s] for s in divisors(N)]
        GM = [phD[s] for s in divisors(N)] + [phE[s] for s in divisors(N)]
        ok, why = is_hom(GN, GM, unital)
        res.append((a, ok, why))
    return res

def check_cond2(N, M, GN, GM):
    P = pullback(N, M)
    return max(np.linalg.norm(h @ P - P @ g) for g, h in zip(GN, GM))

def in_span(X, Ys):
    return coords(Ys, X)[1] < 1e-6

def coprime_map(N, M):
    b = M // N; assert math.gcd(N, b) == 1
    # CRT：y ∈ ℤ/M ↦ (y mod N, y mod b)、添字 (x, z) ↦ x*b + z
    C = np.zeros((M, M))
    for y in range(M): C[(y % N) * b + (y % b), y] = 1
    def phi(T): return C.T @ np.kron(T, np.eye(b)) @ C
    return phi

if __name__ == '__main__':
    out = []
    def rep(s): print(s); out.append(s)
    pairs = [(2, 4), (2, 8), (3, 9), (4, 8), (2, 6), (3, 6), (2, 10), (3, 12)]
    for N, M in pairs:
        DN, EN, _ = gens(N); DM, EM, _ = gens(M)
        BN, _ = basis_words([DN[s] for s in divisors(N)] + [EN[s] for s in divisors(N)])
        BM, BMm = basis_words([DM[t] for t in divisors(M)] + [EM[t] for t in divisors(M)])
        line = f'(N,M)=({N},{M})  dim A_N={len(BN)}  dim A_M={len(BM)}  gcd(N,M/N)={math.gcd(N, M // N)}'
        for unital in (True, False):
            rs = strong_candidates(N, M, unital)
            good = [a for a, ok, why in rs if ok]
            line += f' | 強い読み・{"単位的" if unital else "非単位的"}：候補 {len(rs)}、通った {len(good)}'
            if good: line += f'（例 {good[0]}）'
            reasons = {}
            for a, ok, why in rs:
                if not ok: reasons[why] = reasons.get(why, 0) + 1
            if reasons: line += f'、落ちた理由 {reasons}'
        rep(line)
        if math.gcd(N, M // N) == 1:
            phi = coprime_map(N, M)
            GN = [DN[s] for s in divisors(N)] + [EN[s] for s in divisors(N)]
            GM = [phi(g) for g in GN]
            c2 = check_cond2(N, M, GN, GM)
            c3D = all(in_span(phi(DN[s]), [DM[t] for t in divisors(M)]) for s in divisors(N))
            c3E = all(in_span(phi(EN[s]), [EM[t] for t in divisors(M)]) for s in divisors(N))
            inA = all(in_span(X, BMm) for X in GM)
            unit = np.linalg.norm(phi(np.eye(N)) - np.eye(M)) < 1e-9
            rep(f'   互いに素：φ(T)=CRT⁻¹(T⊗1)：条件2 誤差 {c2:.1e}、条件3 D {c3D}・E {c3E}、像 ⊆ A_M {inA}、単位元 {unit}')
    open('/home/claude/out/prereg258/stage2.log', 'w').write('\n'.join(out) + '\n')
