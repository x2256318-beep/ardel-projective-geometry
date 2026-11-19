"""対照群（関数体）：R = F_p[t]/(t^e) で、相互作用の各項目が同じ形で成り立つか（数値。証明ではない）。2026-11-19。
A_R：R^× の軌道（殻）の指示関数の掛け算 D と、双対殻への射影 E が生成する代数（records/gamma_corner/control_fqt.py と同じ構成）。
J：殻ごとの反転 t^k w ↦ t^k w⁻¹。F：加法指標 ψ_a(x) = exp(2πi λ(ax)/p)（λ = t^{e-1} の係数）によるフーリエ。
"""
import itertools, sys, cmath, math
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import orth_basis, in_span

def ring(p, e):
    els = list(itertools.product(range(p), repeat=e))
    idx = {x: i for i, x in enumerate(els)}
    def mul(x, y):
        z = [0] * e
        for i in range(e):
            for j in range(e - i):
                z[i + j] = (z[i + j] + x[i] * y[j]) % p
        return tuple(z)
    units = [x for x in els if x[0] % p != 0]
    return els, idx, mul, units

def alg(p, e):
    els, idx, mul, units = ring(p, e)
    n = len(els)
    F = np.array([[np.exp(2j * np.pi * mul(a, x)[e - 1] / p) for x in els] for a in els]) / np.sqrt(n)
    seen, orbs = set(), []
    for x in els:
        if x in seen: continue
        o = {mul(u, x) for u in units}; seen |= o; orbs.append(sorted(idx[y] for y in o))
    D = [np.diag([1.0 if i in o else 0.0 for i in range(n)]).astype(complex) for o in orbs]
    E = [F.conj().T @ np.diag([1.0 if i in o else 0.0 for i in range(n)]) @ F for o in orbs]
    G = D + E
    B = orth_basis([np.eye(n, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(n, n) for i in range(B.shape[1])]
        B2 = orth_basis(mats + [a @ g for a in mats for g in G])
        if B2.shape[1] == B.shape[1]: break
        B = B2
    return els, idx, mul, units, B, D, E, F, orbs

def val(x):
    for i, c in enumerate(x):
        if c: return i
    return len(x)

def inv_unit(mul, units, w):
    one = tuple([1] + [0] * (len(w) - 1))
    for u in units:
        if mul(u, w) == one: return u
    raise ValueError

def shell_inv(p, e, els, idx, mul, units):
    n = len(els); J = np.zeros((n, n), dtype=complex)
    for x in els:
        k = val(x)
        if k == e: y = x
        else:
            # x = t^k w、w は法 t^{e-k} の単数（代表：x を k だけ左に詰め、残りを 0 で埋める）
            m = e - k
            _, _, mul_m, units_m = ring(p, m)
            w = x[k:]; wi = inv_unit(mul_m, units_m, w)
            y = tuple([0] * k + list(wi))
        J[idx[x], idx[y]] = 1.0
    return J

for p, emax in [(2, 4), (3, 3), (5, 2)]:
    for e in range(1, emax + 1):
        els, idx, mul, units, B, D, E, F, orbs = alg(p, e)
        n = len(els)
        comm = lambda X: all(np.allclose(B[:, i].reshape(n, n) @ X, X @ B[:, i].reshape(n, n)) for i in range(B.shape[1]))
        R = {}
        for u in units:
            M = np.zeros((n, n), dtype=complex)
            for x in els: M[idx[x], idx[mul(u, x)]] = 1.0
            R[u] = M
        J = shell_inv(p, e, els, idx, mul, units)
        Fi = F.conj().T
        swap = all(any(np.allclose(F @ d @ Fi, x) for x in E) for d in D) and all(any(np.allclose(F @ x @ Fi, d) for d in D) for x in E)
        JFnorm = all(in_span(B, J @ F @ B[:, i].reshape(n, n) @ Fi @ J.T) for i in range(B.shape[1]))
        # 単数の角と、ガウス和の位相（原始指標で、導手ごとに一定か）
        Ui = [idx[u] for u in units]; phi = len(Ui)
        S = np.zeros((n, phi), dtype=complex)
        for j, i in enumerate(Ui): S[i, j] = 1.0
        cor = orth_basis([S.T @ B[:, i].reshape(n, n) @ S for i in range(B.shape[1])])
        # 指標：R_u の単数への制限の同時対角化
        rng = np.random.default_rng(2); c = rng.normal(size=phi) + 1j * rng.normal(size=phi)
        Mx = sum(c[k] * (S.T @ R[u] @ S) for k, u in enumerate(units))
        w, V = np.linalg.eig(Mx)
        one = tuple([1] + [0] * (e - 1)); i1 = units.index(one)
        phases = []; Umat = np.zeros((phi, phi), dtype=complex)
        for j in range(phi):
            v = V[:, j] / V[i1, j]
            # 導手 t^f：u ≡ 1 (mod t^f) で χ(u) = 1 となる最小の f
            f = next(f for f in range(e + 1) if all(abs(v[k] - 1) < 1e-8 for k, u in enumerate(units) if all(u[i] == one[i] for i in range(f))))
            # J F χ = λ χ の固有値 λ（原始指標ではガウス和の位相）
            g = np.zeros(n, dtype=complex); g[Ui] = v
            h = J @ F @ g
            lam = h[Ui[i1]] / v[i1]
            phases.append((f, lam))
            Umat += lam * np.outer(v, v.conj()) / phi
        prim = [lam for f, lam in phases if f == e]
        var = (max(abs(a - b) for a in prim for b in prim) if len(prim) > 1 else 0.0)
        Uin = in_span(cor, Umat)
        print(f'p={p} e={e}: dimA={B.shape[1]} R_u可換 {all(comm(X) for X in R.values())} J可換 {comm(J)} F交換 {swap} JF正規化 {JFnorm} '
              f'角の次元 {cor.shape[1]} 導手の数 {len({f for f, _ in phases})} 原始の位相の幅 {var:.3f} JF|単数∈角 {Uin}')
