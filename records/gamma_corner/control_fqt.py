"""対照群（関数体）：R = F_p[t]/(t^e) → R' = F_p[t]/(t^{e'})（e' ≤ e）で、同じ角の写像の確認（数値。証明ではない）。
A_R：R^× の乗法の軌道（殻）の指示関数の掛け算 D と、加法指標の R^× 軌道（双対殻）への射影 E が生成する代数。
加法指標 ψ_a(x) = exp(2πi λ(a x)/p)、λ = t^{e-1} の係数。"""
import itertools, sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
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

def orbits(els, idx, mul, units):
    seen, orbs = set(), []
    for x in els:
        if x in seen: continue
        o = {mul(u, x) for u in units}
        seen |= o; orbs.append(sorted(idx[y] for y in o))
    return orbs

def alg(p, e):
    els, idx, mul, units = ring(p, e)
    n = len(els)
    F = np.array([[np.exp(2j * np.pi * mul(a, x)[e - 1] / p) for x in els] for a in els]) / np.sqrt(n)
    orbs = orbits(els, idx, mul, units)
    D = [np.diag([1.0 if i in o else 0.0 for i in range(n)]).astype(complex) for o in orbs]
    E = [F.conj().T @ np.diag([1.0 if i in o else 0.0 for i in range(n)]) @ F for o in orbs]
    G = D + E
    B = orth_basis([np.eye(n, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(n, n) for i in range(B.shape[1])]
        B2 = orth_basis(mats + [a @ g for a in mats for g in G])
        if B2.shape[1] == B.shape[1]: break
        B = B2
    return els, B, D, E, F, orbs

for p, emax in [(2, 4), (3, 3)]:
    for e in range(1, emax + 1):
        els, B, D, E, F, orbs = alg(p, e)
        for e2 in range(1, e + 1):
            els2, B2, D2, E2, F2, _ = alg(p, e2)
            n, n2 = len(els), len(els2)
            P = np.zeros((n, n2), dtype=complex)
            idx2 = {x: i for i, x in enumerate(els2)}
            for i, x in enumerate(els): P[i, idx2[x[:e2]]] = 1.0
            I = P / np.sqrt(n / n2)
            phi = lambda T: I @ T @ I.conj().T
            inA = all(in_span(B, phi(X)) for X in D2 + E2)
            Q = I @ I.conj().T
            img = orth_basis([phi(B2[:, i].reshape(n2, n2)) for i in range(B2.shape[1])]).shape[1]
            cor = orth_basis([Q @ B[:, i].reshape(n, n) @ Q for i in range(B.shape[1])]).shape[1]
            Estrict = all(any(np.allclose(phi(X), Y) for Y in E) for X in E2)
            print(f'p={p} e\'={e2} → e={e}: dimA_R\'={B2.shape[1]} dimA_R={B.shape[1]} 像⊂A_R {inA} φ(E)は E のどれか {Estrict} dim像={img} dim角={cor}')
