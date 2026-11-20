"""
Partial inversion / non-local part e of the gluing phases (A1 removed).

For N = prod p^k (odd primes here; local primitive characters enumerated via a generator),
alpha : P_N -> U(1) free. We study
  (L)  alpha(chi^(p)) / alpha(chi) depends only on chi_p          (chi^(p): conjugate the p-component)
  Loc  = { prod_p f_p(chi_p) }
  (G1) homogeneous inversion condition  alpha(conj chi) * alpha(chi) = c(parity)   [known c; differences satisfy
       alpha(conj chi) alpha(chi) = 1]
  (G2') N = ab: alpha / (local product) is a function of (chi_a(b), chi_b(a), parities)   [kappa NOT prescribed]
  Par  = functions of the parity vector (chi_p(-1))_p
Two layers are computed:
  * continuous part: Lie algebra (real-valued log-phases), dimensions over R
  * sign part: +-1-valued functions, dimensions over F_2 (where the parity quadratic form lives)
Consistency only (not a derivation): the A1 phase rootNum = tau(chi)/(i^a sqrt N) is tested against (L).
Numerics are not proofs.
"""
import itertools, cmath, math, sys
import numpy as np

def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in set(f for f in range(2, p) if (p - 1) % f == 0 and all(f % r for r in range(2, f)))):
            return g
    return 1

def local_chars(p, k):
    """primitive characters mod p^k (p odd): chi(g^m) = exp(2 pi i j m / phi); primitive iff not trivial on 1+p^{k-1}."""
    q = p ** k; phi = q - q // p
    # generator of (Z/p^k)^x
    g = next(x for x in range(2, q) if math.gcd(x, p) == 1 and all(pow(x, phi // r, q) != 1 for r in {f for f in range(2, phi + 1) if phi % f == 0 and all(f % s for s in range(2, f))}))
    dlog = {}
    x = 1
    for m in range(phi):
        dlog[x] = m; x = x * g % q
    chars = []
    for j in range(phi):
        val = lambda n, j=j: 0 if math.gcd(n, p) != 1 else cmath.exp(2j * cmath.pi * j * dlog[n % q] / phi)
        # primitive: nontrivial on the kernel of reduction mod p^{k-1}
        if k == 1:
            prim = j != 0
        else:
            prim = abs(val(1 + p ** (k - 1)) - 1) > 1e-9
        if prim:
            chars.append(j)
    return q, phi, g, dlog, chars

def setup(primes_powers):
    loc = []
    for (p, k) in primes_powers:
        q, phi, g, dlog, chars = local_chars(p, k)
        loc.append(dict(p=p, k=k, q=q, phi=phi, dlog=dlog, chars=chars))
    P = list(itertools.product(*[L['chars'] for L in loc]))
    idx = {c: i for i, c in enumerate(P)}
    N = 1
    for L in loc: N *= L['q']
    return loc, P, idx, N

def val(L, j, n):
    n %= L['q']
    if math.gcd(n, L['p']) != 1: return 0
    return cmath.exp(2j * cmath.pi * j * L['dlog'][n] / L['phi'])

def parity(L, j):  # 0 even, 1 odd
    return 0 if abs(val(L, j, -1) - 1) < 1e-9 else 1

def conj_comp(L, j): return (-j) % L['phi']

def rank(rows, field='R'):
    if not rows: return 0
    M = np.array(rows, dtype=float)
    if field == 'R':
        return np.linalg.matrix_rank(M, tol=1e-8)
    # F_2 rank
    M = (M.astype(int) % 2)
    r = 0; m, n = M.shape
    for c in range(n):
        piv = next((i for i in range(r, m) if M[i, c]), None)
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(m):
            if i != r and M[i, c]: M[i] ^= M[r]
        r += 1
    return r

def nullspace_dim(constraints, n, field):
    return n - rank(constraints, field)

def analyse(pp, label):
    loc, P, idx, N = setup(pp)
    n = len(P); r = len(loc)
    # --- constraint rows for (L): for each p, and pairs chi, chi' with same chi_p:
    # a(chi^(p)) - a(chi) - a(chi'^(p)) + a(chi') = 0
    def flip(c, t):
        c = list(c); c[t] = conj_comp(loc[t], c[t]); return tuple(c)
    Lrows = []
    for t in range(r):
        groups = {}
        for c in P: groups.setdefault(c[t], []).append(c)
        for jt, cs in groups.items():
            base = cs[0]
            for c in cs[1:]:
                row = [0] * n
                for (cc, s) in [(flip(c, t), 1), (c, -1), (flip(base, t), -1), (base, 1)]:
                    row[idx[cc]] += s
                if any(row): Lrows.append(row)
    G1rows = []
    for c in P:
        cb = tuple(conj_comp(loc[t], c[t]) for t in range(r))
        row = [0] * n; row[idx[c]] += 1; row[idx[cb]] += 1
        G1rows.append(row)
    # spanning sets
    def span_loc():
        vecs = [[1] * n]
        for t in range(r):
            for j in loc[t]['chars']:
                vecs.append([1 if c[t] == j else 0 for c in P])
        return vecs
    def span_par():
        vecs = []
        for pv in itertools.product([0, 1], repeat=r):
            v = [1 if tuple(parity(loc[t], c[t]) for t in range(r)) == pv else 0 for c in P]
            if any(v): vecs.append(v)
        return vecs
    def span_cross():
        if r != 2: return None
        a, b = loc[0]['q'], loc[1]['q']
        keyf = lambda c: (round(val(loc[0], c[0], b).real, 6), round(val(loc[0], c[0], b).imag, 6),
                          round(val(loc[1], c[1], a).real, 6), round(val(loc[1], c[1], a).imag, 6),
                          parity(loc[0], c[0]), parity(loc[1], c[1]))
        fibers = {}
        for c in P: fibers.setdefault(keyf(c), []).append(c)
        return [[1 if c in set(fs) else 0 for c in P] for fs in fibers.values()]
    def sub_dim(span, cons, field):
        """dim of span ∩ nullspace(cons)"""
        if not span: return 0
        B = np.array(span, dtype=float)
        if field == 'R':
            # basis of span
            u, s, vt = np.linalg.svd(B, full_matrices=False)
            Bb = vt[s > 1e-8]
            if not cons: return len(Bb)
            C = np.array(cons, dtype=float)
            M = C @ Bb.T
            return len(Bb) - np.linalg.matrix_rank(M, tol=1e-8)
        else:
            # brute force over F_2 small: compute via rank of [B; ...]: dim(span ∩ ker C) = dim span - rank(C restricted)
            # get basis of span over F2
            Bm = (B.astype(int) % 2); basis = []
            M = Bm.copy(); rr = 0; mm, nn = M.shape
            for col in range(nn):
                piv = next((i for i in range(rr, mm) if M[i, col]), None)
                if piv is None: continue
                M[[rr, piv]] = M[[piv, rr]]
                for i in range(mm):
                    if i != rr and M[i, col]: M[i] ^= M[rr]
                rr += 1
            basis = M[:rr]
            if not cons: return rr
            C = (np.array(cons).astype(int) % 2)
            img = (C @ basis.T) % 2
            return rr - rank(img.T.tolist(), 'F2')
    out = {}
    for field in ['R', 'F2']:
        cons_L = Lrows
        S = nullspace_dim(cons_L, n, field)
        Loc = sub_dim(span_loc(), [], field)
        S_G1 = nullspace_dim(cons_L + G1rows, n, field)
        Loc_G1 = sub_dim(span_loc(), G1rows, field)
        LocPar = sub_dim(span_loc() + span_par(), [], field)
        LocPar_G1 = sub_dim(span_loc() + span_par(), G1rows, field)
        res = dict(S_over_Loc=S - Loc, SG1_over_LocG1=S_G1 - Loc_G1,
                   Par_over_Loc=LocPar - Loc, ParG1_over_LocG1=LocPar_G1 - Loc_G1)
        cr = span_cross()
        if cr is not None:
            LocCross = sub_dim(span_loc() + cr, cons_L, field)            # (Loc + F_cross) ∩ S
            LocCross_G1 = sub_dim(span_loc() + cr, cons_L + G1rows, field)
            res['SG2_over_Loc'] = LocCross - Loc
            res['SG1G2_over_LocG1'] = LocCross_G1 - Loc_G1
        out[field] = res
    # consistency: rootNum satisfies (L)?
    def tau(c):
        s = 0
        for x in range(N):
            if math.gcd(x, N) != 1: continue
            v = 1
            for t in range(r): v *= val(loc[t], c[t], x)
            s += v * cmath.exp(2j * cmath.pi * x / N)
        return s
    def rootnum(c):
        a = 0 if all(True for _ in [0]) else 0
        chim1 = 1
        for t in range(r): chim1 *= val(loc[t], c[t], -1)
        a = 0 if abs(chim1 - 1) < 1e-9 else 1
        return tau(c) / ((1j) ** a * math.sqrt(N))
    W = {c: rootnum(c) for c in P}
    okL = True
    for t in range(r):
        ratios = {}
        for c in P:
            rr_ = W[flip(c, t)] / W[c]
            key = c[t]
            if key in ratios and abs(ratios[key] - rr_) > 1e-7: okL = False
            ratios.setdefault(key, rr_)
    classes = [len({frozenset({j, conj_comp(L, j)}) for j in L['chars']}) for L in loc]
    par_classes = [len({parity(L, j) for j in L['chars']}) for L in loc]
    print(f"{label}: N={N} |P_N|={n} conj-classes per prime={classes} parities present={par_classes}  rootNum satisfies (L): {okL}")
    for field in ['R', 'F2']:
        print(f"   [{'continuous (dim over R)' if field=='R' else 'sign part (dim over F2)'}] " + ", ".join(f"{k}={v}" for k, v in out[field].items()))

if __name__ == '__main__':
    cases = [([(5, 1), (7, 1)], '5*7'), ([(5, 1), (13, 1)], '5*13'), ([(3, 1), (5, 1)], '3*5'),
             ([(5, 1), (9, 1) if False else (3, 2)], '5*9'), ([(7, 1), (13, 1)], '7*13'),
             ([(5, 1), (7, 1), (13, 1)], '5*7*13'), ([(3, 1), (5, 1), (7, 1)], '3*5*7')]
    for pp, lab in cases:
        analyse(pp, lab)
