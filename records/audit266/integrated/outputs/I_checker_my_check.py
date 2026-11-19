# Independent check (numeric, not a proof). Lean-style definitions from §C:
# kS = extS(ket), ket at shell 0 on Z/p^K: x -> chi(x mod p^c) (normalisation common, dropped)
# BS(F,G) = extS(conv F.1 G.1); BN(F,G) = W(BS(W F, W G)) = extN(conv F.2 G.2)
import math, cmath, sys
sys.path.insert(0, '/tmp/indep_int266_I')
import numpy as np
from equator_U_check import characters, is_primitive, mul, J, tau, w

def model(p, c, K, c1, c2):
    Nc = p**c; NK = p**K
    U = [x for x in range(NK) if math.gcd(x, NK) == 1]
    Us = set(U)
    inv = lambda x: pow(x, -1, NK)
    ev = lambda ch, x: ch.get(x % Nc, 0.0)
    def extS(h): return (h, {y: (h[inv(y)] if y in Us else 0.0) for y in range(NK)})
    def extN(h): return ({x: (h[inv(x)] if x in Us else 0.0) for x in range(NK)}, h)
    def conv(f, g): return {x: sum(f[y]*g[(x-y) % NK] for y in range(NK)) for x in range(NK)}
    k1 = extS({x: ev(c1, x) for x in range(NK)}); k2 = extS({x: ev(c2, x) for x in range(NK)})
    BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
    return U, BS, BN

def lean_div(a, b): return 0.0 if abs(b) < 1e-12 else a/b

def run(p, c, K):
    Nc = p**c
    chars = characters(Nc); prim = [ch for ch in chars if is_primitive(Nc, ch, p)]
    stats = dict(pairs=0, Jzero=0, ratio_ok=0, ratio_tested=0, np12=0, np12_thm4_fail=0, np12_thm4_fail_unit=0,
                 np12_thm4_fail_nonunit=0, p12_thm4_ok=0, p12=0, wcoef_eq_conjJhat2_np=0, thm1_np_ok=0, thm2_np_ok=0)
    for c1 in prim:
        for c2 in prim:
            stats['pairs'] += 1
            c12 = mul(c1, c2); prim12 = is_primitive(Nc, c12, p)
            Jv = J(Nc, c1, c2)
            U, BS, BN = model(p, c, K, c1, c2)
            coef = lean_div(w(Nc, c12), w(Nc, c1)*w(Nc, c2))**2
            Jh = Jv/math.sqrt(Nc)
            # theorem 4 statement on all points of both charts
            ok_all = all(np.isclose(BN[i][x], coef*BS[i][x], atol=1e-7) for i in range(2) for x in BS[0])
            if abs(Jv) < 1e-9: stats['Jzero'] += 1
            else:
                rs = [BN[0][x]/BS[0][x] for x in U if abs(BS[0][x]) > 1e-9]
                stats['ratio_tested'] += 1
                stats['ratio_ok'] += bool(rs) and all(np.isclose(t, np.conj(Jv)/Jv) for t in rs)
            if prim12:
                stats['p12'] += 1; stats['p12_thm4_ok'] += ok_all
            else:
                stats['np12'] += 1
                if not ok_all:
                    stats['np12_thm4_fail'] += 1
                    unit_bad = any(not np.isclose(BN[i][x], coef*BS[i][x], atol=1e-7) for i in range(2) for x in U)
                    nonunit_bad = any(not np.isclose(BN[i][x], coef*BS[i][x], atol=1e-7) for i in range(2) for x in BS[0] if math.gcd(x, p) != 1)
                    stats['np12_thm4_fail_unit'] += unit_bad; stats['np12_thm4_fail_nonunit'] += nonunit_bad
                stats['wcoef_eq_conjJhat2_np'] += np.isclose(coef, np.conj(Jh)**2)
                # theorems 1,2 without h12 (Lean division convention)
                rhs1 = math.sqrt(Nc)*lean_div(tau(Nc, c12), tau(Nc, c1)*tau(Nc, c2))
                stats['thm1_np_ok'] += np.isclose(np.conj(Jh), rhs1)
                a1 = 0 if abs(c1[Nc-1]-1) < 1e-8 else 1; a2 = 0 if abs(c2[Nc-1]-1) < 1e-8 else 1
                s = -1 if (a1 == 1 and a2 == 1) else 1
                rhs2 = s*lean_div(w(Nc, c12), w(Nc, c1)*w(Nc, c2))
                stats['thm2_np_ok'] += np.isclose(np.conj(Jh), rhs2)
    print(f"p={p} c=n+1={c} K={K}:", stats)

if __name__ == '__main__':
    for (p, c, K) in [(5,1,1),(7,1,1),(5,1,2),(7,1,2),(3,2,2),(3,2,3),(5,2,2),(3,3,3),(3,1,1),(3,1,2)]:
        run(p, c, K)
