# Drop h1 (chi1 non-primitive, chi2 primitive, chi1chi2 primitive): do thms 1,2,4 hold? (Lean division convention)
import math, sys
sys.path.insert(0, '/tmp/indep_int266_I')
import numpy as np
from equator_U_check import characters, is_primitive, mul, J, tau, w
from my_check import model, lean_div
for (p, c, K) in [(5,1,1),(7,1,1),(3,2,2),(5,2,2),(3,2,3)]:
    Nc = p**c; chars = characters(Nc)
    prim = [ch for ch in chars if is_primitive(Nc, ch, p)]; nonprim = [ch for ch in chars if not is_primitive(Nc, ch, p)]
    tot = t1 = t2 = t4 = zero_both = 0
    for c1 in nonprim:
        for c2 in prim:
            c12 = mul(c1, c2)
            if not is_primitive(Nc, c12, p): continue
            tot += 1
            Jh = J(Nc, c1, c2)/math.sqrt(Nc)
            r1 = math.sqrt(Nc)*lean_div(tau(Nc, c12), tau(Nc, c1)*tau(Nc, c2))
            a1 = 0 if abs(c1[Nc-1]-1) < 1e-8 else 1; a2 = 0 if abs(c2[Nc-1]-1) < 1e-8 else 1
            s = -1 if (a1 and a2) else 1
            r2 = s*lean_div(w(Nc, c12), w(Nc, c1)*w(Nc, c2))
            t1 += np.isclose(np.conj(Jh), r1); t2 += np.isclose(np.conj(Jh), r2)
            U, BS, BN = model(p, c, K, c1, c2); coef = lean_div(w(Nc, c12), w(Nc, c1)*w(Nc, c2))**2
            t4 += all(np.isclose(BN[i][x], coef*BS[i][x], atol=1e-7) for i in range(2) for x in BS[0])
            zero_both += np.isclose(abs(Jh), 0) and np.isclose(abs(r1), 0) and all(abs(BN[i][x]) < 1e-7 for i in range(2) for x in BN[0])
    print(f"p={p} n+1={c} K={K}: triples(chi1 nonprim) {tot}; thm1 holds {t1}; thm2 holds {t2}; thm4 holds {t4}; all-zero {zero_both}")
