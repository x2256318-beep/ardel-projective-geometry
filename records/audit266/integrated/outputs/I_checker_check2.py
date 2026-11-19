# equator_U_check (2): the script compares conj(Jhat)^2 with the unsquared w-ratio.
# Compare with the natural "square removed on both sides" version conj(Jhat) = w12/(w1 w2).
import math, sys
sys.path.insert(0, '/tmp/indep_int266_I')
import numpy as np
from equator_U_check import characters, is_primitive, mul, J, w, key
for (p, K) in [(5,1),(7,1),(11,1),(13,1),(3,2),(5,2),(3,3),(7,2)]:
    N = p**K; prim = [c for c in characters(N) if is_primitive(N, c, p)]
    pk = {key(N, c) for c in prim}
    n = mixed = natural = c_is_one = s_plus = 0
    for c1 in prim:
        for c2 in prim:
            c12 = mul(c1, c2)
            if key(N, c12) not in pk: continue
            n += 1
            Jh = J(N, c1, c2)/math.sqrt(N); c = w(N, c12)/(w(N, c1)*w(N, c2))
            mixed += np.isclose(np.conj(Jh)**2, c)
            natural += np.isclose(np.conj(Jh), c)
            c_is_one += np.isclose(c, 1)
            a1 = 0 if abs(c1[N-1]-1) < 1e-8 else 1; a2 = 0 if abs(c2[N-1]-1) < 1e-8 else 1
            s_plus += not (a1 == 1 and a2 == 1)
    print(f"N={N}: pairs {n}; script's test conj(Jh)^2==c: {mixed}; c==1: {c_is_one}; natural conj(Jh)==c: {natural}; pairs with s=+1: {s_plus}")
