import math, cmath, sys
import numpy as np
sys.path.insert(0, '/tmp/indep_int266_R2')
from equator_U_check import characters, is_primitive, mul, J, w
# (A) n>=1: chi1, chi2 primitive, chi1chi2 imprimitive => J = 0 ?
for (p, K) in [(3,2),(5,2),(7,2),(3,3),(11,2),(5,3),(3,4)]:
    N = p**K; chars = characters(N); prim = [c for c in chars if is_primitive(N,c,p)]
    tot=0; nz=0; mx=0
    for c1 in prim:
        for c2 in prim:
            c12 = mul(c1,c2)
            if is_primitive(N,c12,p): continue
            tot += 1; v = abs(J(N,c1,c2)); mx = max(mx, v); nz += v > 1e-7
    print(f"(A) p={p} K={K}: imprimitive-product pairs {tot}, J!=0 {nz}, max|J| {mx:.2e}")
# (B) N=5, N=49: s=+1 count among primitive triples, and count with wratio == 1
def even(N,c): return abs(c[N-1]-1) < 1e-8
for (p,K) in [(5,1),(7,2),(7,1),(3,3)]:
    N=p**K; chars=characters(N); prim=[c for c in chars if is_primitive(N,c,p)]
    tot=sp=ok1=wr1=0
    for c1 in prim:
        for c2 in prim:
            c12=mul(c1,c2)
            if not is_primitive(N,c12,p): continue
            tot+=1
            s = 1 if (even(N,c1) or even(N,c2)) else -1
            sp += (s==1)
            Jh = J(N,c1,c2)/math.sqrt(N)
            rat = w(N,c12)/(w(N,c1)*w(N,c2))
            ok1 += np.isclose(np.conj(Jh), rat)          # both sides unsquared
            assert np.isclose(np.conj(Jh), s*rat)        # theorem 2
            wr1 += np.isclose(rat, 1)
    print(f"(B) N={N}: triples {tot}, s=+1 {sp}, conj(Jhat)=ratio {ok1}, ratio==1 {wr1}")
