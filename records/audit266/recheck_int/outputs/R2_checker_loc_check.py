import math, sys
import numpy as np
sys.path.insert(0, '/tmp/indep_int266_R2')
from equator_U_check import characters, is_primitive, mul, J, w
def run(p, K):
    N = p**K; U = [x for x in range(N) if math.gcd(x, N) == 1]; NU = [x for x in range(N) if x not in U]
    chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
    ev = lambda c, x: c.get(x % N, 0.0); inv = lambda x: pow(x, -1, N)
    extS = lambda h: (h, {y: (h[inv(y)] if y in U else 0.0) for y in range(N)})
    extN = lambda h: ({x: (h[inv(x)] if x in U else 0.0) for x in range(N)}, h)
    conv = lambda f, g: {x: sum(f[y]*g[(x-y) % N] for y in range(N)) for x in range(N)}
    fu = fnu = both = tot = 0
    for c1 in prim:
        for c2 in prim:
            c12 = mul(c1, c2)
            if is_primitive(N, c12, p): continue
            k1 = extS({x: ev(c1, x) for x in range(N)}); k2 = extS({x: ev(c2, x) for x in range(N)})
            BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
            coef = (w(N, c12)/(w(N, c1)*w(N, c2)))**2
            bu = not all(np.isclose(BN[i][x], coef*BS[i][x]) for i in (0,1) for x in U)
            bnu = not all(np.isclose(BN[i][x], coef*BS[i][x]) for i in (0,1) for x in NU)
            tot += 1; fu += bu; fnu += bnu
    print(f"p={p} K={K}: nonprim {tot}, fails at unit pts {fu}, fails at non-unit pts {fnu}")
for pk in [(5,1),(7,1),(3,2),(5,2)]: run(*pk)
