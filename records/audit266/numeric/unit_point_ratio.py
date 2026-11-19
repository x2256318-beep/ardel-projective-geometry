"""再照合の指摘 2 の確認（数値。証明ではない）。2026-11-20。
PAG23 の定義どおり：BS(F,G) = extS(conv F.1 G.1)、BN(F,G) = extN(conv F.2 G.2)、kS = extS(ket)、殻 0 のケットは χ(x)（正規化は両辺に共通なので省く）。
単数の点 x での BN.1(x)/BS.1(x) が conj(J)/J に等しいか、conj(Ĵ)² と比べる。χ₁χ₂ が原始的でない組（χ₂ = χ̄₁ など）を含める。
"""
import math, cmath, sys
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/p1_gluing')
from equator_U_check import characters, is_primitive, mul, J
import numpy as np

def run(p, K):
    N = p ** K
    U = [x for x in range(N) if math.gcd(x, N) == 1]
    chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
    def ev(c, x): return c.get(x % N, 0.0)
    def inv(x): return pow(x, -1, N)
    def extS(h): return (h, {y: (h[inv(y)] if y in U else 0.0) for y in range(N)})
    def extN(h): return ({x: (h[inv(x)] if x in U else 0.0) for x in range(N)}, h)
    def conv(f, g): return {x: sum(f[y] * g[(x - y) % N] for y in range(N)) for x in range(N)}
    tot = ok_ratio = eq_sq = 0; nonprim12 = 0; nonprim12_eqsq = 0
    for c1 in prim:
        for c2 in prim:
            k1 = extS({x: ev(c1, x) for x in range(N)}); k2 = extS({x: ev(c2, x) for x in range(N)})
            BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
            Jv = J(N, c1, c2)
            if abs(Jv) < 1e-9: continue
            r = [BN[0][x] / BS[0][x] for x in U if abs(BS[0][x]) > 1e-9]
            tot += 1
            ok_ratio += all(np.isclose(t, np.conj(Jv) / Jv) for t in r)
            sq = (np.conj(Jv) / math.sqrt(N)) ** 2
            same = all(np.isclose(t, sq) for t in r)
            eq_sq += same
            c12 = mul(c1, c2)
            if not is_primitive(N, c12, p):
                nonprim12 += 1; nonprim12_eqsq += same
    print(f"p={p} K={K}: 組（J≠0）{tot}、単数の点で比 = conj(J)/J：{ok_ratio}、比 = conj(Ĵ)²：{eq_sq}、"
          f"うち χ₁χ₂ が原始的でない組 {nonprim12}（比 = conj(Ĵ)² は {nonprim12_eqsq}）")

if __name__ == '__main__':
    for (p, K) in [(5, 1), (7, 1), (3, 2), (5, 2)]:
        run(p, K)
