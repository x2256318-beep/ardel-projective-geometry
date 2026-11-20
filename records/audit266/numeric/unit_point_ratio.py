"""再照合の指摘 2 の確認（数値。証明ではない）。2026-11-20。
PAG23 の定義どおり：BS(F,G) = extS(conv F.1 G.1)、BN(F,G) = extN(conv F.2 G.2)、kS = extS(ket)、殻 0 のケットは χ(x)（正規化は両辺に共通なので省く）。
単数の点 x での BN.1(x)/BS.1(x) が conj(J)/J に等しいか、conj(Ĵ)² と比べる。χ₁χ₂ が原始的でない組（χ₂ = χ̄₁ など）を含める。
2026-11-20 の統合照合 I の指摘で足した：J = 0 の組は比が定まらないので除くが、その数を数えて出す（調べた K = 2、p = 3, 5 では χ₁χ₂ が原始的でない組はすべて J = 0。一般の場合は見込み。2026-11-20 に一般形から直した、照合 R3 の指摘）。
定理 4 の係数 c = (𝔀(χ₁χ₂)/(𝔀(χ₁)𝔀(χ₂)))²（Lean の 0 での割り算の規約：分母が 0 なら c = 0）とも比べ、単数でない点を含む関数全体で BN = c·BS かを数える。
"""
import math, cmath, sys
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/p1_gluing')
from equator_U_check import characters, is_primitive, mul, J, w
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
    tot = ok_ratio = eq_sq = 0; nonprim12 = 0; nonprim12_eqsq = 0; skipped_J0 = 0; skipped_J0_nonprim = 0
    thm4_prim = thm4_prim_ok = thm4_np = thm4_np_ok = 0
    for c1 in prim:
        for c2 in prim:
            k1 = extS({x: ev(c1, x) for x in range(N)}); k2 = extS({x: ev(c2, x) for x in range(N)})
            BS = extS(conv(k1[0], k2[0])); BN = extN(conv(k1[1], k2[1]))
            Jv = J(N, c1, c2)
            c12 = mul(c1, c2); prim12 = is_primitive(N, c12, p)
            den = w(N, c1) * w(N, c2)
            coef = (w(N, c12) / den) ** 2 if abs(den) > 1e-12 else 0.0
            whole = all(np.isclose(BN[i][x], coef * BS[i][x]) for i in (0, 1) for x in range(N))
            if prim12: thm4_prim += 1; thm4_prim_ok += whole
            else: thm4_np += 1; thm4_np_ok += whole
            if abs(Jv) < 1e-9:
                skipped_J0 += 1; skipped_J0_nonprim += (not prim12); continue
            r = [BN[0][x] / BS[0][x] for x in U if abs(BS[0][x]) > 1e-9]
            tot += 1
            ok_ratio += all(np.isclose(t, np.conj(Jv) / Jv) for t in r)
            sq = (np.conj(Jv) / math.sqrt(N)) ** 2
            same = all(np.isclose(t, sq) for t in r)
            eq_sq += same
            if not prim12:
                nonprim12 += 1; nonprim12_eqsq += same
    print(f"p={p} K={K}: 組（J≠0）{tot}、単数の点で比 = conj(J)/J：{ok_ratio}、比 = conj(Ĵ)²：{eq_sq}、"
          f"うち χ₁χ₂ が原始的でない組 {nonprim12}（比 = conj(Ĵ)² は {nonprim12_eqsq}）。"
          f"J = 0 で除いた組 {skipped_J0}（うち χ₁χ₂ が原始的でない組 {skipped_J0_nonprim}）。"
          f"定理 4 の係数で関数全体 BN = c·BS：χ₁χ₂ 原始的 {thm4_prim_ok}/{thm4_prim}、原始的でない {thm4_np_ok}/{thm4_np}")

if __name__ == '__main__':
    for (p, K) in [(5, 1), (7, 1), (3, 2), (5, 2)]:
        run(p, K)
