"""equator_U_check.py の (3) の続き：r = (φ/𝔀)² の偏角 θ（ℝ/ℤ に正規化）が θ_i + θ_j − θ_k ∈ ℤ（χ_i χ_j = χ_k、3 つとも原始的）を満たす解の数を、
行の張る格子 L ⊂ ℤ^m の指数 [ℤ^m : L] として数える（L が全階数のとき解の数 = 指数）。「r(χ) = χ(a)（a は単数）」の解の数 φ(N) と比べる（数値。証明ではない）。2026-11-19 夜。"""
import math, sys
sys.path.insert(0, '.')
from equator_U_check import characters, is_primitive, mul, key
from fractions import Fraction

def lattice_index(rows, m):
    """整数の行のリストが張る格子の、ℤ^m での指数（全階数でなければ None）。行の整数のガウス消去（エルミート標準形）で。"""
    M = [list(r) for r in rows if any(r)]
    col = 0; piv = []
    r0 = 0
    while col < m and r0 < len(M):
        # col 列で、r0 以降の行の gcd を r0 行に集める
        while True:
            nz = [i for i in range(r0, len(M)) if M[i][col] != 0]
            if not nz: break
            i0 = min(nz, key=lambda i: abs(M[i][col]))
            M[r0], M[i0] = M[i0], M[r0]
            done = True
            for i in range(r0 + 1, len(M)):
                if M[i][col] != 0:
                    q = M[i][col] // M[r0][col]
                    M[i] = [a - q * b for a, b in zip(M[i], M[r0])]
                    if M[i][col] != 0: done = False
            if done: break
        if any(M[i][col] != 0 for i in range(r0, len(M))):
            piv.append(abs(M[r0][col])); r0 += 1
        col += 1
    if len(piv) < m: return None
    return math.prod(piv)

if __name__ == '__main__':
  for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (5, 2), (3, 3), (7, 2)]:
      N = p ** K
      chars = characters(N); prim = [c for c in chars if is_primitive(N, c, p)]
      pk = {key(N, c): i for i, c in enumerate(prim)}
      rows = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              k = pk.get(key(N, mul(c1, c2)))
              if k is None: continue
              r = [0] * len(prim); r[i] += 1; r[j] += 1; r[k] -= 1; rows.append(r)
      idx = lattice_index(rows, len(prim))
      phiN = N // p * (p - 1)
      print(f'N = {N}：原始指標 {len(prim)} 個、解の数（格子の指数）{idx}、φ(N) = {phiN}')
