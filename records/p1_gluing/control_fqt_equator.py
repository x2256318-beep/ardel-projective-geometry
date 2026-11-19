"""対照群（関数体）：R = F_p[t]/(t^e) で、赤道の等式 conj(Ĵ)² = (𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2)))²（𝔀 = τ/√|R|）と、解の数（格子の指数）＝ |R^×| が同じ形で成り立つか（数値。証明ではない）。2026-11-19 夜。
加法指標 ψ(x) = exp(2πi λ(x)/p)（λ は t^{e−1} の係数）。原始指標：1 + t^{e−1}R の上で自明でない指標（e = 1 では自明でない指標）。"""
import itertools, cmath, math, sys
import numpy as np
sys.path.insert(0, '.')
from equator_solution_count import lattice_index

def ring(p, e):
    els = list(itertools.product(range(p), repeat=e)); idx = {x: i for i, x in enumerate(els)}
    def mul(x, y):
        z = [0] * e
        for i in range(e):
            for j in range(e - i): z[i + j] = (z[i + j] + x[i] * y[j]) % p
        return tuple(z)
    def sub(x, y): return tuple((a - b) % p for a, b in zip(x, y))
    units = [x for x in els if x[0] % p != 0]
    return els, idx, mul, sub, units

if __name__ == '__main__':
  for (p, e) in [(5, 1), (7, 1), (3, 2), (5, 2), (3, 3), (2, 3), (2, 4)]:
      els, idx, mul, sub, units = ring(p, e); n = len(els); one = tuple([1] + [0] * (e - 1))
      ui = {u: i for i, u in enumerate(units)}; m = len(units)
      rng = np.random.default_rng(3); c = rng.normal(size=m) + 1j * rng.normal(size=m)
      M = np.zeros((m, m), dtype=complex)
      for k, a in enumerate(units):
          for u in units: M[ui[u], ui[mul(a, u)]] += c[k]
      w_, V = np.linalg.eig(M)
      chars = [{u: V[ui[u], j] / V[ui[one], j] for u in units} for j in range(m)]
      if e == 1: sub1 = [u for u in units if u != one]
      else: sub1 = [u for u in units if all(u[i] == one[i] for i in range(e - 1))]
      prim = [ch for ch in chars if any(abs(ch[u] - 1) > 1e-8 for u in sub1)]
      key = lambda ch: tuple(np.round([ch[u] for u in units], 6))
      pk = {key(ch): i for i, ch in enumerate(prim)}
      psi = lambda x: cmath.exp(2j * math.pi * x[e - 1] / p)
      tau = lambda ch: sum(ch[u] * psi(u) for u in units)
      ev = lambda ch, x: ch.get(x, 0.0)
      J = lambda c1, c2: sum(ev(c1, x) * ev(c2, sub(one, x)) for x in els)
      wv = lambda ch: tau(ch) / math.sqrt(n)
      bad = cnt = 0; rows = []
      for i, c1 in enumerate(prim):
          for j, c2 in enumerate(prim):
              c12 = {u: c1[u] * c2[u] for u in units}; k = pk.get(key(c12))
              if k is None: continue
              cnt += 1
              lhs = np.conj(J(c1, c2) / math.sqrt(n)) ** 2
              rhs = (wv(c12) / (wv(c1) * wv(c2))) ** 2
              bad += not np.isclose(lhs, rhs)
              r = [0] * len(prim); r[i] += 1; r[j] += 1; r[k] -= 1; rows.append(r)
      idx_ = lattice_index(rows, len(prim)) if rows else None
      print(f'F_{p}[t]/(t^{e})：原始指標 {len(prim)} 個、組 {cnt}、等式の不一致 {bad}、解の数 {idx_}、|R^×| = {m}')
