"""恒等の法則 φ_{N,N} = id と、帰納系の 2 法則の数値照合（証明ではない）。"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from corner_check import iota, divisors
rng = np.random.default_rng(0)
bad = []
for N in range(1, 31):
    S = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
    I = iota(N, N)
    if not np.allclose(I @ S @ I.conj().T, S): bad.append(N)
print(f'N = 1〜30：φ_(N,N)(S) = S が合わない N {bad}（ランダムな S、退化の N = 1 を含む）')
