"""0 拡張 ψ = Ad V の像が角 P A_M P 全体か（数値。証明ではない）。"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from corner_check import A, orth_basis, divisors, vemb
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
bad = []; n = 0
for M in range(1, Mmax + 1):
    BM, DM, EM = A(M)
    for N in divisors(M):
        BN, _, _ = A(N); V = vemb(N, M); P = V @ V.conj().T; k = M // N
        assert np.allclose(P, sum(DM[t] for t in DM if t % k == 0))
        img = orth_basis([V @ BN[:, i].reshape(N, N) @ V.conj().T for i in range(BN.shape[1])]).shape[1]
        cor = orth_basis([P @ BM[:, i].reshape(M, M) @ P for i in range(BM.shape[1])]).shape[1]
        n += 1
        if img != cor or img != BN.shape[1]: bad.append((N, M, img, cor))
print(f'組 {n}、像 ≠ 角 の組 {bad}（P = Σ_(M/N | t) D_t も全組で確認）')
