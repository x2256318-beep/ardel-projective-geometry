"""統合照合（records/tail_audit4）の指摘を受けた追加の数値（証明ではない）。2026-11-19。
(a) 素朴な核 τ/√f の位相で作った U'_N が単数の角に入る N。
(b) range(D_1) ∩ range(E_1) が、0 拡張した原始指標の張る空間と一致するか（次元だけでなく空間として）。
(c) その空間の上で J∘H（J は素数冪ごとの殻の反転の CRT の積、H は Hartley/√N）が、原始指標 χ に W(χ) を掛ける作用と一致するか
    （W(χ) = τ(χ)/(i^a √N)。単数の上の U_N の原始指標での固有値と同じ値）。
(d) A_N の可換子 A_N' の次元、A_N' = span{R_u} となる N、A_N' が可換になる N。
(e) F_M ι = V F_N を実際に比べた組（M = kN ≤ Nmax、k = 2, 3）の数。
"""
import math, sys, cmath
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/projection_interaction')
from corner_check import A, orth_basis, in_span, divisors, iota, vemb, fourier
from interaction_check import units, Rmat, hartley, shell_inv, characters, conductor, root_num_prim

def commutant_dim(N, gens):
    I = np.eye(N)
    K = sum((np.kron(G.T, I) - np.kron(I, G)).conj().T @ (np.kron(G.T, I) - np.kron(I, G)) for G in gens)
    ev = np.linalg.eigvalsh(K)
    return int((ev < 1e-8 * max(1.0, ev.max())).sum()), K

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 36
a_list, b_bad, c_bad, d_eq, d_comm, e_pairs = [], [], [], [], [], 0
for N in range(2, Nmax + 1):
    B, D, E = A(N); Ui = units(N); phi = len(Ui)
    chars = characters(N)
    S = np.zeros((N, phi), dtype=complex)
    for j, u in enumerate(Ui): S[u, j] = 1.0
    cor = orth_basis([S.T @ B[:, i].reshape(N, N) @ S for i in range(B.shape[1])])
    # (a)
    Un = np.zeros((phi, phi), dtype=complex)
    for c in chars:
        v = np.array([c[u] for u in Ui]); w, f, even = root_num_prim(N, c)
        naive = w * (1 if even else 1j)   # τ/√f
        Un += naive * np.outer(v, v.conj()) / phi
    if in_span(cor, Un): a_list.append(N)
    # (b)
    Q = D[1] @ E[1] @ D[1]; Qh = (Q + Q.conj().T) / 2
    ev, W = np.linalg.eigh(Qh); Wint = W[:, ev > 1 - 1e-8]
    prim = [c for c in chars if conductor(N, c) == N]
    P = np.array([[c.get(x, 0.0) if math.gcd(x, N) == 1 else 0.0 for x in range(N)] for c in prim]).T if prim else np.zeros((N, 0))
    if Wint.shape[1] != P.shape[1] or (P.shape[1] and not (np.allclose(Wint @ (Wint.conj().T @ P), P))):
        b_bad.append(N)
    # (c)
    J, _ = shell_inv(N); H = hartley(N)
    for k, c in enumerate(prim):
        w, f, even = root_num_prim(N, c)
        if not np.allclose(J @ H @ P[:, k], w * P[:, k]): c_bad.append(N); break
    # (d)
    gens = list(D.values()) + list(E.values())
    dc, K = commutant_dim(N, gens)
    dR = orth_basis([Rmat(N, u) for u in Ui]).shape[1]
    if dc == dR: d_eq.append(N)
    ev2, V2 = np.linalg.eigh(K); null = V2[:, ev2 < 1e-8 * max(1.0, ev2.max())]
    mats = [null[:, i].reshape(N, N, order='F') for i in range(null.shape[1])]
    if all(np.allclose(X @ Y, Y @ X) for X in mats for Y in mats): d_comm.append(N)
    # (e)
    for kk in (2, 3):
        M = N * kk
        if M <= Nmax:
            e_pairs += 1
            assert np.allclose(fourier(M) @ iota(N, M), vemb(N, M) @ fourier(N))
print(f'(a) 素朴な核 τ/√f の U\'_N が角に入る N（2〜{Nmax}）：{a_list}')
print(f'(b) range(D_1)∩range(E_1) ≠ 原始指標の span となる N：{b_bad}')
print(f'(c) J∘H χ ≠ W(χ)χ となる原始指標がある N：{c_bad}')
print(f'(d) A_N\' = span{{R_u}}（次元の一致）となる N：{d_eq}／A_N\' が可換となる N：{d_comm}')
print(f'(e) F_M ι = V F_N を比べた組（k = 2, 3、M ≤ {Nmax}）：{e_pairs} 組、すべて一致')
