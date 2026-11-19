# 照合の入力（極限の具体形の数値、records/limit_form/crt_corner_check.py）

## A. 記録の文（この数値を引いている文、そのまま）

- notes/pag2_limit_form_preregistration.md §1 (3)：

- **(a) 角の写像が中国剰余定理の分解と両立すること**：φ_{ab, a'b'} = φ_{a,a'} ⊗ φ_{b,b'}（a', b' が互いに素）。
  - 数値：1098 回の照合ですべて合った（`crt_corner_check.log`）。
  - 引き戻し・繊維の和・正規化がそれぞれ積に分かれることから、自動的に出る見込み（手計算）。
- **(b) V_∞ への作用の well-defined 性と忠実性**：Part 260・261 の文から短く出る見込み（手計算）。
- **(c) 制限テンソル積への分解**：(a) と直極限の一般論の組み合わせ。
- 局所の単位 e_1 = φ_{1,q}(1) は定数への射影 E^{(q)}_q と一致した（数値、q = 2, 4, 8, 16, 3, 9, 27, 5, 25）。

- notes/pag2_founding_material_index.md 5.5：
  - 素点ごとに、局所の単位 e_1（定数への射影）に関する制限テンソル積 ⊗'_p に分かれる（照合者の答え、確信度：高）。Flath 型の当てはめ。角の写像が中国剰余定理と両立することは数値で 1098 回確かめた。

- handoff/PAG2_handoff_part259.md：
  - 数値：角の写像は中国剰余定理と両立する（1098 回）。

## B. スクリプト records/limit_form/crt_corner_check.py
```python
"""極限の具体形の問いの見込み（数値。証明ではない）。
(1) 角の写像は中国剰余定理の分解と両立するか：互いに素な a', b' で a | a', b | b' のとき、
    V_{a'b'} ≅ V_{a'} ⊗ V_{b'}（CRT）のもとで φ_{ab, a'b'} = φ_{a, a'} ⊗ φ_{b, b'}。
(2) 局所の単位 e_1 = φ_{1, p^k}(1) は p^k 周期の…ではなく、定数への射影（E^{(p^k)}_{p^k}）であること。
"""
import sys, math, itertools
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import A, iota, divisors

def corner(N, M):
    I = iota(N, M)
    return lambda S: I @ S @ I.conj().T

def crt_perm(a, b):
    """V_{ab} の基底 δ_x を V_a ⊗ V_b の基底 δ_{x mod a} ⊗ δ_{x mod b} に送る置換行列。"""
    n = a * b
    P = np.zeros((n, n))
    for x in range(n):
        P[(x % a) * b + (x % b), x] = 1
    return P

bad = []; n = 0
for (a1, b1) in [(2, 3), (4, 3), (2, 9), (4, 9), (8, 3), (3, 5), (9, 5), (4, 5), (2, 15)]:
    if math.gcd(a1, b1) != 1: continue
    for a in divisors(a1):
        for b in divisors(b1):
            Ba, Da, Ea = A(a); Bb, Db, Eb = A(b)
            P1 = crt_perm(a, b); P2 = crt_perm(a1, b1)
            ph = corner(a * b, a1 * b1); pa = corner(a, a1); pb = corner(b, b1)
            for i in range(Ba.shape[1]):
                for j in range(Bb.shape[1]):
                    Sa = Ba[:, i].reshape(a, a); Sb = Bb[:, j].reshape(b, b)
                    S = P1.T @ np.kron(Sa, Sb) @ P1
                    lhs = P2 @ ph(S) @ P2.T
                    rhs = np.kron(pa(Sa), pb(Sb))
                    n += 1
                    if not np.allclose(lhs, rhs): bad.append((a, b, a1, b1))
print(f'(1) CRT との両立：照合 {n} 回、合わない組 {sorted(set(bad))}')
bad2 = []
for p in [2, 3, 5]:
    for k in range(1, 4):
        q = p ** k
        if q > 30: continue
        BM, DM, EM = A(q)
        if not np.allclose(corner(1, q)(np.eye(1)), EM[q]): bad2.append(q)
print(f'(2) e_1 = φ_(1,q)(1) = E^(q)_q（定数への射影）：合わない q {bad2}')
```

## C. 記録のログ records/limit_form/crt_corner_check.log
```
(1) CRT との両立：照合 1098 回、合わない組 []
(2) e_1 = φ_(1,q)(1) = E^(q)_q（定数への射影）：合わない q []
```

## D. スクリプトが使う定義 records/gamma_corner/corner_check.py
```python
"""方向 γ の立て直し：着手前の見込み確認（数値。証明ではない）。2026-11-19。

N | M、π^*：ℤ/M → ℤ/N に沿った引き戻し（Part 197 の pull）、ι = π^*/√(M/N)（等長）。φ(T) = ι T ι^†。
V：部分群への埋め込み x ↦ (M/N)x に沿った 0 拡張（等長）、ψ(T) = V T V^†。
A_N：D_s（殻の指示関数の掛け算）と E_s（双対殻への射影）が生成する代数（Part 214 の shellAlg）。
"""
import itertools, math, sys
import numpy as np

def divisors(n): return [d for d in range(1, n + 1) if n % d == 0]

def fourier(N):
    return np.array([[np.exp(-2j*np.pi*k*x/N) for x in range(N)] for k in range(N)]) / np.sqrt(N)

def gens(N):
    F = fourier(N)
    D = {s: np.diag([1.0 if math.gcd(N, x) == s else 0.0 for x in range(N)]).astype(complex) for s in divisors(N)}
    E = {s: F.conj().T @ np.diag([1.0 if math.gcd(N, k) == s else 0.0 for k in range(N)]) @ F for s in divisors(N)}
    return D, E

def orth_basis(mats, tol=1e-9):
    """行列の張る空間の正規直交基底（ベクトル化）。"""
    if not mats: return np.zeros((0, 0))
    A = np.array([m.ravel() for m in mats]).T
    U, S, _ = np.linalg.svd(A, full_matrices=False)
    r = int((S > tol * max(1.0, S[0])).sum())
    return U[:, :r]

def algebra(N):
    D, E = gens(N)
    G = list(D.values()) + list(E.values())
    B = orth_basis([np.eye(N, dtype=complex)] + G)
    while True:
        mats = [B[:, i].reshape(N, N) for i in range(B.shape[1])]
        prods = [a @ g for a in mats for g in G]
        B2 = orth_basis(mats + prods)
        if B2.shape[1] == B.shape[1]: return B, D, E
        B = B2

def in_span(B, X, tol=1e-7):
    v = X.ravel()
    return np.linalg.norm(v - B @ (B.conj().T @ v)) < tol * max(1.0, np.linalg.norm(v))

def iota(N, M):
    P = np.zeros((M, N), dtype=complex)
    for y in range(M): P[y, y % N] = 1.0
    return P / np.sqrt(M // N)

def vemb(N, M):
    k = M // N
    V = np.zeros((M, N), dtype=complex)
    for x in range(N): V[(k * x) % M, x] = 1.0
    return V

cache = {}
def A(N):
    if N not in cache: cache[N] = algebra(N)
    return cache[N]

def check_pair(N, M):
    k = M // N
    BN, DN, EN = A(N); BM, DM, EM = A(M)
    I = iota(N, M); V = vemb(N, M)
    out = {}
    out['iso'] = np.allclose(I.conj().T @ I, np.eye(N)) and np.allclose(V.conj().T @ V, np.eye(N))
    phi = lambda T: I @ T @ I.conj().T
    psi = lambda T: V @ T @ V.conj().T
    spanD = orth_basis(list(DM.values())); spanE = orth_basis(list(EM.values()))
    # φ
    out['phi_in_AM'] = all(in_span(BM, phi(X)) for X in list(DN.values()) + list(EN.values()))
    out['phi_E_strict'] = all(np.allclose(phi(EN[s]), EM[k * s]) for s in DN)
    out['phi_D_in_spanD'] = [s for s in DN if in_span(spanD, phi(DN[s]))]
    Q = sum(EM[t] for t in EM if t % k == 0)
    out['phi_one_is_Q'] = np.allclose(phi(np.eye(N)), Q)
    pullN = I * np.sqrt(k)
    out['cond_i'] = all(np.allclose(phi(X) @ pullN, pullN @ X) for X in list(DN.values()) + list(EN.values()))
    # 像の次元と角 Q A_M Q の次元
    imgs = [phi(BN[:, i].reshape(N, N)) for i in range(BN.shape[1])]
    corner = [Q @ BM[:, i].reshape(M, M) @ Q for i in range(BM.shape[1])]
    out['dimAN'] = BN.shape[1]; out['dimAM'] = BM.shape[1]
    out['dim_img'] = orth_basis(imgs).shape[1]; out['dim_corner'] = orth_basis(corner).shape[1]
    # ψ（0 拡張）
    out['psi_in_AM'] = all(in_span(BM, psi(X)) for X in list(DN.values()) + list(EN.values()))
    out['psi_D_strict'] = all(np.allclose(psi(DN[s]), DM[k * s]) for s in DN)
    out['psi_E_in_spanE'] = [s for s in EN if in_span(spanE, psi(EN[s]))]
    # フーリエ共役：F_M V F_N^† = c·ι（c は定数）
    W = fourier(M) @ V @ fourier(N).conj().T
    c = W[0, 0] / I[0, 0]
    out['fourier_conj'] = np.allclose(W, c * I) and abs(abs(c) - 1) < 1e-9
    # BC の ρ：φ(τ_x) = (N/M) Σ_{y ≡ x mod N} τ_y（τ は平行移動）
    def tau(n, x):
        T = np.zeros((n, n), dtype=complex)
        for z in range(n): T[(z + x) % n, z] = 1.0
        return T
    out['bc_rho'] = all(np.allclose(phi(tau(N, x)), sum(tau(M, y) for y in range(M) if y % N == x) / k) for x in range(N))
    return out

def check_chain(N, M, L):
    return np.allclose(iota(M, L) @ iota(N, M), iota(N, L)) and np.allclose(vemb(M, L) @ vemb(N, M), vemb(N, L))

if __name__ == '__main__':
    Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    pairs = [(N, M) for M in range(1, Mmax + 1) for N in divisors(M)]
    bad = []
    print('N M gcd(N,M/N) | dimA_N dimA_M dim像 dim角 | φ⊂A_M φ(E)厳密 φ(D)∈spanD(sの数/全) φ(1)=Q (i) | ψ⊂A_M ψ(D)厳密 ψ(E)∈spanE フーリエ共役 BCのρ')
    for N, M in pairs:
        o = check_pair(N, M)
        g = math.gcd(N, M // N)
        line = (f"{N} {M} {g} | {o['dimAN']} {o['dimAM']} {o['dim_img']} {o['dim_corner']} | {o['phi_in_AM']} {o['phi_E_strict']} "
                f"{len(o['phi_D_in_spanD'])}/{len(divisors(N))} {o['phi_one_is_Q']} {o['cond_i']} | {o['psi_in_AM']} {o['psi_D_strict']} "
                f"{len(o['psi_E_in_spanE'])}/{len(divisors(N))} {o['fourier_conj']} {o['bc_rho']}")
        print(line)
        if not (o['iso'] and o['phi_in_AM'] and o['phi_E_strict'] and o['phi_one_is_Q'] and o['cond_i'] and o['psi_in_AM']
                and o['psi_D_strict'] and o['fourier_conj'] and o['bc_rho'] and o['dim_img'] == o['dimAN']):
            bad.append((N, M))
    chains = [(N, M, L) for L in range(1, Mmax + 1) for M in divisors(L) for N in divisors(M)]
    cbad = [c for c in chains if not check_chain(*c)]
    print(f'組 {len(pairs)}、期待から外れた組 {bad}')
    print(f'合成の鎖 N|M|L：{len(chains)} 本、合成が合わない鎖 {cbad}')
    eq = [(N, M) for N, M in pairs if check_pair(N, M)['dim_img'] == check_pair(N, M)['dim_corner']]
    print(f'像 = 角（次元が等しい）組の数：{len(eq)}/{len(pairs)}')
```
