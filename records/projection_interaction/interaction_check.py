"""無限素点・スケーリング・貼り合わせ U と、有限素点の側の代数 A_N の相互作用（着手前の見込み確認。数値。証明ではない）。2026-11-19。

記号：V_N = ℤ/N 上の関数。A_N = ⟨D_s, E_s⟩（Part 214（PAG218）の shellAlg）。R_u f(x) = f(ux)（Part 214（PAG218）の dil）。
P = R_{-1}（パリティ、無限素点の符号）。H = 離散 Hartley 変換/√N（核 cas(2πxy/N)）。F = フーリエ（e(−kx/N)/√N）。
J = 殻ごとの反転：x = s·w（s = gcd(x, N)、w は法 N/s の単数）↦ s·w⁻¹（w⁻¹ は法 N/s）。
U_N = Σ_χ phaseA1(χ)·P_χ（Part 254 の UA1、単数の上の関数）。phaseA1(χ) = rootNum(χ の原始指標)。
"""
import math, sys, cmath
import numpy as np
sys.path.insert(0, '/home/claude/ardel-projective-geometry/records/gamma_corner')
from corner_check import A, orth_basis, in_span, divisors, iota, vemb, fourier

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1] if N > 1 else [0]

def Rmat(N, u):
    R = np.zeros((N, N), dtype=complex)
    for x in range(N): R[x, (u * x) % N] = 1.0   # (R f)(x) = f(ux)
    return R

def hartley(N):
    return np.array([[math.cos(2*math.pi*x*y/N) + math.sin(2*math.pi*x*y/N) for y in range(N)] for x in range(N)], dtype=complex) / math.sqrt(N)

def factor(N):
    f, n, p = {}, N, 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def local_inv(q, x):
    """ℤ/q（q = p^e）の殻ごとの反転：p^k w ↦ p^k w⁻¹。"""
    if x % q == 0: return 0
    s = math.gcd(x, q); m = q // s
    return (s * pow((x // s) % m, -1, m)) % q

def crt(res):
    x, M = 0, 1
    for q, r in res:
        t = ((r - x) * pow(M, -1, q)) % q; x += M * t; M *= q
    return x % M

def shell_inv(N, naive=False):
    """naive = True：法 N の殻ごとの反転 s·w ↦ s·w⁻¹（法 N/s）。False：素数冪ごとの反転の CRT の積。"""
    J = np.zeros((N, N), dtype=complex); img = {}
    qs = [p ** e for p, e in factor(N).items()]
    for x in range(N):
        if naive:
            s = math.gcd(x, N); m = N // s
            y = 0 if m == 1 else (s * pow((x // s) % m, -1, m)) % N
        else:
            y = crt([(q, local_inv(q, x % q)) for q in qs]) if N > 1 else 0
        img[x] = y; J[x, y] = 1.0  # (J f)(x) = f(J x)
    return J, img

def comm_all(B, X, N):
    return all(np.allclose(B[:, i].reshape(N, N) @ X, X @ B[:, i].reshape(N, N)) for i in range(B.shape[1]))

def normalizes(B, X, N):
    Xi = np.linalg.inv(X)
    return all(in_span(B, X @ B[:, i].reshape(N, N) @ Xi) for i in range(B.shape[1]))

def characters(N):
    """(ℤ/N)^× の指標を、R_u の同時対角化で求める（値の辞書 u ↦ χ(u)）。"""
    U = units(N); n = len(U)
    if n == 1: return [{U[0]: 1.0}]
    idx = {u: i for i, u in enumerate(U)}
    rng = np.random.default_rng(1)
    c = rng.normal(size=n) + 1j * rng.normal(size=n)
    Mx = np.zeros((n, n), dtype=complex)
    for k, a in enumerate(U):
        for u in U: Mx[idx[u], idx[(a * u) % N]] += c[k]
    w, V = np.linalg.eig(Mx)
    chars = []
    for j in range(n):
        v = V[:, j] / V[idx[1], j]
        chars.append({u: v[idx[u]] for u in U})
    return chars

def conductor(N, chi):
    for d in divisors(N):
        if all(abs(chi[u] - 1) < 1e-8 for u in chi if (u - 1) % d == 0): return d
    return N

def root_num_prim(N, chi):
    f = conductor(N, chi)
    # 法 f の原始指標：法 f の単数 y に、y ≡ u (mod f) となる法 N の単数 u をとる
    prim = {}
    for u in chi: prim.setdefault(u % f, chi[u])
    tau = sum(prim[y] * cmath.exp(2j*math.pi*y/f) for y in prim) if f > 1 else 1.0
    even = abs(prim.get(f - 1 if f > 1 else 0, 1.0) - 1) < 1e-8
    return tau / ((1 if even else 1j) * math.sqrt(f)), f, even

def run(Nmax):
    rep = {k: [] for k in ['Jnaive_comm', 'R_comm', 'P_comm', 'P_in_A', 'J_iso', 'J_comm', 'J_in_A', 'J_in_dil', 'JR', 'H_swap', 'JH_norm',
                           'Fphi_psi', 'corner_dim', 'U_comm_corner', 'U_in_corner', 'Pu_in_corner', 'Vprim', 'JH_Vprim']}
    for N in range(2, Nmax + 1):
        B, D, E = A(N); dvs = divisors(N)
        Rs = {u: Rmat(N, u) for u in units(N)}
        P = Rmat(N, N - 1)
        rep['R_comm'].append((N, all(comm_all(B, R, N) for R in Rs.values())))
        rep['P_comm'].append((N, comm_all(B, P, N)))
        rep['P_in_A'].append((N, in_span(B, P)))
        Jn, _ = shell_inv(N, naive=True)
        rep['Jnaive_comm'].append((N, comm_all(B, Jn, N)))
        J, img = shell_inv(N)
        rep.setdefault('J_units_inv', []).append((N, all(img[u] == pow(u, -1, N) for u in units(N)) if N > 1 else True))
        rep['J_iso'].append((N, all(math.gcd(img[x] - img[y], N) == math.gcd(x - y, N) for x in range(N) for y in range(N))))
        rep['J_comm'].append((N, comm_all(B, J, N)))
        rep['J_in_A'].append((N, in_span(B, J)))
        dilB = orth_basis(list(Rs.values()))
        rep['J_in_dil'].append((N, in_span(dilB, J)))
        rep['JR'].append((N, all(np.allclose(J @ Rs[u], Rs[pow(u, -1, N)] @ J) for u in units(N))))
        H = hartley(N)
        rep['H_swap'].append((N, all(np.allclose(H @ D[s] @ H, E[s]) and np.allclose(H @ E[s] @ H, D[s]) for s in dvs)))
        rep['JH_norm'].append((N, normalizes(B, J @ H, N)))
        # F φ F⁻¹ = ψ(F · F⁻¹)（M = N·k、k ≤ 3）
        # 比べた組だけを数える（統合照合 tail_audit4 の指摘 2-1 で直した。以前は比べない N も「偽でない」に数えていた）
        for k in (2, 3):
            M = N * k
            if M > Nmax: continue
            FN, FM = fourier(N), fourier(M); I, V = iota(N, M), vemb(N, M)
            rep['Fphi_psi'].append(((N, M), np.allclose(FM @ I, V @ FN)))
        # 単数の角：D_1 A_N D_1 を単数の上の関数に制限
        Ui = units(N)
        S = np.zeros((N, len(Ui)), dtype=complex)
        for j, u in enumerate(Ui): S[u, j] = 1.0
        cor = orth_basis([S.T @ B[:, i].reshape(N, N) @ S for i in range(B.shape[1])])
        chars = characters(N)
        conds = sorted({conductor(N, c) for c in chars})
        rep['corner_dim'].append((N, cor.shape[1], len(conds)))
        # U_N = Σ phase(χ) P_χ（単数の上）。P_χ = χ χ^* / φ(N)（関数 χ(u) をベクトルに）
        phi = len(Ui)
        Umat = np.zeros((phi, phi), dtype=complex); Pu = np.zeros((phi, phi), dtype=complex)
        for c in chars:
            v = np.array([c[u] for u in Ui]); Pc = np.outer(v, v.conj()) / phi
            w, f, even = root_num_prim(N, c)
            Umat += w * Pc; Pu += (1 if even else -1) * Pc
        Pd = {}
        for c in chars:
            v = np.array([c[u] for u in Ui]); d = conductor(N, c)
            Pd[d] = Pd.get(d, 0) + np.outer(v, v.conj()) / phi
        rep.setdefault('corner_eq_condproj', []).append((N, all(in_span(cor, X) for X in Pd.values()) and cor.shape[1] == len(Pd)))
        rep['U_comm_corner'].append((N, all(np.allclose(cor[:, i].reshape(phi, phi) @ Umat, Umat @ cor[:, i].reshape(phi, phi)) for i in range(cor.shape[1]))))
        rep['U_in_corner'].append((N, in_span(cor, Umat)))
        rep.setdefault('U_is_identity', []).append((N, np.allclose(Umat, np.eye(phi))))
        rep['Pu_in_corner'].append((N, in_span(cor, Pu)))
        # V_prim = range(D_1) ∩ range(E_1)：次元 = 原始指標の数
        Q = D[1] @ E[1] @ D[1]
        ev = np.linalg.eigvalsh((Q + Q.conj().T) / 2)
        dim_int = int((ev > 1 - 1e-8).sum())
        nprim = sum(1 for c in chars if conductor(N, c) == N)
        rep['Vprim'].append((N, dim_int, nprim))
        # JH は range(D_1) ∩ range(E_1) を保つ
        W = np.linalg.eigh((Q + Q.conj().T) / 2)[1][:, ev > 1 - 1e-8]
        X = J @ H @ W
        rep['JH_Vprim'].append((N, W.shape[1] == 0 or np.allclose(W @ (W.conj().T @ X), X)))
    return rep

if __name__ == '__main__':
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 24
    rep = run(Nmax)
    for k, v in rep.items():
        if k in ('corner_dim', 'Vprim'):
            bad = [t for t in v if t[1] != t[2]]
            print(f'{k}: 組 {len(v)}、不一致 {bad}')
        elif k in ('P_in_A', 'J_in_A', 'J_in_dil', 'U_in_corner', 'Pu_in_corner', 'U_is_identity'):
            print(f'{k}: 真となる N = {[n for n, b in v if b]}')
        else:
            print(f'{k}: 偽となる N = {[n for n, b in v if not b]}（{len(v)} 個）')
