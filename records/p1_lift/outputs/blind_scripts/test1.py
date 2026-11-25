import sys; sys.path.insert(0, '/tmp/blind_p1lift')
from p1 import *

def divisors(L): return [d for d in range(1, L+1) if L % d == 0]

def solve_family(L, torus=True, W=False):
    Ns = divisors(L)
    shapes = {N: (len(P1(N)[0]), len(units(N))) for N in Ns}
    off = {}; tot = 0
    for N in Ns: off[N] = tot; tot += shapes[N][0]*shapes[N][1]
    rows = []; rhs = []
    def var(N, i, j): return off[N] + i*shapes[N][1] + j
    def add_mat_eq(N, Lm, Rm, target, side):
        pass
    # constraints linear in E_N entries: express via kron
    blocks = []
    for N in Ns:
        n, m = shapes[N]
        # res E_N = I : (I_m ⊗ res) vec(E)  with column-major vec
        A = np.kron(np.eye(m), res(N)); b = np.eye(m).reshape(-1, order='F')
        blocks.append((N, A, b, None, None))
        if torus:
            for u in units(N):
                # E T_G - T_F E = 0
                A = np.kron(torusG(N, u).T, np.eye(n)) - np.kron(np.eye(m), torusF(N, u))
                blocks.append((N, A, np.zeros(n*m), None, None))
        if W:
            invG = np.zeros((m, m)); U = units(N)
            for j, x in enumerate(U): invG[j, U.index(pow(x, -1, N) if N > 1 else 0)] = 1
            A = np.kron(invG.T, np.eye(n)) - np.kron(np.eye(m), Wop(N))
            blocks.append((N, A, np.zeros(n*m), None, None))
    big = []; bb = []
    for N, A, b, _, _ in blocks:
        row = np.zeros((A.shape[0], tot)); row[:, off[N]:off[N]+A.shape[1]] = A
        big.append(row); bb.append(b)
    for N in Ns:
        for M in Ns:
            if M != N and M % N == 0:
                nN, mN = shapes[N]; nM, mM = shapes[M]
                # E_M RG - RF E_N = 0  -> vec: (RG^T ⊗ I) vec E_M - (I ⊗ RF) vec E_N
                row = np.zeros((nM*mN, tot))
                row[:, off[M]:off[M]+nM*mM] = np.kron(RG(N, M).T, np.eye(nM))
                row[:, off[N]:off[N]+nN*mN] -= np.kron(np.eye(mN), RF(N, M))
                big.append(row); bb.append(np.zeros(nM*mN))
    A = np.vstack(big); b = np.concatenate(bb)
    x, *_ = np.linalg.lstsq(A, b, rcond=None)
    resid = np.linalg.norm(A@x-b)
    rank = np.linalg.matrix_rank(A)
    return resid, tot-rank, x, off, shapes

for L in [6, 9, 12, 15, 8, 30]:
    for tor, W in [(False, False), (True, False), (True, True)]:
        r, nul, x, off, shapes = solve_family(L, tor, W)
        print(L, 'torus' if tor else '', 'W' if W else '', 'consistent' if r < 1e-8 else 'INCONSISTENT', 'free dim', nul)
