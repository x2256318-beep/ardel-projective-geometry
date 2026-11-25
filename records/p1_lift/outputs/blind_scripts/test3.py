import sys; sys.path.insert(0, '/tmp/blind_p1lift')
from p1 import *
from test1 import divisors
from test2 import Vstrat
import numpy as np

def Rsign(N, p):
    """1 - 2 P_v, v = 1_{0-disc at p} - 1_{inf-disc at p} on X_N (identity if p∤N)."""
    pN, _ = P1(N); n = len(pN)
    if N % p: return np.eye(n)
    v = np.array([1.0 if a % p == 0 else (-1.0 if b % p == 0 else 0.0) for (a, b) in pN])
    return np.eye(n) - 2*np.outer(v, v)/(v@v)

for L, p in [(30, 3), (36, 3), (20, 5)]:
    Ns = divisors(L)
    Vs = {N: Rsign(N, p)@Vstrat(N) for N in Ns}
    ok = True
    for N in Ns:
        V = Vs[N]
        ok &= np.allclose(V.conj().T@V, np.eye(len(V)))
        ok &= np.allclose(res(N)@V, Umat(N)@res(N))
        ok &= np.allclose(Wop(N)@V@Wop(N), np.linalg.inv(V))
        ok &= all(np.allclose(V@torusF(N, u), torusF(N, u)@V) for u in units(N))
        ok &= all(np.allclose(Vs[M]@RF(N, M), RF(N, M)@V) for M in Ns if M % N == 0)
        if N % p == 0: ok &= not np.allclose(V, Vstrat(N))
    print('L', L, 'p', p, 'sign-twisted V satisfies all and differs from stratified:', ok)
