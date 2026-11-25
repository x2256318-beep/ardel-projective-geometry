import sys; sys.path.insert(0, '/tmp/blind_p1lift')
from p1 import *
from test1 import solve_family, divisors

def Etorus(N):
    # E(g) for g in G_N: expand g in chars, E(chi)([a:b]) = chi*(a) conj chi*(b)
    pN, _ = P1(N); U = units(N); C = chars(N)
    B = np.array([[ch[x] for ch in C] for x in U]); Binv = np.linalg.inv(B)
    Phi = np.zeros((len(pN), len(C)), complex)
    for k, ch in enumerate(C):
        f, c = primitive(N, ch)
        for j, (a, b) in enumerate(pN):
            if f == 1: Phi[j, k] = 1
            else:
                Phi[j, k] = c.get(a % f, 0)*np.conj(c.get(b % f, 0))
    return Phi @ Binv

# compare with solved unique family
L = 12
r, nul, x, off, shapes = solve_family(L, True, False)
for N in divisors(L):
    n, m = shapes[N]
    EN = x[off[N]:off[N]+n*m].reshape((n, m), order='F')
    print('N', N, 'match formula', np.allclose(EN, Etorus(N)))

def primes_of(n): return set(factor(n).keys()) if n > 1 else set()

def stratum(N, a, b):
    return frozenset(p for p in primes_of(N) if a % p and b % p)

def Vstrat(N, R=None):
    """V on stratum S: U_{N_S} on the unit coordinate, identity (or R_p) on the rest.
    Implementation: for q in stratum S, write N = N_S * N', unit coordinate x = a/b mod N_S.
    (Vf)(q) = sum_y U_{N_S}[x,y] f(q with N_S-component replaced by [y:1])."""
    pN, _ = P1(N); fN = factor(N) if N > 1 else {}
    V = np.zeros((len(pN), len(pN)), complex)
    for j, (a, b) in enumerate(pN):
        S = stratum(N, a, b)
        NS = 1
        for p in S: NS *= p**fN[p]
        Np = N//NS
        UNS = Umat(NS); uS = units(NS)
        x = (a*pow(b, -1, NS)) % NS if NS > 1 else 0
        i = uS.index(x)
        for k, y in enumerate(uS):
            # CRT: point with N_S-comp [y:1], N'-comp [a:b]
            if NS == 1: a2, b2 = a, b
            else:
                # find a2,b2 mod N: a2≡y,b2≡1 mod NS ; a2≡a,b2≡b mod Np
                e1 = NS*pow(NS, -1, Np) % N if Np > 1 else 0  # ≡1 mod Np, 0 mod NS
                e2 = (1-e1) % N
                a2 = (y*e2 + a*e1) % N; b2 = (1*e2 + b*e1) % N
            V[j, pt(N, a2, b2)] += UNS[i, k]
    return V

def check(N, M, V):
    ok = True
    return ok

Ls = [12, 30, 18, 20]
for L in Ls:
    Ns = divisors(L)
    Vs = {N: Vstrat(N) for N in Ns}
    allok = True
    for N in Ns:
        V = Vs[N]
        u = np.allclose(V.conj().T@V, np.eye(len(V)))
        lift = np.allclose(res(N)@V, Umat(N)@res(N))
        Wr = np.allclose(Wop(N)@V@Wop(N), np.linalg.inv(V))
        tor = all(np.allclose(V@torusF(N, uu), torusF(N, uu)@V) for uu in units(N))
        comp = all(np.allclose(Vs[M]@RF(N, M), RF(N, M)@V) for M in Ns if M % N == 0)
        if not (u and lift and Wr and tor and comp): allok = False; print('fail', N, u, lift, Wr, tor, comp)
    print('L', L, 'stratified V: unitary, lift, WVW=V^-1, torus, compatible:', allok)

# naive V = E U res + (1 - E res)
for N in [6, 10, 12, 15]:
    E = Etorus(N); V = E@Umat(N)@res(N) + np.eye(len(P1(N)[0])) - E@res(N)
    print('naive V at N', N, 'unitary?', np.allclose(V.conj().T@V, np.eye(len(V))), 'lift?', np.allclose(res(N)@V, Umat(N)@res(N)))

# W commuting impossible: does U commute with inversion?
for N in [5, 7, 8]:
    U = Umat(N); us = units(N); I = np.zeros((len(us),)*2)
    for j, x in enumerate(us): I[j, us.index(pow(x, -1, N))] = 1
    print('N', N, 'U commutes with inversion?', np.allclose(U@I, I@U), ' I U I = U^-1?', np.allclose(I@U@I, np.linalg.inv(U)))

# rho retraction formula: rho = 1 - (ab)^n + a^{n+1} b^{n-1}, n = N!-ish
def rho(N, a, b):
    n = math.factorial(N) if N < 10 else math.lcm(*range(1, N+1))*N
    return (1 - pow(a*b, n, N) + pow(a, n+1, N)*pow(b, n-1, N)) % N

good = True
for M in [12, 30, 36, 60]:
    for N in divisors(M):
        for (a, b) in P1(M)[0]:
            if N == 1: continue
            rM = rho(M, a, b); rN = rho(N, a, b)
            if math.gcd(rM, M) != 1 or rM % N != rN: good = False
            if rho(M, b, a) != pow(rM, -1, M): good = False
            # well-definedness on class
            for u in units(M):
                if rho(M, u*a, u*b) != rM: good = False
    for x in units(M):
        if rho(M, x, 1) != x: good = False
print('rho: retraction, compatible, W-compatible, well-defined:', good)
