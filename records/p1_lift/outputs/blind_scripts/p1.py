import numpy as np, math, itertools, cmath, sys
from functools import lru_cache

def units(N): return [x for x in range(N) if math.gcd(x, N) == 1] if N > 1 else [0]

@lru_cache(None)
def P1(N):
    if N == 1: return [(0, 0)], {(0, 0): 0}
    U = units(N); pts = []; idx = {}
    for a in range(N):
        for b in range(N):
            if math.gcd(math.gcd(a, b), N) != 1: continue
            c = min(((u*a) % N, (u*b) % N) for u in U)
            if c not in idx: idx[c] = len(pts); pts.append(c)
    full = {}
    for a in range(N):
        for b in range(N):
            if math.gcd(math.gcd(a, b), N) != 1: continue
            full[(a, b)] = idx[min(((u*a) % N, (u*b) % N) for u in U)]
    return pts, full

def pt(N, a, b):
    if N == 1: return 0
    return P1(N)[1][(a % N, b % N)]

def Epts(N): return [pt(N, x, 1) for x in units(N)]

def RF(N, M):  # pullback F_N -> F_M
    pN, _ = P1(N); pM, _ = P1(M)
    R = np.zeros((len(pM), len(pN)))
    for j, (a, b) in enumerate(pM): R[j, pt(N, a, b)] = 1
    return R

def RG(N, M):
    uN, uM = units(N), units(M)
    R = np.zeros((len(uM), len(uN)))
    for j, x in enumerate(uM): R[j, uN.index(x % N if N > 1 else 0)] = 1
    return R

def res(N):
    pN, _ = P1(N); E = Epts(N)
    R = np.zeros((len(E), len(pN)))
    for i, p in enumerate(E): R[i, p] = 1
    return R

def torusF(N, u):
    pN, _ = P1(N); T = np.zeros((len(pN), len(pN)))
    for j, (a, b) in enumerate(pN): T[j, pt(N, u*a, b)] = 1  # (Tf)(q)=f(u q)
    return T

def torusG(N, u):
    U = units(N); T = np.zeros((len(U), len(U)))
    for j, x in enumerate(U): T[j, U.index((u*x) % N if N > 1 else 0)] = 1
    return T

def Wop(N):
    pN, _ = P1(N); T = np.zeros((len(pN), len(pN)))
    for j, (a, b) in enumerate(pN): T[j, pt(N, b, a)] = 1
    return T

# Dirichlet characters
def factor(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d, 0)+1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0)+1
    return f

def chars(N):
    """all characters mod N as dicts x->value on units"""
    U = units(N)
    if N == 1: return [{0: 1}]
    # brute force: group hom via discrete structure; use generic method: characters = eigen of regular rep
    # simple approach: build via CRT on prime powers using generators (p odd cyclic; 2^e)
    out = [dict()]
    comps = []
    for p, e in factor(N).items():
        q = p**e
        Uq = units(q)
        # find generators set and their orders
        if p == 2 and e >= 3:
            gens = [(-1) % q, 5]; ords = [2, q//4]
        else:
            n = len(Uq); g = next(g for g in Uq if all(pow(g, n//r, q) != 1 for r in factor(n)))
            gens = [g]; ords = [n]
        # discrete log table
        logs = {}
        for exps in itertools.product(*[range(o) for o in ords]):
            v = 1
            for g, k in zip(gens, exps): v = v*pow(g, k, q) % q
            logs[v] = exps
        cl = []
        for ks in itertools.product(*[range(o) for o in ords]):
            cl.append({x: cmath.exp(2j*math.pi*sum(k*l/o for k, l, o in zip(ks, logs[x], ords))) for x in Uq})
        comps.append((q, cl))
    res_ = []
    for combo in itertools.product(*[c[1] for c in comps]):
        d = {}
        for x in U:
            v = 1
            for (q, _), ch in zip(comps, combo): v *= ch[x % q]
            d[x] = v
        res_.append(d)
    return res_

def conductor(N, ch):
    for f in sorted(d for d in range(1, N+1) if N % d == 0):
        # chi factors through mod f iff chi(x)=1 for x ≡1 mod f
        if all(abs(ch[x]-1) < 1e-9 for x in ch if (x-1) % f == 0):
            return f

def primitive(N, ch):
    f = conductor(N, ch)
    if f == 1: return 1, {0: 1}
    d = {}
    for x in ch: d.setdefault(x % f, ch[x])
    return f, d

def wroot(N, ch):
    f, c = primitive(N, ch)
    if f == 1: return 1
    tau = sum(c[x]*cmath.exp(2j*math.pi*x/f) for x in c)
    a = 0 if abs(c[f-1]-1) < 1e-9 else 1
    return tau/((1j)**a*math.sqrt(f))

def Umat(N):
    U = units(N); C = chars(N)
    B = np.array([[ch[x] for ch in C] for x in U])  # columns = chars
    D = np.diag([wroot(N, ch) for ch in C])
    return B @ D @ np.linalg.inv(B)
