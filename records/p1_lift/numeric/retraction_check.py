"""C2 の着手前の数値：素数ごとの規則で作った ρ_N : P¹(ℤ/N) → (ℤ/N)^× が、赤道で恒等・還元と両立・W と両立（ρ∘W = ρ⁻¹）になるか（N ∣ M ≤ 60）。"""
from math import gcd
def fac(n):
    f={};p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def units(N): return [u for u in range(N) if gcd(u,N)==1] if N>1 else [0]
def canon(a,b,N):
    return min(((u*a)%N,(u*b)%N) for u in units(N)) if N>1 else (0,0)
def P1(N):
    return {canon(a,b,N) for a in range(max(N,1)) for b in range(max(N,1)) if N==1 or gcd(gcd(a,b),N)==1}
def crt(res):  # res: list of (r, m)
    x,M=0,1
    for r,m in res:
        t=((r-x)*pow(M,-1,m))%m; x+=M*t; M*=m
    return x%M
def rho_local(a,b,q):  # q = p^k, (a,b) unimodular mod p
    p=min(fac(q)) 
    if b%p:   # [x:1], x = a/b
        x=(a*pow(b,-1,q))%q
        return x if x%p else (1+x)%q
    else:     # a unit, [1:y], y=b/a, p | y
        y=(b*pow(a,-1,q))%q
        return pow((1+y)%q,-1,q)
def rho(a,b,N):
    if N==1: return 0
    return crt([(rho_local(a%(p**k),b%(p**k),p**k),p**k) for p,k in fac(N).items()])
bad=0
for M in range(1,61):
    for (a,b) in P1(M):
        r=rho(a,b,M)
        assert M==1 or gcd(r,M)==1
        # equator identity
        if M>1 and gcd(a,M)==1 and gcd(b,M)==1:
            assert r==(a*pow(b,-1,M))%M
        # W
        if M>1: assert (rho(b,a,M)*r)%M==1, (M,a,b)
        for N in range(1,M+1):
            if M%N: continue
            if N>1 and rho(a%N,b%N,N)!=r%N: bad+=1
print("compat failures:",bad)
print("all checks passed" if bad==0 else "FAILED")  # 統合照合 III-a の指摘で、無条件の表示を直した
