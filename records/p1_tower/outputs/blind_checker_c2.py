from math import gcd
import cmath
def pf(n):
    s=set();d=2
    while d*d<=n:
        while n%d==0: s.add(d); n//=d
        d+=1
    if n>1: s.add(n)
    return s
def units(N): return [u for u in range(N) if gcd(u,N)==1] if N>1 else [0]
def canon(a,b,N): return min(((u*a)%N,(u*b)%N) for u in units(N)) if N>1 else (0,0)
def P1(N): return {canon(a,b,N) for a in range(N) for b in range(N) if N==1 or gcd(gcd(a,b),N)==1}
ok=True
for M in range(1,61):
    PM=P1(M); exp=M
    for p in pf(M): exp=exp*(p+1)//p
    if len(PM)!=exp: ok=False;print("count",M)
    for N in range(1,M):
        if M%N==0 and {canon(a%N,b%N,N) for a,b in PM}!=P1(N): ok=False;print("surj",N,M)
print("count&surj ok up to 60:",ok)
ex=[]
for M in range(2,13):
    for N in range(1,M):
        if M%N: continue
        pre=sum(1 for a,b in P1(M) if (N==1) or (gcd(a,N)==1 and gcd(b,N)==1))
        eq=sum(1 for a,b in P1(M) if gcd(a,M)==1 and gcd(b,M)==1)
        if pre!=eq: ex.append((N,M,pre,eq))
print("preimage(eq_N) vs eq_M differ:",ex[:6])
