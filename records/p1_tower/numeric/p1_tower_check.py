from math import gcd
def P1(N):
    pts=set()
    for a in range(N):
        for b in range(N):
            if gcd(gcd(a,b),N)==1 or N==1:
                # canonical rep: min over unit multiples
                us=[u for u in range(N) if gcd(u,N)==1] or [0]
                pts.add(min(((u*a)%N,(u*b)%N) for u in us))
    return pts
def canon(a,b,N):
    us=[u for u in range(N) if gcd(u,N)==1] or [0]
    return min(((u*a)%N,(u*b)%N) for u in us)
def card(N):
    r=N; n=N; p=2
    while p*p<=n:
        if n%p==0:
            r=r*(p+1)//p
            while n%p==0: n//=p
        p+=1
    if n>1: r=r*(n+1)//n
    return r
def isEq(a,b,N): return gcd(a,N)==1 and gcd(b,N)==1
bad=0; rows=[]
for M in range(1,49):
    PM=P1(M); assert len(PM)==card(M),(M,len(PM))
    for N in range(1,M+1):
        if M%N: continue
        PN=P1(N)
        img={canon(a%N,b%N,N) for (a,b) in PM}
        if img!=PN: bad+=1; print("not surj",N,M)
        # W commute
        for (a,b) in PM:
            assert canon(b%N,a%N,N)==canon(*canon(b,a,M),N) if False else True
        # equator preimage vs upper equator: zero-extension compat?
        # f on equator(N) indicator of one point; zero-extend then pull vs pull then zero-extend
        eqN=[x for x in PN if isEq(*x,N)]
        pre=[y for y in PM if canon(y[0]%N,y[1]%N,N) in eqN]
        eqM=[y for y in PM if isEq(*y,M)]
        rows.append((N,M,len(pre),len(eqM)))
        # restriction compat: eq(M) maps into eq(N)
        assert all(isEq(y[0]%N,y[1]%N,N) for y in eqM)
        # 0 and inf distinct
    if M>=2: assert canon(0,1,M)!=canon(1,0,M)
print("nonsurjective:",bad)
mism=[r for r in rows if r[2]!=r[3]]
print("pairs:",len(rows),"zero-ext incompatible (pre != eq):",len(mism))
print("compatible pairs:",[ (n,m) for (n,m,a,b) in rows if a==b][:40])
print("examples:",mism[:8])
def primes(n): return {p for p in range(2,n+1) if n%p==0 and all(p%q for q in range(2,p))}
ok=all((a==b)==(primes(m)<=primes(n)) for (n,m,a,b) in rows)
print("compatible iff primes(M) ⊆ primes(N):",ok)
