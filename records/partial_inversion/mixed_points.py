import math, itertools
def factor(N):
    f={};n=N;p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def P1(N):
    pts=set()
    for a in range(N):
        for b in range(N):
            if math.gcd(math.gcd(a,b),N)==1:
                # normalize: smallest representative under units
                rep=min(((u*a)%N,(u*b)%N) for u in range(1,N) if math.gcd(u,N)==1)
                pts.add(rep)
    return pts
def norm(a,b,N): return min(((u*a)%N,(u*b)%N) for u in range(1,N) if math.gcd(u,N)==1)
for N in [6,10,12,15,30,36,60]:
    P=P1(N); f=factor(N)
    Pt=set(norm(x,1,N) for x in range(N))|set(norm(1,y,N) for y in range(N) if math.gcd(y,N)>1)
    # local inversion at p: swap coordinates mod p^k, keep elsewhere (CRT)
    def loc_inv(pt,p):
        a,b=pt; q=p**f[p]; r=N//q
        # find a',b' with a'≡b, b'≡a mod q ; a'≡a, b'≡b mod r
        e=next(t for t in range(N) if t%q==1 and t%r==0)  # idempotent for q
        a2=(e*b+(1-e)*a)%N; b2=(e*a+(1-e)*b)%N
        return norm(a2,b2,N)
    clos=set(Pt); ch=True
    while ch:
        ch=False
        for pt in list(clos):
            for p in f:
                q=loc_inv(pt,p)
                if q not in clos: clos.add(q); ch=True
    glob=all(norm(pt[1],pt[0],N) in Pt for pt in Pt)
    pred=1
    for p,k in f.items(): pred*= p**k+p**(k-1)
    print(f"N={N:3d} primes={list(f)} |P1(Z/N)|={len(P)} (formula {pred}) |Pt(N)|={len(Pt)} mixed={len(P)-len(Pt)} PtClosedUnderGlobalW={glob} closureUnderLocalInversions=P1:{clos==P} partial-inversion group size 2^{len(f)}")
