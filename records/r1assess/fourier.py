import sys; exec(open('uniq.py').read().split('for a,b in')[0])
for a,b in [(2,3),(2,5),(4,3),(2,9),(6,5),(4,9)]:
    r=run(a,b); M=a*b; dM=divs(M); da=divs(a); FM=F(M); FMi=np.linalg.inv(FM); P=pull(a,M)
    Dt=[D(M,t) for t in dM]
    res=[]
    for g in r['good']:
        amap=dict(r['oldmap']); amap.update(g)
        ok=True
        for s in da:
            phiD=sum((D(M,t) for t in dM if math.gcd(t,a)==s),np.zeros((M,M),complex))
            assert np.linalg.norm(phiD@P-P@D(a,s))<1e-9
            phiE=sum((E(M,t) for t in dM if amap[t]==s),np.zeros((M,M),complex))
            ok &= np.linalg.norm(FMi@phiD@FM-phiE)<1e-9
        res.append(ok)
    # twist check: chi(x)=(-1)^x on Z/a conj fixes D, permutes E
    tw=None
    if a%2==0:
        C=np.diag([(-1)**x for x in range(a)]).astype(complex)
        tw={s:[t for t in da if np.linalg.norm(C@E(a,s)@C-E(a,t))<1e-9] for s in da}
    print(a,b,'good',len(r['good']),'Fourier-equivariant',res,'twist by (-1)^x:',tw)
