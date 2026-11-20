import cmath
from math import gcd
def prim_root(N,p):
    phi=N//p*(p-1)
    for g in range(2,N):
        if gcd(g,N)!=1: continue
        x=1;o=0
        while True:
            x=x*g%N;o+=1
            if x==1: break
        if o==phi: return g,phi
def run(p,m):
    N=p**m; g,phi=prim_root(N,p)
    log={};x=1
    for j in range(phi): log[x]=j; x=x*g%N
    xs=[x for x in range(N) if x in log and (1-x)%N in log]
    cnt=0;mx=0;cntP=0;mn=9e9
    for k1 in range(phi):
        if k1%p==0: continue
        for k2 in range(phi):
            if k2%p==0: continue
            J=sum(cmath.exp(2j*cmath.pi*(k1*log[x]+k2*log[(1-x)%N])/phi) for x in xs)
            if (k1+k2)%p==0:
                cnt+=1; mx=max(mx,abs(J))
            else:
                cntP+=1; mn=min(mn,abs(J)**2/N)
    print(f"p={p} m={m}: nonprim-product pairs={cnt}, max|J|={mx:.2e}; prim-product pairs={cntP}, |J|^2/N in [{mn:.6f}]")
for p,m in [(3,2),(5,2),(7,2),(11,2),(3,3),(3,4),(5,3)]:
    run(p,m)
