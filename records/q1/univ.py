import cmath, math
from math import gcd
def units(N): return [u for u in range(1,N+1) if gcd(u,N)==1] if N>1 else [0]
def factor(N):
    f={};d=2
    while d*d<=N:
        while N%d==0: f[d]=f.get(d,0)+1; N//=d
        d+=1
    if N>1: f[N]=f.get(N,0)+1
    return f
def comp_chars(p,e):
    q=p**e; U=[u for u in range(1,q+1) if u%p] if q>1 else [1]
    if q==1: return [ {u:1 for u in [0]} ]
    if p==2:
        if e==1: return [{1:1}]
        gens=[(q-1,2),(5,2**(e-2))]
    else:
        phi=q//p*(p-1)
        for g in range(2,q):
            if g%p and len({pow(g,k,q) for k in range(phi)})==phi: break
        gens=[(g,phi)]
    # discrete logs
    import itertools
    logs={}
    for ks in itertools.product(*[range(o) for _,o in gens]):
        x=1
        for (g,o),k in zip(gens,ks): x=x*pow(g,k,q)%q
        logs[x]=ks
    chars=[]
    for js in itertools.product(*[range(o) for _,o in gens]):
        chars.append({u:cmath.exp(2j*math.pi*sum(j*k/o for j,k,(g,o) in zip(js,logs[u],gens))) for u in logs})
    return chars
def all_chars(N):
    import itertools
    fs=factor(N); comps=[(p**e,comp_chars(p,e)) for p,e in fs.items()]
    res=[]
    for combo in itertools.product(*[c for _,c in comps]):
        def chi(a,combo=combo):
            v=1
            for (q,_),c in zip(comps,combo): v*=c[a%q] if q>1 else 1
            return v
        res.append({u:chi(u) for u in units(N)})
    return res
def conductor(chi,N):
    for f in sorted(d for d in range(1,N+1) if N%d==0):
        ok=all(abs(chi[a]-chi[b])<1e-9 for a in chi for b in chi if (a-b)%f==0)
        if ok: return f
def W_star(chi,N):
    f=conductor(chi,N)
    if f==1: return 1
    star={}
    for a in range(1,f):
        if gcd(a,f)!=1: continue
        for u in chi:
            if (u-a)%f==0: star[a]=chi[u]; break
    tau=sum(star[a]*cmath.exp(2j*math.pi*a/f) for a in star)
    par = 0 if abs(star[f-1]-1)<1e-9 else 1
    return tau/((1j)**par*math.sqrt(f))
ex=[]
for N in range(1,73):
    cs=all_chars(N) if N>1 else [{0:1}]
    Ws=[W_star(c,N) if N>1 else 1 for c in cs]
    found=any(all(abs(Ws[i]-cs[i][c])<1e-7 for i in range(len(cs))) for c in units(N))
    if found: ex.append(N)
print("N<=72 with point-induced U:",ex)
