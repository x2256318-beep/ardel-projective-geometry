import numpy as np, math, cmath
rng=np.random.default_rng(0)
def characters(f):
    U=[u for u in range(1,f+1) if math.gcd(u,f)==1] if f>1 else [0]
    if f==1: return U,[np.array([1+0j])]
    n=len(U); idx={u:i for i,u in enumerate(U)}
    M=np.zeros((n,n),complex)
    for u in U:
        P=np.zeros((n,n))
        for v in U: P[idx[(u*v)%f],idx[v]]=1
        M+=rng.normal()*P
    w,V=np.linalg.eig(M)
    chars=[]
    for j in range(n):
        v=V[:,j]; c=v/v[idx[1]]
        # character is conj of eigvec? normalize to homomorphism check
        ch=np.array([c[idx[u]] for u in U])
        chars.append(ch)
    # verify homomorphism (either c or conj c)
    out=[]
    for ch in chars:
        ok=all(abs(ch[idx[(u*v)%f]]-ch[idx[u]]*ch[idx[v]])<1e-8 for u in U for v in U)
        if not ok:
            ch=np.conj(ch); ok=all(abs(ch[idx[(u*v)%f]]-ch[idx[u]]*ch[idx[v]])<1e-8 for u in U for v in U)
        assert ok
        out.append(ch)
    return U,out
def primitive(f,U,ch):
    if f==1: return True
    for d in range(1,f):
        if f%d==0:
            if all(abs(ch[i]-1)<1e-8 for i,u in enumerate(U) if (u-1)%d==0): return False
    return True
def phases(f):
    U,chs=characters(f); res=[]
    for ch in chs:
        if not primitive(f,U,ch): continue
        if f==1: res.append((1,1,0)); continue
        tau=sum(ch[i]*cmath.exp(2j*math.pi*u/f) for i,u in enumerate(U))
        a=0 if abs(ch[U.index(f-1)]-1)<1e-8 else 1
        naive=tau/math.sqrt(f); hart=tau/((1j)**a*math.sqrt(f))
        res.append((naive,hart,a))
    return res
P={f:phases(f) for f in range(1,61)}
def passes(N,k):
    for f in range(1,N+1):
        if N%f: continue
        vals=[r[k] for r in P[f]]
        if len(vals)>1 and max(abs(v-vals[0]) for v in vals)>1e-8: return False
    return True
print('naive pass N<=60:',[N for N in range(1,61) if passes(N,0)])
print('hartley pass N<=60:',[N for N in range(1,61) if passes(N,1)])
for f in [1,3,4,8,12,24]:
    print(f,[(np.round(r[0],6),np.round(r[1],6),r[2]) for r in P[f]])
print('count primitive N<=60:',sum(len(P[f]) for f in range(1,61)))
