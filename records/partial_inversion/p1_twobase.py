import numpy as np, math, sys
sys.path.insert(0,'/home/claude/scripts')
def closure(G,n):
    B=[]
    def add(M):
        v=M.reshape(-1).astype(complex)
        if B:
            Q=np.array(B); r=v-Q.T@(Q.conj()@v)
        else: r=v
        nr=np.linalg.norm(r)
        if nr>1e-8*max(1,np.linalg.norm(v)): B.append(r/nr); return True
        return False
    add(np.eye(n))
    for M in G: add(M)
    ch=True
    while ch:
        ch=False
        for X in [b.reshape(n,n) for b in B]:
            for Y in G:
                if add(X@Y): ch=True
    return [b.reshape(n,n) for b in B]
def zdim(B,G):
    rows=[np.array([(X@Y-Y@X).reshape(-1) for X in B]).T for Y in G]
    M=np.vstack(rows); s=np.linalg.svd(M,compute_uv=False)
    return len(B)-int((s>1e-8*s[0]).sum())
def v(a,p,K):
    a%=p**K
    if a==0: return K
    j=0
    while a%p==0: a//=p; j+=1
    return j
def run(p,K):
    N=p**K
    pts=[(x,1) for x in range(N)]+[(1,y) for y in range(0,N,p)]
    n=len(pts); idx={q:i for i,q in enumerate(pts)}
    def norm(a,b):
        a%=N;b%=N
        if math.gcd(b,p)==1 or (b%p and True):
            if b%p: inv=pow(b,-1,N); return ((a*inv)%N,1)
        inv=pow(a,-1,N); return (1,(b*inv)%N)
    R=np.zeros((n,n),int)
    for i,(a,b) in enumerate(pts):
        for j,(c,d) in enumerate(pts): R[i,j]=v(a*d-b*c,p,K)
    A=[(R==j).astype(float) for j in range(K+1)]
    i0=idx[(0,1)]; iinf=idx[(1,0)]
    Ds=lambda a:[np.diag(A[j][a]) for j in range(K+1)]
    T0=closure(A+Ds(i0),n); Tinf=closure(A+Ds(iinf),n); T2=closure(A+Ds(i0)+Ds(iinf),n)
    # torus t_u : [a:b] -> [ua:b]
    units=[u for u in range(1,N) if u%p]
    def perm(f):
        P=np.zeros((n,n))
        for i,(a,b) in enumerate(pts): P[idx[norm(*f(a,b))],i]=1
        return P
    Tor=[perm(lambda a,b,u=u:(u*a,b)) for u in units]
    w=perm(lambda a,b:(b,a))
    # commutant dims = number of orbitals
    def orbitals(gens):
        # union-find on pairs
        parent=list(range(n*n))
        def f(x):
            while parent[x]!=x: parent[x]=parent[parent[x]]; x=parent[x]
            return x
        maps=[ [int(np.argmax(P[:,i])) for i in range(n)] for P in gens]
        for m in maps:
            for i in range(n):
                for j in range(n):
                    a,b=f(i*n+j),f(m[i]*n+m[j])
                    if a!=b: parent[a]=b
        return len({f(x) for x in range(n*n)})
    comm_tor=orbitals(Tor); comm_torw=orbitals(Tor+[w])
    inside=all(np.allclose(X@P,P@X) for X in T2 for P in Tor[:3])
    print(f"p={p} K={K} |P1|={n}  dimT(0)={len(T0)} dimT(inf)={len(Tinf)} dimT(0,inf)={len(T2)} centerT(0,inf)={zdim(T2,A+Ds(i0)+Ds(iinf))}  dim End_torus={comm_tor} dim End_(torus+w)={comm_torw}  T(0,inf) commutes w/ torus={inside}")
for p,K in [(2,2),(3,1),(3,2),(2,3),(5,1),(5,2),(2,4),(3,3),(7,1),(7,2)]:
    run(p,K)
