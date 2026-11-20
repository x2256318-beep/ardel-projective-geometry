import numpy as np, math, itertools
def gens(N):
    divs=[t for t in range(1,N+1) if N%t==0]
    g=lambda x: math.gcd(x,N) if x%N else N
    # dual idempotents: diagonal projection onto shell gcd(x,N)=t
    Ds=[np.diag([1.0 if g(x)==t else 0.0 for x in range(N)]) for t in divs]
    # adjacency matrices A_t: (x,y) with gcd(x-y,N)=t ; BM algebra span = span of E_s
    As=[np.array([[1.0 if g((x-y)%N)==t else 0.0 for y in range(N)] for x in range(N)]) for t in divs]
    return Ds,As,len(divs)
def span_closure(G,N):
    basis=[]; 
    def add(M,B):
        v=M.reshape(-1)
        if not B: 
            if np.linalg.norm(v)>1e-9: B.append(v/np.linalg.norm(v)); return True
            return False
        Q=np.array(B); r=v-Q.T@(Q@v)
        if np.linalg.norm(r)>1e-8*max(1,np.linalg.norm(v)): B.append(r/np.linalg.norm(r)); return True
        return False
    I=np.eye(N); add(I,basis)
    for M in G: add(M,basis)
    changed=True
    while changed:
        changed=False
        cur=[b.reshape(N,N) for b in basis]
        for X in cur:
            for Y in G:
                if add(X@Y,basis): changed=True
    return [b.reshape(N,N) for b in basis]
def center_dim(B,G):
    # solve Z in span(B) commuting with generators
    n=len(B); rows=[]
    for Y in G:
        rows.append(np.array([(X@Y-Y@X).reshape(-1) for X in B]).T)
    M=np.vstack(rows)
    s=np.linalg.svd(M,compute_uv=False)
    return n-int((s>1e-8*s[0]).sum())
res={}
for N in [2,3,4,5,7,8,9,16,25,27,32,6,10,12,15,18,20,30]:
    Ds,As,d=gens(N); G=Ds+As
    B=span_closure(G,N); dim=len(B); z=center_dim(B,G)
    res[N]=dim
    k=None; p=None
    fac=[q for q in range(2,N+1) if N%q==0 and all(q%r for r in range(2,q))]
    ppow=len(fac)==1
    form=''
    if ppow:
        p=fac[0]; k=round(math.log(N,p))
        form=(3*k*k+5*k+2)//2 if p>2 else (3*k*k+3*k+2)//2
    almost = (dim - z) == d*d-1   # one d x d block, all others 1x1
    print(f"N={N:3d} d(N)={d} dimA={dim:4d} dimZ={z:3d} primepow={ppow} formula={form} almostComm={almost}")
for a,b in [(2,3),(2,5),(4,3),(3,5),(2,9),(4,5)]:
    print(f"A_{a*b}: {res[a*b]} vs A_{a}*A_{b}: {res[a]*res[b]}")
