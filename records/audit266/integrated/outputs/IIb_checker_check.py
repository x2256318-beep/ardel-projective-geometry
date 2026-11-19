import numpy as np, math, itertools
def shells(N):
    divs=[d for d in range(1,N+1) if N%d==0]
    return divs,[np.array([1.0 if math.gcd(x,N)==d else 0.0 for x in range(N)]) for d in divs]
def dimT0(N):
    divs,sh=shells(N)
    gens=[np.diag(s) for s in sh]
    for d in divs:
        A=np.array([[1.0 if math.gcd((x-y)%N,N)==d else 0.0 for y in range(N)] for x in range(N)])
        gens.append(A)
    gens.append(np.eye(N))
    def basis(mats):
        V=np.array([m.flatten() for m in mats])
        u,s,vt=np.linalg.svd(V,full_matrices=False)
        r=(s>1e-8*s[0]).sum()
        return [vt[i].reshape(N,N) for i in range(r)]
    B=basis(gens)
    while True:
        prods=B+[x@y for x in B for y in B]
        B2=basis(prods)
        if len(B2)==len(B): return len(B)
        B=B2
for N in [1,2,3,4,5,7,8,9,15,16,25,27,32,49,81,11,13]:
    d=dimT0(N)
    # formula for prime powers
    f=None
    for p in [2,3,5,7,11,13]:
        k=0;M=N
        while M%p==0: M//=p;k+=1
        if M==1 and k>0: f=(k+1)**2+k*(k+1)//2-(k if p==2 else 0)
    print(N,d,f)
