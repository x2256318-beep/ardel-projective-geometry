# R1 assessment: on a coprime step a -> ab, how many unital algebra homs A_a -> A_ab satisfy
# (i) phi(S) pi^* = pi^* S and (ii) phi(D_s) in span{D_t}, phi(E_s) in span{E_t} ?
import numpy as np, itertools, math, sys
def divs(n): return [d for d in range(1,n+1) if n%d==0]
def F(N):
    w=np.exp(-2j*np.pi/N); return np.array([[w**(x*y) for y in range(N)] for x in range(N)])
def D(N,s): return np.diag([1.0 if math.gcd(N,x)==s else 0.0 for x in range(N)]).astype(complex)
def E(N,s):  # convolution by geps = F^{-1} diag(dind) F
    Fm=F(N); return np.linalg.inv(Fm)@D(N,s)@Fm
def pull(a,M):
    P=np.zeros((M,a)); 
    for x in range(M): P[x,x%a]=1
    return P
def algdim(gens,tol=1e-8):
    n=gens[0].shape[0]; basis=[]
    def add(X):
        v=X.reshape(-1)
        B=np.array(basis+[v]); 
        if np.linalg.matrix_rank(B,tol)>len(basis): basis.append(v); return True
        return False
    add(np.eye(n,dtype=complex)); frontier=[]
    for g in gens:
        if add(g): frontier.append(g)
    allm=[b.reshape(n,n) for b in basis]
    changed=True
    while changed:
        changed=False
        cur=[b.reshape(n,n) for b in basis]
        for X in cur:
            for g in gens:
                if add(X@g): changed=True
    return len(basis)
def blk(A,B):
    n,m=A.shape[0],B.shape[0]; Z=np.zeros((n+m,n+m),complex); Z[:n,:n]=A; Z[n:,n:]=B; return Z
def run(a,b):
    M=a*b; P=pull(a,M); da=divs(a); dM=divs(M)
    gens_a=[D(a,s) for s in da]+[E(a,s) for s in da]
    dimA=algdim(gens_a)
    # (i) for D: phi(D_s)=sum c_t D_t forced? solve least squares on pull condition
    Dt=[D(M,t) for t in dM]; Et=[E(M,t) for t in dM]
    def solve(basis,target):
        A=np.array([ (X@P).reshape(-1) for X in basis]).T
        sol,res,rk,_=np.linalg.lstsq(A,target.reshape(-1),rcond=None)
        null=A.shape[1]-rk
        return sol,null,np.linalg.norm(A@sol-target.reshape(-1))
    info=[]
    for s in da:
        _,nullD,rD=solve(Dt,P@D(a,s)); _,nullE,rE=solve(Et,P@E(a,s))
        info.append((s,nullD,round(rD,9),nullE,round(rE,9)))
    # old shells t for E: those with E_t P != 0
    old=[t for t in dM if np.linalg.norm(E(M,t)@P)>1e-9]; new=[t for t in dM if t not in old]
    # forced old coefficient: E_t P = P E_s for which s
    oldmap={}
    for t in old:
        for s in da:
            if np.linalg.norm(E(M,t)@P-P@E(a,s))<1e-9: oldmap[t]=s
    phiD={}
    for s in da:
        sol,_,_=solve(Dt,P@D(a,s)); phiD[s]=sum(c*X for c,X in zip(sol,Dt))
    good=[]
    for assign in itertools.product(da,repeat=len(new)):
        amap=dict(oldmap); amap.update(dict(zip(new,assign)))
        phiE={s:sum((Et[dM.index(t)] for t in dM if amap[t]==s),np.zeros((M,M),complex)) for s in da}
        pairs=[blk(D(a,s),phiD[s]) for s in da]+[blk(E(a,s),phiE[s]) for s in da]
        if algdim(pairs)==dimA: good.append(dict(zip(new,assign)))
    return dict(a=a,b=b,dimA=dimA,oldmap=oldmap,new=new,info=info,n_assign=len(da)**len(new),good=good)
for a,b in [(2,3),(3,2),(2,5),(3,4),(4,3),(2,9),(6,5),(5,6),(4,9)]:
    r=run(a,b)
    print(r['a'],r['b'],'dimA',r['dimA'],'new shells',r['new'],'assignments',r['n_assign'],'good',len(r['good']),r['good'][:3])
    print('   oldmap',r['oldmap'],' (s,nullD,resD,nullE,resE)',r['info'])
    sys.stdout.flush()
