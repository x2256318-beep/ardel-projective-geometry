import numpy as np
from math import gcd
def divisors(n): return [d for d in range(1,n+1) if n%d==0]
# counts
S=sum(len(divisors(M)) for M in range(1,31)); print("sum d(M), M<=30 =",S, " minus 30 =",S-30)
chains=sum(1 for L in range(1,31) for M in divisors(L) for N in divisors(M)); print("chains N|M|L<=30 =",chains)
chains_strict=sum(1 for L in range(1,31) for M in divisors(L) for N in divisors(M) if N<M<L); print("strict chains =",chains_strict)

def dind(N,s): return np.array([1.0 if gcd(N,x)==s else 0.0 for x in range(N)])  # gcd(N,0)=N
def geps(N,s):
    d=dind(N,s); return np.array([sum(np.exp(2j*np.pi*j*k/N)*d[j] for j in range(N))/N for k in range(N)])
def E(N,s):
    g=geps(N,s); return np.array([[g[(x-z)%N] for z in range(N)] for x in range(N)])
def D(N,s): return np.diag(dind(N,s)).astype(complex)
def pull(N,M): 
    P=np.zeros((M,N));
    for y in range(M): P[y,y%N]=1
    return P
def phi(N,M,S,c=None):
    P=pull(N,M); c = N/M if c is None else c
    return c*P@S@P.T
def alg(N):
    gens=[E(N,s) for s in divisors(N)]+[D(N,s) for s in divisors(N)]+[np.eye(N)]
    basis=[]
    def addv(X,B):
        V=np.array([b.flatten() for b in B+[X]])
        if np.linalg.matrix_rank(V,tol=1e-8)>len(B): B.append(X); return True
        return False
    for g in gens: addv(g,basis)
    changed=True
    while changed:
        changed=False
        for a in list(basis):
            for b in list(basis):
                if addv(a@b,basis): changed=True
    return basis
def inspan(X,B):
    V=np.array([b.flatten() for b in B]).T
    sol,res,rk,sv=np.linalg.lstsq(V,X.flatten(),rcond=None)
    return np.linalg.norm(V@sol-X.flatten())<1e-8
A2=alg(2); A4=alg(4); print("dim A2, A4 =",len(A2),len(A4))
N,M=2,4; P=pull(N,M); I2=np.eye(2); I4=np.eye(4)
phi1=phi(N,M,I2)
u=I2+D(2,2); ui=np.linalg.inv(u)
psi1=lambda S: phi(N,M,u@S@ui)
lam=lambda S: S[0,1]
psi2=lambda S: phi(N,M,S)+lam(S)*(I4-phi1)
# (b)
print("psi1(1)=phi(1):",np.allclose(psi1(I2),phi1)," psi2(1)=phi(1):",np.allclose(psi2(I2),phi1))
# (a) for all S in basis of A2, f basis
def cond_a(psi):
    return all(np.allclose(psi(S)@P, P@S) for S in A2)
print("(a) phi:",cond_a(lambda S:phi(N,M,S))," psi1:",cond_a(psi1)," psi2:",cond_a(psi2))
# multiplicativity
def mult(psi): return all(np.allclose(psi(a@b),psi(a)@psi(b)) for a in A2 for b in A2)
print("mult phi:",mult(lambda S:phi(N,M,S))," psi1:",mult(psi1)," psi2:",mult(psi2))
print("into A4: psi1",all(inspan(psi1(S),A4) for S in A2)," psi2",all(inspan(psi2(S),A4) for S in A2))
print("differs from phi: psi1",any(not np.allclose(psi1(S),phi(N,M,S)) for S in A2)," psi2",any(not np.allclose(psi2(S),phi(N,M,S)) for S in A2))
# (1,2): A1 = C, (b) alone determines linear map
# normalization-free composition and identity
ok=True
for L in range(1,13):
    for Mm in divisors(L):
        for Nn in divisors(Mm):
            Sx=np.random.randn(Nn,Nn)
            if not np.allclose(phi(Mm,L,phi(Nn,Mm,Sx,1),1),phi(Nn,L,Sx,1)): ok=False
print("composition without normalization holds:",ok)
# normalization-free product
Sx=np.random.randn(2,2); Tx=np.random.randn(2,2)
print("phi'(S)phi'(T) = (M/N) phi'(ST):",np.allclose(phi(2,4,Sx,1)@phi(2,4,Tx,1),2*phi(2,4,Sx@Tx,1)))
# D side: for all N|M, N<M, M<=30, all s|N: phi(D_s) not diagonal
bad=[]; cnt=0
for Mm in range(1,31):
    for Nn in divisors(Mm):
        if Nn<Mm:
            cnt+=1
            for s in divisors(Nn):
                X=phi(Nn,Mm,D(Nn,s)); off=X-np.diag(np.diag(X))
                if np.allclose(off,0): bad.append((Nn,Mm,s))
print("pairs N<M:",cnt," non-diagonal for all s|N:",bad==[])
