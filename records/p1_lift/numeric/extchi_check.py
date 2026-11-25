"""Part 264（PAG268）の数値（2026-11-25、統合照合 III-a の指摘で追加）：奇素数冪の法 p^c で、
chiPt χ（法 p^c の式）と extChi χ（導手 f の原始指標の式を引き戻したもの）が P¹(ℤ/p^c) の全点で一致するのは、
導手が 1 でないとき、そのときに限るか。"""
import cmath
from math import gcd
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in range(2,p) if (p-1)%q==0 and all(q%r for r in range(2,q))): return g
def chars(p,c):
    N=p**c; phi=N-N//p; g=prim_root(p)
    if pow(g,p-1,p*p)==1: g+=p
    log={}; x=1
    for j in range(phi): log[x]=j; x=x*g%N
    return N,phi,[(lambda k:(lambda a: 0 if a%p==0 else cmath.exp(2j*cmath.pi*k*log[a%N]/phi)))(k) for k in range(phi)]
def conductor(chi,p,c):
    for j in range(0,c+1):
        f=p**j
        if all(abs(chi(a)-chi(b))<1e-9 for a in range(p**c) for b in range(p**c) if a%p and b%p and (a-b)%f==0): return j
def P1(N):
    us=[u for u in range(N) if gcd(u,N)==1]; pts=set()
    for a in range(N):
        for b in range(N):
            if gcd(gcd(a,b),N)==1: pts.add(min(((u*a)%N,(u*b)%N) for u in us))
    return pts
bad=0; rows=[]
for p,c in [(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(7,2)]:
    N,phi,X=chars(p,c)
    for k,chi in enumerate(X):
        j=conductor(chi,p,c); f=p**j
        def prim(a): return 1 if f==1 else chi(a if a%p==0 else next(x for x in range(a%f,N,f) if x%p))
        eq=True
        for (a,b) in P1(N):
            v1=chi(a)*chi(b).conjugate() if chi(b)!=0 else 0
            v2=prim(a)*(prim(b).conjugate() if isinstance(prim(b),complex) else prim(b)) if f>1 else 1
            if f>1 and (a%p==0 or b%p==0): v2=0
            if abs(v1-v2)>1e-9: eq=False
        rows.append((p,c,j,eq))
        if eq != (j>=1): bad+=1
print("(p, c, 導手の指数, 一致) の数え上げ：", {(p,c):(sum(1 for r in rows if r[:2]==(p,c) and r[3]), sum(1 for r in rows if r[:2]==(p,c))) for (p,c,_,_) in rows})
print("「一致 ⇔ 導手 > 1」の例外：", bad)
