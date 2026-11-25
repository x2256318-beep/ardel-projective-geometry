"""Part 264（PAG268）の数値（2026-11-25、統合照合 III-a の指摘で追加、統合照合 IV の指摘で直した）：素数冪の法 p^c で、
chiPt χ（法 p^c の式 χ(a)χ̄(b)）と extChi χ（導手 f の原始指標 χ* の式 χ*(a mod f)·conj χ*(b mod f) を引き戻したもの）が
P¹(ℤ/p^c) の全点で一致するのは、導手が 1 でないとき、そのときに限るか。p = 2 を含む。
χ* の値は、法 f で単数でない剰余では 0、単数の剰余 r では χ(r の法 p^c での単数の持ち上げ) として、導手の法での gcd から計算する。"""
import cmath, itertools
from math import gcd
def units(N): return [u for u in range(N) if gcd(u,N)==1]
def gens(p,c):
    N=p**c
    if p==2:
        if c==1: return N,[]
        if c==2: return N,[(N-1,2)]
        return N,[(N-1,2),(5,N//4)]
    g=next(g for g in range(2,N) if gcd(g,N)==1 and len({pow(g,k,N) for k in range(N)})==N-N//p)
    return N,[(g,N-N//p)]
def chars(p,c):
    N,G=gens(p,c)
    logs={}
    for exps in itertools.product(*[range(o) for _,o in G]):
        x=1
        for (g,_),e in zip(G,exps): x=x*pow(g,e,N)%N
        logs[x]=exps
    out=[]
    for ks in itertools.product(*[range(o) for _,o in G]):
        def chi(a,ks=ks):
            a%=N
            if gcd(a,N)!=1: return 0
            return cmath.exp(2j*cmath.pi*sum(k*e/o for k,e,(_,o) in zip(ks,logs[a],G)))
        out.append(chi)
    return N,out
def conductor(chi,p,c):
    N=p**c
    for j in range(c+1):
        f=p**j
        if all(abs(chi(a)-chi(b))<1e-9 for a in units(N) for b in units(N) if (a-b)%f==0): return f
def P1(N):
    us=units(N); pts=set()
    for a in range(N):
        for b in range(N):
            if gcd(gcd(a,b),N)==1: pts.add(min(((u*a)%N,(u*b)%N) for u in us))
    return pts
bad=0; summary={}
for p,c in [(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(5,1),(5,2),(7,1),(7,2)]:
    N,X=chars(p,c); ok=0
    for chi in X:
        f=conductor(chi,p,c)
        def prim(r):  # χ* の値：法 f で単数でなければ 0、単数なら単数の持ち上げで χ を評価
            r%=f
            if f==1: return 1
            if gcd(r,f)!=1: return 0
            return chi(next(x for x in range(r,N,f) if gcd(x,N)==1))
        eq=all(abs(chi(a)*chi(b).conjugate()-prim(a)*complex(prim(b)).conjugate())<1e-9 for (a,b) in P1(N))
        ok+=eq
        if eq != (f>1): bad+=1
    summary[(p,c)]=(ok,len(X))
print("法 p^c ごとの（一致した指標の数, 指標の数）：", summary)
print("「一致 ⇔ 導手 > 1」の例外：", bad)
