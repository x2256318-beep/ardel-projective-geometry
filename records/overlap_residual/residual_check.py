#!/usr/bin/env python3
"""著者の定義（2026-11-28 20:59）「重なり＝大域の回転 𝔀(χ) から素点の寄与を差し引いた残り」の数値の照合。
規約 T、ω_q(q) = χ(q)。有限素点の局所定数は形 (II)：ε_p = χ_p の局所ガウス和/√p^e × 交差項 ∏_{q≠p} χ_q(p^e)（段 6・PAG261）。
(a) 残り r(χ) = 𝔀(χ)/∏_p ε_p と (−i)^a の差（法 N ≤ 120 の原始指標すべて）。
(b) 端点 1「∏_p ε_p = 1（残りが全体と一致、ε_∞ = 𝔀）」になる原始指標の数と、そのときの 𝔀 の値。
(c) 端点 2「N ∣ 24」：𝔀(χ) と残り r(χ)。
(d) 作用素として：分岐素点の J_p∘F_p は幅 e ≥ 1 の平行移動（恒等にならない）、不分岐素点の記号 σ(z) は恒等的に 1 ではない（段 9 のログの再掲。ここでは計算しない）。
"""
import cmath, math, itertools
import numpy as np
RNG=np.random.default_rng(1)
def e(t): return cmath.exp(2j*math.pi*t)
def units(N): return [u for u in range(1,N) if math.gcd(u,N)==1]
def factor(N):
    f={};d=2
    while d*d<=N:
        while N%d==0: f[d]=f.get(d,0)+1; N//=d
        d+=1
    if N>1: f[N]=f.get(N,0)+1
    return f
def chars_prime_power(q):
    U=units(q); idx={u:i for i,u in enumerate(U)}; m=len(U)
    A=np.zeros((m,m),complex)
    for g in U:
        M=np.zeros((m,m))
        for u in U: M[idx[g*u%q],idx[u]]=1
        A+=complex(RNG.normal(),RNG.normal())*M
    _,V=np.linalg.eig(A)
    out=[]
    for k in range(m):
        c={u:V[idx[u],k]/V[idx[1],k] for u in U}
        c={u:v/abs(v) for u,v in c.items()}
        out.append(c)
    return out
def primitive(q,c):
    for d in range(1,q):
        if q%d==0 and all(abs(c[u]-1)<1e-8 for u in c if (u-1)%d==0): return False
    return True
cache={}
def prims(q):
    if q not in cache: cache[q]=[c for c in chars_prime_power(q) if primitive(q,c)]
    return cache[q]
res=[];end1=[];end2=[]
for N in range(3,121):
    f=factor(N); mods=[p**k for p,k in f.items()]
    if any(len(prims(q))==0 for q in mods): continue
    for combo in itertools.product(*[prims(q) for q in mods]):
        chi={u:np.prod([c[u%q] for c,q in zip(combo,mods)]) for u in units(N)}
        a=0 if abs(chi[N-1]-1)<1e-8 else 1
        tau=sum(chi[u]*e(u/N) for u in chi)
        W=tau/((1j)**a*math.sqrt(N))
        prod=1
        for i,(ci,qi) in enumerate(zip(combo,mods)):
            p=min(d for d in range(2,qi+1) if qi%d==0); ei=round(math.log(qi,p))
            taui=sum(ci[u]*e(u/qi) for u in ci)
            cross=np.prod([cj[pow(p,ei,qj)] for j,(cj,qj) in enumerate(zip(combo,mods)) if j!=i]) if len(mods)>1 else 1
            prod*=taui/math.sqrt(qi)*cross
        r=W/prod
        res.append(abs(r-(-1j)**a))
        if abs(prod-1)<1e-8: end1.append((N,a,W))
        if 24%N==0: end2.append((N,a,W,r))
print(f"(a) 原始指標 {len(res)} 個（法 3〜120）：残り r と (−i)^a の差の最大 {max(res):.1e}")
print(f"(b) ∏ε_p = 1 となる原始指標 {len(end1)} 個。そのときの (法, a, 𝔀) の例：", [(N,a,round(W.real,6)+1j*round(W.imag,6)) for N,a,W in end1[:8]])
print(f"    𝔀 の値の集合：", sorted({(round(W.real,6),round(W.imag,6)) for _,_,W in end1}))
print("(c) N ∣ 24 の原始指標：", [(N,a,round(W.real,6)+1j*round(W.imag,6),round(r.real,6)+1j*round(r.imag,6)) for N,a,W,r in end2])
