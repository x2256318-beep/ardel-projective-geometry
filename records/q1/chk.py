import cmath, math, itertools
def chars_mod_p(p):
    # primitive root
    for g in range(2,p):
        if len({pow(g,k,p) for k in range(p-1)})==p-1: break
    log={pow(g,k,p):k for k in range(p-1)}
    out=[]
    for j in range(1,p-1):  # nontrivial = primitive for prime p
        chi={u: cmath.exp(2j*math.pi*j*log[u]/(p-1)) for u in log}
        out.append(chi)
    return out
def W(chi,p):
    tau=sum(chi[x]*cmath.exp(2j*math.pi*x/p) for x in chi)
    a=0 if abs(chi[p-1]-1)<1e-9 else 1
    return tau/((1j)**a*math.sqrt(p))
for p in [5,7,11,13]:
    cs=chars_mod_p(p); Ws=[W(c,p) for c in cs]
    best=min(max(abs(Ws[i]-cs[i][c]) for i in range(len(cs))) for c in range(1,p))
    # also allow global scalar lambda: W = lam*chi(c)
    best2=min(max(abs(Ws[i]-Ws[0]/cs[0][c]*cs[i][c]) for i in range(len(cs))) for c in range(1,p))
    print(p,"min over c of max|W(chi)-chi(c)| =",round(best,3)," with scalar:",round(best2,3))
