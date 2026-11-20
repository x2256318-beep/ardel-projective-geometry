import cmath, math
def prim_root(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in {q for q in range(2,p) if (p-1)%q==0 and all(q%r for r in range(2,q))}):
            return g
def run(p,m):
    N=p**m; ph=N//p*(p-1); g=prim_root(p)
    if pow(g,p-1,p*p)==1: g+=p
    log={}; x=1
    for j in range(ph): log[x]=j; x=x*g%N
    units=[x for x in range(N) if x%p]
    mx=0; cnt=0
    for k1 in range(ph):
        if k1%p==0: continue
        for k2 in range(ph):
            if k2%p==0 or (k1+k2)%p!=0: continue
            J=sum(cmath.exp(2j*math.pi*(k1*log[x]+k2*log[(1-x)%N])/ph) for x in units if (1-x)%p)
            mx=max(mx,abs(J)); cnt+=1
    exp_cnt=p**(m-2)*(p-1)**2*(N//p//p*(p-1) if m>=2 else 0) if m>=2 else 0
    print(f"p={p} n+1={m}: pairs={cnt} (formula {p**(m-2)*(p-1)**2*((p**(m-1))//p*(p-1))}), max|J|={mx:.2e}")
for p,m in [(13,2),(7,3),(5,4)]: run(p,m)
