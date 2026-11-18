# 局所 ε 因子の積の数値確認（Tate の学位論文の規約と、その逆の規約）
# 規約 T（Tate 1950・Roy–Schmidt–Yi・Burnol）：ψ_∞(x)=e^{-2πix}、ψ_p(x)=e^{+2πi{x}_p}
# 規約 C（逆）：ψ_∞(x)=e^{+2πix}、ψ_p(x)=e^{-2πi{x}_p}
# イデール指標 χ_A と Dirichlet 指標 ξ の対応（ψ によらない）：不分岐の ℓ で χ_ℓ(ℓ)=ξ(ℓ)。
#   分岐する p では χ_p|_{Z_p^×} = (ξ^{(p)})^{-1}（RSY (150)）、χ_p(p)=∏_{ℓ|N,ℓ≠p} ξ^{(ℓ)}(p)（ℚ^× で自明から）
import cmath, math, itertools

def factorint(n):
    f = {}; d = 2
    while d*d <= n:
        while n % d == 0: f[d] = f.get(d, 0)+1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0)+1
    return f
def totient(n):
    r = n
    for p in factorint(n): r = r//p*(p-1)
    return r
def primitive_root(m):
    ph = totient(m); qs = list(factorint(ph))
    for g in range(2, m):
        if math.gcd(g, m) == 1 and all(pow(g, ph//q, m) != 1 for q in qs): return g
import numpy as np

def e(t): return cmath.exp(2j*math.pi*t)

def unit_group_gens(pk_p, k):
    """(Z/p^k)^× の生成元と位数（巡回でない 2^k は 2 つ）"""
    m = pk_p**k
    if pk_p == 2:
        if k == 1: return [], []
        if k == 2: return [3], [2]
        return [m-1, 5], [2, 2**(k-2)]
    g = primitive_root(m)
    return [g], [int(totient(m))]

def dlog_table(p, k):
    m = p**k
    gens, ords = unit_group_gens(p, k)
    tab = {}
    for exps in itertools.product(*[range(o) for o in ords]):
        v = 1
        for g, x in zip(gens, exps): v = v*pow(g, x, m) % m
        tab[v] = exps
    if not gens: tab[1 % m] = ()
    return tab, ords

def local_chars(p, k):
    """法 p^k の指標をすべて（値の関数として）列挙。原始性も判定"""
    m = p**k
    tab, ords = dlog_table(p, k)
    chars = []
    for js in itertools.product(*[range(o) for o in ords]):
        def chi(a, js=js, tab=tab, ords=ords, m=m):
            a %= m
            if math.gcd(a, m) != 1: return 0
            ex = tab[a]
            return cmath.exp(2j*math.pi*sum(j*x/o for j, x, o in zip(js, ex, ords)))
        chars.append(chi)
    def primitive(chi):
        if k == 0: return True
        # 法 p^(k-1) で周期的（単数の上で 1 + p^(k-1) 倍で不変）なら非原始
        mm = p**(k-1)
        for a in range(1, m):
            if math.gcd(a, m) == 1:
                b = a + mm if k >= 1 else a
                if math.gcd(b, m) == 1 and abs(chi(a) - chi(b % m)) > 1e-9:
                    return True
        return False if k >= 1 else True
    return [(c, primitive(c)) for c in chars]

def run(N):
    fac = factorint(N)
    ps = sorted(fac)
    comps = [[c for c, prim in local_chars(p, fac[p]) if prim] for p in ps]
    rows = []
    for combo in itertools.product(*comps):
        def xi(a, combo=combo):
            v = 1
            for c in combo: v *= c(a)
            return v
        G = sum(xi(a)*e(a/N) for a in range(N))
        par = 0 if abs(xi(N-1) - 1) < 1e-9 else 1   # χ(−1)=1 なら偶
        if N == 1: par = 0
        # 有限素点の局所 ε(0)：規約 T と C
        epsT, epsC = 1, 1
        for p, c in zip(ps, combo):
            k = fac[p]; m = p**k
            chi_p_at_p = 1
            for q, cq in zip(ps, combo):
                if q != p: chi_p_at_p *= cq(p)
            # ∫_{p^{-k}Z_p^×} χ_p^{-1}(x) ψ_p(x) dx = χ_p(p)^k Σ_y ξ^{(p)}(y) ψ_p(y/p^k)
            sT = sum(c(y)*e(y/m) for y in range(m) if math.gcd(y, m) == 1)
            sC = sum(c(y)*e(-y/m) for y in range(m) if math.gcd(y, m) == 1)
            epsT *= chi_p_at_p**k * sT
            epsC *= chi_p_at_p**k * sC
        epsinf_T = (-1j)**par
        epsinf_C = (1j)**par
        rootNum = G/((1j)**par*math.sqrt(N))
        rows.append(dict(N=N, par=par, G=G, epsT=epsT, epsC=epsC,
                         finT_err=abs(epsT - G), finC_err=abs(epsC - (xi(N-1) if N > 1 else 1)*G),
                         globT_err=abs(epsinf_T*epsT/math.sqrt(N) - rootNum),
                         globC_err=abs(epsinf_C*epsC/math.sqrt(N) - rootNum),
                         unit_err=abs(abs(epsT)/math.sqrt(N) - 1)))
    return rows

Ns = [1, 3, 4, 5, 7, 8, 9, 11, 12, 13, 15, 16, 20, 21, 24, 25, 27, 28, 32, 35, 40, 44, 45, 48, 56, 60, 63, 72, 84, 105, 120]
tot = 0; worst = dict(finT=0, finC=0, globT=0, globC=0, unit=0); parcount = [0, 0]
for N in Ns:
    rs = run(N)
    for r in rs:
        tot += 1; parcount[r['par']] += 1
        worst['finT'] = max(worst['finT'], r['finT_err']); worst['finC'] = max(worst['finC'], r['finC_err'])
        worst['globT'] = max(worst['globT'], r['globT_err']); worst['globC'] = max(worst['globC'], r['globC_err'])
        worst['unit'] = max(worst['unit'], r['unit_err'])
    print(f"N={N:4d}  原始指標 {len(rs):3d} 個")
print("合計", tot, "個（偶", parcount[0], "・奇", parcount[1], "）")
print("最大誤差：", {k: f"{v:.2e}" for k, v in worst.items()})

# 規約を取り違えた場合（規約 T の ψ_p と規約 C の ε_∞ の組）は奇の指標で合わないことの確認
bad = 0; odd = 0
for N in Ns:
    for r in run(N):
        if r['par'] == 1:
            odd += 1
            if abs((1j)*r['epsT']/math.sqrt(N) - r['G']/(1j*math.sqrt(N))) > 1e-6: bad += 1
print("混ぜた規約で合わない奇の指標：", bad, "/", odd)

# 無限素点：f(x)=x e^{-πx²} の ψ_∞ によるフーリエ変換 f^(y)=∫ f(x) ψ_∞(xy) dx
xs = np.linspace(-12, 12, 400001); dx = xs[1]-xs[0]
f = xs*np.exp(-math.pi*xs**2)
for name, sgn in [("T: ψ_∞=e^{-2πix}", -1), ("C: ψ_∞=e^{+2πix}", +1)]:
    ratios = []
    for y in [0.3, 0.7, 1.0, 1.9]:
        fh = np.sum(f*np.exp(sgn*2j*math.pi*xs*y))*dx
        ratios.append(fh/(y*math.exp(-math.pi*y**2)))
    print(name, "f^(y)/f(y) =", [f"{r.real:+.6f}{r.imag:+.6f}i" for r in ratios])
# 偶の場合 f=e^{-πx²} は自己双対（比 1）
f0 = np.exp(-math.pi*xs**2)
fh0 = np.sum(f0*np.exp(-2j*math.pi*xs*0.8))*dx
print("偶（e^{-πx²}）：比 =", f"{(fh0/math.exp(-math.pi*0.64)).real:+.6f}{(fh0/math.exp(-math.pi*0.64)).imag:+.6f}i")

# PAG256 の parFac（偶で 1、奇で −i）は規約 T の ε_∞ と同じ値
print("parFac: 偶 1, 奇", ((1-1j) + (1+1j)*(-1))/2, "／ 規約 T の ε_∞(sgn) =", -1j)
