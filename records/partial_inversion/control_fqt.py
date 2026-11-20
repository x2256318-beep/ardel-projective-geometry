"""
Control group F_q(t), q prime: does the root number satisfy the local covariance (L)?

Modulus h = f*g with f = t, g = t - 1 (degree 1 each, coprime). (F_q[t]/h)^x = F_q^x x F_q^x via a -> (a(0), a(1)).
Characters chi = chi_f * chi_g, chi_f(a) = lam^{j1}(a(0)), chi_g(a) = lam^{j2}(a(1)), lam a generator of the dual of F_q^x.
Primitive iff j1 != 0 and j2 != 0.  "Sign" psi = chi|_{F_q^x} = lam^{j1+j2}.
Gauss sum G(chi) = sum_{a mod h} chi(a) e(a/h), e(a/h) = exp(2 pi i * a1 / q) where a = a1 t + a0 (coefficient of 1/t).
Root number (formula as reported by the blind checker, David-Florea-Lalin Cor. 2.3; NOT independently verified):
   odd  (psi != 1): W = q^{-(deg h - 1)/2} G(chi) / tau(psi)
   even (psi == 1): W = q^{-(deg h - 1)/2} G(chi) / sqrt(q)
(L): W(chi^(f)) / W(chi) depends only on chi_f, where chi^(f) conjugates the f-component.
Also checked: G is multiplicative up to local cross terms (G(chi) = chi_f(g) chi_g(f) G(chi_f) G(chi_g)), so the
non-local part comes from the infinity factor only.  Variants tau(conj psi), extra psi(-1) factors change W only by
factors in Loc or by conjugation, which does not affect whether (L) fails.
Numerics are not proofs.
"""
import cmath, math, itertools

def run(q):
    g0 = next(x for x in range(2, q) if all(pow(x, (q - 1) // r, q) != 1 for r in range(2, q) if (q - 1) % r == 0 and all(r % s for s in range(2, r)))) if q > 2 else 1
    dlog = {}; x = 1
    for m in range(q - 1): dlog[x] = m; x = x * g0 % q
    lam = lambda j, a: 0 if a % q == 0 else cmath.exp(2j * cmath.pi * j * dlog[a % q] / (q - 1))
    e = lambda a1: cmath.exp(2j * cmath.pi * a1 / q)
    def tau(j):  # Gauss sum over F_q of lam^j
        return sum(lam(j, a) * e(a) for a in range(1, q))
    def G(j1, j2):
        s = 0
        for a1 in range(q):
            for a0 in range(q):
                v0, v1 = a0 % q, (a1 + a0) % q   # a(0), a(1)
                if v0 == 0 or v1 == 0: continue
                s += lam(j1, v0) * lam(j2, v1) * e(a1)
        return s
    def Gloc_f(j1):  # modulus t: a = a0, e(a/t) = exp(2 pi i a0 / q)
        return sum(lam(j1, a0) * e(a0) for a0 in range(1, q))
    def Gloc_g(j2):  # modulus t-1: a = a0, a/(t-1) = a0/t + ..., e = exp(2 pi i a0/q); value at t=1 is a0
        return sum(lam(j2, a0) * e(a0) for a0 in range(1, q))
    def W(j1, j2):
        jp = (j1 + j2) % (q - 1)
        norm = q ** (-(2 - 1) / 2)
        return norm * G(j1, j2) / (tau(jp) if jp else math.sqrt(q))
    prim = [j for j in range(1, q - 1)]
    # multiplicativity check of G (local cross terms chi_f(g) chi_g(f): g = t-1 at t=0 is -1, f = t at t=1 is 1)
    mult_ok = all(abs(G(j1, j2) - lam(j1, -1) * lam(j2, 1) * Gloc_f(j1) * Gloc_g(j2)) < 1e-8 for j1 in prim for j2 in prim)
    # (L) at f
    viol = []
    for j1 in prim:
        ratios = [(j2, W((-j1) % (q - 1), j2) / W(j1, j2)) for j2 in prim]
        base = ratios[0][1]
        bad = [(j2, r) for j2, r in ratios if abs(r - base) > 1e-7]
        if bad: viol.append((j1, base, bad[0]))
    nonreal_signs = any(abs(lam(j, g0).imag) > 1e-9 for j in range(q - 1))
    print(f"q={q}: |F_q^x|={q-1}, non-real characters of F_q^x exist: {nonreal_signs}; G multiplicative up to local cross terms: {mult_ok}; "
          f"root number satisfies (L): {not viol}")
    for j1, base, (j2, r) in viol[:2]:
        print(f"    violation: chi_f = lam^{j1}: ratio {base:.4f} (chi_g = lam^{prim[0]}) vs {r:.4f} (chi_g = lam^{j2})")

for q in [3, 5, 7, 11, 13]:
    run(q)
