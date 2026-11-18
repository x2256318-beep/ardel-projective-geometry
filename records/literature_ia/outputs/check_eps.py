"""Independent check of claims C2-C6 (local/global epsilon factors, Gauss sums, Hartley kernel).
Only numpy/scipy. Run: python3 -I /tmp/indep_ia/check_eps.py
"""
import numpy as np
from math import gcd
from itertools import product
from scipy import integrate, special

TOL = 1e-9
I = 1j

def e(x):
    return np.exp(2j * np.pi * x)

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def prim_root(p, k):
    m = p ** k
    phi = (p - 1) * p ** (k - 1)
    fs = factor(phi)
    for g in range(2, m):
        if gcd(g, m) != 1:
            continue
        if all(pow(g, phi // q, m) != 1 for q in fs):
            return g
    return 1

def chars_prime_power(p, k):
    """All Dirichlet characters mod p^k as arrays of length p^k (0 on non-units)."""
    m = p ** k
    out = []
    if p == 2 and k >= 3:
        # x = (-1)^s 5^t
        logs = {}
        for s in range(2):
            for t in range(2 ** (k - 2)):
                logs[((-1) ** s * pow(5, t, m)) % m] = (s, t)
        for a in range(2):
            for b in range(2 ** (k - 2)):
                arr = np.zeros(m, dtype=complex)
                for x, (s, t) in logs.items():
                    arr[x] = (-1) ** (a * s) * e(b * t / 2 ** (k - 2))
                out.append(arr)
        return out
    phi = (p - 1) * p ** (k - 1)
    g = prim_root(p, k) if m > 2 else 1
    logs = {}
    x = 1
    for t in range(phi):
        logs[x % m] = t
        x = (x * g) % m
    for j in range(phi):
        arr = np.zeros(m, dtype=complex)
        for x, t in logs.items():
            arr[x] = e(j * t / phi)
        out.append(arr)
    return out

def is_primitive_pp(arr, p, k):
    m = p ** k
    if k == 1:
        # nontrivial
        return any(abs(arr[x] - 1) > TOL for x in range(1, m) if gcd(x, m) == 1)
    d = p ** (k - 1)
    return any(abs(arr[x] - 1) > TOL for x in range(1, m, d) if gcd(x, m) == 1 and x % d == 1)

def primitive_chars(N):
    """Yield (xi_array_mod_N, components dict p->(k, array mod p^k))."""
    if N == 1:
        yield np.array([1.0 + 0j]), {}
        return
    fs = factor(N)
    comps = []
    for p, k in fs.items():
        lst = [c for c in chars_prime_power(p, k) if is_primitive_pp(c, p, k)]
        comps.append([(p, k, c) for c in lst])
    for combo in product(*comps):
        xi = np.ones(N, dtype=complex)
        for (p, k, c) in combo:
            m = p ** k
            xi *= np.array([c[x % m] for x in range(N)])
        yield xi, {p: (k, c) for (p, k, c) in combo}

def gauss(xi, N, sign=+1):
    return sum(xi[x] * e(sign * x / N) for x in range(N))

def parity(xi, N):
    v = xi[(-1) % N]
    if abs(v - 1) < TOL:
        return 0
    assert abs(v + 1) < TOL
    return 1

# ---------- local p-adic epsilon via the local functional equation (numerical, finite sums) ----------
def chi_p_value_on_p(p, comps):
    """chi_p(p) forced by triviality of chi on Q^x: prod_{l | N, l != p} xi^{(l)}(p)."""
    v = 1 + 0j
    for l, (k, c) in comps.items():
        if l != p:
            v *= c[p % (l ** k)]
    return v

def local_eps_via_lfe(p, k, comp_arr, chip_p, s, conv, m_extra=1):
    """eps(s, chi_p, psi_p) = Z(1-s, chi^{-1}, fhat) / Z(s, chi, f), f = 1_{u0 + p^m Z_p}, u0 a unit.
    chi_p(p^n u) = chip_p^n * conj(comp_arr[u mod p^k])  (chi_p|Z_p^x = (xi^{(p)})^{-1}).
    psi_p(x) = e(sgn * {x}_p), sgn = +1 (conv T) or -1 (conv C). dx: vol(Z_p)=1 (self-dual); d^x x = dx/|x|.
    """
    sg = +1 if conv == 'T' else -1
    m = k + m_extra
    pk = p ** k
    u0 = 1 if p != 2 else 3
    # Z(s, chi, f) = int_{u0+p^m Z_p} chi(x) |x|^s dx/|x| = chi(u0) * p^{-m}
    chi_u = lambda u: np.conj(comp_arr[u % pk])
    Zf = chi_u(u0) * p ** (-m)
    # fhat(y) = int f(x) psi(x y) dx = p^{-m} psi(u0 y) 1_{p^{-m}Z_p}(y)
    # Z(1-s, chi^{-1}, fhat) = sum over shells y = p^{-j} v, v in Z_p^x, j <= m
    total = 0j
    for j in range(-3, m + 1):  # shells j<=0 contribute 0 (chi ramified); include a few to show it
        L = max(k, j, 1)
        # integrand on shell: chi^{-1}(p^{-j} v) |y|^{1-s} fhat(y) / |y| ; dy over shell = p^{j} dv
        acc = 0j
        for v in range(p ** L):
            if v % p == 0:
                continue
            y_frac = (u0 * v % p ** max(j, 0)) / p ** j if j > 0 else 0.0  # {u0 y}_p
            chi_inv = (chip_p ** j) * comp_arr[v % pk]  # chi^{-1}(p^{-j} v) = chi_p(p)^{j} * xi^{(p)}(v)
            acc += chi_inv * e(sg * y_frac)
        acc *= p ** (-L)            # dv measure of each class mod p^L
        absy = float(p) ** j
        total += acc * p ** j * absy ** (1 - s) / absy * p ** (-m)
    return total / Zf

def local_eps_tate_formula(p, k, comp_arr, chip_p, s, conv):
    """Claimed: eps(s) = int_{p^{-k}Z_p^x} chi^{-1}(x)|x|^{-s} psi(x) dx."""
    sg = +1 if conv == 'T' else -1
    pk = p ** k
    acc = 0j
    for u in range(pk):
        if u % p == 0:
            continue
        acc += (chip_p ** k) * comp_arr[u] * e(sg * u / pk)
    acc *= p ** (-k) * p ** k  # measure of u + p^k Z_p scaled by |p^{-k}|=p^k
    return acc * float(p) ** (-k * s)

# ---------- archimedean epsilon via local functional equation (numerical quadrature) ----------
def arch_eps(a, sign_psi, s=0.3):
    """psi(x) = e(sign_psi * x). f = x^a e^{-pi x^2}. eps = Z(1-s,chi^{-1},fhat)/Z(s,chi,f) * L(s)/L(1-s)."""
    f = lambda x: x ** a * np.exp(-np.pi * x * x)
    def fhat(y):
        re = integrate.quad(lambda x: f(x) * np.cos(2 * np.pi * sign_psi * x * y), -10, 10, limit=200)[0]
        im = integrate.quad(lambda x: f(x) * np.sin(2 * np.pi * sign_psi * x * y), -10, 10, limit=200)[0]
        return re + 1j * im
    sgn = lambda x: np.sign(x) ** a
    def Z(ss, g):
        # int_{R^x} chi(x)|x|^ss g(x) dx/|x|
        re = integrate.quad(lambda x: (sgn(x) * abs(x) ** (ss - 1) * g(x)).real, 1e-12, 8, limit=400)[0]
        re += integrate.quad(lambda x: (sgn(-x) * abs(x) ** (ss - 1) * g(-x)).real, 1e-12, 8, limit=400)[0]
        im = integrate.quad(lambda x: (sgn(x) * abs(x) ** (ss - 1) * g(x)).imag, 1e-12, 8, limit=400)[0]
        im += integrate.quad(lambda x: (sgn(-x) * abs(x) ** (ss - 1) * g(-x)).imag, 1e-12, 8, limit=400)[0]
        return re + 1j * im
    Lr = lambda ss: np.pi ** (-(ss + a) / 2) * special.gamma((ss + a) / 2)
    gamma_factor = Z(1 - s, fhat) / Z(s, lambda x: f(x) + 0j)
    return gamma_factor * Lr(s) / Lr(1 - s)

def theta_ratio(xi, N, a, t=1.3, nmax=400):
    n = np.arange(1, nmax)
    xin = np.array([xi[k % N] for k in n])
    th = lambda tt, ch: np.sum(n ** a * ch * np.exp(-np.pi * n * n * tt / N))
    return th(1 / t, xin) / (t ** (a + 0.5) * th(t, np.conj(xin)))

def main():
    print("== C2: archimedean epsilon by numerical local functional equation ==")
    for a in (0, 1):
        for sp, name in ((-1, 'T: psi=e(-x)'), (+1, 'C: psi=e(+x)')):
            vals = [arch_eps(a, sp, s) for s in (0.3, 0.5, 0.8)]
            print(f"  chi_inf={'sgn' if a else '1  '}  {name}:  eps(s) for s=0.3,0.5,0.8 =",
                  ", ".join(f"{v.real:+.6f}{v.imag:+.6f}i" for v in vals))

    print("\n== C3/C4: local eps (LFE numerics vs Tate formula) and product vs tau ==")
    Ns = [N for N in range(1, 101)] + [120, 128, 135, 180, 243, 256, 360, 400]
    n_chars = 0
    max_err = {'loc': 0, 'C3': 0, 'C4': 0, 'C5T': 0, 'C5C': 0, 'theta': 0, 'C6eps': 0, 'C6cas': 0}
    mixed_bad_odd = 0; mixed_ok_odd = 0; mixed_ok_even = 0; n_odd = 0; n_even = 0
    lfe_checked = 0
    for N in Ns:
        for xi, comps in primitive_chars(N):
            n_chars += 1
            a = parity(xi, N)
            tau = gauss(xi, N)
            W = tau / (I ** a * np.sqrt(N))
            # local epsilons
            prodT0 = 1 + 0j; prodC0 = 1 + 0j; prodT_half = 1 + 0j; prodC_half = 1 + 0j
            for p, (k, c) in comps.items():
                cp = chi_p_value_on_p(p, comps)
                eT = local_eps_tate_formula(p, k, c, cp, 0.0, 'T')
                eC = local_eps_tate_formula(p, k, c, cp, 0.0, 'C')
                if N <= 60 or N in (128, 135, 243):
                    for s in (0.0, 0.5, 0.37):
                        for conv in ('T', 'C'):
                            v1 = local_eps_via_lfe(p, k, c, cp, s, conv)
                            v2 = local_eps_tate_formula(p, k, c, cp, s, conv)
                            max_err['loc'] = max(max_err['loc'], abs(v1 - v2))
                            lfe_checked += 1
                prodT0 *= eT; prodC0 *= eC
                prodT_half *= local_eps_tate_formula(p, k, c, cp, 0.5, 'T')
                prodC_half *= local_eps_tate_formula(p, k, c, cp, 0.5, 'C')
            max_err['C3'] = max(max_err['C3'], abs(prodT0 - tau), abs(prodT_half - tau / np.sqrt(N)))
            max_err['C4'] = max(max_err['C4'], abs(prodC0 - xi[(-1) % N] * tau),
                                abs(prodC_half - xi[(-1) % N] * tau / np.sqrt(N)))
            epsT_inf = (-I) ** a
            epsC_inf = (+I) ** a
            max_err['C5T'] = max(max_err['C5T'], abs(epsT_inf * prodT_half - W))
            max_err['C5C'] = max(max_err['C5C'], abs(epsC_inf * prodC_half - W))
            mixed = epsC_inf * prodT_half  # T's psi_p with C's eps_inf
            if a == 1:
                n_odd += 1
                if abs(mixed - W) > 1e-6: mixed_bad_odd += 1
                else: mixed_ok_odd += 1
                assert abs(mixed + W) < 1e-9
            else:
                n_even += 1
                if abs(mixed - W) < 1e-9: mixed_ok_even += 1
            if N > 1:
                max_err['theta'] = max(max_err['theta'], abs(theta_ratio(xi, N, a) - W))
            # C6
            epsx = ((1 - I) + (1 + I) * xi[(-1) % N]) / 2
            max_err['C6eps'] = max(max_err['C6eps'], abs(epsx - epsT_inf))
            for y in range(N):
                lhs = sum(xi[x] * (np.cos(2 * np.pi * x * y / N) + np.sin(2 * np.pi * x * y / N)) for x in range(N))
                rhs = epsx * tau * np.conj(xi[y % N])
                max_err['C6cas'] = max(max_err['C6cas'], abs(lhs - rhs))
    print(f"  primitive characters tested: {n_chars} (moduli 1..100 and 120,128,135,180,243,256,360,400)")
    print(f"  local eps: LFE numerics vs Tate formula, {lfe_checked} comparisons, max |diff| = {max_err['loc']:.2e}")
    print(f"  C3 max |prod_T eps_p(0) - tau|, |prod_T eps_p(1/2) - tau/sqrtN| = {max_err['C3']:.2e}")
    print(f"  C4 max |prod_C eps_p - xi(-1) tau| (s=0 and 1/2)            = {max_err['C4']:.2e}")
    print("\n== C5 ==")
    print(f"  conv T: max |eps_inf * prod eps_p(1/2) - W| = {max_err['C5T']:.2e}")
    print(f"  conv C: max |eps_inf * prod eps_p(1/2) - W| = {max_err['C5C']:.2e}")
    print(f"  mixed (T psi_p, C eps_inf): odd chars disagreeing {mixed_bad_odd}/{n_odd} (all equal -W); even agreeing {mixed_ok_even}/{n_even}")
    print(f"  independent check of W via theta transformation theta(1/t,xi) = W t^(a+1/2) theta(t,conj xi): max err {max_err['theta']:.2e}")
    print("\n== C6 ==")
    print(f"  max |eps(xi) - eps_T,inf| = {max_err['C6eps']:.2e}")
    print(f"  max |sum xi(x) cas(2 pi x y/N) - eps(xi) tau(xi) conj(xi(y))| over all y = {max_err['C6cas']:.2e}")

    # Non-primitive control for C6 (y arbitrary fails without primitivity)
    print("\n== C6 control: imprimitive character (trivial char mod 4 induced from mod 1; char mod 12 induced from mod 3) ==")
    for N, xi in ((4, np.array([0, 1, 0, 1], dtype=complex)),
                  (12, np.array([0 if gcd(x, 12) > 1 else (1 if x % 3 == 1 else -1) for x in range(12)], dtype=complex))):
        tau = gauss(xi, N); epsx = ((1 - I) + (1 + I) * xi[(-1) % N]) / 2
        bad = [y for y in range(N) if abs(sum(xi[x] * (np.cos(2*np.pi*x*y/N) + np.sin(2*np.pi*x*y/N)) for x in range(N)) - epsx * tau * np.conj(xi[y])) > 1e-9]
        print(f"  N={N}: y with mismatch: {bad}")

if __name__ == '__main__':
    main()
