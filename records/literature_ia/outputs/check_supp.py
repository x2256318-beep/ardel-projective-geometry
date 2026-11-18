"""Supplement: (i) global product at general s equals N^{1/2-s} W; (ii) cas with reversed argument;
(iii) psi_p x C eps_inf mixing is not trivial on Q (example x=1/2).
Run: python3 -I /tmp/indep_ia/check_supp.py
"""
import sys
sys.path.insert(0, '/tmp/indep_ia')
import numpy as np
from check_eps import primitive_chars, parity, gauss, chi_p_value_on_p, local_eps_tate_formula

I = 1j
err_s = 0; err_rev = 0; n = 0
for N in list(range(3, 61)) + [64, 81, 125]:
    for xi, comps in primitive_chars(N):
        n += 1
        a = parity(xi, N); tau = gauss(xi, N); W = tau / (I ** a * np.sqrt(N))
        for s in (0.0, 0.21, 0.5, 0.9):
            for conv, einf in (('T', (-I) ** a), ('C', (I) ** a)):
                prod = einf
                for p, (k, c) in comps.items():
                    prod *= local_eps_tate_formula(p, k, c, chi_p_value_on_p(p, comps), s, conv)
                err_s = max(err_s, abs(prod - N ** (0.5 - s) * W))
        lhs = sum(xi[x] * (np.cos(2*np.pi*x/N) - np.sin(2*np.pi*x/N)) for x in range(N))  # cas(-2 pi x/N)
        err_rev = max(err_rev, abs(lhs - xi[N-1] * np.sqrt(N) * W))
print(f"chars tested: {n}")
print(f"max |eps_inf * prod_p eps_p(s) - N^(1/2-s) W| over s in (0,0.21,0.5,0.9), both conventions: {err_s:.2e}")
print(f"max |sum xi(x) cas(-2 pi x/N) - xi(-1) sqrt(N) W| : {err_rev:.2e}  (reversed kernel gives xi(-1) W, i.e. -W for odd)")
# mixing check: psi_inf = e(+x) (conv C) with psi_p = e(+{x}_p) (conv T) at x = 1/2 in Q: product over all places
x_frac = 1/3
val = np.exp(2j*np.pi*x_frac) * np.exp(2j*np.pi*x_frac)  # only p=3 has nonzero fractional part {1/3}_3 = 1/3
print(f"mixed global character at x=1/3: {val:.3f} (not 1, so not a character of A/Q); conv T gives {np.exp(-2j*np.pi*x_frac)*np.exp(2j*np.pi*x_frac):.3f}")
