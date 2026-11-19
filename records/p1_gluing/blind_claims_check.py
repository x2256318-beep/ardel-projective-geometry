"""盲検の出力の主張のうち 2 つを数値で確かめる（証明ではない）。2026-11-19 夜。
(a) 2 乗を外した形：conj(Ĵ) = (−1)^{a1 a2}·𝔀(χ1χ2)/(𝔀(χ1)𝔀(χ2))（法 p^K、p 奇、3 つとも原始的）。
(b) 関数体 F_7[t]/(t^2) で、盲検の挙げた本来のルート数 ω（η = χ|F_7^× が自明なら g、そうでなければ g·√7/τ_7(η)、g = τ/√|R|）が、
    条件「(φ/g)² が原始指標の上で乗法的」を満たさないこと（加法指標の取り替えは η(b) 倍で乗法的なので、結論に影響しない）。"""
import math, cmath, sys
import numpy as np
sys.path.insert(0, '.')
from equator_U_check import characters, is_primitive, mul, key, J, w, tau
from control_fqt_equator import ring

bad = tot = 0
for (p, K) in [(5, 1), (7, 1), (11, 1), (13, 1), (3, 2), (5, 2), (3, 3), (7, 2)]:
    N = p ** K; prim = [c for c in characters(N) if is_primitive(N, c, p)]
    pk = {key(N, c) for c in prim}
    for c1 in prim:
        for c2 in prim:
            c12 = mul(c1, c2)
            if key(N, c12) not in pk: continue
            a1 = 0 if abs(c1[N - 1] - 1) < 1e-8 else 1; a2 = 0 if abs(c2[N - 1] - 1) < 1e-8 else 1
            lhs = np.conj(J(N, c1, c2) / math.sqrt(N)); rhs = (-1) ** (a1 * a2) * w(N, c12) / (w(N, c1) * w(N, c2))
            tot += 1; bad += not np.isclose(lhs, rhs)
print(f'(a) 法 p^K（8 つの法）の組 {tot}：符号つきの 1 乗の等式の不一致 {bad}')

p, e = 7, 2
els, idx, mul_, sub, units = ring(p, e); n = len(els); one = (1, 0)
ui = {u: i for i, u in enumerate(units)}; m = len(units)
rng = np.random.default_rng(5); c = rng.normal(size=m) + 1j * rng.normal(size=m)
M = np.zeros((m, m), dtype=complex)
for k, a in enumerate(units):
    for u in units: M[ui[u], ui[mul_(a, u)]] += c[k]
_, V = np.linalg.eig(M)
chars = [{u: V[ui[u], j] / V[ui[one], j] for u in units} for j in range(m)]
sub1 = [u for u in units if u[0] == 1]
prim = [ch for ch in chars if any(abs(ch[u] - 1) > 1e-8 for u in sub1)]
kf = lambda ch: tuple(np.round([ch[u] for u in units], 6)); pk = {kf(ch): i for i, ch in enumerate(prim)}
psi = lambda x: cmath.exp(2j * math.pi * x[1] / p)
g = lambda ch: sum(ch[u] * psi(u) for u in units) / math.sqrt(n)
consts = [(cc, 0) for cc in range(1, p)]
def omega(ch):
    eta = {cc: ch[(cc, 0)] for cc in range(1, p)}
    if all(abs(eta[cc] - 1) < 1e-8 for cc in eta): return g(ch)
    t7 = sum(eta[cc] * cmath.exp(2j * math.pi * cc / p) for cc in eta)
    return g(ch) * math.sqrt(p) / t7
fails = trip = 0
for c1 in prim:
    for c2 in prim:
        c12 = {u: c1[u] * c2[u] for u in units}
        if kf(c12) not in pk: continue
        trip += 1
        r = lambda ch: (omega(ch) / g(ch)) ** 2
        fails += not np.isclose(r(c12), r(c1) * r(c2))
print(f'(b) F_7[t]/(t^2)：原始指標の三つ組 {trip}、(ω/g)² が乗法的でない組 {fails}（0 でなければ ω は条件を満たさない）')
