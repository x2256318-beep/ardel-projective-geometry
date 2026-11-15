"""Part 257（PAG261）の数値照合。数値の確認は証明ではない。

Lean の文（予定）に合わせて、互いに素な法の並び l = [N_1, ..., N_k] と指標 χ_i（法 N_i）から、
法 lvl = N_1·...·N_k の指標 listChar を「先頭と残りの積」で作り、次を確かめる。
 (1) 漸化式：τ(listChar (a::l)) = χ_a(lvl l)·listChar l (N_a)·τ(χ_a)·τ(listChar l)
 (2) 形 (I)：τ(listChar l) = ∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)
 (3) 形 (II)：τ(listChar l) = ∏_i τ(χ_i)·∏_{j≠i} χ_j(N_i)
 (4) W の形：W(listChar l) = ε_∞(listChar l)·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（ε_∞ = 偶で 1、奇で −i）
 (5) 符号：ε_∞(listChar l) = (−1)^{k(k−1)/2}·∏ ε_∞(χ_i)（k は奇の χ_i の数）、したがって W(listChar l) = (−1)^{k(k−1)/2}·交差項·∏ W(χ_i)
 (6) listChar l (−1) = ∏ χ_i(−1)、listChar l (n) = ∏ χ_i(n)（n は自然数）
 (7) 原始性：χ_i がすべて原始なら listChar l も原始。逆も（数値で見るだけ）
 (8) 分解：法 lvl のすべての指標は listChar l の形にちょうど 1 通りに書ける（個数と一意性）
 (9) 退化例：l = [a] では τ(listChar [a]) = τ(χ_a)、交差項 = 1
 (10) 並べ替え：listChar の値は並びの順によらない（同じ数の法）
 (11) 原始でない χ_i も含めて (2)〜(5) が成り立つ（原始性は要らない）
"""
import sys, math, cmath, itertools, random
exec(open('/home/claude/out/prereg257/_step279_defs.py', encoding='utf-8').read())
random.seed(280)

def val(chi, N, a):
    a %= N
    return chi.get(a, 0) if math.gcd(a, N) == 1 else 0

def list_char(chis, mods):
    """先頭と残りの積で作る（Lean の listChar と同じ形）。値の辞書（法 lvl の単数で）。"""
    if not mods:
        return {0: 1 + 0j}, 1
    c_rest, n_rest = list_char(chis[1:], mods[1:])
    N = mods[0] * n_rest
    out = {}
    for a in range(N):
        if math.gcd(a, N) == 1:
            out[a] = val(chis[0], mods[0], a) * val(c_rest, n_rest, a)
    return out, N

def tau(chi, N):
    if N == 1: return 1 + 0j
    return sum(val(chi, N, a) * cmath.exp(2j * math.pi * a / N) for a in range(N))

def par(chi, N): return 0 if N == 1 else parity(chi, N)
def eps(chi, N): return 1 if par(chi, N) == 0 else -1j
def Wn(chi, N): return eps(chi, N) * tau(chi, N) / math.sqrt(N)  # W = τ/(i^a·√N) = ε_∞·τ/√N

def is_prim(chi, N): return True if N == 1 else is_primitive(chi, N)

def cross_rec(chis, mods):
    if not mods: return 1
    c_rest, n_rest = list_char(chis[1:], mods[1:])
    return val(chis[0], mods[0], n_rest) * val(c_rest, n_rest, mods[0]) * cross_rec(chis[1:], mods[1:])

def cross_I(chis, mods):
    v = 1
    for i in range(len(mods)):
        rest = 1
        for j in range(len(mods)):
            if j != i: rest *= mods[j]
        v *= val(chis[i], mods[i], rest)
    return v

def cross_II(chis, mods):
    v = 1
    for i in range(len(mods)):
        for j in range(len(mods)):
            if j != i: v *= val(chis[j], mods[j], mods[i])
    return v

CH = {}
def chars(N):
    if N not in CH: CH[N] = [{0: 1 + 0j}] if N == 1 else characters(N)
    return CH[N]

# 互いに素な法の並び（素数冪でないものも含む）
families = [[3, 4], [4, 3], [5, 8], [3, 5, 7], [7, 5, 3], [4, 9, 5], [8, 3, 5], [3, 4, 5, 7], [7, 16],
            [9, 10], [15, 4], [21, 4, 5], [11, 12], [1, 5, 3], [5], [1], [13, 6], [27, 4], [5, 7, 8]]
err = {k: 0.0 for k in ['rec', 'I', 'II', 'W', 'sign', 'Wsign', 'neg1', 'nat', 'deg']}
cnt = 0; cnt_nonprim = 0; prim_ok = True; prim_conv_ok = True; nmax = 4000
for mods in families:
    pools = [chars(m) for m in mods]
    combos = list(itertools.product(*[range(len(p)) for p in pools]))
    random.shuffle(combos)
    for idx in combos[:nmax // len(families)]:
        chis = [pools[i][k] for i, k in enumerate(idx)]
        L, n = list_char(chis, mods)
        t = tau(L, n)
        # (1)
        if mods:
            c_rest, n_rest = list_char(chis[1:], mods[1:])
            rhs = val(chis[0], mods[0], n_rest) * val(c_rest, n_rest, mods[0]) * tau(chis[0], mods[0]) * tau(c_rest, n_rest)
            err['rec'] = max(err['rec'], abs(t - rhs))
        prod_tau = 1
        for c, m in zip(chis, mods): prod_tau *= tau(c, m)
        err['I'] = max(err['I'], abs(t - cross_I(chis, mods) * prod_tau), abs(cross_rec(chis, mods) - cross_I(chis, mods)))
        err['II'] = max(err['II'], abs(t - cross_II(chis, mods) * prod_tau))
        # (4)
        loc = 1
        for i, (c, m) in enumerate(zip(chis, mods)):
            f = tau(c, m) / math.sqrt(m)
            for j, (c2, m2) in enumerate(zip(chis, mods)):
                if j != i: f *= val(c2, m2, m)
            loc *= f
        err['W'] = max(err['W'], abs(Wn(L, n) - eps(L, n) * loc))
        # (5)
        k = sum(par(c, m) for c, m in zip(chis, mods))
        pe = 1; pw = 1
        for c, m in zip(chis, mods): pe *= eps(c, m); pw *= Wn(c, m)
        s = (-1) ** (k * (k - 1) // 2)
        err['sign'] = max(err['sign'], abs(eps(L, n) - s * pe))
        err['Wsign'] = max(err['Wsign'], abs(Wn(L, n) - s * cross_rec(chis, mods) * pw))
        # (6)
        pm = 1
        for c, m in zip(chis, mods): pm *= val(c, m, -1)
        err['neg1'] = max(err['neg1'], abs(val(L, n, -1) - pm))
        for nn in range(0, 3 * n + 2, max(1, n // 7)):
            pv = 1
            for c, m in zip(chis, mods): pv *= val(c, m, nn)
            err['nat'] = max(err['nat'], abs(val(L, n, nn) - pv))
        # (7)
        allp = all(is_prim(c, m) for c, m in zip(chis, mods))
        if allp and not is_prim(L, n): prim_ok = False
        if is_prim(L, n) and not allp: prim_conv_ok = False
        if not allp: cnt_nonprim += 1
        # (9)
        if len(mods) == 1:
            err['deg'] = max(err['deg'], abs(t - tau(chis[0], mods[0])), abs(cross_rec(chis, mods) - 1))
        cnt += 1

tol = 1e-8
report('(1) 漸化式 τ(listChar (a::l)) = χ_a(lvl l)·listChar l (N_a)·τ(χ_a)·τ(listChar l)', err['rec'] < tol, f'{cnt} 組、誤差 {err["rec"]:.1e}')
report('(2) 形 (I)：τ = ∏ χ_i(∏_{j≠i} N_j)·τ(χ_i)。漸化式の交差項 = 形 (I) の交差項', err['I'] < tol, f'誤差 {err["I"]:.1e}')
report('(3) 形 (II)：τ = ∏ τ(χ_i)·∏_{j≠i} χ_j(N_i)', err['II'] < tol, f'誤差 {err["II"]:.1e}')
report('(4) W = ε_∞(listChar)·∏ (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)', err['W'] < tol, f'誤差 {err["W"]:.1e}')
report('(5) ε_∞(listChar) = (−1)^{k(k−1)/2}·∏ ε_∞(χ_i)、W(listChar) = (−1)^{k(k−1)/2}·交差項·∏ W(χ_i)', max(err['sign'], err['Wsign']) < tol,
       f'誤差 {err["sign"]:.1e}・{err["Wsign"]:.1e}')
report('(6) listChar(−1) = ∏ χ_i(−1)、listChar(n) = ∏ χ_i(n)（自然数 n、単数でない n も含む）', max(err['neg1'], err['nat']) < tol,
       f'誤差 {err["neg1"]:.1e}・{err["nat"]:.1e}')
report('(7) すべて原始 ⇔ listChar も原始（両向き。Lean は isPrimitive_listChar_iff）。phaseA1 の式の数値の項目はない（rootNum_listChar からの帰結）', prim_ok and prim_conv_ok, f'順 {prim_ok}、逆 {prim_conv_ok}')
report('(9) 退化例 l = [a]：τ(listChar [a]) = τ(χ_a)、交差項 = 1', err['deg'] < tol, f'誤差 {err["deg"]:.1e}')
report('(11) 原始でない χ_i を含む組でも (1)〜(6) が成り立つ（原始性は要らない）', cnt_nonprim > 0 and max(err.values()) < tol, f'原始でない成分を含む組 {cnt_nonprim} 個')

# (8) 分解の個数と一意性
ok8 = True; det8 = []
for mods in [[3, 4], [5, 8], [3, 5, 7], [4, 9, 5], [9, 10], [7, 16]]:
    n = math.prod(mods)
    seen = {}
    for idx in itertools.product(*[range(len(chars(m))) for m in mods]):
        L, _ = list_char([chars(m)[k] for m, k in zip(mods, idx)], mods)
        key = tuple(round(L[a].real, 6) + 1j * round(L[a].imag, 6) for a in sorted(L))
        if key in seen: ok8 = False
        seen[key] = idx
    total = len(chars(n))
    if len(seen) != total: ok8 = False
    det8.append(f'{mods}:{len(seen)}/{total}')
report('(8) 法 lvl の指標はすべて listChar の形に、ちょうど 1 通りに書ける（組の数 = 指標の数、重複なし）', ok8, '、'.join(det8))

# (10) 並べ替え
ok10 = True
for mods in [[3, 4, 5], [8, 9, 7]]:
    for idx in list(itertools.product(*[range(len(chars(m))) for m in mods]))[:60]:
        chis = [chars(m)[k] for m, k in zip(mods, idx)]
        L1, n1 = list_char(chis, mods)
        L2, n2 = list_char(chis[::-1], mods[::-1])
        if n1 != n2 or any(abs(L1[a] - L2[a]) > 1e-9 for a in L1): ok10 = False
report('(10) 並びを逆にしても listChar の値は同じ（法も同じ数）', ok10, '[3,4,5]・[8,9,7] の各 60 組')

print('合格', sum(l.startswith('OK') for l in lines), '/', len(lines))
