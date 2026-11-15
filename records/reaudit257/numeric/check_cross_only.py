"""再照合のときの確認：交差項だけでずれる組（s = 1 で交差項 ≠ 1）。法 3 の奇の指標と法 7 の 3 次の指標（A2 の手計算の例）。"""
import cmath, math
def chars(p, g):
    # 素数 p、原始根 g の法 p の指標を、χ(g) = ζ^k で全部作る
    n = p - 1; out = []
    log = {pow(g, e, p): e for e in range(n)}
    for k in range(n):
        out.append({a: (cmath.exp(2j*math.pi*k*log[a]/n) if a % p else 0) for a in range(p)})
    return out
def W(chi, n):
    tau = sum(chi[a % n] * cmath.exp(2j*math.pi*a/n) for a in range(n))
    odd = abs(chi[(n-1) % n] + 1) < 1e-9
    return tau / ((1j if odd else 1) * math.sqrt(n))
def prod(c1, M, c2, N):
    return {a: c1[a % M] * c2[a % N] for a in range(M*N)}
c3 = [c for c in chars(3, 2) if abs(c[2] + 1) < 1e-9]          # 法 3 の奇の指標
c7 = [c for c in chars(7, 3) if abs(c[3]**3 - 1) < 1e-9 and abs(c[3] - 1) > 1e-9]  # 法 7 の 3 次の指標（2 個）
ok = True
for c1 in c3:
    for c2 in c7:
        even2 = abs(c2[6] - 1) < 1e-9
        s = -1 if (not even2 and True) else 1  # c1 は奇なので、s = −1 は c2 が奇のとき
        cross = c1[7 % 3] * c2[3 % 7]
        w = W(prod(c1, 3, c2, 7), 21); w1 = W(c1, 3); w2 = W(c2, 7)
        law = abs(w - s * cross * w1 * w2) < 1e-9
        print('c2 even', even2, 's', s, 'cross', cross, '|cross-1|', round(abs(cross-1), 6), 'law', law, 'W != W1W2', abs(w - w1*w2) > 1e-9)
        ok &= even2 and abs(cross - 1) > 1e-9 and law and abs(w - w1*w2) > 1e-9
print('結果:', 'OK' if ok else 'NG')
