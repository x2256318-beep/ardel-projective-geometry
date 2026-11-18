"""A_M が三つ組の積 D_a E_b D_c の張る空間に等しいか（三重正則性に当たる性質）の数値確認。証明ではない。"""
import sys
import numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from corner_check import A, orth_basis, divisors
Mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
bad = []
for M in range(1, Mmax + 1):
    BM, D, E = A(M)
    trip = orth_basis([D[a] @ E[b] @ D[c] for a in D for b in E for c in D]).shape[1]
    if trip != BM.shape[1]: bad.append((M, trip, BM.shape[1]))
    print(M, BM.shape[1], trip)
print('三つ組の張る空間が A_M より小さい M：', bad)
