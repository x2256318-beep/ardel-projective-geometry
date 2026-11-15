## 結論

(i) と (ii) を両方課すと、(N, M) の答えは **gcd(N, M/N) = 1 のときに限り存在する** という二分法で決まります。互いに素なら存在し、そうでなければ存在しません。(i) と (ii) からは φ(I) = I が自動的に従うので、単位元を保つかどうかで答えは変わりません。下の否定の議論はすべて手計算です。

以下 k = M/N、W = im π^*（周期 N の関数）とします。

---

### Q1

**答え**：存在するのは gcd(N, k) = 1 のときだけです。単位元を保つ版と保たない版で違いはありません。

**根拠（手計算）**
1. **D の像は (i) と (ii) で一意に決まる。** φ は準同型なので φ(D_s) は冪等元です。直交冪等元 D_t の線形結合で冪等なものは、部分和 Σ_{t∈U} D_t に限られます。(i) を f = 1 に適用すると U = {t ∣ M : gcd(N, t) = s} が強制されます。つまり φ(D_s) = D̃_s（π^{-1}(S_s) の指示関数）です。ここから φ(I) = Σ_s D̃_s = I_M となり、φ は自動的に単位的になります。
2. **E の像も部分的に決まる。** π^* E_s = E_{ks} π^* が成り立ち、t が k の倍数でないとき E_t π^* = 0 です。よって φ(E_s) = Σ_{t∈T_s} E_t と書けます。ここで T_s は M の約数の分割の各ブロックで、T_s ∩ {k s' : s' ∣ N} = {k s} を満たす必要があります。
3. **障害となる関係式。** A_N の中では D_N = e_{00}（S_N = {0} の指示関数）、E_N = J/N です。したがって D_N E_N D_N = (1/N) D_N が成り立ちます。これを φ で送ると、D̃_N は部分群 H = Nℤ/Mℤ の指示関数になります。H の上へ圧縮した核を ℤ/k 上でフーリエ比較すると、次と同値になります。
   - 「Ξ := ⋃_{t∈T_N} {ξ : gcd(M, ξ) = t} が、ℤ/M における kℤ/Mℤ の完全代表系である（各剰余類 mod k にちょうど 1 点）」
4. **gcd(N, k) &gt; 1 なら不可能。** 素数 p が p ∣ N かつ p ∣ k を満たすとします。Ξ は p 成分が単数になる剰余類 η mod k にも 1 点を持たなければなりません。その点が属する殻 t は v_p(t) = 0 です。CRT で分解すると、殻 t とその剰余類の交わりは p 成分だけで p^{v_p(N)} ≥ 2 点を持つので、完全代表系になりえません。
5. **gcd(N, k) = 1 なら存在する。** CRT により ℤ/M ≅ ℤ/N × ℤ/k、V_M = V_N ⊗ V_k となり、殻と周波数殻はどちらも積に分解します（D_{su} = D_s ⊗ D_u、E_{su} = E_s ⊗ E_u）。よって A_M = A_N ⊗ A_k です。これは Hanaki–Kim–Maekawa の Theorem 3.1（直積スキームの Terwilliger 代数はテンソル積）と一致します。π^* f = f ⊗ 1 なので、φ(T) = T ⊗ I_k が (i) と (ii) を満たす単位的準同型になります。

**補足（問いの外）**：(ii) を外して (i) だけを課す場合、非単位的な準同型は常に存在します。φ(T) = π^* T (π^*)^{-1} P_W ⊕ 0 とし、P_W = Σ_s E_{ks} とすれば、生成元の像 D̃_s P_W と E_{ks} はどちらも A_M に入ります。ただし D 側の (ii) は一般に破れます。(i) だけで単位的な準同型が存在するかどうかは確かめていません（不明）。

**確信度**：高。自分で導出した結果で、文献照合はできていません。

---

### Q2

**答え**
- gcd(N, k) = 1 のときは存在します（φ = T ⊗ I_k）。
- N = p^e、M = p^{e+1}（e ≥ 1）のときは存在しません。さらに一般に N = p^e、M = p^{e+f}（e, f ≥ 1）でも存在しません。T_N に加えられるのは殻 p^j（j &lt; f）だけで、その各剰余類 mod p^f には p^e ≥ 2 点が入るからです。

小さい例は次のとおりです。

| (N, M) | gcd(N, M/N) | 結果 |
|---|---|---|
| (2, 4) | 2 | なし |
| (2, 8) | 2 | なし |
| (3, 9) | 3 | なし |
| (2, 6) | 1 | あり |
| (3, 6) | 1 | あり |

(2, 4) は直接確かめられます。殻は {0}, {2}, {1, 3} で、Ξ は「0 を含む 2 元集合で、偶数類と奇数類から 1 点ずつ」でなければなりません。殻の和でそうなるものはありません。表現論で見ても同じ結論です。A_2 = M_2(ℂ) で、E_2 の階数は加群の次元のちょうど半分でなければなりません。一方 W^⊥（周波数 1, 3）の上では φ(E_2) は 0 か I にしかなれません。

**確信度**：高。

---

### Q3

**答え**：Terwilliger 代数のあいだで、商 ℤ/M → ℤ/N に沿った写像や帰納系の存在を扱う文献は見つかりませんでした。見つからなかった、というだけで、存在しないとは言えません。

近い文献は次のとおりです。
- Hanaki–Kim–Maekawa, "Terwilliger algebras of direct and wreath products of association schemes"（[プレプリント](https://soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf)）。
  - Theorem 3.1：直積の T はテンソル積。これが互いに素の場合の存在を与えます。
  - Theorem 4.1：wreath 積で、(Y, T) が thin または 1-class のときの中心的原始冪等元。
  - 掲載誌の J. Algebra 343 (2011) は Bastian–Humphries の引用によるもので、プレプリント本体には記載がありません。
  - 本文を確認した範囲では、商スキームや部分スキームが誘導する準同型は扱っていません。
- Bastian–Humphries, "Schur rings over cyclic groups having Almost Commutative Terwilliger algebras"（arXiv 2606.19095, 2026 年 6 月, https://arxiv.org/abs/2606.19095）。
  - C_{p^n} 上で単数群全体の軌道スキームは K_p ≀ … ≀ K_p（Corollary 3.6, Theorem 3.7）。
  - dim T の公式（Proposition 3.3）。
  - wedge 積と商 G → G/K に関する AC 性の遺伝（Proposition 5.6, Theorem 5.10）。
  - ここで扱われているのは AC 性の遺伝で、代数のあいだの写像ではありません。
- Bost–Connes 系の有限レベルと Terwilliger 代数を結びつける文献は見つかりませんでした。

**確信度**：中。存在しないことの確信ではなく、検索の範囲が限られているためです。

---

### Q4

**答え**：e ≥ 2 なら存在しません。ℤ/p^e のときと同じ理由で決まり、p が q に置き換わるだけです。

**根拠**：R_e = F_q[t]/(t^e) は鎖環（Frobenius 環）です。生成指標 ψ を使って R̂_e ≅ R_e と同一視すると、単数の軌道は空間側でも周波数側でも付値の殻になります。
- 核 K = t^{e-1} R_e の零化群は K^⊥ = t R_e です。
- Q1 と同じ関係式 D_top E_top D_top = (1/|R_{e-1}|) D_top から、「Ξ が R_e における t R_e の完全代表系である」ことが必要になります。
- T_top に追加できるのは付値 0 の殻（単数）だけです。その殻は各非零剰余類に q^{e-1} 点を持ちます。
- よって完全代表系になるのは e − 1 = 0 のときだけです。
- 互いに素の類似（F_q[t]/(fg) で gcd(f, g) = 1）では、CRT によりテンソル積となり存在します。

**確信度**：高（手計算）。

---

### 検索した語
1. Terwilliger algebra direct product of association schemes tensor product
2. Terwilliger algebra Schur ring cyclic group Z_n orbit scheme units
3. Terwilliger algebra quotient association scheme homomorphism inductive limit
4. Hanaki Kim Maekawa Terwilliger algebras of direct and wreath products of association schemes J. Algebra 2011
5. Bost-Connes system finite level Z/N association scheme Terwilliger algebra
6. Bastian Humphries Terwilliger algebra orbit Schur ring cyclic group p^n wreath product K_p
7. "Terwilliger algebra" profinite OR "inverse limit" OR "direct limit" association schemes Z/p^n tower

### 開いたページ
- https://arxiv.org/pdf/2606.19095
- https://arxiv.org/abs/2606.19095
- https://soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf

検索結果に出たが開いていないページ：arXiv 2503.02837, 2305.19258, 0809.1052, 1109.1334, 2410.21600, 2101.09636。
