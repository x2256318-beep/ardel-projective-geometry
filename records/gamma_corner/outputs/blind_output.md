## 照合結果（WebSearch と WebFetch のみ使用。数値計算なし。論文本文は WebFetch の要約を通した読み）

### Q1. φ は A_N を A_M に送るか。像は角 Q A_M Q 全体か

**答え**：送る。像は Q A_M Q 全体に等しい（gcd(N, M/N) によらない）。φ は単射な *-準同型だが単位的でない（φ(1) = Q）。

- **φ(E_s) = E^M_{(M/N)s}**。ι は周波数 ξ の指標を周波数 (M/N)ξ の指標に送り、gcd(N, ξ) = s ⇔ gcd(M, (M/N)ξ) = (M/N)s。
- **φ(D_s) = (Σ_{t|M, gcd(t,N)=s} D^M_t) · Q**（φ(D_s) は「gcd(N, x) = s」の指示関数（N 周期）の掛け算と Q の積で、両者は可換。gcd(N, x) = gcd(N, gcd(M, x)) なので指示関数は D^M_t の和）。
- **Q = Σ_{u|M, (M/N)|u} E^M_u**（Bose–Mesner 代数に入るので Q ∈ A_M）。
- 例：(2,4)：φ(D_1) = D^4_1 Q、φ(D_2) = (D^4_2 + D^4_4)Q、Q = E^4_2 + E^4_4、φ(E_s) = E^4_{2s}。(3,9)：φ(D_1) = D^9_1 Q、φ(D_3) = (D^9_3 + D^9_9)Q、Q = E^9_3 + E^9_9。(2,8)：φ(D_2) = (D^8_2 + D^8_4 + D^8_8)Q、Q = E^8_4 + E^8_8。(6,12)：φ(D_2) = (D^12_2 + D^12_4)Q、φ(D_6) = (D^12_6 + D^12_12)Q、Q = Σ_{2|u} E^12_u、φ(E_s) = E^12_{2s}。
- 注：φ は E 側の殻を殻へ送るが、D 側の像は Q が付くため D^M_t の線形結合にならない（N < M のとき Q は対角でない）。

**角全体に等しいことの根拠**（Q2 の主張と下のフーリエ共役 Ad F_M による）：
1. **三重正則性**：ℤ/p^e の単数軌道スキームは K_p ≀ … ≀ K_p（e 個）（[Bastian–Humphries 2026, Theorem 3.7](https://arxiv.org/abs/2606.19095)）で、K_n の wreath 積は三重正則（[Bhattacharyya–Song–Tanaka, J. Algebraic Combin. 31 (2010) 455–466](https://www.maths.tcd.ie/EMIS/journals/JACO/Volume31_3/q6uk7j772331187r.html)、[arXiv:0809.1052, Theorem 3.10](https://arxiv.org/abs/0809.1052)）。
2. 一般の N は中国剰余定理で素数冪の直積。T(X×Y) ≅ T(X)⊗T(Y)（Hanaki–Kim–Maekawa、Bastian–Humphries の Theorem 5.2 に引用）から T_0 = T が保たれ、Munemasa の Lemma 4（三重正則 ⇔ T = span{E*_i A_j E*_k}）で ℤ/M のスキームは三重正則。
3. 次元：Q A_M Q はフーリエ共役で P A_M P に移り、その次元は A_N の次元（Q2 の議論）。φ は単射なので像 = 角。例：dim A_2 = 4、dim A_4 = 10、dim A_3 = 5、dim A_9 = 12（Bastian–Humphries の次元式と照合）。

**確信度**：包含と各式は高。像が角全体に等しいことは高（ただし文献の結果と手計算の組み合わせで、数値での確認はしていない）。

### Q2. ψ について同じ問い。φ との関係

**答え**：ψ(A_N) ⊂ A_M で、ψ(A_N) = P A_M P（角全体）。ψ(1) = P で非単位的。
- ψ(D_s) = D^M_{(M/N)s}、ψ(E_s) = (Σ_{t|M, gcd(t,N)=s} E^M_t) · P（両者は可換）、P = Σ_{(M/N)|t} D^M_t。ψ は D 側の殻を殻へ送るが、E 側の像は Bose–Mesner 代数に入らない。
- **φ との関係**：正規化したユニタリ DFT で F_M ι = V F_N（直接計算）。また F D_s F⁻¹ = E_s、F E_s F⁻¹ = D_s（S_s = −S_s による）。したがって **ψ = Ad(F_M) ∘ φ ∘ Ad(F_N)⁻¹**、F_M Q F_M⁻¹ = P で、φ と ψ の命題は互いに同値。

**根拠**（ψ(A_N) = P A_M P の手計算）：H = (M/N)ℤ/Mℤ は閉部分集合 C = {t : (M/N) | t} の和で、H に制限したスキームは ℤ/N のスキームそのもの。三重正則性から P A_M P = span{E*_i A_j E*_k : i, k ∈ C}。i, k ∈ C なら x − y ∈ H なので j ∉ C の項は 0。E*_i A_j E*_k = E*_i (P A_j P) E*_k ∈ ψ(A_N)。逆向きの包含は自明。

**確信度**：高（手計算。数値確認なし）。

### Q3. 文献での扱い

**答え**：
- **Bose–Mesner 代数の場合は古典的**：商スキームの代数は {E_j}_{j∈J} の張る空間に同型で、Σ_{j∈J} E_j = (1/r)(I⊗J) は 𝔄 の中のべき等元による角（ここでは Q）。部分スキームの代数は fiber への制限（P による圧縮。P は双対代数の側で 𝔄 には入らない）。典拠：[Kodalen, PhD thesis, WPI 2019, §2.5, Lemma 2.13・2.14](https://arxiv.org/pdf/1905.06959)（BCN などを引用）。定義は Zieschang の *Theory of Association Schemes*（2005）、Theorem 2.1.8(ii)・4.1.3（[French, arXiv:1208.1173](https://arxiv.org/pdf/1208.1173) 経由で確認）。本件では φ(𝔄_N) = Q𝔄_M、ψ(𝔄_N) = P𝔄_M P、ψ(𝔄*_N) = P𝔄*_M、φ(𝔄*_N) = Q𝔄*_M Q。
- **Terwilliger 代数では** P も Q も T に入るので両方とも本物の角になる。どんなスキームでも T(部分) ⊆ PTP と ι T(X//C) ι† ⊆ QTQ は成り立つが、部分スキームの側の等号には三重正則性が十分条件として効く（Q2 の議論）。商の側は、並進スキームならフーリエ双対で部分スキームの側に移るが、一般のスキームでの条件は確かめていない。三重正則でないスキームで等号が実際に崩れるかも未確認。
- **「部分スキーム・商スキームの T(0) が角として現れる」を書いた文献は見つからなかった**。近いもの：[Munemasa, "An application of Terwilliger's algebra", 1993 preprint, Lemma 4](https://www.math.is.tohoku.ac.jp/~munemasa/preprints/T-algebraSpinModel.pdf)（三重正則 ⇔ T = T_0）、[Bastian–Humphries, arXiv:2606.19095 (2026)](https://arxiv.org/abs/2606.19095) Lemma 3.13（特性部分群への制限で AC 性が保たれる）・Prop. 5.6（wedge 積の G/K）は性質の遺伝で、角は扱わない。[Watanabe, arXiv:2305.19258, Cor. 7.5](https://arxiv.org/abs/2305.19258)（部分 poset への制限での所属。角ではない）。[Jiang, arXiv:2403.08537](https://arxiv.org/abs/2403.08537)（E*_g T E*_g を多用するが部分・商スキームは扱わない）。Hanaki–Kim–Maekawa と Hanaki（factor schemes）の本文は取得できなかった（リダイレクト先 URL が長すぎる）。

**確信度**：Bose–Mesner の古典的事実は高。「Terwilliger 版の記述は見つからなかった」は低〜中（不存在の証明ではない。MathSciNet・zbMATH は未使用）。

### Q4. 合成との両立、帰納極限、Bost–Connes

**答え**：
- **両立する**：π_{N,L} = π_{N,M}∘π_{M,L}、√(L/M)√(M/N) = √(L/N) から ι_{N,L} = ι_{M,L} ι_{N,M}、よって φ_{M,L}∘φ_{N,M} = φ_{N,L}（すべての N | M | L）。ψ も同様（x ↦ (L/N)x）。整除順序は有向（lcm）なので帰納極限は整除順序全体で取れる。
- **極限の具体形（手計算）**：J_N f = √N·f∘π_N で V_N を L²(Ẑ, Haar) に等長に埋め込むと J_M ι = J_N なので φ は包含になる。A_∞ = ∪ J_N A_N J_N† は有限階作用素からなる非単位的 *-代数で Ẑ^× の作用と可換、各段は角：Q_N A_∞ Q_N = J_N A_N J_N†（Q_N は位 N の関数への射影）。C* 完備化は有限次元 C* 代数の単射な帰納極限なので AF 代数。フーリエで ℓ²(ℚ/ℤ) の描像に移すと ψ が包含になる。
- **Bost–Connes との関係（手計算・観察）**：BC 代数を C(Ẑ) ⋊_α ℕ^×（α_n(f)(x) = f(x/n)·1_{nẐ}(x)。Laca–Raeburn 1999 による C*(ℚ/ℤ) ⋊_ρ ℕ^× との同一視、[Laca, PIMS notes 2010](https://www.pims.math.ca/files/DAY3_4_NOTES_SSNCG_2010.pdf)）とし、L²(Ẑ) 上で掛け算と等長作用素 (S_n g)(x) = √n·g(x/n)·1_{nẐ}(x) で表現する（共変関係を確認済み）。このとき J_{nN} V_{N,nN} = S_n J_N、すなわち **ψ_{N,nN} は Ad(μ_n) に当たる**。ψ(1) = P は μ_n μ_n* = ρ_n(1) = 1_{nẐ} の位 nN での姿で、D 側では Ad μ_n は ρ_n として働く。Ad μ_n は A_∞ を角 1_{nẐ} A_∞ 1_{nẐ} の上へ同型に送る（ρ_n が C*(ℚ/ℤ) を ρ_n(1)C*(ℚ/ℤ)ρ_n(1) に送ることの類似）。D 側の極限の関数は span{1_{dẐ}} = span{μ_d μ_d*} = C(Ẑ)^{Ẑ^×} の局所定数部分。E 側（指標の位数による射影）は BC 代数のこの表現の外にある。
- **文献**：帰納系 (A_N, φ_{N,M}) やその極限、Terwilliger 代数・アソシエーションスキームと BC 系を結ぶ文献は見つからなかった。

**確信度**：両立は高。BC との対応の式は中（手計算のみ、数値確認なし）。文献なしの判定は低〜中。

### Q5. F_q[t]/(t^e) → F_q[t]/(t^{e'})

**答え**：同じ理由で同じ答え（手計算の見込み）。単数軌道は付値 v = 0, …, e で、スキームは K_q ≀ … ≀ K_q（e 個。各段 t^k R/t^{k+1}R ≅ F_q の非零元が一つの軌道）なので、三重正則性は Bhattacharyya–Song–Tanaka（任意の n_i ≥ 2）でそのまま得られる。有限鎖環は Frobenius 環なので生成指標で R_e は自己双対、付値の分割も自己双対。商 R_e → R_{e'} は部分群 t^{e−e'}R_e への埋め込みとフーリエ双対。式は M/N を t^{e−e'} に置き換えるだけ：φ(E_{v'}) = E_{v'+e−e'}、ψ(D_{v'}) = D_{v'+e−e'}、Q = Σ_{v≥e−e'} E_v、P = Σ_{v≥e−e'} D_v。使ったのは超距離（木）の組合せ構造とポントリャーギン双対性だけで、ℤ に固有の算術は使っていない。

**確信度**：中〜高（手計算。F_q[t] の場合を直接扱った文献は確認していない）。

---

### 検索した語
1. Terwilliger algebra quotient scheme closed subset subscheme
2. "triply regular" association scheme Terwilliger algebra spanned E*_i A_j E*_k Munemasa
3. Terwilliger algebra cyclotomic scheme Z_n orbit Schur ring units Bastian Humphries
4. Terwilliger algebra Bost-Connes
5. "triply regular" "direct product" association schemes Terwilliger algebra tensor product
6. Zieschang factor scheme adjacency algebra isomorphic e_T CS e_T closed subset quotient scheme
7. Hanaki "factor schemes" representations … idempotent closed subset e_T
8. imprimitive association scheme quotient scheme Bose-Mesner algebra … "system of imprimitivity"
9. Terwilliger algebra halved graph bipartite … Curtin halved
10. Hanaki Kim Maekawa "Terwilliger algebras of direct and wreath products of association schemes"
11. "Terwilliger algebra" "closed subset" coset subscheme idempotent E^* T E^* …
12. "Terwilliger algebra" "factor scheme" OR "quotient scheme" homomorphism T(X//H)
13. inductive limit OR direct limit "Terwilliger algebras" profinite OR p-adic association scheme
14. Laca Raeburn semigroup crossed product … C(Ẑ) ⋊ N^× Bost-Connes
15. Bost-Connes "association scheme" OR "Schur ring" OR "Hecke algebra" Z/N units finite level truncation
16. association scheme finite chain ring unit orbits valuation wreath product Terwilliger algebra Galois ring
17. "Terwilliger algebra" imprimitive scheme quotient subscheme "triply regular" corner algebra

### 開いたページ
本文：Munemasa preprint（Lemma 4）、arXiv:0809.1052（abs と pdf。Thm 3.10、Prop 3.5）、arXiv:2606.19095（abs と pdf。Thm 3.7、Thm 2.1、Lemma 3.13、Thm 4.6、Thm 5.2）、arXiv:2305.19258（abs と pdf）、arXiv:1905.06959（§2.5）。要旨・メタデータ：arXiv:1008.2228、[arXiv:2210.15733](https://arxiv.org/abs/2210.15733)、[Iowa State 博士論文（Bhattacharyya 2008）](https://dr.lib.iastate.edu/entities/publication/ed418cf0-755c-4314-96bc-5df89278976c/full)、JACO の BST 2010 ページ、arXiv:2403.08537、[arXiv:1806.07010](https://ar5iv.labs.arxiv.org/html/1806.07010)。その他：[ar5iv 1109.1334](https://ar5iv.labs.arxiv.org/html/1109.1334)（冒頭 10 万字）、arXiv:1208.1173、[RIMS 講究録 1327-6](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1327-6.pdf)（無関係）、Laca の PIMS ノート。取得失敗：Hanaki–Kim–Maekawa の PDF と Hanaki（factor schemes）の PDF（リダイレクト先 URL が長すぎて拒否）。
