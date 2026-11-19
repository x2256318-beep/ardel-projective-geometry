# 照合報告：A_∞ の作用、制限テンソル積への分解、文献（盲検の問いテスト、通知の本文を写したもの）

**総括**：Q1・Q2・Q4 は既知の一般論（Flath 型の制限テンソル積、中国剰余定理、帰納極限とテンソル積の交換、中心化代数）を当てはめれば答えが出る。この型の構成を Terwilliger 代数について書いた文献は見つからなかった（見つからなかったことは存在しないことの証明ではない）。

前提：コードは実行しておらず数値確認はしていない。手計算の部分はその旨を書く。ページはすべて WebFetch の要約を通して読んだもので、原文を直接は読んでいない。

記号：μ は Ẑ の Haar 確率測度、ι_N = π_N^* は V_N → V_∞、(P_N f)(a) = N∫_{a+NẐ} f dμ。

## Q1. A_∞ は V_∞ に作用するか、忠実か、像は何か

- **作用する**：φ_{N,∞}(S) = ι_N S P_N と置くと、レベルの取り方によらず定まる（手計算：π_{M'M,*}π_{M'M}^* = (M'/M)·id から φ_{N,M'}(S)π^*_{M'M} = π^*_{M'M} φ_{N,M}(S)）。核で書くと K(x,y) = N·S(x mod N, y mod N) で、Ẑ×Ẑ 上の局所定数な核を持つ有限階作用素。Q_N = φ_{N,∞}(1) は NẐ 周期の関数への条件付き期待値（L²(Ẑ,μ) での直交射影）。
- **忠実**：ι_N は単射、P_N は全射で、各 φ_{N,M} も単射だから。各 f ∈ V_N は Q_N で固定されるので A_∞V_∞ = V_∞（非退化な加群）。
- **生成元の姿**：
  - D 側：φ_{N,∞}(D_s) = M_{1_Ω}·Q_N、Ω = {x ∈ Ẑ : gcd(x,N) = s} は開かつ閉な集合。掛け算作用素 M_{1_Ω} 自体は無限階なので A_∞ には入らない（乗数の側）。
  - E 側：φ_{N,∞}(E_s) = Π_{N/s}。Π_d は位数がちょうど d の指標 e_r（r ∈ ℚ/ℤ）の張る空間への射影で、階数は φ(d)、核はラマヌジャン和 c_d(x−y)。N によらないので、記録の φ(E_s) = E_{(M/N)s} と合う。Q_N = Σ_{d|N} Π_d で、メビウス反転すると E 側は {Q_d} の張る空間に等しい。E 側はコンパクトなゲルファント対 (Ẑ⋊Ẑ^×, Ẑ^×) の球ヘッケ代数の作用そのもの。
- **像の記述（2 通り）**：
  - (a) T_∞ を「Ẑ^× 不変な局所定数関数 g による M_g と、Π_d たちとが生成する単位的な代数」とすると、A_∞ は T_∞ の中で Π_d たちが生成する両側イデアルに等しく、T_∞ = {M_g} ⊕ A_∞、A_∞ = T_∞ ∩（有限階作用素）（手計算、確信度：高）。
  - (b) A_∞ は G_0 = ∏_p Isom_0(ℤ_p)（各 ℤ_p の、0 を固定する等長変換の群の積）と可換な、局所定数核を持つ有限階作用素の全体に等しい。核で言えば K(x,y) が (v_p(x), v_p(y), v_p(x−y))_p だけで決まること（手計算、確信度：中〜高）。
  - (b) の根拠：循環スキーム ℤ/p^k は K_p の k 重の輪積で、Bhattacharyya–Song から dim A_{p^k} = (k+1)² + k(k+1)/2 = (3k²+5k+2)/2（p が奇数）、(3k²+3k+2)/2（p = 2）。Bastian–Humphries の命題 3.3 の値と一致。一方、根付き p 分木の葉 0 の固定部分群が葉の対の上に持つ軌道を三つ組 (v(x), v(y), v(x−y)) で数えると、p が奇数でも 2 でもちょうど同じ数になる。T(0) は常に中心化代数に含まれるので、次元が等しいことから A_{p^k} は中心化代数に等しい。テンソル積をとれば一般の N でも A_N = End(V_N)^{G_N}。
  - (b) の系：記録で Lean の外として残っている「像が角全体であること」（Q A_M Q = φ(A_N)）は、中心化代数の角がまた中心化代数になることと、固定部分群の写像 Stab_M → Stab_N が全射であることから出る（手計算、確信度：中〜高）。
  - 局所の代数は A_{p^∞} ≅ End_fin(C^∞(ℤ_p)^{ℤ_p^×}) ⊕ ℂ^{(ℕ)} の形になる見込み（主加群のブロックは主加群のブロックへ、1 次元のブロックは 1 次元のブロックへ移る。確信度：中）。Part 261 の「局所的な単位元はあるが左単位元はない」と矛盾しない。
- **Ẑ^× の可換子全体ではない**：N = 5 で dim A_5 = 5 に対し、(ℤ/5)^× の中心化代数は 7 次元。例えば f ↦ f(2·) は後者に入るが A_5 には入らず、レベルを上げても A_M に入らない。G_0 が Ẑ^× より真に大きいことの反映。
- 確信度：作用・忠実性・(a) は高。(b) と角の性質は中〜高。局所の構造は中。

## Q2. 制限テンソル積への分解

**答え**：なる。A_∞ ≅ ⊗'_p (A_{p^∞}; e_p)、V_∞ ≅ ⊗'_p (V_{p^∞}; 1_{ℤ_p}) で、作用も局所の作用の制限テンソル積（既知の当てはめ、確信度：高）。

1. 中国剰余定理と、直積スキームの Terwilliger 代数がテンソル積になること（Bastian–Humphries の定理 5.2。D_s・E_s が純テンソルになり、ℂ 上のテンソル積の中で T(A)⊗1 と 1⊗T(B) が生成される）から A_N ≅ ⊗_{p|N} A_{p^{k_p}}。
2. π^*、π_*、係数 N/M はすべて素数ごとに分かれるので φ_{N,M} = ⊗_p φ_{p^k, p^{k'}}。N を割らない素数の因子は ℂ = A_1 → A_{p^{k'}}、1 ↦ e_1。
3. 整除の順序は ⊕_p ℕ と同型で、フィルター付きの帰納極限は各変数のテンソル積と交換する。体の上では単射のテンソル積も単射。したがって lim_N = lim_S ⊗_{p∈S} A_{p^∞} で推移写像は a ↦ a ⊗ e_q。まさに Flath の型の ⊗'。生成元も対応：Π_d = ⊗_{p|d} Π_{p^{v_p(d)}} ⊗ ⊗_{p∤d} e_1（e_1 = Π_1 は位数 1 の指標、すなわち定数関数への射影）。V_∞ の側は C^∞(Ẑ) = ⊗' C^∞(ℤ_p)（1_{ℤ_p} に関して。アデールの Schwartz–Bruhat 空間の分解の、台が Ẑ に入る部分）。e_p·1_p = 1_p が、Flath の設定の「e_{K_v} が球ベクトルを固定する」にあたる。

## Q3. 既存の文献

- **見つかった同じ型の結果（既知）**：
  - Flath：大域ヘッケ代数が e_{K_v} に関する局所ヘッケ代数の ⊗' になり、許容既約表現も球ベクトルに関する ⊗' になる。書誌（"Decomposition of representations into tensor products", Proc. Sympos. Pure Math. 33 Part 1, AMS 1979, pp. 179–183）は記憶で、原文もページも未照合。統一的な証明として [Deitmar, A general tensor product theorem, arXiv:1002.0475](https://ar5iv.labs.arxiv.org/html/1002.0475)（主定理 2.1）。
  - Schwartz–Bruhat 関数：アデール上の空間は、ほとんどすべての素点で整数環の特性関数をとる制限テンソル積として定義される（[Wikipedia](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Bruhat_function) が Bump『Automorphic Forms and Representations』p. 300 と Ramakrishnan–Valenza p. 260 を引用。両書とも未照合）。
  - Bost–Connes 型：[Laca–Larsen–Neshveyev, arXiv:math/0609316](https://arxiv.org/abs/math/0609316)（DOI から Adv. Math. 2007 と推定）。定理 3.2：固定点代数 C*_r(P,P_0)^{Ẑ^*} ≅ ⊗_p 𝔄_p^{ℤ_p^*}。序論はこれを Bost–Connes の 1 次元の場合との平行として述べる。§3.3：古典的なヘッケ代数 H(S,Γ) が H(S_p,Γ) のテンソル積になること（同論文の文献 [7] 第 IV 章を引用、[7] の書誌は未確認）。Bost–Connes 1995 の原論文の素数ごとの分解は、CERN のページがボット対策で開けず未照合（確信度：低）。
  - Terwilliger 代数の有限レベル：[Bastian–Humphries, arXiv:2606.19095 (2026)](https://arxiv.org/abs/2606.19095)（定理 5.2 直積とテンソル積、命題 3.3 次元。レベル間の写像と極限は扱っていない）、[Bhattacharyya–Song, arXiv:0809.1052](https://ar5iv.labs.arxiv.org/html/0809.1052)（T((K_n)^{≀d}) ≅ M_{d+1} ⊕ ℂ^{d(d+1)/2}、n ≥ 3）。
- **見つからなかったもの**：Terwilliger 代数の帰納系・直極限、プロ有限な対象の上の Terwilliger 代数、その ⊗' への分解。近い枠組みはあるが、いずれもボーズ・メスナーの水準で Terwilliger 代数も極限もない（読めた範囲で）：[Voit, Continuous association schemes and hypergroups](https://ar5iv.labs.arxiv.org/html/1708.01177)、[Nakada, arXiv:2511.02385](https://arxiv.org/abs/2511.02385v1)、[Bastian–Brewer–Misseldine, arXiv:1806.07010](https://arxiv.org/abs/1806.07010)。Hanaki–Kim–Maekawa の PDF は URL が長すぎて取得拒否。
- 確信度：同じ型の結果があることは高。Terwilliger 版がないことは低〜中（MathSciNet・zbMATH は使えていない）。

## Q4. 𝔽_q[t] の場合

同じ理由で決まる（確信度：高）。A = 𝔽_q[t] は剰余環が有限の単項イデアル整域で中国剰余定理が使える。A/(P^k) は局所環なので単数の軌道は v_P で決まり、スキームは K_n の k 重の輪積（n = q^{deg P}）。E 側の射影は単数で不変な双対群の軌道として内在的に決まり、加法指標 ψ の選び方によらない。直積の定理と、帰納極限とテンソル積の交換は一般論。したがって A_∞ ≅ ⊗'_P A_{|P|^∞}、V_∞ = C^∞(Â)。局所因子は剰余体の大きさ n だけで決まり、n = 2 か n ≥ 3 かで分かれる（ℚ での p = 2 と奇素数の区別に対応）。同じ論法は剰余体が有限な任意のデデキント整域でも通る。

## 残余についての意見

- Q1・Q2・Q4 には、既知の当てはめで済まない残余は見当たらない。§7 の対照群テストに照らすと 𝔽_q[t] でも同じ文が成り立つ。さらに Q1 の局所構造の見込みが正しければ、A_{p^∞} は抽象的な代数としては p によらない。その場合、A_∞ を抽象代数として見たときには、算術は「素点の集合が可算個ある」こと以外に何も入っていない。p への依存はラベルのついた加群 V_∞ の側（球の大きさ）にしか現れない。
- 小さいノートの水準で書かれていない可能性があるもの：A_N = End(V_N)^{G_N}（木の自己同型の固定部分群の中心化代数）、角の性質、V_∞ の G_0 等型成分への分解。
- 構成に最初から入っていないもの：無限素点、ℚ_+^* によるスケーリング（Bost–Connes の μ_n）、貼り合わせ U は A_∞ に一切現れない。残余を持つ問いを立てるなら、⊗'_p の外にあるこれらとの相互作用を含める必要がある（確信度：中）。

## 検索した語（24 本、要点）・開いたページ

検索語：Flath decomposition / Bost–Connes tensor product over primes / Terwilliger algebra infinite association scheme direct limit profinite / Schwartz–Bruhat restricted tensor product / Terwilliger algebra rooted tree ultrametric p-adic / Laca–Raeburn / Schur rings profinite・Q/Z / "Terwilliger algebra" inductive limit / Hanaki Kim Maekawa / profinite association schemes / Gelfand pair Z_p ⋊ Z_p^× / Bastian Humphries / restricted tensor product Terwilliger など。
読めたページ：Wikipedia「Schwartz–Bruhat function」、arXiv math/0609316、AIM「The C*-algebra of Bost–Connes」、arXiv math/9911134、2511.02385、1806.07010、1906.09469、2509.16174、2606.19095、EMS JNCG 11140、Booher のノート。一部だけ：ar5iv 0806.2401、1708.01177、1002.0475、0809.1052、arXiv html 2503.02837。開けなかった：Wikipedia「Bost–Connes system」、CERN cds 283504、Hanaki–Kim–Maekawa の PDF。
