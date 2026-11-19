# 統合照合 II-a の入力：尾の台帳 L3（Part 260（PAG264）の統合照合の後の直し）と L4（Part 261（PAG265）の再照合の後の直し）（2026-11-20）

照合の対象：§L3-4 と §L4-4 の「直した後の散文」のうち、前の照合の出力（§L3-1・§L4-1）を受けて直した文。直す前の散文（§L3-2・§L4-2）と比べて、直しが指摘を正しく反映したか、形式文（§L3-3・§L4-3 の Lean の全文）より強いことを言っていないか、新しいずれを生んでいないかを見る。


## §L3 台帳 L3

```markdown
### L3：Part 260（PAG264）の統合照合の後の直し（2026-11-19 午後、コミット ef021d6 の後）

- 範囲：恒等の法則と尾の統合照合（`records/audit264/outputs/integrated_output.md`）の後に直した散文 11 点（PAG264 の冒頭の説明と、ノート `pag2_pag264_corner_maps.md` §1〜§3）。§9 に列挙がある。
- 経緯：自己申告で「尾の台帳は空」としていた。2026-11-19 19:58 の著者の規則に照らして戻した（20:02 に届いた補足 15 との照らし合わせで見つけた）。
- 扱い：次の統合照合の対象。
```


### §L3-1 Part 260 の統合照合の出力（`records/audit264/outputs/integrated_output.md`、全文）

# 統合照合の成果物（PAG264／Part 260、通知の本文を写したもの）

（条件：新しいエージェント、Read 1 回で input_integrated.md の 1〜623 行、約 440 秒。依頼文は request_integrated.md。照合者の申告：プロジェクトの CLAUDE.md は最初から文脈にあったが、照合の根拠には使っていない。）

## 1. 新しい 3 定理

この 3 定理は section `uniq` にあり、文に M が現れないので `M` と `[NeZero M]` は引数に入らない。仮定は N ≥ 1 だけ。整除の証明は `dvd_refl N` で書かれているが、証明の中身は文の意味に影響しないので、N ∣ N のどの証明でも同じ文になる。

**fsum_self**
- 逆翻訳：N を正の整数とする。ℤ/N 上の任意の複素数値関数 g について、恒等写像 ℤ/N → ℤ/N の各繊維の上で g を足した関数は g 自身に等しい。
- 証人：N = 3、g = (1, 2, 5)。各点の繊維は 1 点なので、繊維の和は (1, 2, 5) = g。
- 除去テスト：N ≥ 1 を外すと、N = 0 では ℤ/0 = ℤ が無限集合で和が定義できない（反例ではなく型が立たない）。一般の N ∣ M（M ≠ N）に替えると両辺の型が合わない。型の合う類似の文はどちらも偽：π_*(π^* f) = f は (1, 2)、f = 1 で左辺 2f（`fsum_pull` の M/N 倍）、π^*(π_* g) = g は (1, 2)、g = δ₀ = (1, 0) で左辺 (1, 1)。したがって「繊維の和が恒等」は N = M に固有。

**cornerOp_self**
- 逆翻訳：N ≥ 1 とし、S を ℂ^{ℤ/N} 上の任意の線形作用素とする（A_N に属さなくてよい）。このとき (N/N)·π^* ∘ S ∘ π_*（π は恒等）は S に等しい。
- 証人：N = 2、S = [[0,1],[1,0]]（2×2 行列なら何でもよい）で φ_{2,2}(S) = S。
- 除去テスト：N < M に替えると、型の合う類似の文「φ(1) = 1」は偽（`cornerOp_one_ne_one`。(1, 2) で φ(1) = ½[[1,1],[1,1]] ≠ I）。係数 N/M を 1 や (N/M)² に替えても、N = M では係数が 1 になるので文はそのまま成り立つ。つまりこの定理は正規化を何も試していない（正規化を確かめているのは `cornerOp_pull`・`cornerOp_mul`・`cornerOp_comp`。係数を外すと N < M で積を保たない：(1, 2)、S = 1 で Q = π^*π_* について Q² = 2Q）。

**cornerHom_self**
- 逆翻訳：N ≥ 1 のとき、A_N から A_N への角の写像（非単位的な代数準同型）は A_N の恒等写像に等しい。
- 証人：N = 2 で φ_{2,2}(D^{(2)}_2) = D^{(2)}_2、φ_{2,2}(E^{(2)}_2) = E^{(2)}_2、とくに φ_{2,2}(1) = 1。
- 除去テスト：N < M に替えると、型の合う類似の文「cornerHom h 1 = 1」は偽（`cornerHom_one_ne_one`）。逆向きの帰結として、`cornerHom_one_ne_one` の仮定 N < M は外せない（N = M、例えば 1 = 1 で反例）。この反例は今回、Lean の文から直接出るようになった。

## 2. 宣言名を挙げた散文の照合

宣言名と内容の対応、Σ の添字、水準の上付きに取り違えはなかった。ずれは次のとおり。

**主なずれ**
1. **D §1「非単位的」の項**：「N = M の場合について、Lean の文は何も言っていない。」は、午後に追加した `cornerOp_self`・`cornerHom_self` から φ_{N,N} = id、とくに φ(1) = 1 が出るので誤りになった。そもそも `cornerOp_one_single` も N = M で φ(1)(δ₀)(0) = 1 を言っていた。直し方：「N = M では φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`）なので φ(1) = 1。N ∣ M のもとで φ(1) ≠ 1 ⟺ N < M（直ちに出る。単独の宣言はない）。」
2. **C 内部照合の件数**：「宣言は定理 37・定義 5」だが、A を数えると定理 40（37 に 3 つを足した数）。機械的照合 2 回の内訳も 3 定理を加える前の数と一致する（1 回目の定理 41 = 39 + 自動生成 2、2 回目の 39 = 37 + 2）。つまり新しい 3 定理は重複照合（第 12 の型）を受けていない。直し方：「定理 40・定義 5」に直し、3 定理が機械的照合を受けていないことを明記するか、3 定理を含めてもう 1 回照合する。
3. **C の照合の節**：「直した内容：…恒等の法則が Lean の外であること…」は、C の 4 と D §1 の現状（恒等の法則は Lean にある）と矛盾する。直し方：「（午後に恒等の法則を Lean に入れたため、この直しは置き換えた）」と注記する。
4. **ラベルの結論が対照群の範囲より広い**：C「対照群でも成り立つ（数値）ので、算術の内容ではない」、D §2「…ℚ に固有の算術ではない」。範囲の節では「ℤ/p^e の段に当たる場合だけ、有限な剰余環で試した」と狭めたのに、結論の側が狭まっていない。C の結論は D より強い。直し方：「ℤ/p^e の段に当たる場合（F_p[t]/(t^e) → F_p[t]/(t^{e'})、関数体そのものではない）に限り、同じ文が成り立つ（数値）。互いに素な段は試していない。」
5. **一意性の反例の量化（C の 4・D §1）**：「(N, M) = (1,2) で φ'(c) = c·1 も (a) を満たす。(a) を外しても、積を保つことを外しても一意でない。」(1, 2) では A_1 = ℂ·1 が 1 次元なので (b) だけで φ(c) = c·φ(1) に決まり、後半の 2 つの反例は (1, 2) では作れない。どの組で作った反例かを明記する必要がある。照合者の手計算（Lean の外、確信度：中〜高）では (2, 4) なら成り立つ：(a) を外す場合、A_2 は非可換で D^{(2)}_2 と E^{(2)}_2 が可換でないので、u = 1 + D^{(2)}_2 による内部自己同型を合成した φ∘Ad(u) は (b) を満たし、φ が単射なので φ と異なる。積を保つことを外す場合、φ + λ(·)(1 − φ(1))（λ は λ(1) = 0 となる 0 でない線形汎関数）は (a)(b) を満たし、φ と異なる。

**軽微なずれ**
6. D §1 D 側の項：「すべての s ∣ N で φ(D^{(N)}_s) は span に入らない」で、何の span かが抜けている。「D^{(M)}_u（u ∈ ℕ）の span」と書く。
7. C の 4・D §1「整除の順序の上で帰納系の 2 法則」：A_0 は定義されないので、添字は正の整数（`NeZero`）。「正の整数の整除の順序」と書く。
8. C の 4「(a) すべての S, f で」：Lean では S は A_N の元。直前の「1. 一般の S ∈ End」と読み違えうるので、「すべての S ∈ A_N と f で」と書く。
9. D §1「像は φ(1) の角に入る」：C には「単独の宣言はない」とあるが D にはない。揃える。
10. C の照合の節「7 点の指摘を受けて直した」：列挙の 8 項目は E の 7 点と一致しない（E の 5（三重正則性の「見込み」）と 6（ι S ι^† の読み）が抜け、7 点の外の項目（水準・件数・対照群）が入っている）。
11. 随伴を保つことの根拠：C は「行列の形からの手計算」、D は「照合者の手計算」。どちらかに揃える。

**入力からは確かめられないもの**（ずれとは判定していない）
- Part 258 の「殻を混ぜない条件」の形式定義が B にないので、`cornerOp_dind_not_mem_span` の span がその条件の D 側と同じかは確認できない。E 側を「満たす」は `cornerOp_geps` から直ちに出る（単独の宣言はない）。
- `dft_oldP`・`dft_geps`・`pull_smul` の文が B にないので、どの PAG にあるかと「定義を展開すると等しくなる式」であることは確認していない。

## 3. 「Lean の外」「数値」「手計算」の照合

- A に実際にないもの（散文の書き方は正しい）：π_* が π^* の随伴であること・ι S ι^† の読み、一意性の 3 つの反例（量化は 2 の 5）、`DirectedSystem` としての束ねと極限 A_∞、D 側の一般化（Lean は (2, 4)、s = 2 だけ）、像が角全体であること（⊇）、Bost–Connes の ρ との対応、随伴を保つこと、対照群、T(0) との同一視。
- 帰納系の法則と恒等の法則：C の 4・D §1 は、合成の法則と恒等の法則を Lean にあると正しく書いている。外としているのは束ねと極限だけで、A と合う。
- A にあるのに「外」「何も言っていない」と書いているもの：D §1 の N = M の文（2 の 1）。C の照合の節と E §8 の 2 の「恒等の法則が Lean の外」（過去の記録としては正しいが、現状の記述として読める）。
- 数値の範囲（推測を含む）：「111 組」は M ≤ 30 で N ∣ M の組（N = M を含む）の数 Σ_{M≤30} d(M) = 111 と一致し、81 = 111 − 30。111 組が N = M の 30 組を含むなら、その 30 組は `cornerHom_self` から直ちに出るので、範囲を明記し、自明でない 81 組と分けて書くとよい。
- A から直ちに出るが散文に書いていないもの：φ(1) が冪等であること、φ(1) ≠ 1 ⟺ N < M。

## 4. E の直しが C・D に入っているか

| E の直し | 状態 |
|---|---|
| 1 非単位的の言い方 | C・D とも入っている。ただし D の付け足し文が、午後の追加で誤りになった（2 の 1） |
| 2 「帰納系をなす」を外す・恒等の法則は Lean の外 | 午後の追加で置き換わった。現状の C の 4・D §1 は A と合う。C の照合の節と E §8 に置き換えの注記がない |
| 3 M = N·t の形 | 入っている |
| 4 D 側の量化と根拠 | C は入っている。D は span の対象が抜けている（2 の 6） |
| 5 三重正則性を「見込み」に | 入っている |
| 6 ι S ι^† は読み | 入っている |
| 7 (a)(b) と書き Part 258 の (ii) と区別 | (a)(b) は入っている。Part 258 の (ii) が何かは C・D のどこにも書かれていない |
| Σ の添字・水準の明示 | 入っている（D の span だけ抜け） |
| 件数の内訳 | 入っているが、3 定理の追加で古くなった（2 の 2） |
| 対照群の範囲 | 範囲の節には入っている。ラベルの結論には伝わっていない（2 の 4） |
| PAG 番号の併記、⊆ の書き分け | 入っている（D には「単独の宣言はない」がない） |

## 5. 問題のなかった項目

宣言名の取り違え：なし。記号の取り違え：なし。宣言名を挙げた文で形式文より強い主張：2 の 1 以外はなし。


### §L3-2 直す前の散文（統合照合に渡した版：PAG264 の冒頭の説明、ノートの §1〜§3・§8）

## C. 散文その 1：PAG264.lean の冒頭の説明
```
/-
アーデル射影幾何 — Part 260（PAG264、短期層の小さいノート、2026-11-19）：角の写像 A_N → A_M（N ∣ M、非単位的な代数準同型）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §4）。2026-11-19 09:37 に著者が採用した。
基礎文書の第 5 章（索引 5.2 の留保「代数版にはならない」）と第 6 章 6.3（Bost–Connes との接続）の材料。新しいパートではない。

記号：N, M ≥ 1（`NeZero`）、N ∣ M、π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。D^{(N)}_s = mulLeft(dind N s)、E^{(N)}_s = convL(geps N s)（水準を上付きで書く）。
- π^* = `pull`（Part 197（PAG201））。P = `oldP N t`（Part 202（PAG206）、M = N·t のときの旧部分への射影）。
- ε^{(M)}_u = geps M u（E^{(M)}_u の畳み込み核）。

定義：
- `fsum h`（h : N ∣ M）：繊維の和 π_* g(x) = Σ_{π y = x} g(y)。
- `cornerOp h S = (N/M)·π^* ∘ S ∘ π_*`（S ∈ End(ℂ^{ℤ/N})）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であること（数え上げの内積）は Lean の外。
- `cornerHom h : shellAlg N →ₙₐ[ℂ] shellAlg M`：非単位的な代数準同型。型は単位元の保存を課さない。

Lean の文：
1. 一般の S ∈ End(ℂ^{ℤ/N})：
   - π_*(π^* f) = (M/N)·f（`fsum_pull`）。
   - 引き戻しと両立 φ(S) π^* = π^* S（`cornerOp_pull`）。
   - 積（`cornerOp_mul`）、和・スカラー倍・0（`cornerOp_add`・`cornerOp_smul`・`cornerOp_zero`）。
   - φ(1)φ(S) = φ(S) = φ(S)φ(1)（`cornerOp_one_mul`・`cornerOp_mul_one`）。
   - 単射（`cornerOp_injective`）。
   - φ(1)(δ₀)(0) = N/M（`cornerOp_one_single`）。N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`）。
2. M = N·t の形：
   - π^*(π_* g) = t·P g（`pull_fsum`）。
   - φ(1) = P（`cornerOp_one_apply`）。
   - ε^{(Nt)}_{ts} ⋆ P g = ε^{(Nt)}_{ts} ⋆ g（`conv_geps_oldP`）。
   - φ(E^{(N)}_s) = E^{(Nt)}_{ts}（`cornerOp_geps_mul`）。
3. 一般の N ∣ M：
   - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。
   - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
   - π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
   - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。
   - φ は A_N を A_M に送る（`cornerOp_mem`）。gcd(N, M/N) は仮定にない。
   - まとめたものが `cornerHom`（値は `cornerHom_coe`）。
   - 像が φ(1) の角に入ること（⊆）は、`cornerOp_mem`・`cornerOp_one_mem`・`cornerOp_one_mul`・`cornerOp_mul_one` から直ちに出る（単独の宣言はない）。
4. 一意性と合成：
   - (a) すべての S, f で φ(S)(π^* f) = π^*(S f)、(b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
   - (a)(b) を満たす非単位的な代数準同型 A_N → A_M（`→ₙₐ` の中で）は、ちょうど 1 つ（`existsUnique_corner`）。
   - 一意性の証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論で、引き戻しとの両立だけで決まるという文ではない。
   - 独立照合の手計算の反例（Lean にしていない）：(b) を外すと一意でない（(N, M) = (1,2) で φ'(c) = c·1 も (a) を満たす）。(a) を外しても、積を保つことを外しても一意でない。
   - 繊維の和の合成（`fsum_trans`）。
   - N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。引き戻しの合成は Part 259（PAG263）の `pull_pull`。
   - 単射（`cornerHom_injective`）。N < M なら cornerHom(1) ≠ 1（`cornerHom_one_ne_one`）。
   - 恒等の法則（2026-11-19 午後に追加）：N → N の繊維の和は恒等（`fsum_self`）、φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。引き戻しの恒等は Part 259（PAG263）の `pull_self`）。
   - 合成の法則と恒等の法則が揃ったので、(A_N, φ_{N,M}) は整除の順序（N ∣ M）の上で、帰納系の 2 法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean にしていない。
5. D 側の証人：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
   - Part 258（PAG262）の殻を混ぜない条件（強い読み）の D 側を満たさない。E 側は 3 の φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} から満たす。
   - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は D^{(M)}_u の span に入らない。
     - 数値：M ≤ 30 の N < M の 81 組。
     - 手計算：(1,2)・(2,6)、独立照合。
     - Lean にあるのは (2,4)、s = 2 だけ。

範囲（Lean にしていないもの）：
- 像が角全体であること（φ(1) A_M φ(1) ⊆ φ(A_N) の側）。
  - 数値：111 組。
  - 手計算：構築側と盲検が一致。三重正則性（文献）からの短い帰結の見込み。
- 帰納系の `DirectedSystem` としての束ねと、その極限 A_∞（有限次元の代数の和集合。完備化は解像度が落ちる側の操作と読む）。
- Bost–Connes の ρ との対応（数値と手計算）。
- 随伴を保つこと φ(S^*) = φ(S)^*（行列の形からの手計算）。
- 対照群 F_p[t]/(t^e) → F_p[t]/(t^{e'})（数値。ℤ/p^e の段に当たる場合だけを試した）。

位置づけ（ラベル）：
- ［既知］：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5）の作用素版。
  - 関数のレベルは Part 202（PAG206）。
- ［再導出（小さい）］：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - 初等的な議論。
  - T(0) 版の文献は、盲検の問いテスト（2026-11-19）では見つからなかった（確信度：低〜中。MathSciNet・zbMATH は未実施）。
- 新規候補はない。対照群でも成り立つ（数値）ので、算術の内容ではない。
- A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：商に沿った非単位的な写像 A_N → A_M の宣言は、鎖になかった（網羅ではない）。
  - Part 202（PAG206）の `oldP` 系を使った：φ(1) = P、`oldP_eq_sum`（P = Σ E）、`geps_conv_pull`、`dft_oldP`。
  - Part 201（PAG205）の `dft_geps` も使った。
- 閉じる前（機械的）：全宣言 4470 件。PAG264 の対象は 46 件で、定理 41（自動生成の congr_simp を含む）と定義 5。
  - 候補は上位 20。定理は両向きに、定義は 1 回で照合し、41·20·2 + 5·20 = 1740 回。
  - 一致と出たのは `cornerOp_apply` と Part 197（PAG201）の `pull_smul` の 1 組だけ。どちらも定義を展開すると等しくなる式で、中身の重複ではない。
  - 候補の上位を言葉で確かめて、下書きの次の 2 つを消した。
    - `pull_trans`：Part 259（PAG263）の `pull_pull` と向きが逆の同じ文（A）。
    - `apply_single_two_of_mem_span`：Part 258（PAG262）の `exists_mulLeft_of_mem_span` から直ちに出る（B）。
  - 単射の証明は Part 259（PAG263）の `pull_injective'` を使う形に直した。
- 2 回目：全宣言 4468 件、対象 44 件（定理 39・定義 5）、39·20·2 + 5·20 = 1660 回。上の定義の展開の 1 組だけ。
- 宣言は定理 37・定義 5 で、自動生成の宣言は数えない。
- 「見つからなかった」は「重複はない」ではない。

照合（恒等の法則の追加と、それまでの尾をまとめた統合照合の記録は `records/audit264/`）：
- 独立照合（形式文と定義だけ）：偽・空虚な文はなかった。除去テストの反例を文面に反映した。
- 直した文面の再照合で、7 点の指摘を受けて直した。
  - 直した内容：非単位的の言い方、恒等の法則が Lean の外であること、条件の記号 (a)(b)、M = N·t の形、D 側の量化と根拠、水準の明示、件数の内訳、対照群の範囲。
  - 再照合の後のこの直しは、主張を狭めるか明確にするもので、照合を受けていない（尾。次の統合照合の対象）。
- 記録は `records/audit264/`。
-/
```

## D. 散文その 2：ノートの §1〜§3
## §1 結果（Lean の文から起こした）

記号：
- N, M ≥ 1 で N ∣ M。π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。Terwilliger 代数 T(0) とは辞書による同一視で、Lean の定理ではない。
- D^{(N)}_s・E^{(N)}_s は水準 N の殻の掛け算と双対殻への射影。
- π^* は引き戻し（Part 197（PAG201）の `pull`）、π_* は繊維の和（`fsum`）。

主な文：
- **写像**：φ(S) = (N/M)·π^* ∘ S ∘ π_*（`cornerOp`）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であることは Lean の外。
- **A_N を A_M に送る**（`cornerOp_mem`）。
  - gcd(N, M/N) は仮定にないので、素数冪の段 (2,4)・(3,9) なども含む。
  - 非単位的な代数準同型 `cornerHom : A_N →ₙₐ A_M`（型は単位元の保存を課さない）としてまとめた。
- **生成元の像**：
  - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
  - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。M = N·t と書いたとき、Part 202（PAG206）の `oldP N t` に等しい（`cornerOp_one_apply`）。
  - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。ここで π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
- **引き戻しと両立**：φ(S)π^* = π^* S（`cornerOp_pull`）。
- **像は φ(1) の角に入る**（⊆。`cornerOp_one_mul`・`cornerOp_mul_one` と `cornerOp_mem` から）。
- **単射**（`cornerOp_injective`・`cornerHom_injective`）。
- **非単位的**：N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`・`cornerHom_one_ne_one`）。N = M の場合について、Lean の文は何も言っていない。
- **一意性**：次の (a)(b) を満たす非単位的な代数準同型 A_N → A_M は、`→ₙₐ` の中でちょうど 1 つ（`existsUnique_corner`）。
  - (a) 引き戻しと両立する。
  - (b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - 証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論。
  - 「引き戻しとの両立だけで決まる」という文ではない。独立照合の手計算の反例（Lean にしていない）：
    - (b) を外すと一意でない。(1,2) では φ'(c) = c·1 も (a) を満たす。
    - (a) を外しても、積を保つことを外しても一意でない。
- **合成**：N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。
  - 恒等の法則 φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。N → N の繊維の和は恒等 `fsum_self`、引き戻しの恒等は Part 259（PAG263）の `pull_self`）。2026-11-19 午後に追加（§9）。
  - 合成と恒等の 2 法則が揃い、(A_N, φ_{N,M}) は整除の順序の上で帰納系の法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean の外。
- **D 側の証人**：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
  - Part 258（PAG262）の殻を混ぜない条件（強い読み）の D 側を満たさない。E 側は満たす。
  - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は span に入らない。
    - 数値：M ≤ 30 の N < M の 81 組。
    - 手計算：(1,2)・(2,6)、独立照合。
    - Lean にあるのは (2,4)、s = 2 だけ。

## §2 ラベル

- **［既知］**：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5。どちらも盲検が挙げたもの）の作用素版。
  - 関数のレベルは Part 202（PAG206）（`geps_conv_pull`、`oldP_eq_sum`）。
- **［再導出（小さい）］**：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - どれも初等的な議論。
  - 盲検の問いテスト（2026-11-19）で見つからなかったもの（確信度：低〜中）：T(0) 版（部分スキーム・商スキームの T(0) が角として現れること）、整除の順序全体の帰納系、Bost–Connes と T(0) を結ぶ文献。
  - 検索語：Terwilliger algebra quotient scheme closed subset subscheme、triply regular、Terwilliger algebra Bost-Connes、inductive limit Terwilliger algebras ほか 17 本（`records/gamma_corner/outputs/blind_output.md`）。
  - 検索先はウェブだけ。MathSciNet・zbMATH は未実施（著者側）。「見つからなかった」は不存在の証明ではない。
- **新規候補はない**。対照群（F_p[t]/(t^e)）でも成り立つ（数値）ので、ℚ に固有の算術ではない。

## §3 範囲（Lean にしていないもの）

- **像が角全体であること**（φ(1) A_M φ(1) ⊆ φ(A_N) の側。逆の包含は §1）。
  - 数値：111/111 組。
  - 手計算：構築側と盲検の手計算が一致。三重正則性（Bhattacharyya–Song–Tanaka 2010、Munemasa 1993 の Lemma 4）からの短い帰結の見込み。
  - 鎖には三重正則性がない。
- **帰納系の `DirectedSystem` としての束ねと、整除の順序全体の極限 A_∞**。
  - A_∞ は有限次元の代数の和集合で、Ẑ 上の局所定数関数に作用する。
  - 完備化（L²(Ẑ)、C* 完備化）は解像度が落ちる側の操作と読み、目標として書かない（§1 の 08:41 の定義）。
- **Bost–Connes の ρ との対応**：群環の側で φ = ρ_{M/N}（数値）。L²(Ẑ) の表現では T(0) の片側だけが BC に対応する（盲検の手計算）。
- **随伴を保つこと** φ(S^*) = φ(S)^*（照合者の手計算）。
- **対照群** F_p[t]/(t^e) → F_p[t]/(t^{e'})：同じ文が成り立つ（数値）。これは関数体そのものではなく有限な剰余環で、ℤ/p^e の段に当たる場合だけを試した。

## E. 散文その 3：ノートの §8（前回の再照合を受けて直したことの一覧）
## §8 直した文面の再照合

- **条件**：新しいエージェントに、冒頭の説明とこのノートの §1〜§3、形式文と定義を渡した（Read 1 回、約 251 秒）。出力は `records/audit264/outputs/recheck_output.md`。
- **結果**：宣言名の取り違えと、形式文にあるのに Lean の外と書いたものは、なかった。
- **散文が形式文より強い・あいまいな箇所（7 点）を直した**：
  1. 「単位元を保たない代数準同型」を「非単位的な代数準同型（型は単位元の保存を課さない）。N < M なら φ(1) ≠ 1」にした。
  2. 「したがって帰納系をなす」を外した。恒等の法則 φ_{N,N} = id は Lean の外と書いた。
  3. `cornerOp_one_apply` が M = N·t の形の文であることを書いた。
  4. D 側の一般化を「N ∣ M、N < M、すべての s ∣ N」と量化し、根拠（数値 81 組と手計算）を揃えた。
  5. 三重正則性からの帰結を「見込み」に揃えた。
  6. ι S ι^† は読みで、随伴の同定は Lean の外と書いた。
  7. 一意性の条件を (a)(b) と書き、Part 258 の (ii) と区別した。
- **ほかに直したこと**：
  - Σ の添字に s ∣ M を書き、水準を E^{(N)}・E^{(M)} と明示した。
  - 件数の内訳を書いた（46 件 = 定理 41（自動生成の congr_simp を含む）＋定義 5、1740 = 41·20·2 + 5·20）。
  - 対照群の範囲を ℤ/p^e の段に当たる場合に狭めた。
  - PAG 番号を併記した。
  - 像が角に入る側（⊆）は Lean の文から直ちに出ると書き分けた。
- **再照合の後のこの直し**：主張を狭めるか明確にするもので、照合を受けていない。補足8の停止の規約の範囲内で、尾として次の統合照合の対象にする。


### §L3-2b 統合照合に渡した定義と前の鎖の補題の文

## B. 使う定義と、証明で使う前の鎖の補題の文（証明は省略）
```lean
-- PAG201（Part 197）
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
theorem card_ker_cast {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') :
    ((Finset.univ.filter (fun z : ZMod N' => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).card : ℂ)
      * N = N'
-- PAG15
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)
def convL : (G → K) →ₗ[K] (G → K) →ₗ[K] (G → K) := LinearMap.mk₂ K conv ...   -- convL f g = conv f g
-- PAG203（Part 199）
noncomputable def rk {N : ℕ} (v d : ℕ) (Ψ : ZMod d → ℂ) : ZMod N → ℂ :=
  fun x => if v ∣ x.val then Ψ ((x.val / v : ℕ) : ZMod d) else 0
-- PAG205（Part 201）。𝓕 は Mathlib の ZMod.dft、𝓕⁻ はその逆
noncomputable def dind (N s : ℕ) : ZMod N → ℂ := fun ξ => if Nat.gcd N ξ.val = s then 1 else 0
noncomputable def geps (N s : ℕ) [NeZero N] : ZMod N → ℂ := 𝓕⁻ (dind N s)
-- PAG206（Part 202）
noncomputable def oldP (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) : ZMod (N * t) → ℂ :=
  ((t : ℂ)⁻¹) • PAG.Part15.conv (rk (N := N * t) N 1 (fun _ => 1)) f
theorem oldP_eq_sum (N t : ℕ) [NeZero N] [NeZero t] (f : ZMod (N * t) → ℂ) :
    oldP N t f = ∑ s ∈ (N * t).divisors.filter (fun s => t ∣ s), PAG.Part15.conv (geps (N * t) s) f
theorem geps_conv_pull (N t s : ℕ) [NeZero N] [NeZero t] (f : ZMod N → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (pull (dvd_mul_right N t) f) =
      pull (dvd_mul_right N t) (PAG.Part15.conv (geps N s) f)
-- PAG218（Part 214）
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
-- PAG232（Part 228）
theorem convL_geps_mem (N s : ℕ) [NeZero N] : PAG.Part15.convL (geps N s) ∈ shellAlg N
theorem mulLeft_dind_mem (N s : ℕ) [NeZero N] : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N
-- PAG262（Part 258）
theorem exists_mulLeft_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    ∃ h : ZMod M → ℂ, T = LinearMap.mulLeft ℂ h
-- PAG263（Part 259）
theorem pull_pull (hNM : N ∣ M) (hML : M ∣ L) (f : ZMod N → ℂ) :
    PAG.Part201.pull hML (PAG.Part201.pull hNM f) = PAG.Part201.pull (hNM.trans hML) f
theorem pull_injective' (hNM : N ∣ M) : Function.Injective (PAG.Part201.pull hNM)
theorem pull_self (f : ZMod N → ℂ) : PAG.Part201.pull (dvd_refl N) f = f
```



### §L3-3 現在の PAG264.lean の全文（docstring を含む）

```lean
/-
アーデル射影幾何 — Part 260（PAG264、短期層の小さいノート、2026-11-19）：角の写像 A_N → A_M（N ∣ M、単位元を保つとは限らない代数準同型。N < M では保たず、N = M では恒等）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §4）。2026-11-19 09:37 に著者が採用した。
基礎文書の第 5 章（索引 5.2 の留保「代数版にはならない」）と第 6 章 6.3（Bost–Connes との接続）の材料。新しいパートではない。

記号：N, M ≥ 1（`NeZero`）、N ∣ M、π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。D^{(N)}_s = mulLeft(dind N s)、E^{(N)}_s = convL(geps N s)（水準を上付きで書く）。
- π^* = `pull`（Part 197（PAG201））。P = `oldP N t`（Part 202（PAG206）、M = N·t のときの旧部分への射影）。
- ε^{(M)}_u = geps M u（E^{(M)}_u の畳み込み核）。

定義：
- `fsum h`（h : N ∣ M）：繊維の和 π_* g(x) = Σ_{π y = x} g(y)。
- `cornerOp h S = (N/M)·π^* ∘ S ∘ π_*`（S ∈ End(ℂ^{ℤ/N})）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であること（数え上げの内積）は Lean の外。
- `cornerHom h : shellAlg N →ₙₐ[ℂ] shellAlg M`：単位元を保つとは限らない代数準同型（型は単位元の保存を課さない。N < M では保たず（`cornerHom_one_ne_one`）、N = M では恒等（`cornerHom_self`））。

Lean の文：
1. 一般の S ∈ End(ℂ^{ℤ/N})：
   - π_*(π^* f) = (M/N)·f（`fsum_pull`）。
   - 引き戻しと両立 φ(S) π^* = π^* S（`cornerOp_pull`）。
   - 積（`cornerOp_mul`）、和・スカラー倍・0（`cornerOp_add`・`cornerOp_smul`・`cornerOp_zero`）。
   - φ(1)φ(S) = φ(S) = φ(S)φ(1)（`cornerOp_one_mul`・`cornerOp_mul_one`）。
   - 単射（`cornerOp_injective`）。
   - φ(1)(δ₀)(0) = N/M（`cornerOp_one_single`）。N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`）。N = M では φ(1) = 1（4 の恒等の法則）なので、N ∣ M のもとで φ(1) ≠ 1 ⟺ N < M（直ちに出る。単独の宣言はない）。
2. M = N·t の形：
   - π^*(π_* g) = t·P g（`pull_fsum`）。
   - φ(1) = P（`cornerOp_one_apply`）。
   - ε^{(Nt)}_{ts} ⋆ P g = ε^{(Nt)}_{ts} ⋆ g（`conv_geps_oldP`）。
   - φ(E^{(N)}_s) = E^{(Nt)}_{ts}（`cornerOp_geps_mul`）。
3. 一般の N ∣ M：
   - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。
   - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
   - π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
   - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。
   - φ は A_N を A_M に送る（`cornerOp_mem`）。gcd(N, M/N) は仮定にない。
   - まとめたものが `cornerHom`（値は `cornerHom_coe`）。
   - 像が φ(1) の角に入ること（⊆）は、`cornerOp_mem`・`cornerOp_one_mem`・`cornerOp_one_mul`・`cornerOp_mul_one` から直ちに出る（単独の宣言はない）。
4. 一意性と合成：
   - (a) すべての S ∈ A_N と f で φ(S)(π^* f) = π^*(S f)、(b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
   - (a)(b) を満たす、単位元の保存を課さない代数準同型 A_N → A_M（`→ₙₐ` の中で）は、ちょうど 1 つ（`existsUnique_corner`）。
   - 一意性の証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論で、引き戻しとの両立だけで決まるという文ではない。
   - 独立照合の手計算の反例（Lean にしていない）：(b) を外すと一意でない（(N, M) = (1,2) で φ'(c) = c·1 も (a) を満たす）。(a) を外しても、積を保つことを外しても一意でない（どちらも (2,4) の例。(1,2) では A_1 = ℂ なので (b) だけで決まる）。
   - 繊維の和の合成（`fsum_trans`）。
   - N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。引き戻しの合成は Part 259（PAG263）の `pull_pull`。
   - 単射（`cornerHom_injective`）。N < M なら cornerHom(1) ≠ 1（`cornerHom_one_ne_one`）。
   - 恒等の法則（2026-11-19 午後に追加）：N → N の繊維の和は恒等（`fsum_self`）、φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。引き戻しの恒等は Part 259（PAG263）の `pull_self`）。
   - 合成の法則と恒等の法則が揃ったので、(A_N, φ_{N,M}) は正の整数の整除の順序（N ∣ M）の上で、帰納系の 2 法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean にしていない。
5. D 側の証人：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
   - Part 258（PAG262）の殻を混ぜない条件（強い読み：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）の D 側を満たさない。E 側は 3 の φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} から満たす（直ちに出る。単独の宣言はない）。
   - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は D^{(M)}_u の span に入らない。
     - 数値：M ≤ 30 の N < M の 81 組。
     - 手計算：(1,2)・(2,6)、独立照合。
     - Lean にあるのは (2,4)、s = 2 だけ。

範囲（Lean にしていないもの）：
- 像が角全体であること（φ(1) A_M φ(1) ⊆ φ(A_N) の側）。
  - 数値：M ≤ 30 で N ∣ M の 111 組（N = M の 30 組を含み、その 30 組は `cornerHom_self` から直ちに出る。自明でないのは N < M の 81 組）。
  - 手計算：構築側と盲検が一致。三重正則性（文献）からの短い帰結の見込み。
- 帰納系の `DirectedSystem` としての束ねと、その極限 A_∞（有限次元の代数の和集合。完備化は解像度が落ちる側の操作と読む）。
- Bost–Connes の ρ との対応（数値と手計算）。
- 随伴を保つこと φ(S^*) = φ(S)^*（独立照合の照合者による、行列の形からの手計算）。
- 対照群 F_p[t]/(t^e) → F_p[t]/(t^{e'})（数値。ℤ/p^e の段に当たる場合だけを試した）。

位置づけ（ラベル）：
- ［既知］：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5）の作用素版。
  - 関数のレベルは Part 202（PAG206）。
- ［再導出（小さい）］：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - 初等的な議論。
  - T(0) 版の文献は、盲検の問いテスト（2026-11-19）では見つからなかった（確信度：低〜中。MathSciNet・zbMATH は未実施）。
- 新規候補はない。対照群は、ℤ/p^e の段に当たる場合（F_p[t]/(t^e) → F_p[t]/(t^{e'})。関数体そのものではない）に限って同じ文が成り立つ（数値）。互いに素な段は試していない。盲検の手計算では、使うのは平行移動スキームの形式（商とフーリエ双対）だけ。ℚ に固有の算術の内容は、試した範囲では見つかっていない。
- A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：商に沿った非単位的な写像 A_N → A_M の宣言は、鎖になかった（網羅ではない）。
  - Part 202（PAG206）の `oldP` 系を使った：φ(1) = P、`oldP_eq_sum`（P = Σ E）、`geps_conv_pull`、`dft_oldP`。
  - Part 201（PAG205）の `dft_geps` も使った。
- 閉じる前（機械的）：全宣言 4470 件。PAG264 の対象は 46 件で、定理 41（自動生成の congr_simp を含む）と定義 5。
  - 候補は上位 20。定理は両向きに、定義は 1 回で照合し、41·20·2 + 5·20 = 1740 回。
  - 一致と出たのは `cornerOp_apply` と Part 197（PAG201）の `pull_smul` の 1 組だけ。どちらも定義を展開すると等しくなる式で、中身の重複ではない。
  - 候補の上位を言葉で確かめて、下書きの次の 2 つを消した。
    - `pull_trans`：Part 259（PAG263）の `pull_pull` と向きが逆の同じ文（A）。
    - `apply_single_two_of_mem_span`：Part 258（PAG262）の `exists_mulLeft_of_mem_span` から直ちに出る（B）。
  - 単射の証明は Part 259（PAG263）の `pull_injective'` を使う形に直した。
- 2 回目：全宣言 4468 件、対象 44 件（定理 39・定義 5）、39·20·2 + 5·20 = 1660 回。上の定義の展開の 1 組だけ。
- 3 回目（午後、恒等の法則の 3 つ）：全宣言 4471 件、対象 3 件、候補上位 20、3·20·2 = 120 回。一致なし。
- 宣言は定理 40・定義 5（午後に 3 つを足した）。自動生成の宣言は数えない。
- 「見つからなかった」は「重複はない」ではない。

照合（記録は `records/audit264/`）：
- 独立照合（形式文と定義だけ）：偽・空虚な文はなかった。除去テストの反例を文面に反映した。
- 直した文面の再照合で、7 点の指摘を受けて直した：(1) 非単位的の言い方、(2) 「帰納系をなす」を外し恒等の法則を Lean の外と書いた、(3) M = N·t の形、(4) D 側の量化と根拠、(5) 三重正則性を「見込み」に、(6) ι S ι^† は読み、(7) 条件の記号 (a)(b)。ほかに水準の明示・件数の内訳・対照群の範囲・PAG 番号を直した。
- 午後に恒等の法則を Lean に入れたので、(2) の「恒等の法則は Lean の外」は置き換えた。
- 統合照合（恒等の法則の 3 定理と、再照合の後の直しの尾をまとめて 1 回）：
  - 足した 3 定理は意図どおりで、宣言名・記号の取り違えはなかった。
  - 散文のずれ 11 点を直した：N = M の文、件数、(2) の置き換えの注記、対照群の結論、反例の組、span の対象、正の整数、S ∈ A_N、⊆ の注記、7 点の列挙、随伴の根拠。
  - 統合照合の後のこの直しは、主張を狭めるか明確にするもの（強める直しはない）。補足8の停止の規約の範囲として、尾の台帳は空とする。
-/
import PAG263

open Complex Finset

namespace PAG.Part264

open PAG.Part201 PAG.Part205 PAG.Part206 PAG.Part218 PAG.Part232

section general

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- 繊維の和 π_* g(x) = Σ_{π y = x} g(y)（π : ℤ/M → ℤ/N、N ∣ M）。 -/
noncomputable def fsum (h : N ∣ M) (g : ZMod M → ℂ) : ZMod N → ℂ :=
  fun x => ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x), g y

omit [NeZero N] in
theorem fsum_add (h : N ∣ M) (g g' : ZMod M → ℂ) : fsum h (g + g') = fsum h g + fsum h g' := by
  funext x; simp only [fsum, Pi.add_apply, sum_add_distrib]

omit [NeZero N] in
theorem fsum_smul (h : N ∣ M) (c : ℂ) (g : ZMod M → ℂ) : fsum h (c • g) = c • fsum h g := by
  funext x; simp only [fsum, Pi.smul_apply, smul_eq_mul, mul_sum]

/-- 引き戻し（線形写像）。 -/
noncomputable def pullLin (h : N ∣ M) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod M → ℂ) where
  toFun := pull h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 繊維の和（線形写像）。 -/
noncomputable def fsumLin (h : N ∣ M) : (ZMod M → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := fsum h
  map_add' := fsum_add h
  map_smul' := fsum_smul h

/-- 繊維の大きさは M/N。 -/
theorem card_fiber (h : N ∣ M) (x : ZMod N) :
    ((univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x)).card : ℂ) = (M : ℂ) / N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨y0, hy0⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod N)) x
  have e : univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x) =
      (univ.filter (fun z : ZMod M => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).map
        (addRightEmbedding y0) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_map, addRightEmbedding_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    constructor
    · intro hy
      exact ⟨y - y0, by rw [map_sub, hy, hy0, sub_self], sub_add_cancel y y0⟩
    · rintro ⟨z, hz, rfl⟩
      rw [map_add, hz, zero_add, hy0]
  rw [e, card_map, eq_div_iff hN]
  exact card_ker_cast h

/-- **1a.** π_*(π^* f) = (M/N)·f。 -/
theorem fsum_pull (h : N ∣ M) (f : ZMod N → ℂ) : fsum h (pull h f) = ((M : ℂ) / N) • f := by
  funext x
  simp only [fsum, pull_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_congr rfl (fun y hy => by rw [(mem_filter.mp hy).2]), sum_const, nsmul_eq_mul, card_fiber]

/-- 角の写像 φ(S) = (N/M)·π^* ∘ S ∘ π_*（= ι S ι^†、ι = π^*/√(M/N)）。 -/
noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)

omit [NeZero N] in
theorem cornerOp_apply (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (g : ZMod M → ℂ) :
    cornerOp h S g = ((N : ℂ) / M) • pull h (S (fsum h g)) := rfl

theorem scal_cancel (N M : ℕ) [NeZero N] [NeZero M] : ((N : ℂ) / M) * ((M : ℂ) / N) = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp

/-- **1b. 引き戻しと両立**：φ(S) π^* = π^* S。 -/
theorem cornerOp_pull (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) :
    cornerOp h S (pull h f) = pull h (S f) := by
  rw [cornerOp_apply, fsum_pull, map_smul, pull_smul, smul_smul, scal_cancel, one_smul]

/-- **1c. 積を保つ**：φ(ST) = φ(S)φ(T)。 -/
theorem cornerOp_mul (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S * T) = cornerOp h S * cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, fsum_smul, fsum_pull,
    smul_smul, scal_cancel, one_smul, Module.End.mul_apply]

omit [NeZero N] in
theorem cornerOp_add (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S + T) = cornerOp h S + cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [LinearMap.add_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, LinearMap.add_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]

omit [NeZero N] in
theorem cornerOp_smul (h : N ∣ M) (c : ℂ) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (c • S) = c • cornerOp h S := by
  apply LinearMap.ext; intro g
  rw [LinearMap.smul_apply, cornerOp_apply, cornerOp_apply, LinearMap.smul_apply, pull_smul, smul_comm]

omit [NeZero N] in
theorem cornerOp_zero (h : N ∣ M) : cornerOp h 0 = 0 := by
  simpa using cornerOp_smul h 0 0

/-- **1d.** 像は角に入る：φ(1) φ(S) = φ(S) = φ(S) φ(1)。 -/
theorem cornerOp_one_mul (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h 1 * cornerOp h S = cornerOp h S := by
  rw [← cornerOp_mul, one_mul]

theorem cornerOp_mul_one (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h S * cornerOp h 1 = cornerOp h S := by
  rw [← cornerOp_mul, mul_one]

/-- **1e.** φ は単射。 -/
theorem cornerOp_injective (h : N ∣ M) : Function.Injective (cornerOp h) := by
  intro S T hST
  apply LinearMap.ext; intro f
  have e := congrArg (fun X : Module.End ℂ (ZMod M → ℂ) => X (pull h f)) hST
  simp only [cornerOp_pull] at e
  exact PAG.Part263.pull_injective' h e

omit [NeZero N] in
/-- 1 点の関数の繊維の和。 -/
theorem fsum_single (h : N ∣ M) (y0 : ZMod M) (c : ℂ) (x : ZMod N) :
    fsum h (Pi.single y0 c) x = if ZMod.castHom h (ZMod N) y0 = x then c else 0 := by
  simp only [fsum]
  rw [sum_pi_single']
  simp only [mem_filter, mem_univ, true_and]

omit [NeZero N] in
/-- **1f.** φ(1)(δ₀)(0) = N/M（N < M なら φ(1) ≠ 1：単位元を保たない）。 -/
theorem cornerOp_one_single (h : N ∣ M) :
    cornerOp h 1 (Pi.single 0 1) 0 = (N : ℂ) / M := by
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, Module.End.one_apply, fsum_single, map_zero,
    ite_eq_left rfl, smul_eq_mul, mul_one]

omit [NeZero N] in
theorem cornerOp_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerOp h 1 ≠ 1 := by
  intro e
  have e2 := cornerOp_one_single h
  rw [e, Module.End.one_apply, Pi.single_eq_same] at e2
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  rw [eq_div_iff hM, one_mul] at e2
  exact absurd (Nat.cast_injective e2) (Nat.ne_of_lt hlt).symm

end general

/-! ### 2. 生成元の像（M = N·t の形） -/

section gens

variable {N t : ℕ} [NeZero N] [NeZero t]

/-- π^*(π_* g) = t·P g（P は Part 202 の旧部分への射影 `oldP`）。 -/
theorem pull_fsum (g : ZMod (N * t) → ℂ) :
    pull (dvd_mul_right N t) (fsum (dvd_mul_right N t) g) = (t : ℂ) • oldP N t g := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  funext x
  rw [pull_apply, Pi.smul_apply, oldP, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ht, one_mul]
  have hre : (∑ y : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) y * g (x - y)) =
      ∑ z : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) (x - z) * g z :=
    (Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun z => by simp [Equiv.subLeft_apply])).symm
  simp only [PAG.Part15.conv]
  rw [hre, fsum, sum_filter]
  refine sum_congr rfl (fun z _ => ?_)
  have key : N ∣ (x - z).val ↔ ZMod.castHom (dvd_mul_right N t) (ZMod N) z =
      ZMod.castHom (dvd_mul_right N t) (ZMod N) x := by
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := dvd_mul_right N t),
      map_sub, sub_eq_zero, eq_comm]
  simp only [PAG.Part203.rk]
  by_cases hz : N ∣ (x - z).val
  · rw [ite_eq_left hz, ite_eq_left (key.mp hz), one_mul]
  · rw [ite_eq_right hz, ite_eq_right (fun e => hz (key.mpr e)), zero_mul]

/-- **2a.** φ(1) = P（`oldP`）。 -/
theorem cornerOp_one_apply (g : ZMod (N * t) → ℂ) :
    cornerOp (dvd_mul_right N t) 1 g = oldP N t g := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  rw [cornerOp_apply, Module.End.one_apply, pull_fsum, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

/-- P(E 側の殻 ts) は動かない：ε_{ts} ⋆ P g = ε_{ts} ⋆ g。 -/
theorem conv_geps_oldP (s : ℕ) (g : ZMod (N * t) → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) = PAG.Part15.conv (geps (N * t) (t * s)) g := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_oldP]
  by_cases htξ : t ∣ ξ.val
  · rw [ite_eq_left htξ]
  · rw [ite_eq_right htξ, dft_geps]
    have hd : dind (N * t) (t * s) ξ = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun h => htξ ((dvd_mul_right t s).trans
        (by rw [← h]; exact Nat.gcd_dvd_right (N * t) ξ.val)))]
    rw [hd, zero_mul, zero_mul]

/-- **2b.** φ(E_s) = E_{ts}。 -/
theorem cornerOp_geps_mul (s : ℕ) :
    cornerOp (dvd_mul_right N t) (PAG.Part15.convL (geps N s)) =
      PAG.Part15.convL (geps (N * t) (t * s)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply]
  show ((N : ℂ) / ((N * t : ℕ) : ℂ)) • pull (dvd_mul_right N t)
      (PAG.Part15.conv (geps N s) (fsum (dvd_mul_right N t) g)) = PAG.Part15.conv (geps (N * t) (t * s)) g
  rw [← geps_conv_pull, pull_fsum]
  have hcs : PAG.Part15.conv (geps (N * t) (t * s)) ((t : ℂ) • oldP N t g) =
      (t : ℂ) • PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) := by
    rw [PAG.Part15.conv_comm, conv_smul_left, PAG.Part15.conv_comm]
  rw [hcs, conv_geps_oldP, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

end gens

/-! ### 3. 生成元の像（一般の N ∣ M）と、A_N を A_M に送ること -/

section mem

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s。 -/
theorem cornerOp_one (h : N ∣ M) :
    cornerOp h 1 = ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  apply LinearMap.ext; intro g
  rw [cornerOp_one_apply, oldP_eq_sum, LinearMap.sum_apply]
  rfl

/-- **3a.** φ(E_s) = E_{(M/N)s}。 -/
theorem cornerOp_geps (h : N ∣ M) (s : ℕ) :
    cornerOp h (PAG.Part15.convL (geps N s)) = PAG.Part15.convL (geps M (M / N * s)) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  exact cornerOp_geps_mul s

omit [NeZero N] in
/-- π^*(1_{D_s}) = Σ_{t ∣ M, gcd(t, N) = s} 1_{D_t}。 -/
theorem pull_dind (h : N ∣ M) (s : ℕ) :
    pull h (dind N s) = ∑ u ∈ M.divisors.filter (fun u => Nat.gcd u N = s), dind M u := by
  funext y
  rw [pull_apply, Finset.sum_apply]
  simp only [dind]
  rw [sum_ite_eq]
  have hg : Nat.gcd N (ZMod.castHom h (ZMod N) y).val = Nat.gcd (Nat.gcd M y.val) N := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, Nat.gcd_comm N, ← Nat.gcd_rec,
      Nat.gcd_comm N, Nat.gcd_comm M, Nat.gcd_assoc, Nat.gcd_eq_right h]
  have hmem : Nat.gcd M y.val ∈ M.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne M⟩
  rw [hg]
  by_cases hs : Nat.gcd (Nat.gcd M y.val) N = s
  · rw [ite_eq_left hs, ite_eq_left (show Nat.gcd M y.val ∈ M.divisors.filter (fun u => Nat.gcd u N = s) from
      mem_filter.mpr ⟨hmem, hs⟩)]
  · rw [ite_eq_right hs, ite_eq_right (show Nat.gcd M y.val ∉ M.divisors.filter (fun u => Nat.gcd u N = s) from
      fun hm => hs (mem_filter.mp hm).2)]

omit [NeZero M] in
theorem mulLeft_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod M → ℂ) :
    LinearMap.mulLeft ℂ (∑ i ∈ s, f i) = ∑ i ∈ s, LinearMap.mulLeft ℂ (f i) := by
  apply LinearMap.ext; intro g
  rw [LinearMap.mulLeft_apply, LinearMap.sum_apply, Finset.sum_mul]
  rfl

omit [NeZero N] in
theorem mulLeft_pull_dind_mem (h : N ∣ M) (s : ℕ) :
    LinearMap.mulLeft ℂ (pull h (dind N s)) ∈ shellAlg M := by
  rw [pull_dind, mulLeft_sum]
  exact Subalgebra.sum_mem _ (fun u _ => mulLeft_dind_mem M u)

omit [NeZero N] in
/-- **3b.** φ(D_s) = (π^*1_{D_s})·φ(1)（D 側の像は殻の掛け算と φ(1) の積）。 -/
theorem cornerOp_dind (h : N ∣ M) (s : ℕ) :
    cornerOp h (LinearMap.mulLeft ℂ (dind N s)) =
      LinearMap.mulLeft ℂ (pull h (dind N s)) * cornerOp h 1 := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, Module.End.one_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem cornerOp_one_mem (h : N ∣ M) : cornerOp h 1 ∈ shellAlg M := by
  rw [cornerOp_one]
  exact Subalgebra.sum_mem _ (fun s _ => convL_geps_mem M s)

/-- **3c.** φ は A_N を A_M に送る（gcd(N, M/N) によらない）。 -/
theorem cornerOp_mem (h : N ∣ M) {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) :
    cornerOp h S ∈ shellAlg M := by
  unfold shellAlg at hS
  induction hS using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [cornerOp_geps]; exact convL_geps_mem M _
    · rw [cornerOp_dind]; exact Subalgebra.mul_mem _ (mulLeft_pull_dind_mem h s) (cornerOp_one_mem h)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, cornerOp_smul]
    exact Subalgebra.smul_mem _ (cornerOp_one_mem h) r
  | add x y _ _ hx hy => rw [cornerOp_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [cornerOp_mul]; exact Subalgebra.mul_mem _ hx hy

/-- **3d. 角の写像** A_N → A_M（単位元を保つとは限らない代数準同型、φ(S) = (N/M)·π^* ∘ S ∘ π_*。N < M では単位元を保たず（`cornerHom_one_ne_one`）、N = M では恒等（`cornerHom_self`））。 -/
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)

theorem cornerHom_coe (h : N ∣ M) (S : shellAlg N) :
    ((cornerHom h S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)) = cornerOp h S := rfl

end mem

/-! ### 4. 一意性と合成 -/

section uniq

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- **4a. 一意性**：引き戻しと両立し、φ(1) = Σ_{(M/N) ∣ s} E_s を満たす、単位元の保存を課さない代数準同型（`→ₙₐ`）は、ちょうど 1 つ（形式文は ∃!。それが φ = `cornerHom h` であることは証明の中で示す）。 -/
theorem existsUnique_corner (h : N ∣ M) :
    ∃! φ : shellAlg N →ₙₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (pull h f) = pull h ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (φ 1 : Module.End ℂ (ZMod M → ℂ)) =
        ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  refine ⟨cornerHom h, ⟨fun S f => cornerOp_pull h S f, ?_⟩, ?_⟩
  · rw [← cornerOp_one]; rfl
  · rintro ψ ⟨hpull, hone⟩
    apply NonUnitalAlgHom.ext; intro S
    apply Subtype.ext
    apply LinearMap.ext; intro g
    have e1 : ψ S = ψ S * ψ 1 := by rw [← map_mul, mul_one]
    rw [cornerHom_coe, e1, Subalgebra.coe_mul, Module.End.mul_apply, hone, ← cornerOp_one,
      cornerOp_apply, Module.End.one_apply, ← pull_smul, hpull, map_smul, pull_smul, cornerOp_apply]

omit [NeZero N] in
theorem fsum_trans {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (g : ZMod L → ℂ) :
    fsum (h1.trans h2) g = fsum h1 (fsum h2 g) := by
  funext x
  simp only [fsum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ZMod.castHom h2 (ZMod M))
    (t := univ.filter (fun y : ZMod M => ZMod.castHom h1 (ZMod N) y = x))]
  · refine sum_congr rfl (fun y hy => ?_)
    apply sum_congr _ (fun _ _ => rfl)
    ext z
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    constructor
    · rintro ⟨_, hz⟩; exact hz
    · intro hz
      refine ⟨?_, hz⟩
      rw [← ZMod.castHom_comp h1 h2, RingHom.comp_apply, hz, hy]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [← RingHom.comp_apply, ZMod.castHom_comp h1 h2, hz]

omit [NeZero N] in
/-- **4b. 合成**：φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem cornerOp_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h2 (cornerOp h1 S) = cornerOp (h1.trans h2) S := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, cornerOp_apply, cornerOp_apply, pull_smul, smul_smul, PAG.Part263.pull_pull h1 h2, fsum_trans h1 h2]
  congr 1
  field_simp

theorem cornerHom_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) :
    (cornerHom h2).comp (cornerHom h1) = cornerHom (h1.trans h2) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_comp h1 h2 S

/-- 恒等の法則の補助：N → N の繊維の和は恒等。 -/
theorem fsum_self (g : ZMod N → ℂ) : fsum (dvd_refl N) g = g := by
  funext x
  simp [fsum, Finset.sum_filter]

/-- **4e. 恒等の法則**：φ_{N,N} = id（引き戻しの恒等は Part 259 の `pull_self`）。 -/
theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, fsum_self, PAG.Part263.pull_self, div_self hN, one_smul]

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_self (S : Module.End ℂ (ZMod N → ℂ))

/-- **4c.** φ は単射。 -/
theorem cornerHom_injective (h : N ∣ M) : Function.Injective (cornerHom h) :=
  fun _ _ hST => Subtype.ext (cornerOp_injective h (congrArg Subtype.val hST))

/-- **4d.** N < M なら φ は単位元を保たない。 -/
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1 :=
  fun e => cornerOp_one_ne_one h hlt (congrArg Subtype.val e)

end uniq

/-! ### 5. D 側は殻の span に入らない（(N, M) = (2, 4) の証人） -/

/-- **5.** (N, M) = (2, 4)：φ(D_2) は D_t の線形結合でない（Part 258 の強い読みの D 側を満たさない）。 -/
theorem cornerOp_dind_not_mem_span :
    cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) ∉
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind 4 u)) := by
  intro hmem
  obtain ⟨m, hm⟩ := PAG.Part262.exists_mulLeft_of_mem_span 4 hmem
  have e : cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) (Pi.single 0 1) 2 = 0 := by
    rw [hm, LinearMap.mulLeft_apply, Pi.mul_apply, Pi.single_eq_of_ne (by decide), mul_zero]
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, LinearMap.mulLeft_apply, Pi.mul_apply, fsum_single] at e
  have hc : ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (2 : ZMod 4) = 0 := by
    rw [map_ofNat]; rfl
  rw [hc, map_zero, ite_eq_left rfl] at e
  simp [dind] at e


end PAG.Part264

#print axioms PAG.Part264.fsum_add
#print axioms PAG.Part264.fsum_smul
#print axioms PAG.Part264.card_fiber
#print axioms PAG.Part264.fsum_pull
#print axioms PAG.Part264.cornerOp_apply
#print axioms PAG.Part264.scal_cancel
#print axioms PAG.Part264.cornerOp_pull
#print axioms PAG.Part264.cornerOp_mul
#print axioms PAG.Part264.cornerOp_add
#print axioms PAG.Part264.cornerOp_smul
#print axioms PAG.Part264.cornerOp_zero
#print axioms PAG.Part264.cornerOp_one_mul
#print axioms PAG.Part264.cornerOp_mul_one
#print axioms PAG.Part264.cornerOp_injective
#print axioms PAG.Part264.fsum_single
#print axioms PAG.Part264.cornerOp_one_single
#print axioms PAG.Part264.cornerOp_one_ne_one
#print axioms PAG.Part264.pull_fsum
#print axioms PAG.Part264.cornerOp_one_apply
#print axioms PAG.Part264.conv_geps_oldP
#print axioms PAG.Part264.cornerOp_geps_mul
#print axioms PAG.Part264.cornerOp_one
#print axioms PAG.Part264.cornerOp_geps
#print axioms PAG.Part264.pull_dind
#print axioms PAG.Part264.mulLeft_sum
#print axioms PAG.Part264.mulLeft_pull_dind_mem
#print axioms PAG.Part264.cornerOp_dind
#print axioms PAG.Part264.cornerOp_one_mem
#print axioms PAG.Part264.cornerOp_mem
#print axioms PAG.Part264.cornerHom_coe
#print axioms PAG.Part264.existsUnique_corner
#print axioms PAG.Part264.fsum_trans
#print axioms PAG.Part264.cornerOp_comp
#print axioms PAG.Part264.cornerHom_comp
#print axioms PAG.Part264.fsum_self
#print axioms PAG.Part264.cornerOp_self
#print axioms PAG.Part264.cornerHom_self
#print axioms PAG.Part264.cornerHom_injective
#print axioms PAG.Part264.cornerHom_one_ne_one
#print axioms PAG.Part264.cornerOp_dind_not_mem_span
```


### §L3-4 現在のノート `notes/pag2_pag264_corner_maps.md`（全文）

```markdown
# アーデル射影幾何 — Part 260（PAG264）：角の写像 A_N → A_M（短期層の小さいノート、2026-11-19）

（新しいパートではない。方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §4）を、2026-11-19 09:37 に著者が採用した。基礎文書の第 5 章（索引 5.2 の留保）と第 6 章 6.3 の材料。
Lean は PAG264.lean：定理 40（午後に恒等の法則の 3 つを足した。§9）、定義 5、sorry 0、警告 0。#print axioms 40 行はすべて標準の公理の範囲。数値は `records/gamma_corner/`、照合の記録は `records/audit264/`。）

## §1 結果（Lean の文から起こした）

記号：
- N, M ≥ 1 で N ∣ M。π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。Terwilliger 代数 T(0) とは辞書による同一視で、Lean の定理ではない。
- D^{(N)}_s・E^{(N)}_s は水準 N の殻の掛け算と双対殻への射影。
- π^* は引き戻し（Part 197（PAG201）の `pull`）、π_* は繊維の和（`fsum`）。

主な文：
- **写像**：φ(S) = (N/M)·π^* ∘ S ∘ π_*（`cornerOp`）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であることは Lean の外。
- **A_N を A_M に送る**（`cornerOp_mem`）。
  - gcd(N, M/N) は仮定にないので、素数冪の段 (2,4)・(3,9) なども含む。
  - 単位元を保つとは限らない代数準同型 `cornerHom : A_N →ₙₐ A_M`（型は単位元の保存を課さない。N < M では保たず、N = M では恒等）としてまとめた（2026-11-19 夕方の索引の再照合の指摘で、「非単位的な」をこの言い方に揃えた。Lean の docstring も同じ）。
- **生成元の像**：
  - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
  - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。M = N·t と書いたとき、Part 202（PAG206）の `oldP N t` に等しい（`cornerOp_one_apply`）。
  - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。ここで π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
- **引き戻しと両立**：φ(S)π^* = π^* S（`cornerOp_pull`）。
- **像は φ(1) の角に入る**（⊆。`cornerOp_one_mul`・`cornerOp_mul_one` と `cornerOp_mem` から直ちに出る。単独の宣言はない）。
- **単射**（`cornerOp_injective`・`cornerHom_injective`）。
- **非単位的**：N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`・`cornerHom_one_ne_one`）。N = M では恒等の法則（下）から φ(1) = 1 なので、N ∣ M のもとで φ(1) ≠ 1 ⟺ N < M（直ちに出る。単独の宣言はない）。
- **一意性**：次の (a)(b) を満たす、単位元の保存を課さない代数準同型 A_N → A_M は、`→ₙₐ` の中でちょうど 1 つ（`existsUnique_corner`）。
  - (a) すべての S ∈ A_N と f で φ(S)(π^* f) = π^*(S f)（引き戻しと両立）。
  - (b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - 証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論。
  - 「引き戻しとの両立だけで決まる」という文ではない。独立照合の手計算の反例（Lean にしていない）：
    - (b) を外すと一意でない。(1,2) では φ'(c) = c·1 も (a) を満たす。
    - (a) を外しても、積を保つことを外しても一意でない（どちらも (2,4) の例。(1,2) では A_1 = ℂ なので (b) だけで決まる）。
- **合成**：N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。
  - 恒等の法則 φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。N → N の繊維の和は恒等 `fsum_self`、引き戻しの恒等は Part 259（PAG263）の `pull_self`）。2026-11-19 午後に追加（§9）。
  - 合成と恒等の 2 法則が揃い、(A_N, φ_{N,M}) は正の整数の整除の順序の上で帰納系の法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean の外。
- **D 側の証人**：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
  - Part 258（PAG262）の殻を混ぜない条件（強い読み：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）の D 側を満たさない。E 側は `cornerOp_geps` から満たす（直ちに出る）。
  - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は D^{(M)}_u（u ∈ ℕ）の span に入らない。
    - 数値：M ≤ 30 の N < M の 81 組。
    - 手計算：(1,2)・(2,6)、独立照合。
    - Lean にあるのは (2,4)、s = 2 だけ。

## §2 ラベル

- **［既知］**：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5。どちらも盲検が挙げたもの）の作用素版。
  - 関数のレベルは Part 202（PAG206）（`geps_conv_pull`、`oldP_eq_sum`）。
- **［再導出（小さい）］**：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - どれも初等的な議論。
  - 盲検の問いテスト（2026-11-19）で見つからなかったもの（確信度：低〜中）：T(0) 版（部分スキーム・商スキームの T(0) が角として現れること）、整除の順序全体の帰納系、Bost–Connes と T(0) を結ぶ文献。
  - 検索語：Terwilliger algebra quotient scheme closed subset subscheme、triply regular、Terwilliger algebra Bost-Connes、inductive limit Terwilliger algebras ほか 17 本（`records/gamma_corner/outputs/blind_output.md`）。
  - 検索先はウェブだけ。MathSciNet・zbMATH は未実施（著者側）。「見つからなかった」は不存在の証明ではない。
- **新規候補はない**。対照群は ℤ/p^e の段に当たる場合（F_p[t]/(t^e) → F_p[t]/(t^{e'})、関数体そのものではない）に限って同じ文が成り立つ（数値）。互いに素な段は試していない。盲検の手計算では、使うのは平行移動スキームの形式（商とフーリエ双対）だけ。ℚ に固有の算術の内容は、試した範囲では見つかっていない。

## §3 範囲（Lean にしていないもの）

- **像が角全体であること**（φ(1) A_M φ(1) ⊆ φ(A_N) の側。逆の包含は §1）。
  - 数値：M ≤ 30 で N ∣ M の 111/111 組（N = M の 30 組は `cornerHom_self` から直ちに出る。自明でないのは N < M の 81 組）。
  - 手計算：構築側と盲検の手計算が一致。三重正則性（Bhattacharyya–Song–Tanaka 2010、Munemasa 1993 の Lemma 4）からの短い帰結の見込み。
  - 鎖には三重正則性がない。
- **帰納系の `DirectedSystem` としての束ねと、整除の順序全体の極限 A_∞**。
  - A_∞ は有限次元の代数の和集合で、Ẑ 上の局所定数関数に作用する。
  - 完備化（L²(Ẑ)、C* 完備化）は解像度が落ちる側の操作と読み、目標として書かない（§1 の 08:41 の定義）。
- **Bost–Connes の ρ との対応**：群環の側で φ = ρ_{M/N}（数値）。L²(Ẑ) の表現では T(0) の片側だけが BC に対応する（盲検の手計算）。
- **随伴を保つこと** φ(S^*) = φ(S)^*（独立照合の照合者による、行列の形からの手計算）。
- **対照群** F_p[t]/(t^e) → F_p[t]/(t^{e'})：同じ文が成り立つ（数値）。これは関数体そのものではなく有限な剰余環で、ℤ/p^e の段に当たる場合だけを試した。

## §4 数値照合

- `records/gamma_corner/corner_check.py`：M ≤ 30 の 111 組と鎖 276 本。
- `psi_corner.py`（0 拡張の側）、`triple_check.py`（三重正則性）、`control_fqt.py`（対照群）。
- `lean_stmt_check.py`：Lean の各文（fsum_pull、pull_dind、cornerOp_dind、cornerOp_one_single、cornerOp_one）を 111 組で確かめた。
  - 1 回目は全組が不一致と出た。原因は照合スクリプトの誤りで、引き戻した関数（ベクトル）と行列の対角を取り違えて比べていた（第 7 の型）。
  - 直した 2 回目は 111/111 組で合った。
- 111 組は N ≠ M/N の組（(1,2)、(2,6)、(3,12) など）を含む。添字 N と M/N の取り違えは、(2,4) だけでは検出できない（独立照合の指摘 (a)）。

## §5 内部照合（第 12 の型）

- **着手前**（言葉の検索）：商に沿った非単位的な写像 A_N → A_M の宣言は、鎖になかった（網羅ではない）。
  - Part 202（PAG206）の `oldP` 系を使った：Q = P、Σ E_t への分解 `oldP_eq_sum`、`geps_conv_pull`。
  - 同じ構成は、Part 258 の着手前の盲検の補足（問いの外）に 1 か所あるだけだった。
- **閉じる前**（機械的）：全宣言 4470 件。PAG264 の対象 46 件（定理 41（自動生成の congr_simp を含む）＋定義 5）、候補上位 20、計 41·20·2 + 5·20 = 1740 回。
  - 一致と出たのは `cornerOp_apply` と Part 197（PAG201）の `pull_smul` の 1 組だけ。どちらも定義を展開すると等しくなる式で、中身の重複ではない。
  - 候補の上位を言葉で確かめて、下書きの 2 つを消した。
    - `pull_trans` は Part 259（PAG263）の `pull_pull` と向きが逆の同じ文（A）。
    - `apply_single_two_of_mem_span` は Part 258（PAG262）の `exists_mulLeft_of_mem_span` から直ちに出る（B）。
  - 単射の証明は Part 259（PAG263）の `pull_injective'` を使う形に直した。
  - 2 回目（4468 件、対象 44 件 = 定理 39 ＋定義 5、1660 回）：定義の展開の 1 組だけ。
  - 3 回目（午後、恒等の法則の 3 つ。全宣言 4471 件、3·20·2 = 120 回）：一致なし。
- 「見つからなかった」は「重複はない」ではない（候補は上位 20 件、言葉の検索も一部）。

## §6 独立照合（第 11 の型）

- **条件**：新しいエージェントに、形式文（docstring・コメントを除いた）と使う定義だけを渡した（Read 1 回、約 462 秒）。依頼文は `records/audit264/request_formal.md`（定型）、出力の全文は `records/audit264/outputs/check_output.md`。
  - 照合者の申告：プロジェクトの CLAUDE.md とユーザーのメモリが、システムによって最初から文脈に入っていた（PAG264 の散文は含まない）。独立性の留保として記録する。
- **結果**：
  - 偽・空虚な形式文はなかった。すべての定理で仮定を満たす具体例が示された。
  - (2,4) では A_2 = End(V_2)、A_4 ≠ End(V_4) なので、`cornerOp_mem` は中身のある主張になる。
- **除去テスト**（照合者の手計算）：
  - `existsUnique_corner` の (ii)・(i)・積を保つことは、どれも外すと一意でなくなる（反例あり）。
  - `cornerOp_mem` の S ∈ A_N を外すと偽になる（N = M = 3）。
  - `cornerOp_one_ne_one` の N < M は必要。
- **直したこと**（主張を変えない文面の直し。§1 と PAG264 の冒頭の説明）：
  1. 一意性は「引き戻しとの両立だけで決まる」文ではないと明記し、反例を添えた。
  2. D 側の現象は互いに素な段でも起きると明記した（指摘 (b)）。
  3. 数値照合が N ≠ M/N の組を含むことを §4 に書いた（指摘 (a)）。
  4. 主張していないこととして「像 = 角全体」と「随伴を保つこと」を範囲に挙げた（指摘 (d)）。
- 直した文面は、閉じる前の再照合を受けた（§8）。

## §7 収束アラームの報告

- 兆候 4（初等的な部品の組み合わせだけ）：続いている。文書の章に仕える短期層として位置づける（推薦案どおり）。
- 兆候 1（自前の名前）：名前は文献の言葉（角、corner）に寄せた。
- 辞書への記入（案）：「角の写像 `cornerHom`」↔ 商スキームのべき等元による角（Bose–Mesner 版は Zieschang 2005、Kodalen 2019 §2.5）。
- 文献照合：盲検の問いテスト（2026-11-19）を実施した。未実施の連続はない。

## §8 直した文面の再照合

- **条件**：新しいエージェントに、冒頭の説明とこのノートの §1〜§3、形式文と定義を渡した（Read 1 回、約 251 秒）。出力は `records/audit264/outputs/recheck_output.md`。
- **結果**：宣言名の取り違えと、形式文にあるのに Lean の外と書いたものは、なかった。
- **散文が形式文より強い・あいまいな箇所（7 点）を直した**：
  1. 「単位元を保たない代数準同型」を「非単位的な代数準同型（型は単位元の保存を課さない）。N < M なら φ(1) ≠ 1」にした。
  2. 「したがって帰納系をなす」を外した。恒等の法則 φ_{N,N} = id は Lean の外と書いた（午後に恒等の法則を Lean に入れたので置き換えた。§9）。
  3. `cornerOp_one_apply` が M = N·t の形の文であることを書いた。
  4. D 側の一般化を「N ∣ M、N < M、すべての s ∣ N」と量化し、根拠（数値 81 組と手計算）を揃えた。
  5. 三重正則性からの帰結を「見込み」に揃えた。
  6. ι S ι^† は読みで、随伴の同定は Lean の外と書いた。
  7. 一意性の条件を (a)(b) と書き、Part 258 の (ii) と区別した。
- **ほかに直したこと**：
  - Σ の添字に s ∣ M を書き、水準を E^{(N)}・E^{(M)} と明示した。
  - 件数の内訳を書いた（46 件 = 定理 41（自動生成の congr_simp を含む）＋定義 5、1740 = 41·20·2 + 5·20）。
  - 対照群の範囲を ℤ/p^e の段に当たる場合に狭めた。
  - PAG 番号を併記した。
  - 像が角に入る側（⊆）は Lean の文から直ちに出ると書き分けた。
- **再照合の後のこの直し**：主張を狭めるか明確にするもの。午後の統合照合（§9）で照らした。

## §9 恒等の法則の追加と統合照合（2026-11-19 午後）

- **足したもの**：`fsum_self`（N → N の繊維の和は恒等）、`cornerOp_self`（φ_{N,N} = id、End(ℂ^{ℤ/N}) 全体で）、`cornerHom_self`（cornerHom(dvd_refl N) = 恒等の非単位的な代数準同型）。
  - 数値：N = 1〜30 のランダムな S（`records/gamma_corner/identity_check.log`）。
  - 内部照合：引き戻しの側の恒等は Part 259（PAG263）の `pull_self` を使った。繊維の和の側は鎖になかった。機械的な照合（3 件、120 回）でも一致はなかった。
- **統合照合**：足した 3 つの定理と、§8 の再照合の後の文面の直し（尾）を、1 回の統合照合で照らした。
  - 条件：新しいエージェントに、形式文の全文・使う定義・散文（冒頭の説明、§1〜§3、§8）を渡した（Read 1 回、約 440 秒）。出力は `records/audit264/outputs/integrated_output.md`。
  - 足した 3 定理：意図どおり。除去テストでは、cornerOp_self は正規化の係数を試していない（N = M では係数が 1）。正規化を確かめているのは `cornerOp_pull`・`cornerOp_mul`・`cornerOp_comp` の方。
  - 宣言名・記号の取り違えはなかった。
  - 散文のずれ 11 点を直した（冒頭の説明と §1〜§3）：
    1. N = M の文：恒等の法則で誤りになった「Lean の文は何も言っていない」を直した。
    2. 件数：定理 40。3 回目の機械的照合も書いた。
    3. 再照合の直し (2) を置き換えたことの注記。
    4. 対照群の結論を、試した範囲（ℤ/p^e の段）に狭めた。
    5. 一意性の反例の組（(a)・積の反例は (2,4)）。
    6. span の対象。
    7. 正の整数の整除の順序。
    8. (a) の S は A_N の元。
    9. ⊆ に単独の宣言がないこと。
    10. 7 点の列挙を再照合の指摘どおりに直した。
    11. 随伴の根拠をそろえた。
  - 統合照合の後のこの直しは、主張を狭めるか明確にするもの（強める直しはない）と申告し、補足8の停止の規約の範囲として尾の台帳は空とした。2026-11-19 19:58 の著者の規則（自己申告では閉じない）に照らして、台帳 `pag2_tail_ledger.md` の L3 に戻した（未照合）。
- ラベルと兆候（補足 15 の条件 6、2026-11-19 夜に書き足した）：恒等の法則の 3 定理は［再導出（小さい）］で、新規候補にはしない。兆候 4（初等的な部品の組み合わせだけ）は続いている。

## §10 恒等の法則の 3 定理の独立照合（2026-11-19 夜）

- 経緯：§9 の 3 定理（`fsum_self`・`cornerOp_self`・`cornerHom_self`）は、散文と同じ入力の統合照合 1 回だけを受けていた。形式文と定義だけを渡す独立照合（第 11 の型の定型）は受けていなかった。著者の確認（2026-11-19 19:14）を受けて、3 定理だけを形式文と定義だけで照らした（記録 `records/audit264_identity/`、依頼文 `request.md`、入力 `input_formal.md`、出力 `outputs/identity_output.md`、約 158 秒）。
- 結果：
  - 逆翻訳は意図どおり（N → N の繊維の和は恒等、φ_{N,N} は End 全体で恒等、cornerHom(N ∣ N) は shellAlg N の恒等）。
  - 非空虚性の証人はある（N = 2, 3 の具体例）。3 文とも定義からすぐ出る自明な文。
  - 除去テスト：NeZero N を外すと文が型として書けない（反例の作りようがない）。N ∣ M に替えた類似の文（fsum ∘ pull = 恒等、pull ∘ fsum = 恒等、φ(1) = 1）は、N = 1、M = 2 で偽。恒等になるのは N = M に特有。
  - 照合者の注意：恒等の法則は正規化の因子 N/M の値（c(N, N) = 1 となる因子ならどれでも成り立つ）や pull・fsum の向きを確かめない。因子を決めるのは乗法性（`cornerOp_mul`、§6 の独立照合の範囲）。節の名前 uniq と中身が合っていない（体裁）。
- 独立性の留保：照合者は、プロジェクトの CLAUDE.md がシステムによって文脈に入っていたことを申告した（これまでの照合と同じ）。
- 形式文・散文の直しはない。
```


## §L4 台帳 L4

```markdown
### L4：Part 261（PAG265）の再照合の後の直し（2026-11-19 午後、コミット 6ba1a54 まで）

- 範囲：3 回目の再照合（`records/audit265/outputs/recheck_output.md`）の指摘 11 点を受けた直し（PAG265 の冒頭の説明・docstring、ノート `pag2_pag265_corner_limit.md`）。
- 経緯：L3 と同じ。
- 扱い：次の統合照合の対象。
```


### §L4-1 Part 261 の再照合（3 回目の照合）の出力（`records/audit265/outputs/recheck_output.md`、全文）と、その入力にあった前の指摘

# 再照合（PAG265 の 3 回目の照合：足した 3 定理と直した文面）。通知の本文を写したもの

（条件：Read 3 回。input_formal.md（全 151 行）、input_prose.md（全 78 行）、input_prev_findings.md（全 19 行）。約 414 秒。CLAUDE.md はシステムが文脈に入れたもので、「出所：入力外」と書いた箇所でだけ参照。）

**総括**：宣言名の取り違えはない。指摘 1〜10 は散文に反映されているが、指摘 3 の直しが新しいずれを生んでいる（2-1）。

## 1. 3 定理

**1-1 ofCorner_one_mul_self**
- 逆翻訳：どの正の整数 a でも、A_a の単位元を極限に送った像 e_a = ι_a(1) はべき等（e_a e_a = e_a）。
- 非空虚性の証人：仮定は a だけで、a = ⟨1, _⟩ で成り立つ。e_a ≠ 0 も言える（A_a は End(ℂ^{ℤ/a}) の部分代数で a ≥ 1 なので 1 ≠ 0、これと ofCorner_injective）。c と 2c の e も異なる（e_c ≠ e_{2c}。ofCorner_cornerSys から e_c = ι_{2c}(φ_{c,2c}(1))、cornerHom_one_ne_one と ofCorner_injective）。どちらも A と B の文だけから出る手計算（確信度：高）。
- 除去テスト：外せる仮定はない。定数 1 を一般の S に替えると偽（S = 2·1 なら ι_a(2)² = ι_a(4) ≠ ι_a(2)）。
- 依存：ofCorner の乗法性（map_mul）と A_a の one_mul だけ。単射性、φ(1) ≠ 1、添字の有向性、cornerOp の具体形は使わない。Mathlib の IsIdempotentElem.one と .map から直ちに出る（B）見込み（名前は記憶、確信度：中）。

**1-2 ofCorner_one_le**
- 逆翻訳：a ∣ b なら、べき等元の順序で e_a は e_b の下にある（e_b e_a = e_a かつ e_a e_b = e_a）。
- 非空虚性の証人：a = 1, b = 2。e_1 ≠ e_2（1-1 と同じ議論）なので自明な場合ではない。a = b なら 1-1 に帰着。
- 除去テスト：h を外すと偽（a = 2, b = 1 で e_1 e_2 = ι_2(φ_{1,2}(1)·1) = e_1 ≠ e_2、e_2 e_1 = e_1 ≠ e_2 で、両方の連言が成り立たない）。向きを逆にした文（a < b, a ∣ b のとき e_a e_b = e_b）も偽。
- 依存：ofCorner_cornerSys、乗法性、A_b の単位元。φ の具体形と単射性は使わず、直極限の一般論で自動的に成り立つ。

**1-3 exists_local_unit_finset**
- 逆翻訳：極限の任意の有限部分集合 F に対して、ある a があり、e_a は F のどの元も左右両側から固定する。べき等性はこの文に入っていない（別の定理）。
- 非空虚性の証人：F = ∅ では a = 1 で空虚に真。F = {ι_2(S), ι_3(T)} には a = 6 が効く。F = {e_2, e_4} では a = 2 は使えず（e_2 e_4 = e_2 ≠ e_4）、a = 4 なら成り立つ。共通の a が各元の水準より上に要ることを、入力の文だけで確かめられる。
- 除去テスト：有限性を外すと偽（F = 極限全体なら e_a が左単位元になり not_exists_left_one に反する。可算集合 {e_n} でもすでに偽で、どの c でも e_c e_{2c} = e_c ≠ e_{2c}）。有向性は帰納の段で上界 c を取るのに使うが、Mathlib の DirectLimit は有向性を前提にしているので形式文からは外せない。ofCorner_one_le は別の仮定ではなく自動的に成り立つ性質なので、外した文は作れない。
- 使っているもの：exists_local_unit（その中で DirectLimit.exists_eq_mk、乗法性、A_a の単位元）、IsDirectedOrder Lvl（上界は積 a·b）、ofCorner_one_le（その中で ofCorner_cornerSys）、極限の積の結合律（Mathlib の NonUnitalRing インスタンス）、Finset.induction_on と classical（CornerLim の DecidableEq）、空集合の場合のレベル 1。
- 使っていないもの：単射性（ofCorner_injective・cornerHom_injective）、cornerOp_one_ne_one・cornerHom_one_ne_one・cornerOp_one_mul、ofCorner_one_mul_self、pull・fsum・正規化の具体形、shellAlg の生成元。
- 正規化が効くのは「φ が乗法的なので極限に積がある」という一点だけ。
- 読み：有向な添字の上で、単位的な環を乗法的な写像でつないだ直極限なら、どれでも成り立つ一般の事実。遷移写像が単位的でも成り立つ（そのとき極限は単位的）。したがって「非単位的」という内容を運ぶのは not_exists_left_one だけで、局所的な単位元の 3 定理は運ばない。exists_local_unit は F = {x} の場合にあたる（同じファイル内の B の関係。補題として使われているので問題ではない）。

## 2. 散文と形式文の突き合わせ

一致している点：A の 14 宣言（定義 3、インスタンス 1、定理 10）はすべて正しい名前と Part/PAG 番号で散文に出ている。11〜13、16〜20、23〜31、35、37 行目は形式文と同じ範囲。「範囲」の項目に A にあるものは含まれず、A にあるのに外と書かれたものもない。

ずれ（行番号は input_prose.md）：
- **2-1（中〜低）42 行目**「素数冪の段にも…よらない。効いているのは、どの狭義の段 c → 2c でも φ(1) ≠ 1 であることと単射性。無平方数の段だけの部分系でも同じ証明が通る見込み」：(i) Lean の証明は d = 2c を使う。c が偶数ならこの段は 2 の指数を上げる素数冪の段で、「よらない」は Lean の証明の性質ではなく別の段の取り方による手の議論。(ii) 無平方数の部分系では c が偶数のとき 2c が部分系に入らないので、「同じ証明」はそのままでは通らない。部分系の上界も積ではなく lcm。(iii) 「どの狭義の段でも φ(1) ≠ 1」（cornerOp_one_ne_one）という一般の事実と、証明で選んだ段 c → 2c が一つの文に混ざっている。前回の指摘 3 の文言そのものの不正確さを引き継いだもの。直し方：「Lean の証明は d = 2c をとり、ofCorner_injective と cornerOp_one_ne_one（N ∣ M, N < M のどの段でも成り立ち、gcd によらない）を使う。d を c の倍数で c より大きいレベル（例：c を割らない素数 p で d = pc）に替えても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。無平方数の部分系（上界は lcm）でもこの取り方で通る見込み（Lean にしていない）」。確信度：中〜高。
- **2-2（低）36 行目**「d = 2c で φ_{c,d}(U) = 1 となる」は単射性の段が抜けている。直し方：「u e_d = e_d と ofCorner_cornerSys から ι_d(φ_{c,d}(U)) = ι_d(1)、ofCorner_injective により φ_{c,d}(U) = 1」。
- **2-3（低）41 行目**「正規化 N/M が効くのは、乗法性（局所的な単位元と、単位元がないこと）の側」：括弧のせいで、正規化がこの 2 つの結果を直接運んでいるように読める。実際に効くのは φ の乗法性（正規化なしでは φ'(S)φ'(T) = (M/N)φ'(ST)、手計算）。2 つの結果は乗法性から得られる積の構造の上の文で、φ(1) ≠ 1 自体は正規化によらない（階数 N < M、手計算）。直し方：「正規化が効くのは φ の乗法性、したがって極限に積の構造があること」。
- **2-4（低）32〜33 行目**「べき等元 e_a が…固定する。したがって F ⊆ e_a·極限·e_a」：べき等性は別の定理。包含は Lean の文ではない（x = e_a x e_a から 1 行）。直し方：「（べき等性は ofCorner_one_mul_self）。包含は x = e_a x e_a から直ちに出る（Lean の文ではない）」を添える。
- **2-5（低、照合者の記憶、確信度：低〜中）34 行目**：Ánh–Márki と Abrams を同じ定義として並べている。照合者の記憶では Abrams の流儀は「可換な冪等元の集合 E」を求める。Lean が与える可換性は比較可能な a, b の間だけ。鎖 {e_{n!}} を E にとれば ofCorner_one_le と 1-3 の議論から出るが Lean の外。直し方：同じ定義と書かずに流儀の違いを注記するか、文献照合のときに確かめる。
- **2-6（低、確認できない）4 行目（題）と 49 行目「非単位的な代数」**：A と B から読めるのは NonUnitalRing、ℂ の Module、ofCorner が →ₙₐ[ℂ] であることまで。積とスカラー倍の両立（IsScalarTower・SMulCommClass）は入力にない（数学的には直ちに出る）。18 行目の書き方（「非単位的な環の構造と ℂ のスカラー倍」）は正確。直し方：Mathlib のインスタンス名を書くか、「両立は手計算」と添える。
- **2-7（低、出所：入力外）46 行目**「…があるのは、N ∣ M で gcd = 1 のときに限る」：CLAUDE.md の要約では N ∣ M は仮定で結論は同値。散文は必要性だけを言い、N ∣ M を結論の側に入れている。直し方：「N ∣ M のとき、…があるのは gcd(N, M/N) = 1 のとき、そのときに限る」。
- **2-8（低、出所：入力外）48 行目**「D 側は殻の span に入らない」の量化（すべての s か、ある s か）がない。直し方：Part 260 の形式文に合わせて量化を書く。参考（手計算、確信度：中〜高）：N < M なら D_s ≠ 0 である s について φ(D_s) は π の同じ繊維の中に 0 でない非対角成分を持つ。D_t たちの span は対角なので、一般の場合の「数値」は短い手の議論で置き換えられる見込み。
- **2-9（低）71〜74 行目**：「·2」が何の 2 倍か書かれていない。DirectedSystem インスタンスは数に入っていない（外すなら「インスタンスは対象外」と書く）。足した 3 定理の機械的な照合の結果が散文になく記録への参照だけ。Mathlib の名前の検索に IsIdempotentElem を入れることを勧める（1-1）。
- **2-10（低、手続き）75 行目**：この照合が終わったら「独立照合は 2 回」を更新する。
- **2-11（ごく低、任意）40 行目**：End 全体で成り立つことは Lean の文そのもの（B の cornerOp_self・cornerOp_comp は End 全体の S についての文）。手計算なのは「正規化なし」の部分だけで、括弧がどちらにかかるかが曖昧。

確認できないもの：46 行目 exists_compatible_hom_iff、47 行目 not_isDirected_udvd、64 行目 Lim・ofL_injective、65 行目 sqLim・sqLim_of_injective、66 行目「どちらも Module.DirectLimit」、71 行目の 4483 件。47 行目「2 と 4 に共通の上界がない」は手計算で再確認（v_2(c) = 1 と v_2(c) = 2 が両立しない）。

## 3. 前回の指摘 1〜10 の反映

| 指摘 | 反映 | 残り・新しいずれ |
|---|---|---|
| 1 | 反映（(a) の道で 3 定理を追加。31〜34、49、58 行目） | 2-4、2-5 |
| 2 | 反映（48 行目） | 2-8（量化） |
| 3 | 反映（42 行目） | 直しが新しいずれ 2-1 を生んだ |
| 4 | 反映（17〜18 行目） | なし |
| 5 | 反映（320 + 60 = 380 で算術は合う） | 2-9 |
| 6 | 反映（40 行目） | 2-11（任意） |
| 7 | 反映（48 行目） | なし |
| 8 | 反映（53 行目） | なし |
| 9 | 65 行目は「別の添字」に直り、「同じ型」の問題は解消 | 宣言自体は今回も確認できない |
| 10 | 入力 1 で修正済み（B の 133〜134 行目が PAG264 の欄に入った） | 雛形に別の問題が 2 つ（下記） |

雛形の残りの問題：B の 140 行目の DirectLimit F f は、137 行目の DirectedSystem と f の束縛の書き方が揃っておらず、A の使い方（a, b を明示した cornerSys）とも揃っていない（照合者の記憶では Mathlib の DirectLimit は f に明示的な i j と FunLike の値をとる。確信度：低〜中。コンパイルが通っているので内容には影響しない）。IsScalarTower などのインスタンスが B にない（2-6）。

## 4. 「なし」の項目
宣言名の取り違え：なし。範囲の内外の誤り：なし。2-1〜2-11 のほかのずれ：照合した範囲ではなし。


#### 前の指摘（`records/audit265/input_prev_findings.md`）

# 入力 3：前回の照合の指摘（成果物 4）

## 成果物 4：散文と形式文のずれ

問題のなかった点：A の 11 宣言はすべて正しい名前で散文に出ている。28 行目（局所的な単位元）と 29 行目（左単位元がない）は形式文と同じ範囲で、30〜31 行目の証明の筋も A と一致。「範囲（Lean にしていないもの）」の 3 項目は確かに A にない。A にあるのに外と書かれたものもない。Part と PAG の番号の対応（254 = 258、260 = 264、261 = 265）は合っている。

指摘：
1. （中）「局所単位元をもつ環」は A より強い文。49 行目「局所的な単位元を持つ非単位的な環（rings with local units）は標準の概念」、40 行目「極限は局所的な単位元を持つ非単位的な代数になる」。標準の定義（Ánh–Márki、Abrams）は、有限集合ごとに冪等元 e があって F ⊆ eRe となることを要求する。A にあるのは 1 元ごとの両側単位元だけで、冪等性も有限集合への共通化もない（1 元ごとの形はむしろ Tominaga の s-unital に近い。定義の確信度は中、記憶によるもので文献は照合していない）。直し方：(a) Lean に `ofCorner a 1 * ofCorner a 1 = ofCorner a 1` と a ∣ b のときの `ofCorner a 1 * ofCorner b 1 = ofCorner a 1`（両側）を足す、または (b) 文面を「各元を両側から固定する e_a = ι_a(1) がある（冪等性・有限集合への共通化は Lean の外、直ちに出る見込み）」に直す。
2. （中、出所：入力外）40 行目「D 側で殻の span に入らない角の写像（Part 260）」は、37 行目で「前の Part の Lean の文との並置」と位置づけているが、入力 1 にこの文はない。CLAUDE.md の要約では Part 260 で Lean にあるのは (2,4) の証人だけで、一般の場合は数値のみ。直し方：「D 側で殻の span に入らない（(2,4) は Lean、一般には数値。Part 260）」。
3. （低〜中）38〜40 行目の対比の並べ方は、素数冪の段が極限が非単位的になる原因のように読める。成果物 3 のとおり not_exists_left_one は狭義の段 c → 2c と φ(1) ≠ 1 だけで出て、無平方数の部分系でも同じ証明が通る。直し方：「単位元がないことは素数冪の段によらない（cornerOp がどの狭義の段でも非単位的であることによる。部分系での文は Lean にしていない）」を 1 行足す。
4. （低）17 行目「`DirectLimit`（Mathlib/Algebra/Colimit/DirectLimit.lean）による帰納極限」：入力 1 の B では、型の定義は Mathlib/Order/DirectedInverseSystem.lean、環・代数の構造が Algebra/Colimit 側。直し方：「Order/DirectedInverseSystem.lean の `DirectLimit`（非単位的な環・代数の構造は Algebra/Colimit/DirectLimit.lean）」。
5. （低）62 行目「対象 11 件、候補上位 20、380 回」：11 × 20 = 220 で、380 は 19 × 20。内訳を書く。
6. （低）34 行目「正規化なしでも成り立ち」：手計算では確かめられるが、Lean の文は正規化つきの cornerOp についてのもの。「（手計算。Lean の文は正規化つき）」を添える。
7. （低）40 行目「単位元を保たず」：φ_{a,a} = id は単位元を保つ。cornerHom_one_ne_one の仮定は N < M。「N < M の段で単位元を保たず」。
8. （低、出所：入力外）44 行目「像が角全体であること（Part 260 の範囲）」：Part 260 で示したとも読めるが、CLAUDE.md によれば Part 260 でも Lean の外。「（Part 260 でも Lean の外）」。
9. （確認できない）exists_compatible_hom_iff、not_isDirected_udvd、Lim、ofL_injective、sqLim、sqLim_of_injective は入力にない。「2 と 4 にユニタリ約数の順序の共通の上界がない」は手計算で確かめた（v_2(c) = 1 と v_2(c) = 2 が両立しない）。54 行目の「同じ型の上の」は、sqLim の添字が Lvl そのものでない場合は言い換えが要る。
10. （入力 1 の不備）入力 1 の 114〜115 行目で cornerOp_one_mul・cornerOp_one_ne_one が「-- Mathlib」の見出しの下に置かれている。PAG264 の欄にあるのは cornerHom_one_ne_one だが、証明が使うのは cornerOp_one_ne_one。次回の入力の雛形で直すことを勧める。



### §L4-2 直す前の散文と形式文（再照合に渡した版）


#### `records/audit265/input_prose.md`

# 入力 2：PAG265.lean の冒頭の説明（散文）
```
/-
アーデル射影幾何 — Part 261（PAG265、短期層の小さいノート、2026-11-19）：角の写像の帰納系と、その極限の非単位的な代数（正の整数の整除の順序の上）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残り。
- 2026-11-19 12:51 に著者が採用した（構築側の推薦）。
- 基礎文書の第 5 章（索引 5.2・5.5）の材料。新しい問いではない。

記号：
- `Lvl`（Part 254（PAG258））：正の整数を整除の前順序で並べた型。a ≤ b ⇔ a ∣ b。有向（`IsDirectedOrder`、上界は積）で、`Nonempty`。
- A_a = `shellAlg a.val`。
- φ = Part 260（PAG264）の `cornerHom`（非単位的な代数準同型）。

定義：
- `cornerSys a b h`（a ≤ b）：φ_{a,b}。
- `CornerLim`：Mathlib の一般の `DirectLimit`（型は Mathlib/Order/DirectedInverseSystem.lean）による帰納極限。
  - 非単位的な環の構造と ℂ のスカラー倍は Mathlib/Algebra/Colimit/DirectLimit.lean のインスタンスによる。遷移写像が非単位的な ℂ 代数準同型なので入る。
- `ofCorner a`：標準の写像 A_a → 極限（`DirectLimit.NonUnitalAlgebra.of`、非単位的な ℂ 代数準同型）。
- e_a = ofCorner_a(1) と書く。

Lean の文：
- 恒等の法則 φ_{a,a} = id（`cornerSys_self`。Part 260 の `cornerOp_self` から）。
- 合成の法則 φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（`cornerSys_comp`。Part 260 の `cornerOp_comp` から）。
- `DirectedSystem` のインスタンス（上の 2 法則）。
- 標準の写像の値（`ofCorner_apply`、rfl）。系の写像との両立 ofCorner_b ∘ φ_{a,b} = ofCorner_a（`ofCorner_cornerSys`）。
- 各 A_a は極限に単射で入る（`ofCorner_injective`）。
  - 遷移写像の単射性（Part 260 の `cornerHom_injective`）を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
  - 添字の有向性は、極限の同値関係の側で使う。
- 局所的な単位元（1 元ごと、`exists_local_unit`）：極限のどの元 x にも、ある a があって e_a x = x = x e_a。
- e_a はべき等（`ofCorner_one_mul_self`）。a ≤ b なら e_b e_a = e_a = e_a e_b（`ofCorner_one_le`）。
- 局所的な単位元（有限集合ごと、`exists_local_unit_finset`）：極限の有限部分集合 F ごとに、ある a があって、べき等元 e_a が F のどの元も両側から固定する。
  - したがって F ⊆ e_a·極限·e_a。
  - 局所的な単位元を持つ環（Ánh–Márki、Abrams の定義：有限集合ごとに冪等元 e があって F ⊆ eRe）の条件の形。この定義の文献との照合は、照合者の記憶によるもので、本文は開いていない。
- 大域の単位元はない（`not_exists_left_one`）：極限には左単位元がない（したがって両側の単位元もない。右単位元がないことは Lean にしていない）。
  - 証明：u = ofCorner_c(U) が左単位元なら、d = 2c で φ_{c,d}(U) = 1 となる。
  - それは Part 260 の `cornerOp_one_mul` と `cornerOp_one_ne_one`（c < d）に反する。

補足（照合者の指摘）：
- 恒等と合成の 2 法則は、`End(ℂ^{ℤ/a})` 全体で、正規化なしでも成り立ち、殻代数の構造を使わない（手計算。Lean の文は正規化つき）。
- 正規化 N/M が効くのは、乗法性（局所的な単位元と、単位元がないこと）の側。
- 単位元がないことは、素数冪の段にも gcd(N, M/N) にもよらない。効いているのは、どの狭義の段 c → 2c でも φ(1) ≠ 1 であることと単射性。無平方数の段だけの部分系でも同じ証明が通る見込み（部分系での文は Lean にしていない）。
- 局所的な単位元（1 元ごと）は直極限の構成からほぼ自動的に出る。単射性も φ(1) ≠ 1 も使わない。

対比（前の Part の Lean の文との並置。新しい定理ではない）：
- 引き戻しと両立し、単位元を保ち、殻を混ぜない（強い読み）代数準同型 A_N → A_M があるのは、N ∣ M で gcd(N, M/N) = 1 のときに限る（Part 258（PAG262）の `exists_compatible_hom_iff`）。
- そのような段（a ∣ b かつ gcd(a, b/a) = 1、ユニタリ約数の順序）は有向でない（Part 259（PAG263）の `not_isDirected_udvd`。2 と 4 に共通の上界がない）。
- Part 260 の角の写像は、N < M の段で単位元を保たない。D 側は殻の span に入らない（(2,4) は Lean、一般には数値。Part 260）。
- この写像は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。

範囲（Lean にしていないもの）：
- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
- 像が角全体であること（Part 260 でも Lean の外）。
- 右単位元がないこと。部分系（無平方数の段など）での同じ文。
- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（§1 の 08:41 の定義）。

位置づけ（ラベル）：
- ［再導出（小さい）］：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。局所的な単位元を持つ環は標準の概念（上の照合の留保つき）。
- 新規候補はない。A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った。
- 別の帰納系との関係：
  - Part 254 には、同じ型 `Lvl` の上に、単数の上の関数の引き戻しの帰納系と ℂ 加群の極限 `Lim`（`ofL_injective`）がある。
  - Part 259 には、別の添字（素数の有限集合）の上に、無平方数の段の極限 `sqLim`（`sqLim_of_injective`）がある。
  - どちらも `Module.DirectLimit` による別の系で、重複ではない。
- Mathlib の名前の検索（1 回目の独立照合の指摘を受けて）：
  - 一般の `DirectLimit` の非単位的な環・代数の構造（`NonUnitalRing` のインスタンス、`DirectLimit.NonUnitalAlgebra.of`）。
  - `DirectLimit.mk_injective`。
  - 最初の版は `Module.DirectLimit`（ℂ 加群）だけで組み、「Mathlib に非単位的な代数の直極限の道具が見当たらない」と書いていた。これは誤りだったので、一般の `DirectLimit` で組み直した。
- 閉じる前の機械的な照合（組み直した版）：全宣言 4483 件、対象 11 件（定理 8 と定義 3）、候補上位 20、8·20·2 + 3·20 = 380 回。
  - 対象の定理 8 には下書きの `cornerSys_apply` を含む。これが Part 260（PAG264）の `cornerHom_coe` と、定義を開けば同じ文（A）だったので消した。
  - ほかに一致と出たのは自動生成の congr_simp だけ。
  - 足した 3 定理の照合は記録 `records/audit265/`。
- 独立照合は 2 回（最初の版、組み直した版）。2 回目の指摘を受けて 3 定理（べき等、順序、有限集合版）を足し、文面を直した。記録 `records/audit265/`。
-/
```


#### `records/audit265/input_formal.md`

# 入力 1：PAG265.lean の形式文の全文（docstring・コメントを除いた）と、使う定義
## A. PAG265.lean
```lean
import PAG264

namespace PAG.Part265

open PAG.Part218 PAG.Part258 PAG.Part264

noncomputable def cornerSys (a b : Lvl) (h : a ≤ b) : shellAlg a.val →ₙₐ[ℂ] shellAlg b.val :=
  cornerHom (N := a.val) (M := b.val) h

theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S := by
  apply Subtype.ext
  exact cornerOp_self (N := a.val) (S : Module.End ℂ (ZMod a.val → ℂ))

theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S := by
  apply Subtype.ext
  exact cornerOp_comp (N := a.val) (M := b.val) (L := c.val) hab hbc (S : Module.End ℂ (ZMod a.val → ℂ))

instance : DirectedSystem (fun a : Lvl => shellAlg a.val)
    (fun a b h => (cornerSys a b h : shellAlg a.val → shellAlg b.val)) where
  map_self a S := cornerSys_self a S
  map_map _ _ _ hab hbc S := cornerSys_comp hab hbc S

abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys

noncomputable def ofCorner (a : Lvl) : shellAlg a.val →ₙₐ[ℂ] CornerLim :=
  DirectLimit.NonUnitalAlgebra.of _ cornerSys a

theorem ofCorner_apply (a : Lvl) (S : shellAlg a.val) :
    ofCorner a S = (⟦⟨a, S⟩⟧ : CornerLim) := rfl

theorem ofCorner_cornerSys {a b : Lvl} (h : a ≤ b) (S : shellAlg a.val) :
    ofCorner b (cornerSys a b h S) = ofCorner a S := by
  rw [ofCorner_apply, ofCorner_apply]
  exact (DirectLimit.eq_of_le (F := fun a : Lvl => shellAlg a.val) (f := cornerSys) ⟨a, S⟩ b h).symm

theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
  DirectLimit.mk_injective cornerSys (fun b c h => cornerHom_injective (N := b.val) (M := c.val) h) a

theorem exists_local_unit (x : CornerLim) :
    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  obtain ⟨a, S, rfl⟩ := DirectLimit.exists_eq_mk cornerSys x
  refine ⟨a, ?_, ?_⟩
  · rw [← ofCorner_apply, ← map_mul, one_mul]
  · rw [← ofCorner_apply, ← map_mul, mul_one]

theorem ofCorner_one_mul_self (a : Lvl) : ofCorner a 1 * ofCorner a 1 = ofCorner a 1 := by
  rw [← map_mul, one_mul]

theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 := by
  rw [← ofCorner_cornerSys h 1]
  exact ⟨by rw [← map_mul, one_mul], by rw [← map_mul, mul_one]⟩

theorem exists_local_unit_finset (F : Finset CornerLim) :
    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨⟨1, Nat.one_pos⟩, fun x hx => by simp at hx⟩
  | insert x F _ ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := exists_local_unit x
    obtain ⟨c, hac, hbc⟩ := (show IsDirectedOrder Lvl from inferInstance).directed a b
    have mono : ∀ {d : Lvl}, d ≤ c → ∀ y : CornerLim, (ofCorner d 1 * y = y ∧ y * ofCorner d 1 = y) →
        (ofCorner c 1 * y = y ∧ y * ofCorner c 1 = y) := by
      intro d hd y hy
      obtain ⟨l, r⟩ := ofCorner_one_le hd
      constructor
      · calc ofCorner c 1 * y = ofCorner c 1 * (ofCorner d 1 * y) := by rw [hy.1]
          _ = ofCorner d 1 * y := by rw [← mul_assoc, l]
          _ = y := hy.1
      · calc y * ofCorner c 1 = (y * ofCorner d 1) * ofCorner c 1 := by rw [hy.2]
          _ = y * ofCorner d 1 := by rw [mul_assoc, r]
          _ = y := hy.2
    refine ⟨c, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact mono hbc y hb
    · exact mono hac y (ha y hy)

theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x := by
  rintro ⟨u, hu⟩
  obtain ⟨c, U, rfl⟩ := DirectLimit.exists_eq_mk cornerSys u
  let d : Lvl := ⟨2 * c.val, Nat.mul_pos (by norm_num) c.pos⟩
  have h : c ≤ d := ⟨2, by simp [d, mul_comm]⟩
  have e := hu (ofCorner d 1)
  rw [← ofCorner_apply, ← ofCorner_cornerSys h U, ← map_mul, mul_one] at e
  have e2 : cornerSys c d h U = 1 := ofCorner_injective d e
  have e3 := congrArg Subtype.val e2
  change cornerOp (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ)) = 1 at e3
  have hq := cornerOp_one_mul (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ))
  rw [e3] at hq
  have hlt : c.val < d.val := by
    show c.val < 2 * c.val
    have := c.pos; omega
  exact cornerOp_one_ne_one (N := c.val) (M := d.val) h hlt (by simpa using hq)

end PAG.Part265
```
## B. 使う定義・前の鎖の補題の文（証明は省略）・Mathlib の定義
```lean
-- PAG258（Part 254）
structure Lvl where
  val : ℕ
  pos : 0 < val
deriving DecidableEq
instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans
instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩
instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩
instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

-- PAG218（Part 214）
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
-- （dind N s は gcd(N, x) = s の指示関数、geps N s はその逆フーリエ変換、convL は畳み込み作用素）

-- PAG264（Part 260）。pull は引き戻し f ↦ f ∘ π（π : ℤ/M → ℤ/N）、fsum は繊維の和
noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M   -- 値は cornerOp h S（cornerHom_coe、rfl）
theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S
theorem cornerOp_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h2 (cornerOp h1 S) = cornerOp (h1.trans h2) S
theorem cornerHom_injective (h : N ∣ M) : Function.Injective (cornerHom h)
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1
theorem cornerOp_one_mul (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp h 1 * cornerOp h S = cornerOp h S
theorem cornerOp_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerOp h 1 ≠ 1

-- Mathlib
-- class DirectedSystem (F : ι → Type*) (f : ∀ ⦃i j⦄, i ≤ j → F i → F j) : Prop where
--   map_self ⦃i⦄ (x : F i) : f le_rfl x = x
--   map_map ⦃k j i⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F i) : f hjk (f hij x) = f (le_trans hij hjk) x
-- DirectLimit F f（Mathlib/Order/DirectedInverseSystem.lean）：有向な前順序 ι の上の DirectedSystem の直極限。
--   台は Σ i, F i を「ある共通の上界で像が等しい」で割った商。⟦⟨i, x⟩⟧ はその類。
-- theorem DirectLimit.eq_of_le (x : Σ i, F i) (j) (h : x.1 ≤ j) : (⟦x⟧ : DirectLimit F f) = ⟦⟨j, f x.1 j h x.2⟩⟧
-- theorem DirectLimit.exists_eq_mk (z : DirectLimit F f) : ∃ i x, z = ⟦⟨i, x⟩⟧
-- theorem DirectLimit.mk_injective (h : ∀ i j hij, Function.Injective (f i j hij)) (i) :
--     Function.Injective fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit F f)
-- Mathlib/Algebra/Colimit/DirectLimit.lean：各 F i が非単位的な環で遷移写像が NonUnitalRingHomClass なら、
--   DirectLimit F f に NonUnitalRing のインスタンス（積は共通の上界に送ってから掛ける）、ℂ のスカラー倍（Module）がある。
-- DirectLimit.NonUnitalAlgebra.of F f i : F i →ₙₐ[R] DirectLimit F f、値は x ↦ ⟦⟨i, x⟩⟧。

```


### §L4-3 現在の PAG265.lean の全文（docstring を含む）

```lean
/-
アーデル射影幾何 — Part 261（PAG265、短期層の小さいノート、2026-11-19）：角の写像の帰納系と、その極限の非単位的な代数（正の整数の整除の順序の上）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残り。
- 2026-11-19 12:51 に著者が採用した（構築側の推薦）。
- 基礎文書の第 5 章（索引 5.2・5.5）の材料。新しい問いではない。

記号：
- `Lvl`（Part 254（PAG258））：正の整数を整除の前順序で並べた型。a ≤ b ⇔ a ∣ b。有向（`IsDirectedOrder`、上界は積）で、`Nonempty`。
- A_a = `shellAlg a.val`。
- φ = Part 260（PAG264）の `cornerHom`（単位元を保つとは限らない代数準同型。N < M では保たない）。

定義：
- `cornerSys a b h`（a ≤ b）：φ_{a,b}。
- `CornerLim`：Mathlib の一般の `DirectLimit`（型は Mathlib/Order/DirectedInverseSystem.lean）による帰納極限。
  - 非単位的な環の構造と ℂ のスカラー倍は Mathlib/Algebra/Colimit/DirectLimit.lean のインスタンスによる（`NonUnitalRing`、`Module`、積とスカラー倍の両立 `IsScalarTower`・`SMulCommClass` のインスタンスもある）。遷移写像が非単位的な ℂ 代数準同型なので入る。
- `ofCorner a`：標準の写像 A_a → 極限（`DirectLimit.NonUnitalAlgebra.of`、非単位的な ℂ 代数準同型）。
- e_a = ofCorner_a(1) と書く。

Lean の文：
- 恒等の法則 φ_{a,a} = id（`cornerSys_self`。Part 260 の `cornerOp_self` から）。
- 合成の法則 φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（`cornerSys_comp`。Part 260 の `cornerOp_comp` から）。
- `DirectedSystem` のインスタンス（上の 2 法則）。
- 標準の写像の値（`ofCorner_apply`、rfl）。系の写像との両立 ofCorner_b ∘ φ_{a,b} = ofCorner_a（`ofCorner_cornerSys`）。
- 各 A_a は極限に単射で入る（`ofCorner_injective`）。
  - 遷移写像の単射性（Part 260 の `cornerHom_injective`）を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
  - 添字の有向性は、極限の同値関係の側で使う。
- 局所的な単位元（1 元ごと、`exists_local_unit`）：極限のどの元 x にも、ある a があって e_a x = x = x e_a。
- e_a はべき等（`ofCorner_one_mul_self`）。a ≤ b なら e_b e_a = e_a = e_a e_b（`ofCorner_one_le`）。
- 局所的な単位元（有限集合ごと、`exists_local_unit_finset`）：極限の有限部分集合 F ごとに、ある a があって、e_a が F のどの元も両側から固定する（e_a のべき等性は `ofCorner_one_mul_self`）。
  - F ⊆ e_a·極限·e_a は x = e_a x e_a から直ちに出る（Lean の文ではない）。
  - 局所的な単位元を持つ環の、Ánh–Márki の流儀の定義（有限集合ごとに冪等元 e があって F ⊆ eRe）の条件の形。Abrams の流儀（可換な冪等元の集合を求める）との異同と、文献の本文との照合は未確認（照合者の記憶による）。
- 大域の単位元はない（`not_exists_left_one`）：極限には左単位元がない（したがって両側の単位元もない。右単位元がないことは Lean にしていない）。
  - 証明：u = ofCorner_c(U) が左単位元なら、d = 2c で u e_d = e_d と `ofCorner_cornerSys` から ofCorner_d(φ_{c,d}(U)) = ofCorner_d(1)、`ofCorner_injective` により φ_{c,d}(U) = 1 となる。
  - それは Part 260 の `cornerOp_one_mul` と `cornerOp_one_ne_one`（c < d）に反する。

補足（照合者の指摘）：
- 恒等と合成の 2 法則は殻代数の構造を使わない（Part 260 の `cornerOp_self`・`cornerOp_comp` は End(ℂ^{ℤ/a}) 全体の文）。正規化なしでも成り立つこと（係数の積が合えばよい）は手計算で、Lean の文は正規化つき。
- 正規化 N/M が効くのは φ の乗法性、したがって極限に積の構造があること（正規化なしでは φ'(S)φ'(T) = (M/N)φ'(ST)、手計算）。φ(1) ≠ 1 自体は正規化によらない。
- 単位元がないことの証明：Lean の証明は d = 2c をとり、`ofCorner_injective` と `cornerOp_one_ne_one`（N ∣ M、N < M のどの段でも成り立ち、gcd によらない）を使う。c が偶数ならこの段は素数冪の段だが、d を c の倍数で c より大きいレベル（例：c を割らない素数 p で d = pc）に替えても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。無平方数の段だけの部分系（上界は lcm）でもこの取り方で通る見込み（Lean にしていない）。
- 局所的な単位元の 3 つの文（1 元ごと、べき等と順序、有限集合ごと）は、有向な添字の上で単位的な環を乗法的な写像でつないだ直極限ならどれでも成り立つ一般の事実（単射性も φ(1) ≠ 1 も使わない）。「非単位的」という内容を運ぶのは `not_exists_left_one` だけ（照合者の指摘）。

対比（前の Part の Lean の文との並置。新しい定理ではない）：
- N ∣ M のとき、引き戻しと両立し、単位元を保ち、殻を混ぜない（強い読み）代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る（Part 258（PAG262）の `exists_compatible_hom_iff`）。
- そのような段（a ∣ b かつ gcd(a, b/a) = 1、ユニタリ約数の順序）は有向でない（Part 259（PAG263）の `not_isDirected_udvd`。2 と 4 に共通の上界がない）。
- Part 260 の角の写像は、N < M の段で単位元を保たない。D 側は殻の span に入らない（(2,4)・s = 2 は Lean。N < M のすべての s ∣ N で入らないことは数値。Part 260）。
- この写像は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。

範囲（Lean にしていないもの）：
- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
- 像が角全体であること（Part 260 でも Lean の外）。
- 右単位元がないこと。部分系（無平方数の段など）での同じ文。
- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（§1 の 08:41 の定義）。

位置づけ（ラベル）：
- ［再導出（小さい）］：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。局所的な単位元を持つ環は標準の概念（上の照合の留保つき）。
- 新規候補はない。A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った。
- 別の帰納系との関係：
  - Part 254 には、同じ型 `Lvl` の上に、単数の上の関数の引き戻しの帰納系と ℂ 加群の極限 `Lim`（`ofL_injective`）がある。
  - Part 259 には、別の添字（素数の有限集合）の上に、無平方数の段の極限 `sqLim`（`sqLim_of_injective`）がある。
  - どちらも `Module.DirectLimit` による別の系で、重複ではない。
- Mathlib の名前の検索（1 回目の独立照合の指摘を受けて）：
  - 一般の `DirectLimit` の非単位的な環・代数の構造（`NonUnitalRing` のインスタンス、`DirectLimit.NonUnitalAlgebra.of`）。
  - `DirectLimit.mk_injective`。
  - 最初の版は `Module.DirectLimit`（ℂ 加群）だけで組み、「Mathlib に非単位的な代数の直極限の道具が見当たらない」と書いていた。これは誤りだったので、一般の `DirectLimit` で組み直した。
- 閉じる前の機械的な照合（組み直した版）：全宣言 4483 件、対象 11 件（定理 8 と定義 3。インスタンスは対象外）、候補上位 20。定理は両向き（·2）、定義は 1 回で、8·20·2 + 3·20 = 380 回。
  - 対象の定理 8 には下書きの `cornerSys_apply` を含む。これが Part 260（PAG264）の `cornerHom_coe` と、定義を開けば同じ文（A）だったので消した。
  - ほかに一致と出たのは自動生成の congr_simp だけ。
  - 足した 3 定理：全宣言 4485 件、3·20·2 = 120 回、一致なし。Mathlib の `IsIdempotentElem.one`・`IsIdempotentElem.map` から `ofCorner_one_mul_self` が直ちに出る見込み（照合者の指摘、B）。
- 独立照合は 3 回（最初の版、組み直した版、足した 3 定理と直した文面の再照合）。
  - 2 回目の指摘を受けて 3 定理（べき等、順序、有限集合版）を足した。
  - 3 回目の指摘 11 点（単位元がないことの証明の段の取り方、単射性の段、正規化の効き方、量化など）を直した。
  - 3 回目の後の直しは主張を狭めるか明確にするもので、補足8の停止の規約の範囲。尾の台帳は空。記録 `records/audit265/`。
-/
import PAG264

namespace PAG.Part265

open PAG.Part218 PAG.Part258 PAG.Part264

/-- 系の写像：a ≤ b（a ∣ b）なら角の写像 φ_{a,b}（Part 260 の `cornerHom`、単位元を保つとは限らない代数準同型。a ≠ b のとき（このとき a.val < b.val）は保たない：`cornerHom_one_ne_one`）。 -/
noncomputable def cornerSys (a b : Lvl) (h : a ≤ b) : shellAlg a.val →ₙₐ[ℂ] shellAlg b.val :=
  cornerHom (N := a.val) (M := b.val) h

/-- 恒等の法則：φ_{a,a} = id。 -/
theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S := by
  apply Subtype.ext
  exact cornerOp_self (N := a.val) (S : Module.End ℂ (ZMod a.val → ℂ))

/-- 合成の法則：φ_{b,c} ∘ φ_{a,b} = φ_{a,c}。 -/
theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S := by
  apply Subtype.ext
  exact cornerOp_comp (N := a.val) (M := b.val) (L := c.val) hab hbc (S : Module.End ℂ (ZMod a.val → ℂ))

/-- **帰納系**：正の整数の整除の順序（Part 254 の `Lvl`）の上で、角の写像は帰納系をなす。 -/
instance : DirectedSystem (fun a : Lvl => shellAlg a.val)
    (fun a b h => (cornerSys a b h : shellAlg a.val → shellAlg b.val)) where
  map_self a S := cornerSys_self a S
  map_map _ _ _ hab hbc S := cornerSys_comp hab hbc S

/-- 角の写像の帰納極限（Mathlib の一般の `DirectLimit`。非単位的な環の構造と ℂ のスカラー倍を持つ）。 -/
abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys

/-- 標準の写像 A_a → 極限（非単位的な ℂ 代数準同型）。 -/
noncomputable def ofCorner (a : Lvl) : shellAlg a.val →ₙₐ[ℂ] CornerLim :=
  DirectLimit.NonUnitalAlgebra.of _ cornerSys a

/-- 標準の写像の値（商の元）。 -/
theorem ofCorner_apply (a : Lvl) (S : shellAlg a.val) :
    ofCorner a S = (⟦⟨a, S⟩⟧ : CornerLim) := rfl

/-- 標準の写像は系の写像と両立する。 -/
theorem ofCorner_cornerSys {a b : Lvl} (h : a ≤ b) (S : shellAlg a.val) :
    ofCorner b (cornerSys a b h S) = ofCorner a S := by
  rw [ofCorner_apply, ofCorner_apply]
  exact (DirectLimit.eq_of_le (F := fun a : Lvl => shellAlg a.val) (f := cornerSys) ⟨a, S⟩ b h).symm

/-- 各段 A_a は極限に単射で入る。 -/
theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
  DirectLimit.mk_injective cornerSys (fun b c h => cornerHom_injective (N := b.val) (M := c.val) h) a

/-- **局所的な単位元**：極限のどの元 x にも、ある a があって、e_a = (φ(1_a) の像) は x = e_a x = x e_a を満たす。 -/
theorem exists_local_unit (x : CornerLim) :
    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  obtain ⟨a, S, rfl⟩ := DirectLimit.exists_eq_mk cornerSys x
  refine ⟨a, ?_, ?_⟩
  · rw [← ofCorner_apply, ← map_mul, one_mul]
  · rw [← ofCorner_apply, ← map_mul, mul_one]

/-- e_a = ofCorner_a(1) はべき等。 -/
theorem ofCorner_one_mul_self (a : Lvl) : ofCorner a 1 * ofCorner a 1 = ofCorner a 1 := by
  rw [← map_mul, one_mul]

/-- a ≤ b なら e_b e_a = e_a = e_a e_b。 -/
theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 := by
  rw [← ofCorner_cornerSys h 1]
  exact ⟨by rw [← map_mul, one_mul], by rw [← map_mul, mul_one]⟩

/-- **局所的な単位元（有限集合版）**：極限の有限部分集合 F ごとに、べき等元 e_a があって、F のどの元も両側から固定する
（F ⊆ e_a·極限·e_a。局所的な単位元を持つ環の、有限集合についての定義の形）。 -/
theorem exists_local_unit_finset (F : Finset CornerLim) :
    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨⟨1, Nat.one_pos⟩, fun x hx => by simp at hx⟩
  | insert x F _ ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := exists_local_unit x
    obtain ⟨c, hac, hbc⟩ := (show IsDirectedOrder Lvl from inferInstance).directed a b
    have mono : ∀ {d : Lvl}, d ≤ c → ∀ y : CornerLim, (ofCorner d 1 * y = y ∧ y * ofCorner d 1 = y) →
        (ofCorner c 1 * y = y ∧ y * ofCorner c 1 = y) := by
      intro d hd y hy
      obtain ⟨l, r⟩ := ofCorner_one_le hd
      constructor
      · calc ofCorner c 1 * y = ofCorner c 1 * (ofCorner d 1 * y) := by rw [hy.1]
          _ = ofCorner d 1 * y := by rw [← mul_assoc, l]
          _ = y := hy.1
      · calc y * ofCorner c 1 = (y * ofCorner d 1) * ofCorner c 1 := by rw [hy.2]
          _ = y * ofCorner d 1 := by rw [mul_assoc, r]
          _ = y := hy.2
    refine ⟨c, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact mono hbc y hb
    · exact mono hac y (ha y hy)

/-- **大域の単位元はない**：極限には左単位元がない（非単位的）。 -/
theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x := by
  rintro ⟨u, hu⟩
  obtain ⟨c, U, rfl⟩ := DirectLimit.exists_eq_mk cornerSys u
  let d : Lvl := ⟨2 * c.val, Nat.mul_pos (by norm_num) c.pos⟩
  have h : c ≤ d := ⟨2, by simp [d, mul_comm]⟩
  have e := hu (ofCorner d 1)
  rw [← ofCorner_apply, ← ofCorner_cornerSys h U, ← map_mul, mul_one] at e
  have e2 : cornerSys c d h U = 1 := ofCorner_injective d e
  have e3 := congrArg Subtype.val e2
  change cornerOp (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ)) = 1 at e3
  have hq := cornerOp_one_mul (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ))
  rw [e3] at hq
  have hlt : c.val < d.val := by
    show c.val < 2 * c.val
    have := c.pos; omega
  exact cornerOp_one_ne_one (N := c.val) (M := d.val) h hlt (by simpa using hq)

end PAG.Part265

#print axioms PAG.Part265.cornerSys_self
#print axioms PAG.Part265.cornerSys_comp
#print axioms PAG.Part265.ofCorner_apply
#print axioms PAG.Part265.ofCorner_cornerSys
#print axioms PAG.Part265.ofCorner_injective
#print axioms PAG.Part265.exists_local_unit
#print axioms PAG.Part265.ofCorner_one_mul_self
#print axioms PAG.Part265.ofCorner_one_le
#print axioms PAG.Part265.exists_local_unit_finset
#print axioms PAG.Part265.not_exists_left_one
```


### §L4-4 現在のノート `notes/pag2_pag265_corner_limit.md`（全文）

```markdown
# アーデル射影幾何 — Part 261（PAG265）：角の写像の帰納系と、その極限の非単位的な代数（短期層の小さいノート、2026-11-19）

（新しいパートでも新しい問いでもない。方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残りを、2026-11-19 12:51 に著者が採用した。基礎文書の第 5 章（索引 5.2・5.5）の材料。
Lean は PAG265.lean：定理 10、sorry 0、警告 0。#print axioms 10 行はすべて標準の公理の範囲。照合の記録は `records/audit265/`。）

## §1 結果（Lean の文から起こした）

記号：
- `Lvl`（Part 254（PAG258））は、正の整数を整除で並べた有向な前順序。
- A_a = `shellAlg a.val`。φ は Part 260（PAG264）の角の写像 `cornerHom`。
- e_a は A_a の単位元の極限での像。

主な文：
- **帰納系**：恒等の法則 φ_{a,a} = id（`cornerSys_self`）と合成の法則（`cornerSys_comp`）。この 2 つで `DirectedSystem` のインスタンスになる。
- **極限**：`CornerLim` は Mathlib の一般の `DirectLimit` による極限。
  - 遷移写像が単位元の保存を課さない ℂ 代数準同型（`→ₙₐ`）なので、Mathlib のインスタンスにより非単位的な環の構造と ℂ のスカラー倍を持つ。
  - 標準の写像 `ofCorner a : A_a → CornerLim` は非単位的な ℂ 代数準同型で、系の写像と両立する（`ofCorner_cornerSys`）。
- **各段は単射に入る**（`ofCorner_injective`）。Part 260 の `cornerHom_injective` を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
- **局所的な単位元**：
  - 1 元ごと（`exists_local_unit`）：極限のどの元 x にも、ある a があって e_a x = x = x e_a。
  - e_a はべき等（`ofCorner_one_mul_self`）。a ∣ b なら e_b e_a = e_a = e_a e_b（`ofCorner_one_le`）。
  - 有限集合ごと（`exists_local_unit_finset`）：有限部分集合 F ごとに、ある a があって、e_a が F のどの元も両側から固定する（F ⊆ e_a·極限·e_a は x = e_a x e_a から直ちに出る。Lean の文ではない）。局所的な単位元を持つ環の、Ánh–Márki の流儀の定義の条件の形。Abrams の流儀（可換な冪等元の集合）との異同と文献の本文との照合は未確認。
- **大域の単位元はない**（`not_exists_left_one`）：極限には左単位元がない。右単位元がないことは Lean にしていない。

## §2 読み（解釈の層。Lean の文ではない）

- 極限は直極限の側でとった。有限次元の代数を、角への埋め込みで整除の順序全体に並べた和で、完備化は使っていない（§1 の 08:41 の定義：極限でも離散構造の観測を維持する）。
- e_a（a が整除で大きくなるほど大きい、べき等元の増大列）は、関数のレベルでは「a で周期的な関数への射影」の極限での像。BC の μ_n μ_n^* に当たる形をしている（Part 260 の範囲の読み。Lean の外）。
- 対比（前の Part の Lean の文との並置）：
  - 単位元を保ち殻を混ぜない写像の系は、互いに素な段にしかなく（Part 258（PAG262））、その順序は有向でない（Part 259（PAG263））。
  - N < M の段で単位元を保たない角の写像の系は、整除の順序全体で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。
  - 局所的な単位元の 3 つの文は、各段が単位的で移行写像が乗法を保つ直極限ならどれでも成り立つ一般の事実で（2026-11-19 夕方の索引の統合照合の指摘で狭めた）、「非単位的」という内容を運ぶのは `not_exists_left_one` だけ。
  - その証明は d = 2c（c が偶数なら素数冪の段）をとるが、c を割らない素数 p で d = pc としても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。効いているのは、N < M のどの段でも φ(1) ≠ 1（`cornerOp_one_ne_one`、gcd によらない）であることと単射性。

## §3 ラベルと範囲

- **［再導出（小さい）］**：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。新規候補はない。A1 とは関係しない。
- 対照群：形式（帰納系と直極限）だけの文なので、関数体の有限レベルでも同じ形で成り立つ見込み（Part 260 の対照群の範囲。この Part では試していない）。
- **Lean の外**：
  - 極限の具体形（Ẑ 上の局所定数関数への作用）と Bost–Connes との対応。
  - 像が角全体であること（Part 260 でも Lean の外）。
  - 右単位元がないこと。部分系での同じ文。
  - 完備化（とらない）。

## §4 内部照合（第 12 の型）

- **着手前**（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った（新しい型を作らなかった）。
- **閉じる前**（機械的）：
  - 組み直した版：全宣言 4483 件、対象 11 件（定理 8 と定義 3）、380 回。下書きの `cornerSys_apply` が Part 260 の `cornerHom_coe` と定義を開けば同じ文（A）だったので消した。
  - 足した 3 定理：120 回、一致なし。
  - 最初の版：200 回、一致なし。
- **Mathlib の名前**：最初の版では一般の `DirectLimit` の代数の構造を見落としていた。1 回目の独立照合の指摘で見つけ、組み直した。第 12 の型の教訓（着手前に Mathlib の名前でも検索する）が、今回は照合で補われた形。

## §5 独立照合（第 11 の型）

- **1 回目**（最初の版、`Module.DirectLimit` の ℂ 加群）：偽・空虚なし。
  - 指摘：Mathlib に一般の `DirectLimit` の非単位的な代数の構造がある可能性。証明の依存先の書き落とし。対比の条件の書き落とし。
  - 対応：Mathlib で確かめ、組み直した。出力は `outputs/check1_output.md`。
- **2 回目**（組み直した版）：偽・空虚なし。
  - 指摘：「局所的な単位元を持つ環」は標準の定義（有限集合ごとに共通のべき等元）より弱い文しか Lean になかった。ほかに文面 9 点。
  - 対応：3 定理を足し、文面を直した。出力は `outputs/check2_output.md`。
- **再照合**（足した 3 定理と直した文面）：§6。

## §6 再照合

- 条件：形式文と定義、散文（冒頭の説明）、2 回目の指摘を渡した（Read 3 回、約 414 秒）。出力は `records/audit265/outputs/recheck_output.md`。
- 足した 3 定理：意図どおり。e_c ≠ e_{2c}、有限性を外すと偽（極限全体なら左単位元になる）などの証人と反例が示された。3 定理は単射性も φ(1) ≠ 1 も使わない一般論。
- 宣言名の取り違えと、範囲の内外の誤りはなかった。2 回目の指摘 1〜10 は反映されていた。
- 新しいずれ 11 点を直した（冒頭の説明とこのノート）：
  1. 単位元がないことの証明の段の取り方（指摘 3 の直しが生んだずれ）。
  2. 単射性の段の書き落とし。
  3. 正規化の効き方。
  4. F ⊆ eRe が Lean の文でないこと。
  5. Ánh–Márki と Abrams の流儀の違い。
  6. 積とスカラー倍の両立のインスタンス。
  7. Part 258 の同値の書き方。
  8. D 側の量化。
  9. 件数の内訳。
  10. 照合の回数。
  11. End 全体と正規化なしの書き分け。
- 再照合の後の直しは主張を狭めるか明確にするものと申告し、補足8の停止の規約の範囲として尾の台帳は空とした。2026-11-19 19:58 の著者の規則（自己申告では閉じない）に照らして、台帳 `pag2_tail_ledger.md` の L4 に戻した（未照合）。

## §7 収束アラームの報告

- 兆候 4（初等的な部品の組み合わせだけ）：続いている。文書の章に仕える短期層。
- 兆候 1（自前の名前）：極限は Mathlib の `DirectLimit` をそのまま使い、自前の構成を作らなかった。
- 文献照合：盲検の問いテストは R-d の推薦の段階（2026-11-19 午前）で実施した。この Part では Mathlib の名前の照合を行った。
```


### §L4-5 L4 の範囲のコミット 6ba1a54 の、PAG265.lean とノートの差分（コミットの中に、再照合の前の直しと後の直しが混ざっている）

```diff
diff --git a/PAG265.lean b/PAG265.lean
new file mode 100644
index 0000000..61865f8
--- /dev/null
+++ b/PAG265.lean
@@ -0,0 +1,200 @@
+/-
+アーデル射影幾何 — Part 261（PAG265、短期層の小さいノート、2026-11-19）：角の写像の帰納系と、その極限の非単位的な代数（正の整数の整除の順序の上）
+
+問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残り。
+- 2026-11-19 12:51 に著者が採用した（構築側の推薦）。
+- 基礎文書の第 5 章（索引 5.2・5.5）の材料。新しい問いではない。
+
+記号：
+- `Lvl`（Part 254（PAG258））：正の整数を整除の前順序で並べた型。a ≤ b ⇔ a ∣ b。有向（`IsDirectedOrder`、上界は積）で、`Nonempty`。
+- A_a = `shellAlg a.val`。
+- φ = Part 260（PAG264）の `cornerHom`（非単位的な代数準同型）。
+
+定義：
+- `cornerSys a b h`（a ≤ b）：φ_{a,b}。
+- `CornerLim`：Mathlib の一般の `DirectLimit`（型は Mathlib/Order/DirectedInverseSystem.lean）による帰納極限。
+  - 非単位的な環の構造と ℂ のスカラー倍は Mathlib/Algebra/Colimit/DirectLimit.lean のインスタンスによる（`NonUnitalRing`、`Module`、積とスカラー倍の両立 `IsScalarTower`・`SMulCommClass` のインスタンスもある）。遷移写像が非単位的な ℂ 代数準同型なので入る。
+- `ofCorner a`：標準の写像 A_a → 極限（`DirectLimit.NonUnitalAlgebra.of`、非単位的な ℂ 代数準同型）。
+- e_a = ofCorner_a(1) と書く。
+
+Lean の文：
+- 恒等の法則 φ_{a,a} = id（`cornerSys_self`。Part 260 の `cornerOp_self` から）。
+- 合成の法則 φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（`cornerSys_comp`。Part 260 の `cornerOp_comp` から）。
+- `DirectedSystem` のインスタンス（上の 2 法則）。
+- 標準の写像の値（`ofCorner_apply`、rfl）。系の写像との両立 ofCorner_b ∘ φ_{a,b} = ofCorner_a（`ofCorner_cornerSys`）。
+- 各 A_a は極限に単射で入る（`ofCorner_injective`）。
+  - 遷移写像の単射性（Part 260 の `cornerHom_injective`）を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
+  - 添字の有向性は、極限の同値関係の側で使う。
+- 局所的な単位元（1 元ごと、`exists_local_unit`）：極限のどの元 x にも、ある a があって e_a x = x = x e_a。
+- e_a はべき等（`ofCorner_one_mul_self`）。a ≤ b なら e_b e_a = e_a = e_a e_b（`ofCorner_one_le`）。
+- 局所的な単位元（有限集合ごと、`exists_local_unit_finset`）：極限の有限部分集合 F ごとに、ある a があって、e_a が F のどの元も両側から固定する（e_a のべき等性は `ofCorner_one_mul_self`）。
+  - F ⊆ e_a·極限·e_a は x = e_a x e_a から直ちに出る（Lean の文ではない）。
+  - 局所的な単位元を持つ環の、Ánh–Márki の流儀の定義（有限集合ごとに冪等元 e があって F ⊆ eRe）の条件の形。Abrams の流儀（可換な冪等元の集合を求める）との異同と、文献の本文との照合は未確認（照合者の記憶による）。
+- 大域の単位元はない（`not_exists_left_one`）：極限には左単位元がない（したがって両側の単位元もない。右単位元がないことは Lean にしていない）。
+  - 証明：u = ofCorner_c(U) が左単位元なら、d = 2c で u e_d = e_d と `ofCorner_cornerSys` から ofCorner_d(φ_{c,d}(U)) = ofCorner_d(1)、`ofCorner_injective` により φ_{c,d}(U) = 1 となる。
+  - それは Part 260 の `cornerOp_one_mul` と `cornerOp_one_ne_one`（c < d）に反する。
+
+補足（照合者の指摘）：
+- 恒等と合成の 2 法則は殻代数の構造を使わない（Part 260 の `cornerOp_self`・`cornerOp_comp` は End(ℂ^{ℤ/a}) 全体の文）。正規化なしでも成り立つこと（係数の積が合えばよい）は手計算で、Lean の文は正規化つき。
+- 正規化 N/M が効くのは φ の乗法性、したがって極限に積の構造があること（正規化なしでは φ'(S)φ'(T) = (M/N)φ'(ST)、手計算）。φ(1) ≠ 1 自体は正規化によらない。
+- 単位元がないことの証明：Lean の証明は d = 2c をとり、`ofCorner_injective` と `cornerOp_one_ne_one`（N ∣ M、N < M のどの段でも成り立ち、gcd によらない）を使う。c が偶数ならこの段は素数冪の段だが、d を c の倍数で c より大きいレベル（例：c を割らない素数 p で d = pc）に替えても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。無平方数の段だけの部分系（上界は lcm）でもこの取り方で通る見込み（Lean にしていない）。
+- 局所的な単位元の 3 つの文（1 元ごと、べき等と順序、有限集合ごと）は、有向な添字の上で単位的な環を乗法的な写像でつないだ直極限ならどれでも成り立つ一般の事実（単射性も φ(1) ≠ 1 も使わない）。「非単位的」という内容を運ぶのは `not_exists_left_one` だけ（照合者の指摘）。
+
+対比（前の Part の Lean の文との並置。新しい定理ではない）：
+- N ∣ M のとき、引き戻しと両立し、単位元を保ち、殻を混ぜない（強い読み）代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る（Part 258（PAG262）の `exists_compatible_hom_iff`）。
+- そのような段（a ∣ b かつ gcd(a, b/a) = 1、ユニタリ約数の順序）は有向でない（Part 259（PAG263）の `not_isDirected_udvd`。2 と 4 に共通の上界がない）。
+- Part 260 の角の写像は、N < M の段で単位元を保たない。D 側は殻の span に入らない（(2,4)・s = 2 は Lean。N < M のすべての s ∣ N で入らないことは数値。Part 260）。
+- この写像は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。
+
+範囲（Lean にしていないもの）：
+- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
+- 像が角全体であること（Part 260 でも Lean の外）。
+- 右単位元がないこと。部分系（無平方数の段など）での同じ文。
+- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（§1 の 08:41 の定義）。
+
+位置づけ（ラベル）：
+- ［再導出（小さい）］：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。局所的な単位元を持つ環は標準の概念（上の照合の留保つき）。
+- 新規候補はない。A1 とは関係しない。
+
+内部照合：
+- 着手前（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った。
+- 別の帰納系との関係：
+  - Part 254 には、同じ型 `Lvl` の上に、単数の上の関数の引き戻しの帰納系と ℂ 加群の極限 `Lim`（`ofL_injective`）がある。
+  - Part 259 には、別の添字（素数の有限集合）の上に、無平方数の段の極限 `sqLim`（`sqLim_of_injective`）がある。
+  - どちらも `Module.DirectLimit` による別の系で、重複ではない。
+- Mathlib の名前の検索（1 回目の独立照合の指摘を受けて）：
+  - 一般の `DirectLimit` の非単位的な環・代数の構造（`NonUnitalRing` のインスタンス、`DirectLimit.NonUnitalAlgebra.of`）。
+  - `DirectLimit.mk_injective`。
+  - 最初の版は `Module.DirectLimit`（ℂ 加群）だけで組み、「Mathlib に非単位的な代数の直極限の道具が見当たらない」と書いていた。これは誤りだったので、一般の `DirectLimit` で組み直した。
+- 閉じる前の機械的な照合（組み直した版）：全宣言 4483 件、対象 11 件（定理 8 と定義 3。インスタンスは対象外）、候補上位 20。定理は両向き（·2）、定義は 1 回で、8·20·2 + 3·20 = 380 回。
+  - 対象の定理 8 には下書きの `cornerSys_apply` を含む。これが Part 260（PAG264）の `cornerHom_coe` と、定義を開けば同じ文（A）だったので消した。
+  - ほかに一致と出たのは自動生成の congr_simp だけ。
+  - 足した 3 定理：全宣言 4485 件、3·20·2 = 120 回、一致なし。Mathlib の `IsIdempotentElem.one`・`IsIdempotentElem.map` から `ofCorner_one_mul_self` が直ちに出る見込み（照合者の指摘、B）。
+- 独立照合は 3 回（最初の版、組み直した版、足した 3 定理と直した文面の再照合）。
+  - 2 回目の指摘を受けて 3 定理（べき等、順序、有限集合版）を足した。
+  - 3 回目の指摘 11 点（単位元がないことの証明の段の取り方、単射性の段、正規化の効き方、量化など）を直した。
+  - 3 回目の後の直しは主張を狭めるか明確にするもので、補足8の停止の規約の範囲。尾の台帳は空。記録 `records/audit265/`。
+-/
+import PAG264
+
+namespace PAG.Part265
+
+open PAG.Part218 PAG.Part258 PAG.Part264
+
+/-- 系の写像：a ≤ b（a ∣ b）なら角の写像 φ_{a,b}（Part 260 の `cornerHom`、非単位的な代数準同型）。 -/
+noncomputable def cornerSys (a b : Lvl) (h : a ≤ b) : shellAlg a.val →ₙₐ[ℂ] shellAlg b.val :=
+  cornerHom (N := a.val) (M := b.val) h
+
+/-- 恒等の法則：φ_{a,a} = id。 -/
+theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S := by
+  apply Subtype.ext
+  exact cornerOp_self (N := a.val) (S : Module.End ℂ (ZMod a.val → ℂ))
+
+/-- 合成の法則：φ_{b,c} ∘ φ_{a,b} = φ_{a,c}。 -/
+theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
+    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S := by
+  apply Subtype.ext
+  exact cornerOp_comp (N := a.val) (M := b.val) (L := c.val) hab hbc (S : Module.End ℂ (ZMod a.val → ℂ))
+
+/-- **帰納系**：正の整数の整除の順序（Part 254 の `Lvl`）の上で、角の写像は帰納系をなす。 -/
+instance : DirectedSystem (fun a : Lvl => shellAlg a.val)
+    (fun a b h => (cornerSys a b h : shellAlg a.val → shellAlg b.val)) where
+  map_self a S := cornerSys_self a S
+  map_map _ _ _ hab hbc S := cornerSys_comp hab hbc S
+
+/-- 角の写像の帰納極限（Mathlib の一般の `DirectLimit`。非単位的な環の構造と ℂ のスカラー倍を持つ）。 -/
+abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys
+
+/-- 標準の写像 A_a → 極限（非単位的な ℂ 代数準同型）。 -/
+noncomputable def ofCorner (a : Lvl) : shellAlg a.val →ₙₐ[ℂ] CornerLim :=
+  DirectLimit.NonUnitalAlgebra.of _ cornerSys a
+
+/-- 標準の写像の値（商の元）。 -/
+theorem ofCorner_apply (a : Lvl) (S : shellAlg a.val) :
+    ofCorner a S = (⟦⟨a, S⟩⟧ : CornerLim) := rfl
+
+/-- 標準の写像は系の写像と両立する。 -/
+theorem ofCorner_cornerSys {a b : Lvl} (h : a ≤ b) (S : shellAlg a.val) :
+    ofCorner b (cornerSys a b h S) = ofCorner a S := by
+  rw [ofCorner_apply, ofCorner_apply]
+  exact (DirectLimit.eq_of_le (F := fun a : Lvl => shellAlg a.val) (f := cornerSys) ⟨a, S⟩ b h).symm
+
+/-- 各段 A_a は極限に単射で入る。 -/
+theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
+  DirectLimit.mk_injective cornerSys (fun b c h => cornerHom_injective (N := b.val) (M := c.val) h) a
+
+/-- **局所的な単位元**：極限のどの元 x にも、ある a があって、e_a = (φ(1_a) の像) は x = e_a x = x e_a を満たす。 -/
+theorem exists_local_unit (x : CornerLim) :
+    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
+  obtain ⟨a, S, rfl⟩ := DirectLimit.exists_eq_mk cornerSys x
+  refine ⟨a, ?_, ?_⟩
+  · rw [← ofCorner_apply, ← map_mul, one_mul]
+  · rw [← ofCorner_apply, ← map_mul, mul_one]
+
+/-- e_a = ofCorner_a(1) はべき等。 -/
+theorem ofCorner_one_mul_self (a : Lvl) : ofCorner a 1 * ofCorner a 1 = ofCorner a 1 := by
+  rw [← map_mul, one_mul]
+
+/-- a ≤ b なら e_b e_a = e_a = e_a e_b。 -/
+theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
+    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 := by
+  rw [← ofCorner_cornerSys h 1]
+  exact ⟨by rw [← map_mul, one_mul], by rw [← map_mul, mul_one]⟩
+
+/-- **局所的な単位元（有限集合版）**：極限の有限部分集合 F ごとに、べき等元 e_a があって、F のどの元も両側から固定する
+（F ⊆ e_a·極限·e_a。局所的な単位元を持つ環の、有限集合についての定義の形）。 -/
+theorem exists_local_unit_finset (F : Finset CornerLim) :
+    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
+  classical
+  induction F using Finset.induction_on with
+  | empty => exact ⟨⟨1, Nat.one_pos⟩, fun x hx => by simp at hx⟩
+  | insert x F _ ih =>
+    obtain ⟨a, ha⟩ := ih
+    obtain ⟨b, hb⟩ := exists_local_unit x
+    obtain ⟨c, hac, hbc⟩ := (show IsDirectedOrder Lvl from inferInstance).directed a b
+    have mono : ∀ {d : Lvl}, d ≤ c → ∀ y : CornerLim, (ofCorner d 1 * y = y ∧ y * ofCorner d 1 = y) →
+        (ofCorner c 1 * y = y ∧ y * ofCorner c 1 = y) := by
+      intro d hd y hy
+      obtain ⟨l, r⟩ := ofCorner_one_le hd
+      constructor
+      · calc ofCorner c 1 * y = ofCorner c 1 * (ofCorner d 1 * y) := by rw [hy.1]
+          _ = ofCorner d 1 * y := by rw [← mul_assoc, l]
+          _ = y := hy.1
+      · calc y * ofCorner c 1 = (y * ofCorner d 1) * ofCorner c 1 := by rw [hy.2]
+          _ = y * ofCorner d 1 := by rw [mul_assoc, r]
+          _ = y := hy.2
+    refine ⟨c, fun y hy => ?_⟩
+    rcases Finset.mem_insert.mp hy with rfl | hy
+    · exact mono hbc y hb
+    · exact mono hac y (ha y hy)
+
+/-- **大域の単位元はない**：極限には左単位元がない（非単位的）。 -/
+theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x := by
+  rintro ⟨u, hu⟩
+  obtain ⟨c, U, rfl⟩ := DirectLimit.exists_eq_mk cornerSys u
+  let d : Lvl := ⟨2 * c.val, Nat.mul_pos (by norm_num) c.pos⟩
+  have h : c ≤ d := ⟨2, by simp [d, mul_comm]⟩
+  have e := hu (ofCorner d 1)
+  rw [← ofCorner_apply, ← ofCorner_cornerSys h U, ← map_mul, mul_one] at e
+  have e2 : cornerSys c d h U = 1 := ofCorner_injective d e
+  have e3 := congrArg Subtype.val e2
+  change cornerOp (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ)) = 1 at e3
+  have hq := cornerOp_one_mul (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ))
+  rw [e3] at hq
+  have hlt : c.val < d.val := by
+    show c.val < 2 * c.val
+    have := c.pos; omega
+  exact cornerOp_one_ne_one (N := c.val) (M := d.val) h hlt (by simpa using hq)
+
+end PAG.Part265
+
+#print axioms PAG.Part265.cornerSys_self
+#print axioms PAG.Part265.cornerSys_comp
+#print axioms PAG.Part265.ofCorner_apply
+#print axioms PAG.Part265.ofCorner_cornerSys
+#print axioms PAG.Part265.ofCorner_injective
+#print axioms PAG.Part265.exists_local_unit
+#print axioms PAG.Part265.ofCorner_one_mul_self
+#print axioms PAG.Part265.ofCorner_one_le
+#print axioms PAG.Part265.exists_local_unit_finset
+#print axioms PAG.Part265.not_exists_left_one
diff --git a/notes/pag2_pag265_corner_limit.md b/notes/pag2_pag265_corner_limit.md
new file mode 100644
index 0000000..b29ad22
--- /dev/null
+++ b/notes/pag2_pag265_corner_limit.md
@@ -0,0 +1,87 @@
+# アーデル射影幾何 — Part 261（PAG265）：角の写像の帰納系と、その極限の非単位的な代数（短期層の小さいノート、2026-11-19）
+
+（新しいパートでも新しい問いでもない。方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残りを、2026-11-19 12:51 に著者が採用した。基礎文書の第 5 章（索引 5.2・5.5）の材料。
+Lean は PAG265.lean：定理 10、sorry 0、警告 0。#print axioms 10 行はすべて標準の公理の範囲。照合の記録は `records/audit265/`。）
+
+## §1 結果（Lean の文から起こした）
+
+記号：
+- `Lvl`（Part 254（PAG258））は、正の整数を整除で並べた有向な前順序。
+- A_a = `shellAlg a.val`。φ は Part 260（PAG264）の角の写像 `cornerHom`。
+- e_a は A_a の単位元の極限での像。
+
+主な文：
+- **帰納系**：恒等の法則 φ_{a,a} = id（`cornerSys_self`）と合成の法則（`cornerSys_comp`）。この 2 つで `DirectedSystem` のインスタンスになる。
+- **極限**：`CornerLim` は Mathlib の一般の `DirectLimit` による極限。
+  - 遷移写像が非単位的な ℂ 代数準同型なので、Mathlib のインスタンスにより非単位的な環の構造と ℂ のスカラー倍を持つ。
+  - 標準の写像 `ofCorner a : A_a → CornerLim` は非単位的な ℂ 代数準同型で、系の写像と両立する（`ofCorner_cornerSys`）。
+- **各段は単射に入る**（`ofCorner_injective`）。Part 260 の `cornerHom_injective` を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
+- **局所的な単位元**：
+  - 1 元ごと（`exists_local_unit`）：極限のどの元 x にも、ある a があって e_a x = x = x e_a。
+  - e_a はべき等（`ofCorner_one_mul_self`）。a ∣ b なら e_b e_a = e_a = e_a e_b（`ofCorner_one_le`）。
+  - 有限集合ごと（`exists_local_unit_finset`）：有限部分集合 F ごとに、ある a があって、e_a が F のどの元も両側から固定する（F ⊆ e_a·極限·e_a は x = e_a x e_a から直ちに出る。Lean の文ではない）。局所的な単位元を持つ環の、Ánh–Márki の流儀の定義の条件の形。Abrams の流儀（可換な冪等元の集合）との異同と文献の本文との照合は未確認。
+- **大域の単位元はない**（`not_exists_left_one`）：極限には左単位元がない。右単位元がないことは Lean にしていない。
+
+## §2 読み（解釈の層。Lean の文ではない）
+
+- 極限は直極限の側でとった。有限次元の代数を、角への埋め込みで整除の順序全体に並べた和で、完備化は使っていない（§1 の 08:41 の定義：極限でも離散構造の観測を維持する）。
+- e_a（a が整除で大きくなるほど大きい、べき等元の増大列）は、関数のレベルでは「a で周期的な関数への射影」の極限での像。BC の μ_n μ_n^* に当たる形をしている（Part 260 の範囲の読み。Lean の外）。
+- 対比（前の Part の Lean の文との並置）：
+  - 単位元を保ち殻を混ぜない写像の系は、互いに素な段にしかなく（Part 258（PAG262））、その順序は有向でない（Part 259（PAG263））。
+  - 単位元を保たない角の写像の系は、整除の順序全体で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。
+  - 局所的な単位元の 3 つの文は、どの直極限でも成り立つ一般の事実で、「非単位的」という内容を運ぶのは `not_exists_left_one` だけ。
+  - その証明は d = 2c（c が偶数なら素数冪の段）をとるが、c を割らない素数 p で d = pc としても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。効いているのは、N < M のどの段でも φ(1) ≠ 1（`cornerOp_one_ne_one`、gcd によらない）であることと単射性。
+
+## §3 ラベルと範囲
+
+- **［再導出（小さい）］**：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。新規候補はない。A1 とは関係しない。
+- 対照群：形式（帰納系と直極限）だけの文なので、関数体の有限レベルでも同じ形で成り立つ見込み（Part 260 の対照群の範囲。この Part では試していない）。
+- **Lean の外**：
+  - 極限の具体形（Ẑ 上の局所定数関数への作用）と Bost–Connes との対応。
+  - 像が角全体であること（Part 260 でも Lean の外）。
+  - 右単位元がないこと。部分系での同じ文。
+  - 完備化（とらない）。
+
+## §4 内部照合（第 12 の型）
+
+- **着手前**（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った（新しい型を作らなかった）。
+- **閉じる前**（機械的）：
+  - 組み直した版：全宣言 4483 件、対象 11 件（定理 8 と定義 3）、380 回。下書きの `cornerSys_apply` が Part 260 の `cornerHom_coe` と定義を開けば同じ文（A）だったので消した。
+  - 足した 3 定理：120 回、一致なし。
+  - 最初の版：200 回、一致なし。
+- **Mathlib の名前**：最初の版では一般の `DirectLimit` の代数の構造を見落としていた。1 回目の独立照合の指摘で見つけ、組み直した。第 12 の型の教訓（着手前に Mathlib の名前でも検索する）が、今回は照合で補われた形。
+
+## §5 独立照合（第 11 の型）
+
+- **1 回目**（最初の版、`Module.DirectLimit` の ℂ 加群）：偽・空虚なし。
+  - 指摘：Mathlib に一般の `DirectLimit` の非単位的な代数の構造がある可能性。証明の依存先の書き落とし。対比の条件の書き落とし。
+  - 対応：Mathlib で確かめ、組み直した。出力は `outputs/check1_output.md`。
+- **2 回目**（組み直した版）：偽・空虚なし。
+  - 指摘：「局所的な単位元を持つ環」は標準の定義（有限集合ごとに共通のべき等元）より弱い文しか Lean になかった。ほかに文面 9 点。
+  - 対応：3 定理を足し、文面を直した。出力は `outputs/check2_output.md`。
+- **再照合**（足した 3 定理と直した文面）：§6。
+
+## §6 再照合
+
+- 条件：形式文と定義、散文（冒頭の説明）、2 回目の指摘を渡した（Read 3 回、約 414 秒）。出力は `records/audit265/outputs/recheck_output.md`。
+- 足した 3 定理：意図どおり。e_c ≠ e_{2c}、有限性を外すと偽（極限全体なら左単位元になる）などの証人と反例が示された。3 定理は単射性も φ(1) ≠ 1 も使わない一般論。
+- 宣言名の取り違えと、範囲の内外の誤りはなかった。2 回目の指摘 1〜10 は反映されていた。
+- 新しいずれ 11 点を直した（冒頭の説明とこのノート）：
+  1. 単位元がないことの証明の段の取り方（指摘 3 の直しが生んだずれ）。
+  2. 単射性の段の書き落とし。
+  3. 正規化の効き方。
+  4. F ⊆ eRe が Lean の文でないこと。
+  5. Ánh–Márki と Abrams の流儀の違い。
+  6. 積とスカラー倍の両立のインスタンス。
+  7. Part 258 の同値の書き方。
+  8. D 側の量化。
+  9. 件数の内訳。
+  10. 照合の回数。
+  11. End 全体と正規化なしの書き分け。
+- 再照合の後の直しは主張を狭めるか明確にするもので、補足8の停止の規約の範囲。尾の台帳は空。
+
+## §7 収束アラームの報告
+
+- 兆候 4（初等的な部品の組み合わせだけ）：続いている。文書の章に仕える短期層。
+- 兆候 1（自前の名前）：極限は Mathlib の `DirectLimit` をそのまま使い、自前の構成を作らなかった。
+- 文献照合：盲検の問いテストは R-d の推薦の段階（2026-11-19 午前）で実施した。この Part では Mathlib の名前の照合を行った。
```
