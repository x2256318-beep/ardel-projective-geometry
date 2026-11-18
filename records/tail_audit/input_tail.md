# 入力：尾の統合照合（2026-11-18）

照合の対象は、照合を受けていない直し（尾）の3群 T1〜T3 です。各群に、直しの前後の文面と、それが述べる対象の Lean の形式文（全文）を付けます。

## T1：F3 の後の記録だけの直し（Part 258 の閉鎖条件の照合 F3 の後）

直しのスクリプト（前の文面 → 後の文面の組をそのまま含む）：

```python
"""F3 の指摘による最後の直し（記録だけ。照合はここで止める）。形式文は変えない。"""
def apply(p, reps):
    s = open(p, encoding='utf-8').read()
    for a, b in reps:
        assert s.count(a) == 1, (p, s.count(a), a[:60]); s = s.replace(a, b)
    open(p, 'w', encoding='utf-8').write(s)
N = '/home/claude/out185/'; L = '/home/claude/leanwork/pagpkg/'
apply(N + 'pag2_internal_audit_249_256.md', [
 ('- **F2 の後の直し（記録だけ。照合は受けていない）**：', '- **F2 の後の直し（3 回目。Part 258 の閉鎖条件 3 の照合 R3 を受けた。§9）**：'),
 ('PAG.lean（最初の形式化の Part 1）〜PAG252.lean', '最初の形式化の Part 1（PAG.lean）〜PAG252.lean'),
 ('- **判定：新 1〜16 のうち 8 件が直り、6 件は一部、2 件は材料不足で確かめられない（xlsx の差分を渡していなかった）。形式文の変更はない（見た差分の範囲で）。**',
  '- **判定：新 1〜16 のうち 8 件が直り、6 件は一部、2 件は材料不足で確かめられない（新 10 は xlsx の差分を、新 15 は `MechChecksA.lean` とその出力を渡していなかった）。形式文の変更はない（見た差分の範囲で）。** R3 の §2 の 9（「記録だけで直した」の言い方）は直した。10（「付録 A」の残り）は、構築者が全文を検索して、取り違えを説明する文と「付録 A.2」のほかに残りがないことを確かめた（2026-11-14 夜）。'),
 ('  - 「64 定理」が `MechChecksA.lean` の 28 定理の分だけ古い → 92 定理と書いた。',
  '  - 「64 定理」が `MechChecksA.lean` の 28 定理の分だけ古い → 92 定理と書いた。MechChecksA を含む 4 ファイル（MechChecks 44・MechChecksA 28・ManualChecks2 14・SampleC2 6）の .out の `#print axioms` 92 行を数え、公理が propext・Classical.choice・Quot.sound の範囲だけであることを確かめた（`audit_internal/lean/*.out`、2026-11-14 18:4x）。'),
])
apply(N + 'pag2_part252_hartley_gluing.md', [
 ('最初の形式化の Part 3（PAG3.lean。PAG 2.0 より前の最初の形式化のファイルで、鎖に import されていない）', '最初の形式化の Part 3（PAG3.lean。PAG 2.0 より前のファイルで、鎖に import されていない）'),
 ('（B2 の判定。注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。以下は構築者の注記：全体として空虚ではない。法 2 に原始指標がないことは Lean の外。`JH_eq_rootNum_mul` は `JH_eq_rootNum_mul_any` に含まれる。`removal_counterexample_four` の第 1 成分はほかの成分と無関係な証人）。',
  '（B2 の判定。注意：原始性を仮定する 4 文は N = 2 では空虚に成り立つ。`JH_eq_rootNum_mul` は `JH_eq_rootNum_mul_any` に含まれる。`removal_counterexample_four` の第 1 成分はほかの成分と無関係な証人。構築者の注記（B4 の後に足した）：全体として空虚ではない。法 2 に原始指標がないことは Lean の外）。'),
])
apply(N + 'pag2_part255_resolution_discrete_limit.md', [
 ('この行と次の「A2 が挙げたコメント」の行を足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。',
  'この行と次の「A2 が挙げたコメント」の行を足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受け、この行は R2 の指摘で書き直した。書き直しの照合は F3）。B4 の「38 行が §9 にない」は直していない（記録だけの指摘のため）。'),
])
apply(N + 'pag2_part254_full_gluing.md', [
 ('B4 の後に題の「法 M の」とこの行だけを足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受けた）。',
  'B4 の後に題の「法 M の」とこの行だけを足した（この直しは Part 258 の閉鎖条件 2 の照合 R2 を受け、この行は R2 の指摘で書き直した。書き直しの照合は F3）。'),
 ('入力は PAG258.lean の最終版から機械的に起こし', '入力は PAG258.lean（Part 254）の最終版から機械的に起こし'),
])
apply(N + 'pag2_part257_local_factor_decomposition.md', [
 ('- 直したあと、PAG261 の形式文が同じこと、組み立て直した .out が同一であることを確かめた。この直しの後の照合：閉鎖条件の直しの照合（F3）で行う。',
  '- R4 の判定で残ったもの：§3-1 の重複定義の記録に、Part 189・190 の名前なしの同じ式（changeLevel の積）を足していない（内部照合の監査の記録 `pag2_internal_audit_249_256.md` に任せる）。§3-2 の `prod_map_div\'` は Mathlib の List 版が見つからないので残した。#9 の step280 のログは R4 に渡していなかった（ログは `audit257/step280.log`、11/11）。\n- 直したあと、PAG261 の形式文が同じこと、組み立て直した .out が同一であることを確かめた。この直しは閉鎖条件の直しの照合（F3）を受けた（形式文の変更なし、N1〜N7 は直った）。F3 の後に、`phaseA1_listChar` の docstring の繰り返しを直した（記録だけ、照合は受けていない）。'),
])
apply(L + 'PAG261.lean', [('（Lean で示したのは、成分がすべて原始のとき。原始でない指標では、phaseA1 は一般には W と違う）。 -/', '（原始でない指標では、phaseA1 は一般には W と違う。これは Lean の外）。 -/')])
for p, notesec in [(N + 'pag2_part252_hartley_gluing.md', 'B2 の段（B2 の判定と構築者の注記を分けた）'), (N + 'pag2_part256_gluing_cross_term.md', 'PAG260 の冒頭の説明の「範囲」の段の括弧（「（両辺 0 で）」を 1 つの文にまとめた）')]:
    s = open(p, encoding='utf-8').read()
    s += f'''
\n## 閉鎖条件 2 の照合（2026-11-14 夜、Part 258 の閉鎖条件）\n\n- 再照合の記録 §9 の B4 の後の直しを、照合者 R2 が照合した（`pag2_reaudit_252_256.md` §10、出力 `closing258/outputs/R2_output.md`）。このノートにかかわる直し：{notesec}。直しの照合は F3（`closing258/outputs/F3_output.md`）。F3 の後の直しは記録だけで、照合は受けていない。\n'''
    open(p, 'w', encoding='utf-8').write(s)
H = '/home/claude/out/final78/PAG2_handoff_part257.md'
s = open(H, encoding='utf-8').read(); s = s.replace('呼ばない）。 書くときは', '呼ばない）。書くときは'); open(H, 'w', encoding='utf-8').write(s)
print('ok')

```

関係する形式文（PAG261.lean の `phaseA1_listChar` とその docstring、現在の版）：

```lean
/-- 成分がすべて原始なら、UA1 の固有値 phaseA1 も同じ式で分かれる（原始でない指標では、phaseA1 は一般には W と違う。これは Lean の外）。 -/
theorem phaseA1_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hp : ∀ i ∈ l, (χ i).IsPrimitive) :
    PAG.Part258.phaseA1 (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part258.phaseA1 (χ i)).prod := by
  rw [PAG.Part258.phaseA1_of_isPrimitive ((isPrimitive_listChar_iff χ l hl).mpr hp),
    rootNum_listChar χ l hl]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rw [PAG.Part258.phaseA1_of_isPrimitive (hp i hi)]
```

## T2：Part 258（PAG262.lean）の照合者 B の後の直し

### T2-a：Lean の冒頭説明と docstring の差分（< 前、> 後）

```diff
2,3c2,3
< アーデル射影幾何 — Part 258（PAG 2.0）：方向βの前提 — N ∣ M で、引き戻しと両立し殻を混ぜない代数準同型 A_N → A_M があるのは
< gcd(N, M/N) = 1 のときに限る
---
> アーデル射影幾何 — Part 258（PAG 2.0）：N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、
> を満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定）
22c22,23
<    掛け算、φ(E_N) は ε の線形結合 g の畳み込みで、𝓕g は双対殻の上で定数かつ 0・1 値。関係から H の上で g = (1/N)·δ₀、
---
>    掛け算（(i) は S = D_N、f = 1 でだけ使う）、φ(E_N) は ε の線形結合 g の畳み込みで、𝓕g は (3) から双対殻の上で定数、
>    E_N² = E_N から 0・1 値。関係から H の上で g = (1/N)·δ₀、
32c33,36
< 位置づけ：存在の側は既知（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Theorem 3.1。鎖では Part 228）。
---
> 位置づけ：存在の側のテンソル積の同型は既知（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Theorem 3.1。盲検の
> 照合者が読んだもので、私は開いていない。A_N = T(0) は辞書の同一視で、Lean にしていない。鎖では Part 228）。写像の作用素 C⁻¹∘L は
> Part 228 にあり（`map_leftHom_le` で A_a の像が A_{ab} に入る）、Part 236（PAG240）の局所作用素 `locHom` の k = 0 と同じ式（法の型が
> b と b·1 で違う。Lean ではつないでいない）。この Part で新しいのは、条件 (i)(ii) の確認と、不存在・二分法の文。
40,42c44,47
< 閉じる前の照合（全宣言 4339 件、PAG262 の 30 件、候補上位 20、`#dupcheck`・`#defeqcheck` を両向きに 1140 回）：下書きの
< `dind_self_apply` は Part 247（PAG251）の同名の定理と、`rightOp_one` は Part 247 の `rightOp_one'` と同じ文だった（両向きに確認）。
< 2 つとも消して前の鎖のものを使った。`crtConj_shellLift` は Part 228 の `crtConj_shellAlgTensorEquiv_tmul` から直ちに出る（B）。
---
> 閉じる前の照合（全宣言 4339 件、PAG262 の 30 件（定理 27・定義 3）、候補上位 20、定理は `#dupcheck` を両向きに、定義は
> `#defeqcheck` を 1 回で、計 27·20·2 + 3·20 = 1140 回）：下書きの `dind_self_apply` は Part 247（PAG251）の同名の定理と、
> `rightOp_one` は Part 247 の `rightOp_one'` と同じ文だった（両向きに確認）。2 つとも消して前の鎖のものを使い、2 回目
> （4337 件、28 件、1060 回）は下の B の 1 組だけ。`crtConj_shellLift` は Part 228 の `crtConj_shellAlgTensorEquiv_tmul` から直ちに出る（B）。
44,45c49,53
< 同名の定理（各点の形）と同じ内容だと分かったので消した。`conv_single` は Part 107（PAG111）の `conv_single_gen` の左右を入れ替えた形に
< 書き直した。`dTop_eTop_dTop` は Part 247 の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と対の式。
---
> 同名の定理（各点の形）と同じ内容だと分かったので消した（2 回目の後。宣言は 27 件）。`conv_single` は Part 107（PAG111）の
> `conv_single_gen` から 1 行（B）。`dTop_eTop_dTop` は Part 247 の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と
> 対の式。照合者 B の指摘で、さらに言葉で検索して（`chineseRemainder`・核の和）：`castHom_crt_symm` は Part 236（PAG240）の
> `crt_fst_eq_castHom` から直ちに出る（それを使う形に書き直した）。数行で出るもの（C）：`shellLift_dind`・`shellLift_geps`（Part 228 から）、
> `shellLift_injective`、`eTop_mul_self`。使っていなかった `pull_one` を消した。
78c86,87
< /-- CRT の逆の点の、法 a への還元は第 1 成分。 -/
---
> /-- CRT の逆の点の、法 a への還元は第 1 成分。
> 内部照合（2026-11-14）：Part 236（PAG240）の `crt_fst_eq_castHom` から直ちに出る。 -/
81,86c90
<   have h := congrArg Prod.fst ((ZMod.chineseRemainder hab).apply_symm_apply q)
<   rw [← h]
<   set y := (ZMod.chineseRemainder hab).symm q
<   show ZMod.castHom (dvd_mul_right a b) (ZMod a) y =
<     ((ZMod.castHom (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)) (ZMod a × ZMod b)) y).1
<   rw [ZMod.castHom_apply, ZMod.castHom_apply, Prod.fst_zmod_cast]
---
>   rw [← PAG.Part240.crt_fst_eq_castHom hab, RingEquiv.apply_symm_apply]
249,251d252
< 
< /-- 引き戻しの 1 は 1。 -/
< theorem pull_one {N M : ℕ} (hNM : N ∣ M) : PAG.Part201.pull hNM (fun _ : ZMod N => (1 : ℂ)) = fun _ => 1 := rfl

```

### T2-b：ノート `pag2_part258_beta_premise.md` の差分（< 前、> 後）

```diff
1c1
< # アーデル射影幾何 — Part 258（PAG 2.0）：方向βの前提 — N ∣ M で、引き戻しと両立し殻を混ぜない代数準同型 A_N → A_M があるのは gcd(N, M/N) = 1 のときに限る（存在の側は既知、不存在の側は文献が見つからなかった）
---
> # アーデル射影幾何 — Part 258（PAG 2.0）：N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、を満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定。存在の側のテンソル積は既知、不存在の側は文献が見つからなかった）
3c3
< 2026-11-14 夜。PAG262.lean（定理 24 個、定義 3 個）、step281.py（段階 2 の数値、13 組）。
---
> 2026-11-14 夜〜11-15。PAG262.lean（定理 23 個、定義 3 個）、step281.py（段階 2 の数値、13 組）。
15c15,16
<   - sorry 0、警告 0。`#print axioms` 24 行（定理と同数）は標準の公理の範囲です（23 行が [propext, Classical.choice, Quot.sound]、1 行が [propext]）。
---
>   - sorry 0、警告 0。`#print axioms` 23 行（定理と同数）は標準の公理の範囲です（22 行が [propext, Classical.choice, Quot.sound]、1 行が [propext]）。
>   - 照合者 B の見立て（Lean にしていない）：不存在の証明が使うのは (i) の 1 点（S = D_N、f = 1）、(ii) の s = N、φ の積と定数倍だけで、φ(1) = 1 は使わない。したがって単位元を保たない写像や、より弱い仮定での不存在に数行で強められる見込み（確信度 中）。
17c18
<   - (2) と (3) から、φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の掛け算、φ(E_N) は ε の線形結合 g の畳み込みで、フーリエ変換 m = 𝓕g は双対殻の上で定数、値は 0 か 1。
---
>   - (2)（S = D_N、f = 1 の 1 点だけ）と (3) から、φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の掛け算。φ(E_N) は ε の線形結合 g の畳み込みで、フーリエ変換 m = 𝓕g は (3) から双対殻の上で定数、E_N² = E_N から値は 0 か 1。
20c21
< - **読み（解釈の言葉。Lean の文ではない）。** 「見方を変える操作が代数の写像として実現できるか」への答えは、互いに素な段（新しい素数を加える）では「できる（テンソル積の左の因子として）」、同じ素数の深さを上げる段では「(1)〜(3) の意味ではできない」です。したがって、N を整除の順に上げていく A_N の帰納系は、(1)〜(3) の写像では組めません。β（A_N の N → ∞ の極限の代数）を (1)〜(3) の写像の帰納極限として立てる道は、素数冪の段で閉じます。登録 §3 の言葉では「不存在の側」の判定です。ただし、(3) の弱い読み（像が A_M に入るだけ）、単位元を保たない写像、(2) を別の形にした写像は、この答えの外です。
---
> - **読み（解釈の言葉。Lean の文ではない）。** 「見方を変える操作が代数の写像として実現できるか」への答えは、互いに素な段（新しい素数を加える）では「できる（テンソル積の左の因子として）」、同じ素数の指数を上げる段（p ∣ N かつ p ∣ M/N。素数冪でない (6,12) なども含む）では「(1)〜(3) の意味ではできない」です。β（A_N の N → ∞ の極限の代数）を (1)〜(3) の写像の帰納極限として立てる道は、この段で閉じます。整除の順の全体（または整除で共終な部分系）では (1)〜(3) の写像の帰納系は組めない、と読みます（共終な系は指数を上げる段を含む、という短い議論は手計算で、Lean にしていない）。互いに素な段だけの系（無平方数の部分系など）は別です（§4）。登録 §3 の言葉では、この読みのもとでの「不存在の側」の判定で、β の前提全体を閉じるものではありません。(3) の弱い読み（像が A_M に入るだけ）、単位元を保たない写像、(2) を別の形にした写像は、この答えの外です。
22c23
< - **位置づけ。** 存在の側は既知です（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Terwilliger algebras of direct and wreath products of association schemes, Theorem 3.1。鎖では Part 228。確信度：高）。不存在の側は、着手前の盲検の問いテストで文献が見つかりませんでした（確信度：中。見つからなかったというだけ）。議論は初等的です。ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項です。
---
> - **位置づけ。** 存在の側のテンソル積の同型は既知です（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Terwilliger algebras of direct and wreath products of association schemes, Theorem 3.1。盲検の照合者が読んだもので、私は開いていない。A_N = T(0) は辞書の同一視で Lean にしていない。確信度：中〜高）。写像の作用素 C⁻¹∘L は鎖の Part 228 にあり（`map_leftHom_le` で A_a の像が A_{ab} に入る）、Part 236（PAG240）の局所作用素 `locHom` の k = 0 と同じ式です（法の型が b と b·1 で違う。Lean ではつないでいない）。この Part で新しいのは条件 (i)(ii) の確認（Lean）と、不存在・二分法の文です。不存在の側は、着手前の盲検の問いテストで文献が見つかりませんでした（確信度：中。見つからなかったというだけ）。議論は初等的です。ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項です。
37c38
< 4. 対照群：F_q[t]/(t^e) → F_q[t]/(t^{e−1}) でも同じ理由で不存在、互いに素の類似では存在（盲検の手計算。私は計算していない）。したがって答えは ℚ に固有の算術ではなく、群・環の形から決まる（登録 §4 の判定：「β の前提の判定」としての価値は変わらないが、「アーデル射影幾何に固有の内容」としては数えない）。
---
> 4. 対照群：盲検の申告によれば（未確認。確信度は盲検の自己申告で高）、F_q[t]/(t^e) → F_q[t]/(t^{e−1}) でも同じ理由で不存在、互いに素の類似では存在。私は計算していない。盲検の申告が正しければ、答えは ℚ に固有の算術ではなく群・環の形から決まり、登録 §4 の判定では「β の前提の判定」としての価値は変わらないが、「アーデル射影幾何に固有の内容」としては数えない。
51c52
< | 互いに素な段で写像がある | 既知 | Hanaki–Kim–Maekawa Theorem 3.1、鎖の Part 228 |
---
> | 互いに素な段で写像がある | 既知（テンソル積）＋条件 (i)(ii) は Lean で確認 | Hanaki–Kim–Maekawa Theorem 3.1（盲検者の確認）、鎖の Part 228・236 |
59,60c60,61
< | 互いに素な段の写像と条件 2・3 | `shellLift`・`crtConj_shellLift`・`shellLift_pull`・`shellLift_dind`・`shellLift_geps`・`shellLift_injective`・`exists_compatible_hom` | (2,6)・(3,6)・(2,10)・(3,12)・(4,12) で CRT の写像が条件を満たす | 既知 |
< | gcd > 1 で写像はない | `no_compatible_hom`（補助：`dTop_eTop_dTop`・`eTop_mul_self`・`exists_mulLeft_of_mem_span`・`exists_convL_of_mem_span`・`dft_const_on_shells`・`mem_ker_iff`・`sum_ker_stdAddChar`・`p_dvd_div_p`・`sq_x_eq_zero`・`x_mul_N`・`mul_x_ne_zero`・`conv_single`） | (2,4)・(2,8)・(3,9)・(4,8)・(6,12)・(2,12)・(6,18)・(9,27) で全数探索して 0 | 著者の判断事項 |
---
> | 互いに素な段の写像と条件 2・3 | `shellLift`・`crtConj_shellLift`・`shellLift_pull`・`shellLift_dind`・`shellLift_geps`・`shellLift_injective`・`exists_compatible_hom` | (2,6)・(3,6)・(2,10)・(3,12)・(4,12) で CRT の写像が条件を満たす（(4,12) の確認行は照合者 B の後に足した） | 既知＋確認 |
> | gcd > 1 で写像はない | `no_compatible_hom`（補助：`dTop_eTop_dTop`・`eTop_mul_self`・`exists_mulLeft_of_mem_span`・`exists_convL_of_mem_span`・`dft_const_on_shells`・`mem_ker_iff`・`sum_ker_stdAddChar`・`p_dvd_div_p`・`sq_x_eq_zero`・`x_mul_N`・`mul_x_ne_zero`・`conv_single`・`castHom_crt_symm`・`crtLin_pull`） | (2,4)・(2,8)・(3,9)・(4,8)・(6,12)・(2,12)・(6,18)・(9,27) で全数探索して 0 | 著者の判断事項 |
63c64
< | 互いに素な組で CRT 以外の写像もある | Lean にしていない | (2,6)・(2,10)・(4,12) で割り当てが 2 つ | — |
---
> | 互いに素な組で CRT 以外の写像もある | Lean にしていない | (2,6)・(2,10) で {1→2, 2→1}、(4,12) で {1→1, 2→4, 4→2}（ログは照合者 B の後に足した） | — |
69c70
< - 結果は上の表のとおり（13 組）。(2,4) の障害は手計算でも確かめた（A_2 = M_2(ℂ) で、階数 1 のべき等元の像の階数は 2 でなければならないが、φ(E_2) は階数 1 か 3）。
---
> - 結果は上の表のとおり（13 組。うち (6,12)・(2,12)・(6,18)・(9,27)・(4,12) の 5 組は、盲検の答えを見た後に二分法を確かめるために足した）。(2,4) の障害は手計算でも確かめた（A_2 = M_2(ℂ) で、階数 1 のべき等元の像の階数は 2 でなければならないが、φ(E_2) は階数 1 か 3）。
77c78
<   - `rw` の motive の型エラー（gcd の書き換えが `ZMod.val` の暗黙の法まで書き換えた）→ `rwa … at` に変えた。
---
>   - 下書きで、`rw` の motive の型エラー（gcd の書き換えが `ZMod.val` の暗黙の法まで書き換えた）→ `rwa … at` に変えた（その補題は後で前の鎖のものに置き換えたので、最終版には残っていない）。
80,81c81,82
< - 閉じる前の内部照合で、下書きの 3 つの宣言が前の鎖と同じ文・同じ内容だったので消した（§7）。
< - sorry 0、警告 0、`#print axioms` 24 行。鎖全体（PAG.lean〜PAG262.lean）は theorem/lemma 3,574（Part 257 の後の 3,550 に 24 を足した数）。
---
> - 閉じる前の内部照合で、下書きの 3 つの宣言が前の鎖と同じ文・同じ内容だったので消した（§7）。照合者 B の後に、使っていない `pull_one` を消し、`castHom_crt_symm` を Part 236 の `crt_fst_eq_castHom` から示す形に書き直した。
> - sorry 0、警告 0、`#print axioms` 23 行。鎖全体（PAG.lean〜PAG262.lean）は theorem/lemma 3,573（Part 257 の後の 3,550 に 23 を足した数）。
99c100
< - **兆候 4：10 パート連続**（Part 249〜258）。補足7 が予告していたとおり。価値は「前提の判定」（β の前提は (1)〜(3) の読みでは素数冪の段で閉じる）。§7 の規定どおり、次の作業を選ぶときに監査を提案する。
---
> - **兆候 4：10 パート連続**（Part 249〜258）。補足7 が予告していたとおり。価値は「前提の判定」（β を (1)〜(3) の写像の帰納極限として立てる道は、同じ素数の指数を上げる段で閉じる）。§7 の規定どおり、次の作業を選ぶときに監査を提案する。
107c108
< - **閉じる前（1 回目）**：全宣言 4339 件を書き出し（`audit258/internal/Extract4.lean`）、PAG262 の 30 件に候補を上位 20 まで選び、`#dupcheck`・`#defeqcheck` を両向きに 1140 回（`Dup262_round1.out`）。一致：
---
> - **閉じる前（1 回目）**：全宣言 4339 件を書き出し（`audit258/internal/Extract4.lean`）、PAG262 の 30 件（定理 27・定義 3）に候補を上位 20 まで選び、定理は `#dupcheck` を両向きに、定義は `#defeqcheck` を 1 回で、計 27·20·2 + 3·20 = 1140 回（`Dup262_round1.out`）。一致：
112c113,115
< - 3 つ（`dind_self_apply`・`rightOp_one`・`geps_self`）を消して前の鎖のものを使い、`conv_single` を前の鎖の定理から示す形に書き直した。**2 回目**（4337 件、28 件、1060 回）の一致は、記録した B の 1 組だけ。
---
> - 順序：`dind_self_apply`・`rightOp_one` を消して **2 回目**（4337 件、28 件 ＝ 定理 25・定義 3、25·20·2 + 3·20 = 1060 回）を行い、一致は記録した B の 1 組だけ。その後、言葉の検索で `geps_self` を見つけて消し、`conv_single` を前の鎖の定理から示す形（B）に書き直した。
> - **照合者 B の指摘による追加の言葉の検索**（`chineseRemainder`・核の和・双対殻の gcd）：`castHom_crt_symm` は Part 236（PAG240）の `crt_fst_eq_castHom` から直ちに出る（B。それを使う形に書き直した）。数行で出るもの（C）：`shellLift_dind`・`shellLift_geps`（Part 228 の `shellAlgTensorEquiv_dind`/`_geps` と `sum_mulLeft_dind`/`sum_convL_geps` から）、`shellLift_injective`、`eTop_mul_self`。`mem_ker_iff`・`sum_ker_stdAddChar`・`dft_const_on_shells` と同じ文は見つからなかった。
> - **より大きな重なり（照合者 B の後に見つけた）**：Part 236（PAG240）は、互いに素な法のリストの枠組み（`prodList`・`CoprimeList`・`coprime_prodList`・`prodList_eq_prod`・素冪のリスト `ppList`・`prodList_ppList`）と、局所作用素 `locHom`（ι_0(S) = C⁻¹(L(S))、`map_locHom_le` で A_{a_k} の像が A_N に入る）を持っている。この Part の写像の作用素は `locHom` の k = 0 と同じ式（法の型が違うので Lean ではつないでいない）。機械的な候補選びは、型の違う同じ構成を拾えなかった。
115c118
< ## 8. 独立照合
---
> ## 8. 独立照合（2026-11-15）
117c120,131
< （照合の後に書く）
---
> - 照合者 B（新しいエージェント、`audit258/inbox_B/inbox.md` の Read だけ、ツール 2 回、約 209 秒）。入力は PAG262.lean の全文と .out、使った前の鎖の宣言の形式文、このノート（照合の前の版）、着手前の文書の §2〜§5・§8、盲検の出力、step281 のログ。予想は `audit258/expected_before_review.md`。出力はそのまま `audit258/outputs/B_output.md`。
> - **形式文：すべて偽・空虚なし。二分法は登録の受容条件（単位的・強い読み）を字句どおり表す。(ii) の span に t ∤ M を含めても無害**（B の判定、確信度 高）。
> - **直したこと。**
>   - 題を形式文から起こした（Lean とノート）。「方向βの前提」は括弧の中の読みにした。
>   - 「素数冪の段で閉じる」→「同じ素数の指数を上げる段（p ∣ N かつ p ∣ M/N）で、(1)〜(3) の写像の帰納極限として立てる道が閉じる」。帰納系の読みに範囲（共終性の議論は Lean の外、互いに素な段だけの系は別）を書いた。
>   - 不存在の筋で、0・1 値の出所（E_N² = E_N）と、(i) を使うのは 1 点だけであることを書いた。
>   - 対照群の結論を「盲検の申告によれば（未確認）」にした。「既知」の確信度を中〜高にし、テンソル積の同型と (i)(ii) の確認を分けた。
>   - (4,12) の CRT の確認と、2 つ目の割り当てをログに足した。13 組のうち 5 組が盲検の後に足したものであることを書いた。
>   - 内部照合の件数の説明（1140・1060 の内訳、28 件の理由）。§3 の「`rwa`」は下書きのことと書いた。`conv_single` を B として記録した。
>   - 使っていない `pull_one` を消した。追加の言葉の検索で `castHom_crt_symm` を Part 236 から示す形にし、Part 236 の枠組みとの重なりを記録した（§7）。
> - 予想との照合：偽・空虚なし（当たり）、span の点は無害（当たり）、強い読みの書き方と「閉じる」の読みが強すぎる（当たり）、単位元を保つ版に限った点（当たり。B は数行で強められる見込みと指摘）。予想になかったもの：題の起こし方、数値の事後の追加、件数の説明、Part 236 との重なり（これは B の後の検索で見つけた）。
> - 直した後の照合は受けていません（形式文の変更は `pull_one` の削除と `castHom_crt_symm` の証明の書き換えだけ。組み立て直して rc = 0、sorry 0、警告 0、axioms 23 行）。

```

### T2-c：PAG262.lean の現在の全文（形式文の正本）

```lean
/-
アーデル射影幾何 — Part 258（PAG 2.0）：N ∣ M のとき、(i) φ(S) π^* = π^* S、(ii) φ(D_s)・φ(E_s) が D_t・E_t の線形結合、
を満たす単位的な代数準同型 φ : A_N → A_M がある ⇔ gcd(N, M/N) = 1（登録の言葉では「方向βの前提」の判定）

問いの出所：著者側の申し送り補足7（2026-11-14）の決定。登録 `preregistration-part255-beta-premise.md` の問いを、突き合わせの記録
`pag2_beta_registration_check.md` §3 の切り分けで修正して行った（着手前の文書 `pag2_part258_preregistration.md`）。
幾何の言葉での問い（読み）：見方を変える（N を上げる）操作は、代数の側で 1 つの写像として実現できるか。

A_N は Part 214（PAG218）の `shellAlg N`：End(ℂ^{ℤ/N}) の中で D_s（空間の殻 gcd(N, x) = s の指示関数の掛け算、`dind`）と
E_s（双対殻の射影 ε_s の畳み込み、`geps`）が生成する代数。単数の軌道によるアソシエーションスキームの、基点 0 での
Terwilliger 代数 T(0) にあたる（辞書）。「見方」「殻構造と両立」は著者の解釈の層と登録の言葉で、Lean の文には出てこない。
登録の受容条件の Lean での形（この Part での読み）：(1) 代数準同型 φ : A_N →ₐ[ℂ] A_M（単位元を保つ）。(2) 射影と両立：
すべての S ∈ A_N で φ(S) π^* = π^* S（π^* は ℤ/M → ℤ/N に沿った引き戻し、Part 197 の `pull`）。(3) 殻を混ぜない（強い読み）：
φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合。

Lean の文：
1. 存在（gcd(a, b) = 1）：`shellLift`（S ↦ Θ(S ⊗ 1)、Θ は Part 228（PAG232）の `shellAlgTensorEquiv`）。CRT の共役で L(S) に移る
   （`crtConj_shellLift`）。条件 2（`shellLift_pull`）。条件 3 は明示の形 φ(D_s) = Σ_{u ∣ b} D_{su}、φ(E_s) = Σ_{u ∣ b} E_{su}
   （`shellLift_dind`・`shellLift_geps`、s ∣ a）。単射（`shellLift_injective`）。まとめて `exists_compatible_hom`。
2. 不存在（素数 p が N と M/N の両方を割る）：`no_compatible_hom`。使うのは A_N の D_N・E_N と、関係 D_N E_N D_N = (1/N) D_N
   （`dTop_eTop_dTop`）、E_N² = E_N（`eTop_mul_self`）だけ。条件 2・3 から φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の
   掛け算（(i) は S = D_N、f = 1 でだけ使う）、φ(E_N) は ε の線形結合 g の畳み込みで、𝓕g は (3) から双対殻の上で定数、
   E_N² = E_N から 0・1 値。関係から H の上で g = (1/N)·δ₀、
   H の上の指標の和（`sum_ker_stdAddChar`）で数えると、ξ ≡ 1 (mod M/N) の剰余類に 𝓕g = 1 の点がちょうど 1 つ。
   ところが u = 1 + M/p は単数で（(M/p)² ≡ 0）、ξ ↦ uξ はその剰余類と双対殻を保つので、点が 2 つになり矛盾。
3. 二分法：`exists_compatible_hom_iff`（N ∣ M のとき、1・2 の性質の写像がある ⇔ gcd(N, M/N) = 1）。

範囲：Lean の文は単位元を保つ代数準同型（→ₐ）と、条件 3 の強い読みについて。単位元を保たない版（盲検の手計算と数値では、
条件から自動的に単位元を保つ）、条件 3 の弱い読み（像が A_M に入るだけ）、条件 2 を外したとき（登録 §5 の除去テスト）、
対照群 F_q[t]/(t^e) は Lean にしていない。互いに素な組で、CRT の写像のほかにも条件を満たす写像があること（数値：(2,6) で
φ(E_1) = E_3 + E_2）も Lean にしていない。

位置づけ：存在の側のテンソル積の同型は既知（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Theorem 3.1。盲検の
照合者が読んだもので、私は開いていない。A_N = T(0) は辞書の同一視で、Lean にしていない。鎖では Part 228）。写像の作用素 C⁻¹∘L は
Part 228 にあり（`map_leftHom_le` で A_a の像が A_{ab} に入る）、Part 236（PAG240）の局所作用素 `locHom` の k = 0 と同じ式（法の型が
b と b·1 で違う。Lean ではつないでいない）。この Part で新しいのは、条件 (i)(ii) の確認と、不存在・二分法の文。
不存在の側は、着手前の盲検の問いテストで文献が見つからなかった（確信度 中。見つからなかったというだけ）。初等的な議論で、
ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項。A1 は公準のまま。ここでの文は A_N についての代数の事実で、
A1 とは関係しない。

内部照合（着手の前）：Part 228（PAG232）の `shellAlgTensorEquiv`・`leftHom`（互いに素な段のテンソル積）、Part 202（PAG206）の
`mem_geps_pull_iff`（関数のレベルの事実：E^{Nt}_{ts} の固定空間は E^N_s の固定空間の引き戻し）。商に沿った A_N → A_M の
写像の宣言は前の鎖に見つからなかった（網羅ではない）。
閉じる前の照合（全宣言 4339 件、PAG262 の 30 件（定理 27・定義 3）、候補上位 20、定理は `#dupcheck` を両向きに、定義は
`#defeqcheck` を 1 回で、計 27·20·2 + 3·20 = 1140 回）：下書きの `dind_self_apply` は Part 247（PAG251）の同名の定理と、
`rightOp_one` は Part 247 の `rightOp_one'` と同じ文だった（両向きに確認）。2 つとも消して前の鎖のものを使い、2 回目
（4337 件、28 件、1060 回）は下の B の 1 組だけ。`crtConj_shellLift` は Part 228 の `crtConj_shellAlgTensorEquiv_tmul` から直ちに出る（B）。
候補選びの外で、宣言の文を言葉で検索して（`geps N N`・`dind N N`・`Pi.single 0 1`）、下書きの `geps_self` が Part 239（PAG243）の
同名の定理（各点の形）と同じ内容だと分かったので消した（2 回目の後。宣言は 27 件）。`conv_single` は Part 107（PAG111）の
`conv_single_gen` から 1 行（B）。`dTop_eTop_dTop` は Part 247 の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と
対の式。照合者 B の指摘で、さらに言葉で検索して（`chineseRemainder`・核の和）：`castHom_crt_symm` は Part 236（PAG240）の
`crt_fst_eq_castHom` から直ちに出る（それを使う形に書き直した）。数行で出るもの（C）：`shellLift_dind`・`shellLift_geps`（Part 228 から）、
`shellLift_injective`、`eTop_mul_self`。使っていなかった `pull_one` を消した。
-/
import PAG261

open Complex Finset

namespace PAG.Part262


open PAG.Part205 PAG.Part218 PAG.Part232
open ZMod (stdAddChar)
open scoped ZMod

variable {a b : ℕ} [NeZero a] [NeZero b]

/-- 互いに素な a, b で、A_a → A_{ab}、S ↦ Θ(S ⊗ 1)（Θ は Part 228 の `shellAlgTensorEquiv`）。 -/
noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))

theorem shellLift_apply (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab S = shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] (1 : shellAlg b)) := rfl

/-- C(φ(S)) = L(S)（C は CRT の共役）。
内部照合（2026-11-14）：Part 228（PAG232）の `crtConj_shellAlgTensorEquiv_tmul` の T = 1 の場合で、そこから直ちに出る（Lean で確認）。 -/
theorem crtConj_shellLift (hab : a.Coprime b) (S : shellAlg a) :
    crtConj hab (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) := by
  rw [shellLift_apply, crtConj_shellAlgTensorEquiv_tmul]
  have h1 : ((1 : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) = 1 := rfl
  rw [h1, PAG.Part251.rightOp_one' a, mul_one]

omit [NeZero a] [NeZero b] in
/-- CRT の逆の点の、法 a への還元は第 1 成分。
内部照合（2026-11-14）：Part 236（PAG240）の `crt_fst_eq_castHom` から直ちに出る。 -/
theorem castHom_crt_symm (hab : a.Coprime b) (q : ZMod a × ZMod b) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) ((ZMod.chineseRemainder hab).symm q) = q.1 := by
  rw [← PAG.Part240.crt_fst_eq_castHom hab, RingEquiv.apply_symm_apply]

omit [NeZero a] [NeZero b] in
theorem crtLin_pull (hab : a.Coprime b) (f : ZMod a → ℂ) (q : ZMod a × ZMod b) :
    crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) q = f q.1 := by
  rw [crtLin_apply, PAG.Part201.pull_apply, castHom_crt_symm]

/-- **条件 2（射影との両立）**：φ(S)(π^* f) = π^*(S f)（π : ℤ/ab → ℤ/a）。 -/
theorem shellLift_pull (hab : a.Coprime b) (S : shellAlg a) (f : ZMod a → ℂ) :
    (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
      PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f) := by
  apply (crtLin hab).injective
  have h1 : ∀ (T : Module.End ℂ (ZMod (a * b) → ℂ)) (g : ZMod (a * b) → ℂ),
      crtLin hab (T g) = crtConj hab T (crtLin hab g) := by
    intro T g; rw [crtConj_apply, LinearEquiv.symm_apply_apply]
  rw [h1, crtConj_shellLift]
  funext p
  rw [leftOp_apply, crtLin_pull]
  have h2 : (fun x : ZMod a => crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) (x, p.2)) = f := by
    funext x; rw [crtLin_pull]
  rw [h2]

set_option synthInstance.maxHeartbeats 200000 in
/-- **条件 3（殻と両立、D）**：φ(D_s) = Σ_{u ∣ b} D_{su}（s ∣ a）。 -/
theorem shellLift_dind (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, LinearMap.mulLeft ℂ (dind (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, mulLeft_dind_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_mulLeft_dind b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_dind hab hs (Nat.dvd_of_mem_divisors hu)

set_option synthInstance.maxHeartbeats 200000 in
/-- **条件 3（殻と両立、E）**：φ(E_s) = Σ_{u ∣ b} E_{su}（s ∣ a）。 -/
theorem shellLift_geps (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, PAG.Part15.convL (geps (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, convL_geps_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_convL_geps b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_geps hab hs (Nat.dvd_of_mem_divisors hu)

/-- φ は単射。 -/
theorem shellLift_injective (hab : a.Coprime b) : Function.Injective (shellLift hab) := by
  intro S S' h
  apply Subtype.ext
  apply leftHom_injective a b
  rw [leftHom_apply, leftHom_apply, ← crtConj_shellLift hab, ← crtConj_shellLift hab, h]

/-- **存在（互いに素な段）**：gcd(a, b) = 1 なら、代数準同型 φ : A_a → A_{ab} で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものがある。 -/
theorem exists_compatible_hom (hab : a.Coprime b) :
    ∃ φ : shellAlg a →ₐ[ℂ] shellAlg (a * b),
      (∀ (S : shellAlg a) (f : ZMod a → ℂ),
        (φ S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
          PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind (a * b) t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps (a * b) t))) := by
  refine ⟨shellLift hab, shellLift_pull hab, fun s => ?_, fun s => ?_⟩
  · by_cases hs : s ∣ a
    · rw [shellLift_dind hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, mulLeft_dind_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show LinearMap.mulLeft ℂ (dind a s) = 0
        rw [dind_eq_zero_of_not_dvd hs]; exact LinearMap.mulLeft_zero_eq_zero ℂ _
      rw [h0, map_zero]
      exact Submodule.zero_mem _
  · by_cases hs : s ∣ a
    · rw [shellLift_geps hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, convL_geps_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show PAG.Part15.convL (geps a s) = 0
        rw [geps_eq_zero_of_not_dvd hs, map_zero]
      rw [h0, map_zero]
      exact Submodule.zero_mem _




/-! ### 不存在の側の準備 -/

/-- δ との畳み込み：g ⋆ δ₀ = g。
内部照合（2026-11-14）：Part 107（PAG111）の `conv_single_gen`（δ₀ ⋆ g = g）の左右を、Part 15 の `conv_comm` で入れ替えたもの。 -/
theorem conv_single (M : ℕ) [NeZero M] (g : ZMod M → ℂ) :
    PAG.Part15.conv g (Pi.single 0 1) = g := by
  rw [PAG.Part15.conv_comm]; exact PAG.Part111.conv_single_gen g

/-- A_N の中の D_N（{0} の指示関数の掛け算）。 -/
noncomputable def dTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, mulLeft_dind_mem N N⟩
/-- A_N の中の E_N（定数 1/N の畳み込み）。 -/
noncomputable def eTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, convL_geps_mem N N⟩

/-- **A_N の関係**：D_N E_N D_N = (1/N) D_N。
内部照合（2026-11-14）：Part 247（PAG251）の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と対の式。前の鎖に同じ文は見つからなかった。 -/
theorem dTop_eTop_dTop (N : ℕ) [NeZero N] :
    dTop N * eTop N * dTop N = (N : ℂ)⁻¹ • dTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f; funext x
  show dind N N x * PAG.Part15.conv (geps N N) (dind N N * f) x = (N : ℂ)⁻¹ * (dind N N x * f x)
  rw [show geps N N = fun _ => (N : ℂ)⁻¹ from funext (PAG.Part243.geps_self N)]
  by_cases hx : x = 0
  · subst hx
    unfold PAG.Part15.conv
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · simp [PAG.Part251.dind_self_apply]
    · intro y _ hy
      simp [PAG.Part251.dind_self_apply, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [PAG.Part251.dind_self_apply, hx]

/-- **E_N はべき等**。 -/
theorem eTop_mul_self (N : ℕ) [NeZero N] : eTop N * eTop N = eTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f
  show PAG.Part15.conv (geps N N) (PAG.Part15.conv (geps N N) f) = PAG.Part15.conv (geps N N) f
  rw [← PAG.Part89.conv_assoc', geps_conv_geps]; simp

/-- D の線形結合は掛け算の作用素。 -/
theorem exists_mulLeft_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    ∃ h : ZMod M → ℂ, T = LinearMap.mulLeft ℂ h := by
  have hle : Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)) ≤
      LinearMap.range (LinearMap.mul ℂ (ZMod M → ℂ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨dind M t, rfl⟩
  obtain ⟨h, hh⟩ := hle hT
  exact ⟨h, hh.symm⟩

/-- E の線形結合は、ε の線形結合 g の畳み込み。 -/
theorem exists_convL_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :
    ∃ g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t), T = PAG.Part15.convL g := by
  have heq : (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) =
      (PAG.Part15.convL : (ZMod M → ℂ) →ₗ[ℂ] _) '' (Set.range fun t : ℕ => geps M t) := by
    rw [← Set.range_comp]; rfl
  rw [heq, Submodule.span_image] at hT
  obtain ⟨g, hg, rfl⟩ := hT
  exact ⟨g, hg, rfl⟩

/-- ε の線形結合のフーリエ変換は、双対殻の上で定数（gcd(M, ξ) だけで決まる）。 -/
theorem dft_const_on_shells (M : ℕ) [NeZero M] {g : ZMod M → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t)) (ξ ξ' : ZMod M)
    (h : Nat.gcd M ξ.val = Nat.gcd M ξ'.val) : 𝓕 g ξ = 𝓕 g ξ' := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [dft_geps]; unfold dind; rw [h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
  | smul c x _ hx => rw [map_smul, Pi.smul_apply, Pi.smul_apply, hx]

/-- 核 H = ker(ℤ/M → ℤ/N) の元は N の倍数。 -/
theorem mem_ker_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (y : ZMod M) :
    ZMod.castHom hNM (ZMod N) y = 0 ↔ ∃ c : ZMod M, y = (N : ZMod M) * c := by
  constructor
  · intro hy
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨(c : ZMod M), ?_⟩
    rw [← ZMod.natCast_zmod_val y, hc]; push_cast; ring
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- **H の上の指標の和**：Σ_{y ∈ H} ψ(a y) = [a·N = 0]·|H|。 -/
theorem sum_ker_stdAddChar {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : ZMod M) :
    ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0), stdAddChar (a * y) =
      if a * (N : ZMod M) = 0 then ((univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0)).card : ℂ)
      else 0 := by
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hH
  by_cases ha : a * (N : ZMod M) = 0
  · simp only [ha, ↓reduceIte]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_ker_iff hNM y).mp (Finset.mem_filter.mp hy).2
    rw [← mul_assoc, ha, zero_mul, AddChar.map_zero_eq_one]
  · simp only [ha, ↓reduceIte]
    set y0 : ZMod M := (N : ZMod M)
    have hy0 : stdAddChar (a * y0) ≠ 1 := by
      intro h1
      apply ha
      rw [← AddChar.map_zero_eq_one (stdAddChar (N := M))] at h1
      exact ZMod.injective_stdAddChar h1
    have hshift : ∑ y ∈ H, stdAddChar (a * (y + y0)) = ∑ y ∈ H, stdAddChar (a * y) := by
      refine Finset.sum_equiv (Equiv.addRight y0) (fun y => ?_) (fun y _ => rfl)
      simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, map_add]
      have : ZMod.castHom hNM (ZMod N) y0 = 0 := by
        rw [map_natCast, ZMod.natCast_self]
      rw [this, add_zero]
    have hmul : ∑ y ∈ H, stdAddChar (a * (y + y0)) = stdAddChar (a * y0) * ∑ y ∈ H, stdAddChar (a * y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
    have h0 : (stdAddChar (a * y0) - 1) * ∑ y ∈ H, stdAddChar (a * y) = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hy0
    · exact h

/-- p ∣ N、p ∣ M/N なら p² ∣ M、したがって p ∣ M/p。 -/
theorem p_dvd_div_p {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) : p ∣ M / p := by
  have hM : M = N * (M / N) := (Nat.mul_div_cancel' hNM).symm
  have hpp : p * p ∣ M := by rw [hM]; exact Nat.mul_dvd_mul hpN hpk
  exact Nat.dvd_div_of_mul_dvd hpp

/-- x = M/p（ℤ/M の中）で x² = 0。 -/
theorem sq_x_eq_zero {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) :
    ((M / p : ℕ) : ZMod M) * ((M / p : ℕ) : ZMod M) = 0 := by
  obtain ⟨r, hr⟩ := p_dvd_div_p hNM hpN hpk
  have hpM : p ∣ M := (hpN.trans hNM)
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨r, ?_⟩
  calc M / p * (M / p) = M / p * (p * r) := by rw [← hr]
    _ = M / p * p * r := by ring
    _ = M * r := by rw [Nat.div_mul_cancel hpM]

/-- x·N = 0（p ∣ N）。 -/
theorem x_mul_N {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) :
    ((M / p : ℕ) : ZMod M) * (N : ZMod M) = 0 := by
  have hpM : p ∣ M := (hpN.trans hNM)
  obtain ⟨c, hc⟩ := hpN
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨c, ?_⟩
  calc M / p * N = M / p * (p * c) := by rw [← hc]
    _ = M / p * p * c := by ring
    _ = M * c := by rw [Nat.div_mul_cancel hpM]

/-- (ξ − 1)·N = 0（ξ ≡ 1 mod M/N）なら ξ·x ≠ 0（p ∤ ξ）。 -/
theorem mul_x_ne_zero {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) (ξ : ZMod M) (hξ : (ξ - 1) * (N : ZMod M) = 0) :
    ξ * ((M / p : ℕ) : ZMod M) ≠ 0 := by
  intro h0
  have hpM : p ∣ M := (hpN.trans hNM)
  set v := ξ.val
  have hξv : ((v : ℕ) : ZMod M) = ξ := ZMod.natCast_zmod_val ξ
  -- p ∣ v
  have h1 : p ∣ v := by
    rw [← hξv, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
    have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos
    have h0' : M / p * p ∣ M / p * v := by
      rw [Nat.div_mul_cancel hpM, mul_comm (M / p)]; exact h0
    exact Nat.dvd_of_mul_dvd_mul_left hpos h0'
  -- p ∣ v − 1（整数で）
  have h2 : (p : ℤ) ∣ (v : ℤ) - 1 := by
    have e : (((((v : ℤ) - 1) * (N : ℤ)) : ℤ) : ZMod M) = 0 := by
      push_cast; rw [hξv]; exact hξ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at e
    have hM : (M : ℤ) = (N : ℤ) * ((M / N : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hNM).symm
    rw [hM, mul_comm ((v : ℤ) - 1)] at e
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hk : ((M / N : ℕ) : ℤ) ∣ (v : ℤ) - 1 := (mul_dvd_mul_iff_left hN0).mp e
    exact (Int.natCast_dvd_natCast.mpr hpk).trans hk
  have h3 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr h1) h2
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3)

/-- **不存在（gcd(N, M/N) > 1 の段）**：素数 p が N と M/N の両方を割るなら、代数準同型 φ : A_N → A_M で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものはない。
証明に使うのは s = N の D_N・E_N と、A_N の関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけ。 -/
theorem no_compatible_hom {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) :
    ¬ ∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) := by
  rintro ⟨φ, h2, hD, hE⟩
  obtain ⟨h, hh⟩ := exists_mulLeft_of_mem_span M (hD N)
  obtain ⟨g, hg, hgg⟩ := exists_convL_of_mem_span M (hE N)
  change (φ (dTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hh
  change (φ (eTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hgg
  -- φ(D_N) は H = ker(ℤ/M → ℤ/N) の指示関数の掛け算
  have hH : ∀ y, h y = dind N N (ZMod.castHom hNM (ZMod N) y) := by
    intro y
    have e := congrFun (h2 (dTop N) (fun _ => 1)) y
    rw [hh] at e
    simpa [PAG.Part201.pull_apply, dTop] using e
  -- φ(E_N) はべき等なので、m = 𝓕 g は 0 か 1
  have hidem : PAG.Part15.conv g g = g := by
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (eTop_mul_self N)
    simp only [map_mul, Subalgebra.coe_mul, hgg] at e
    have e2 := LinearMap.congr_fun e (Pi.single 0 1)
    simpa [PAG.Part15.convL_apply, conv_single] using e2
  set m := 𝓕 g with hm
  have hm01 : ∀ ξ, m ξ = 0 ∨ m ξ = 1 := by
    intro ξ
    have e := congrFun (congrArg 𝓕 hidem) ξ
    rw [PAG.Part16.dft_conv, Pi.mul_apply] at e
    have : m ξ * (m ξ - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  -- 関係 D_N E_N D_N = (1/N) D_N を φ で送り、δ₀ に当てる：H の上で g = (1/N)·δ₀
  have hδ : h * Pi.single 0 1 = Pi.single 0 1 := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp [hH, PAG.Part251.dind_self_apply]
    · simp [hz]
  have hgH : ∀ y, ZMod.castHom hNM (ZMod N) y = 0 → g y = (N : ℂ)⁻¹ * (if y = 0 then 1 else 0) := by
    intro y hy
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (dTop_eTop_dTop N)
    simp only [map_mul, map_smul, Subalgebra.coe_mul, Subalgebra.coe_smul, hh, hgg] at e
    have e2 := congrFun (LinearMap.congr_fun e (Pi.single 0 1)) y
    have hy1 : h y = 1 := by rw [hH, hy, PAG.Part251.dind_self_apply]; simp
    have key1 : ∀ F : ZMod M → ℂ, (LinearMap.mulLeft ℂ h * PAG.Part15.convL g * LinearMap.mulLeft ℂ h) F =
        h * PAG.Part15.conv g (h * F) := fun F => rfl
    have key2 : ∀ F : ZMod M → ℂ, ((N : ℂ)⁻¹ • LinearMap.mulLeft ℂ h) F = (N : ℂ)⁻¹ • (h * F) := fun F => rfl
    rw [key1, key2, hδ, conv_single, Pi.mul_apply, Pi.smul_apply, hy1, one_mul, smul_eq_mul] at e2
    rw [e2]
    by_cases hy0 : y = 0
    · subst hy0; simp
    · simp [hy0]
  -- フーリエの逆変換
  have hginv : ∀ y, g y = (M : ℂ)⁻¹ * ∑ ξ, stdAddChar (ξ * y) * m ξ := by
    intro y
    have e : 𝓕⁻ m = g := by rw [hm]; exact (ZMod.dft).symm_apply_apply g
    rw [← e, ZMod.invDFT_apply]
    simp [smul_eq_mul]
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hHdef
  set C1 := univ.filter (fun ξ : ZMod M => (ξ - 1) * (N : ZMod M) = 0) with hC1def
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- 数え上げ：|H|·Σ_{ξ ≡ 1 (mod M/N)} m(ξ) = M/N
  have hS1 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (M : ℂ) * (N : ℂ)⁻¹ := by
    rw [Finset.sum_eq_single (0 : ZMod M)]
    · rw [hgH 0 (map_zero _)]; simp
    · intro y hyH hy0
      rw [hgH y (Finset.mem_filter.mp hyH).2]; simp [hy0]
    · intro h0
      have h0H : (0 : ZMod M) ∈ H := by
        rw [hHdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, map_zero _⟩
      exact absurd h0H h0
  have hS2 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (H.card : ℂ) * ∑ ξ ∈ C1, m ξ := by
    have step : ∀ y, stdAddChar (-y) * ((M : ℂ) * g y) = ∑ ξ, m ξ * stdAddChar ((ξ - 1) * y) := by
      intro y
      rw [hginv, ← mul_assoc (M : ℂ), mul_inv_cancel₀ hM, one_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [sub_mul, one_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun y _ => step y), Finset.sum_comm]
    have hinner : ∀ ξ, ∑ y ∈ H, m ξ * stdAddChar ((ξ - 1) * y) =
        m ξ * (if (ξ - 1) * (N : ZMod M) = 0 then (H.card : ℂ) else 0) := by
      intro ξ; rw [← Finset.mul_sum]; congr 1; exact sum_ker_stdAddChar hNM (ξ - 1)
    rw [Finset.sum_congr rfl (fun ξ _ => hinner ξ), hC1def, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    split_ifs <;> ring
  have hcard : (H.card : ℂ) * N = M := by
    have := PAG.Part201.card_ker_cast (N := N) (N' := M) hNM
    exact this
  have hC1 : ∑ ξ ∈ C1, m ξ = 1 := by
    have e := hS2.symm.trans hS1
    have hHc : (H.card : ℂ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; exact hM hcard.symm
    have : (H.card : ℂ) * ∑ ξ ∈ C1, m ξ = (H.card : ℂ) * 1 := by
      rw [e, ← hcard]; field_simp
    exact mul_left_cancel₀ hHc this
  have hS : ∑ ξ ∈ C1, m ξ = ((C1.filter (fun ξ => m ξ = 1)).card : ℂ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter (fun ξ => m ξ = 1)]
    apply Finset.sum_congr rfl
    intro ξ _
    rcases hm01 ξ with h0 | h1
    · simp [h0]
    · simp [h1]
  have hone : (C1.filter (fun ξ => m ξ = 1)).card = 1 := by
    have := hS.symm.trans hC1
    exact_mod_cast this
  obtain ⟨ξ0, hξ0⟩ := Finset.card_eq_one.mp hone
  have hξ0mem : ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by rw [hξ0]; exact Finset.mem_singleton_self _
  -- もう 1 つの元 ξ1 = (1 + M/p)·ξ0
  set x : ZMod M := ((M / p : ℕ) : ZMod M) with hx
  have hx2 : x * x = 0 := sq_x_eq_zero hNM hpN hpk
  have hxN : x * (N : ZMod M) = 0 := x_mul_N hNM hpN
  let u : (ZMod M)ˣ := ⟨1 + x, 1 - x, by linear_combination (-1 : ZMod M) * hx2,
    by linear_combination (-1 : ZMod M) * hx2⟩
  have hξ1mem : (u : ZMod M) * ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by
    simp only [hC1def, Finset.mem_filter, Finset.mem_univ, true_and] at hξ0mem ⊢
    refine ⟨?_, ?_⟩
    · show ((1 + x) * ξ0 - 1) * (N : ZMod M) = 0
      linear_combination hξ0mem.1 + ξ0 * hxN
    · rw [← hξ0mem.2]
      exact dft_const_on_shells M hg _ _ (PAG.Part207.gcd_val_unit_mul M u ξ0)
  have hne : (u : ZMod M) * ξ0 ≠ ξ0 := by
    intro e
    have hξ0C : (ξ0 - 1) * (N : ZMod M) = 0 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hξ0mem).1).2
      exact this
    apply mul_x_ne_zero hNM hp hpN hpk ξ0 hξ0C
    have e' : (1 + x) * ξ0 = ξ0 := e
    linear_combination e'
  have : (u : ZMod M) * ξ0 ∈ ({ξ0} : Finset (ZMod M)) := hξ0 ▸ hξ1mem
  exact hne (Finset.mem_singleton.mp this)


/-! ### 二分法 -/

/-- **二分法**：N ∣ M のとき、(i)(ii) を満たす代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) := by
  constructor
  · intro hex
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    exact no_compatible_hom hNM hp (hpd.trans (Nat.gcd_dvd_left _ _)) (hpd.trans (Nat.gcd_dvd_right _ _)) hex
  · intro hc
    rcases hNM with ⟨k, rfl⟩
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    rw [Nat.mul_div_cancel_left k hN0] at hc
    have : NeZero k := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
    exact exists_compatible_hom hc

end PAG.Part262


```

## T3：Part 259（PAG263.lean）の照合者 B の後の直しと、照合を受けていない記録

### T3-a：PAG263.lean の差分（< 照合者 B が見た版、> 現在）

```diff
1d0
< 
14,21c13,26
< 1. 互いに素な段の順序 `UDvd`（N ∣ M かつ gcd(N, M/N) = 1）：反射的（`udvd_refl`）・推移的（`udvd_trans`）だが
<    有向でない。素数 p について p と p² の共通の上界がない（`not_directed_udvd`）。
< 2. 生成元 D_s・E_s で一致する A_N からの代数準同型は等しい（`shellAlg_hom_ext`）。(i)(ii) から φ(D_s) は
<    一意に決まる（`compat_dind_unique`。N ∣ M だけで、互いに素は要らない）。
< 3. (i)(ii)(iii) を満たす写像は高々 1 つ（`compatF_unique`）。`shellLift`（φ(S) = S ⊗ 1）はフーリエと両立し
<    （`shellLift_fC`）、(i)(ii)(iii) を満たす（`compatF_shellLift`）。gcd(a, b) = 1 なら (i)(ii)(iii) を満たすのは
<    `shellLift` だけ（`compatF_iff_eq_shellLift`）。N ∣ M のとき、(i)(ii)(iii) を満たす写像がちょうど 1 つあるのは
<    gcd(N, M/N) = 1 のとき、かつそのときに限る（`existsUnique_compatF_iff`）。
---
> 1. 互いに素な段の順序 `UDvd`（N ∣ M かつ gcd(N, M/N) = 1。古典的な「ユニタリ約数」の関係 N ∥ M。
>    E. Cohen, Math. Z. 74 (1960) 66–80）：N > 0 で反射的（`udvd_refl`）、推移的（`udvd_trans`）。Part 216 の層
>    `InLayer` で c = d = N とした場合と同じ（`udvd_iff_inLayer`、N > 0）。素数 p について p と p² の共通の上界がなく
>    （`not_directed_udvd`）、したがって ℕ の上で有向でない（`not_isDirected_udvd`）。
> 2. 生成元 D_s・E_s で一致する A_N からの代数準同型は等しい（`shellAlg_hom_ext`）。(i)(ii) の D の側から φ(D_s) は
>    一意に決まる（`compat_dind_unique`。文は N ∣ M だけを仮定するが、gcd(N, M/N) ≠ 1 なら Part 258 により (i)(ii) を
>    満たす φ はないので、その場合は空虚に真）。
> 3. 一意性：(i)(ii)(iii) を満たす写像は高々 1 つ（`compatF_unique`）。これは φ(D_s) の一意性を (iii) で E の側へ
>    運ぶだけの、ほぼ即座の帰結である（(ii) の E の側も互いに素も使わない）。同じ理由で (ii) の E の側は (i)、(ii) の
>    D の側、(iii) から出る（`compatF_of_dind`）。内容があるのは存在の側：`shellLift`（φ(S) = S ⊗ 1）がフーリエと
>    両立すること（`shellLift_fC`）。gcd(a, b) = 1 なら (i)(ii)(iii) を満たすのは `shellLift` だけ
>    （`compatF_iff_eq_shellLift`）。N ∣ M のとき、(i)(ii)(iii) を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1
>    （`existsUnique_compatF_iff`）。互いに素でないときに成り立たないのは、(i)(ii) を満たす写像が 1 つもないから
>    （Part 258）で、複数あるからではない。
25,28c30,35
< 5. (iii) を外すと一意でない：gcd(2, b) = 1、1 < b のとき、A_2 の自己同型 ψ(S) = χ S χ⁻¹（χ(x) = (−1)^x、
<    `twist2`。D_s を固定し E_1 と E_2 を入れ替える）を使った φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))（`twLift`、
<    Θ は Part 228 の `shellAlgTensorEquiv`）は (i)(ii) を満たし（`compat_twLift`）、`shellLift` と異なる
<    （`twLift_ne_shellLift`）。したがって (i)(ii) を満たす A_2 → A_{2b} は一意でない（`not_existsUnique_compat`）。
---
> 5. (iii) を外すと一意でない場合がある（a = 2 の例）：gcd(2, b) = 1、1 < b のとき、A_2 の自己同型（対合、
>    `twist2_twist2`・`twist2_bijective`）ψ(S) = χ S χ⁻¹（χ(x) = (−1)^x、`twist2`。D_s を固定し E_1 と E_2 を入れ替える）
>    を使った φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))（`twLift`、Θ は Part 228 の `shellAlgTensorEquiv`）は (i)(ii) を
>    満たし（`compat_twLift`）、`shellLift` と異なる（`twLift_ne_shellLift`）。したがって (i)(ii) を満たす A_2 → A_{2b}
>    は一意でない（`not_existsUnique_compat`）。Lean が示すのはこの場合だけ。R1 の査定の数値（9 組）では、a が奇数なら
>    (i)(ii) だけで一意で、(iii) が効くのは a が偶数のときだけと見られる（Lean にしていない）。
31c38,39
<    （`sqLim_of_injective`）。(i) を満たす写像は単射（`compat_injective`）。
---
>    （`sqLim_of_injective`。遷移写像の単射性 `compat_injective` からほぼ自動的に出る）。この系は、極大な有向部分系
>    （各素数の指数を 1 つに固定したもの）のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。
33,35c41,45
< Lean にしていないこと：一意でない写像の個数（数値の観察では a が偶数なら 2^{d(b)−1}、奇数なら 1。R1 の査定 §2）、
< a が 2 以外の偶数の場合の捩れ。`sqLim` の代数の構造と、それが制限テンソル積 ⊗'_p A_p に同型であること。
< 他の有向な部分系（各素数の指数を固定したもの）。どの有向な部分系も整除の順序で共終でないこと（初等的）。
---
> Lean にしていないこと：一意でない写像の個数（数値の観察では a が偶数なら 2^{d(b)−1}、奇数なら 1）、a が 2 以外の
> 偶数の場合の捩れ、a が奇数での (i)(ii) だけによる一意性。`sqLim` の代数の構造と、それが制限テンソル積 ⊗'_p A_p に
> 同型であること。他の有向な部分系。どの有向な部分系も整除の順序で共終でないこと（初等的）。照合 B が手計算で示した
> (iii) の言い換え（𝓕⁻¹ π^* 𝓕 は双対側の部分群の埋め込み ι_* なので、(i)(iii) から φ(S) ι_* = ι_* S。逆向きも
> 成り立つ見込み。確信度：中）。
92a103,108
> /-- **有向でない**（照合 B の指摘で追加）：ℕ の上の UDvd は有向でない（p = 2 の場合）。 -/
> theorem not_isDirected_udvd : ¬ IsDirected ℕ UDvd := by
>   intro h
>   obtain ⟨M, h1, h2⟩ := h.directed 2 (2 ^ 2)
>   exact not_udvd_and_udvd_sq Nat.prime_two ⟨h1, h2⟩
> 
183a200,225
> /-- フーリエ共役は D_t の張る空間を E_t の張る空間に移す（補助）。 -/
> theorem fourierConj_mem_spanE {T : Module.End ℂ (ZMod M → ℂ)}
>     (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
>     fourierConj M T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
>   have h : (Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))).map
>       (fourierConj M).toLinearMap =
>       Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
>     rw [Submodule.map_span, ← Set.range_comp]
>     congr 2
>     funext t
>     exact fourierConj_mulLeft_dind M t
>   rw [← h]
>   exact Submodule.mem_map_of_mem hT
> 
> /-- **(ii) の E の側は余分**（照合 B の指摘で追加）：(i)、(ii) の D の側、(iii) から CompatF が出る。 -/
> theorem compatF_of_dind (hNM : N ∣ M) {φ : shellAlg N →ₐ[ℂ] shellAlg M}
>     (h1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
>       (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
>         PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
>     (h2 : ∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
>       Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
>     (h3 : ∀ S : shellAlg N, φ (fC N S) = fC M (φ S)) : CompatF hNM φ := by
>   refine ⟨⟨h1, h2, fun s => ?_⟩, h3⟩
>   rw [← fC_dind, h3, fC_coe]
>   exact fourierConj_mem_spanE (h2 s)
> 
427a470,478
> /-- χ の共役は対合。 -/
> theorem chiConj_chiConj (T : Module.End ℂ (ZMod 2 → ℂ)) : chiConj (chiConj T) = T := by
>   apply LinearMap.ext; intro h; funext x
>   rw [chiConj_apply, chiConj_apply]
>   have hc : chi2 * (chi2 * h) = h := by
>     funext y; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
>   simp only [Pi.mul_apply]
>   rw [hc, ← mul_assoc, chi2_mul_self, one_mul]
> 
429,436c480
<   have hh : ∀ T, chiConj (chiConj T) = T := by
<     intro T; apply LinearMap.ext; intro h; funext x
<     rw [chiConj_apply, chiConj_apply]
<     have hc : chi2 * (chi2 * h) = h := by
<       funext y; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
<     simp only [Pi.mul_apply]
<     rw [hc, ← mul_assoc, chi2_mul_self, one_mul]
<   rw [← chiConj_geps_two, hh]
---
>   rw [← chiConj_geps_two, chiConj_chiConj]
460a505,511
> 
> /-- ψ は対合（照合 B の指摘で追加。したがって A_2 の自己同型）。 -/
> theorem twist2_twist2 (S : shellAlg 2) : twist2 (twist2 S) = S :=
>   Subtype.ext (chiConj_chiConj _)
> 
> theorem twist2_bijective : Function.Bijective twist2 :=
>   Function.Involutive.bijective twist2_twist2

```

### T3-b：ノート `pag2_part259_unitary_step_maps.md`（照合者 B の後に書いた。全文が未照合）

# アーデル射影幾何 PAG 2.0 — Part 259：互いに素な段の写像の一意性と、帰納系の添字（PAG263.lean）

（2026-11-15。著者の指示「Lean」（07:27）に従って始めた。問いの出所は二つある。基礎文書の骨格（著者側）の第5章と、方向ラウンドの項目 (b) の R1 である。R1 の査定（`pag2_R1_assessment.md`、数値と手計算）の主張を Lean にした。）

## §0 結論（Lean の文から）

記号は次のとおり。
- A_N = `shellAlg N`、D_s = mulLeft(dind N s)、E_s = convL(geps N s)、π^* は引き戻し。
- `Compat`（Part 258 の条件）：(i) φ(S) π^* = π^* S。(ii) φ(D_s) は D_t の線形結合で、φ(E_s) は E_t の線形結合。
- `CompatF`：`Compat` に (iii) フーリエとの両立 φ(𝓕S𝓕⁻¹) = 𝓕φ(S)𝓕⁻¹ を足したもの。

1. **一意な存在の二分法**（`existsUnique_compatF_iff`）。N ∣ M のとき、(i)(ii)(iii) を満たす単位的な代数準同型 A_N → A_M がちょうど 1 つあるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。
   - 互いに素な段では、その写像は `shellLift`（S ↦ S ⊗ 1）である（`compatF_iff_eq_shellLift`）。
   - 互いに素でない段で成り立たないのは、(i)(ii) を満たす写像が 1 つもないから（Part 258）であって、複数あるからではない。
2. **(iii) を外すと一意でない場合がある**（`not_existsUnique_compat`）。gcd(2, b) = 1 かつ 1 < b のとき、(i)(ii) だけを満たす A_2 → A_{2b} は 2 つ以上ある。もう 1 つは、χ(x) = (−1)^x による A_2 の自己同型で捩った写像 `twLift` である。Lean が示すのはこの a = 2 の場合だけ。数値（9 組）では、a が奇数なら (i)(ii) だけで一意だった。
3. **帰納系**（`canon_self`・`canon_comp`）。互いに素な段の標準の写像は、合成と両立する。
4. **添字は有向でない**（`not_directed_udvd`・`not_isDirected_udvd`）。p と p² の両方の上に来る互いに素な段はない。互いに素な段は、古典的なユニタリ約数 N ∥ M の関係である（E. Cohen, Math. Z. 74 (1960) 66–80）。
5. **有向な部分系の例**。素数の有限集合の積（無平方数）の段は、包含の順で帰納系をなす（`DirectedSystem` のインスタンス）。ℂ 加群としての帰納極限 `sqLim` に、各段は単射で入る（`sqLim_of_injective`）。

規模：定理 67 個、定義 14 個、インスタンス 3 個。sorry 0、警告 0。公理は標準の範囲（[propext, Classical.choice, Quot.sound] または [propext, Quot.sound]）。

## §1 どこに内容があるか（照合 B の指摘を受けて）

- **一意性（`compatF_unique`）は、ほぼ即座の帰結である。** (i) を定数 1 に当てると φ(D_s) が決まり（`compat_dind_unique`）、(iii) はそれを E の側に運ぶだけ。同じ理由で、(ii) の E の側は (i)、(ii) の D の側、(iii) から出る（`compatF_of_dind`）。
- **内容があるのは次の 3 つである。**
  - 存在：`shellLift` がフーリエと両立すること（`shellLift_fC`）。
  - (iii) が外せないこと：a = 2 の捩れ。
  - 帰納系の添字の構造：有向でないこと、有向な部分系、単射性。
- **(iii) は自然な条件である見込み**（照合 B の手計算、確信度：中〜高、Lean にしていない）。𝓕⁻¹ π^* 𝓕 は、双対側の部分群の埋め込みに沿った零延長 ι_* になる。そのため (i)(iii) から φ(S) ι_* = ι_* S が出る。逆向きも成り立つ見込み（確信度：中）。成り立てば、(iii) は「射影 π とその双対の埋め込み ι の両方と両立する」と言い換えられる。
- **「互いに素は要らない」と書いた文について。** `compat_dind_unique`・`compatF_unique`・`compatF_comp` は N ∣ M だけを仮定する。しかし互いに素でなければ Part 258 により前提を満たす写像がないので、その場合は空虚に真である。

## §2 第5章への帰結（解釈。Lean の文ではない）

骨格の第5章の文は、次の形なら Lean の文から書ける。

> 「互いに素な段（ユニタリ約数）の写像は、引き戻しとの両立・殻を混ぜないこと・フーリエとの両立で一意に決まり（`shellLift`）、合成と両立する。添字の順序は有向でなく、帰納極限は有向な部分系（例：無平方数の段）の上でとる。」

ただし次の 3 点も併記する必要がある。
- 無平方数の系は、極大な有向部分系（各素数の指数を 1 つに固定したもの）のうち、指数がすべて 1 の場合にすぎない。A_{p^k}（k ≥ 2）を含まない。
- `sqLim` は ℂ 加群で、代数の構造と制限テンソル積 ⊗'_p A_p との同型は Lean にしていない（制限テンソル積の構成そのものは［既知］）。
- どの有向な部分系も整除の順序で共終でない。したがって関数のレベルの極限 ℂ[ℚ/ℤ]（Part 197・202）の代数版にはならない（初等的、Lean にしていない）。

## §3 ラベル

- ユニタリ約数の順序の性質（推移性、有向でないこと）：［既知］（Cohen 1960。照合 B が挙げ、Web で書誌を確かめた）。
- 一意性・非一意性・帰納系（A_N の間の写像に (i)(ii)(iii) を課したもの）：［再導出（小さい）］の見込み。照合 B は標準的な文献を知らず、新しいとも既知とも断定できないとした。初等的なので、アソシエーション・スキーム（Terwilliger 代数・Bose–Mesner 代数の双対）の文献に同等の観察がある可能性がある。文献照合は未了。
- ラベルを確定するのは著者側。

## §4 照合

**着手前の内部照合。** Lean の全宣言（4337 件）と xlsx を名前と言葉で検索した。
- 使えたもの：Part 242 の `fourierConj`（D と E を入れ替える）、Part 228 の `shellAlg_eq_adjoin`、Part 254 の `Lvl` と `DirectedSystem`（関数のレベルの帰納系の前例）、Part 239・247 の `geps_self`。
- 同じ主張は見つからなかった。

**閉じる前の内部照合。** 全宣言 4424 件、TF-IDF の上位 20 件と照らして 3440 回、`#dupcheck`・`#defeqcheck` にかけ、言葉でも検索した。
- `pull_injective'` は、Part 202 の `pull_injective`（M = N·t の形）から出す形に直した。
- `pull_pull` は、Part 192 の `castHom_castHom` から出す形に直した。
- `UDvd` は、Part 216 の層 `InLayer` で c = d = N とした場合と同じだった。一致を示す定理（`udvd_iff_inLayer`）を足した。
- 残った一致は 1 件だけで、Part 202 の文が今回の一般化から出るという向きのもの（記録済み）。

**独立照合 B**（新しいエージェント。形式文の全文と、使う定義の原文を渡した。予想は事前に `predictions.md` に書いた）。
- 形式文の誤りは指摘されなかった。
- 指摘を受けて直したこと：
  - (iii) を外した場合の非一意性を a = 2 の例に限った。これは数値の観察「奇数なら一意」と食い違う一般の主張として読めたため。
  - 一意性がほぼ即座の帰結であることを明記した。
  - 互いに素でない場合が空虚であることを書いた。
  - (ii) の E の側が余分であることを示した（`compatF_of_dind`）。
  - ¬IsDirected を系として足した（`not_isDirected_udvd`）。
  - ψ が対合で全単射であることを足した（`twist2_twist2`・`twist2_bijective`）。
  - 無平方数の系が指数 1 の場合にすぎないことを書いた。
  - ユニタリ約数という用語を足した。
- 予想との照合：予想の 1〜3（有向性の言い方、(iii) の自明さ、`sqLim` の代数の構造）は当たった。予想しなかった指摘は 3 つ。
  - 奇数で一意という観察が見出しと食い違うこと。
  - ユニタリ約数という既知の名前があること。
  - (iii) の双対の埋め込みによる言い換え。
- 直した後の照合は受けていない。

## §5 収束アラーム（CLAUDE.md §7）

- 兆候 4（初等的な部品だけ）：Part 249〜259 の 11 パート連続。このパートは骨格の第5章の不足を埋めるもので、基礎文書への移行（著者側、2026-11-15）の進め方に沿っている。
- 兆候 1 の内側版：`UDvd` が Part 216 の `InLayer` と同じ概念だった。また古典的なユニタリ約数でもあった。どちらも閉じる前に記録した。

## §6 ファイル

- `PAG263.lean`。
- 照合の記録 `audit259/`：`input_full.md`、`predictions.md`、`outputs/B_output.md`、内部照合の一式 `internal/`。
- R1 の査定 `r1assess/`（数値 uniq.py・aut.py・fourier.py とログ）。
- `lean_verification_status.xlsx`（final80）：行 3602〜3668、手順 281。


### T3-c：検証表 xlsx の行 3602〜3668 の主張文（生成スクリプト。各行は (定理名, 主張, 証明の方針, 使った補題)）

```python
R=[
('udvd_refl','互いに素な段の順序 UDvd（def：N ∣ M かつ gcd(N, M/N) = 1。古典的なユニタリ約数 N ∥ M、Cohen 1960）は反射的（N > 0）','N/N = 1','Nat.div_self'),
('udvd_trans','UDvd は推移的','M = Na、L = Nab と書き、gcd(N, ab) = 1','Nat.Coprime.mul_right, Nat.Coprime.coprime_dvd_left'),
('udvd_iff_inLayer','UDvd N M ⇔ Part 216 の層 InLayer N N M（N > 0。内部照合で見つけた同じ概念）','定義を開く','Nat.mul_div_cancel_left'),
('not_udvd_and_udvd_sq','素数 p で UDvd p M と UDvd p² M は同時に成り立たない','M = p²k なら M/p = pk で gcd(p, pk) = p','Nat.Coprime.eq_one_of_dvd'),
('not_directed_udvd','有向でない：p と p² の両方の上に来る互いに素な段はない','上の補題','—'),
('not_isDirected_udvd','有向でない：ℕ の上の UDvd は有向でない（照合 B の指摘で追加）','p = 2 の場合','IsDirected.directed'),
('shellAlg_hom_ext','生成元 D_s・E_s で一致する A_N からの代数準同型は等しい','等化子の部分代数が生成元を含む','AlgHom.equalizer, Algebra.adjoin_le'),
('pull_pull','引き戻しの合成：π_{M→L}^* π_{N→M}^* = π_{N→L}^*','Part 192 の castHom_castHom（内部照合）','PAG.Part196.castHom_castHom'),
('pull_self','N → N の引き戻しは恒等（補助）','castHom_self','ZMod.castHom_self'),
('pull_one','定数 1 の引き戻しは 1（補助）','rfl','—'),
('compat_dind_unique','(i) と (ii) の D の側から φ(D_s) は一意に決まる（文は N ∣ M だけを仮定。互いに素でなければ空虚に真）','φ(D_s) は掛け算の作用素 g・、(i) を定数 1 に当てると g = π^*(D_s 1)','PAG.Part262.exists_mulLeft_of_mem_span'),
('fC_coe','fC（def：Part 242 の fourierConj を A_N に制限した代数同型）の値（補助）','rfl','AlgEquiv.subalgebraMap'),
('fC_dind','fC(D_s) = E_s','Part 242 の fourierConj_mulLeft_dind','PAG.Part246.fourierConj_mulLeft_dind'),
('fC_geps','fC(E_s) = D_s','Part 242 の fourierConj_convL_geps','PAG.Part246.fourierConj_convL_geps'),
('compatF_unique','一意性：(i)(ii)(iii)（CompatF、def。Compat は Part 258 の (i)(ii)、def）を満たす代数準同型は高々 1 つ（φ(D_s) の一意性を (iii) で運ぶだけの、ほぼ即座の帰結）','D の側は compat_dind_unique、E_s = fC(D_s) と (iii)、生成元で一致','shellAlg_hom_ext'),
('fourierConj_mem_spanE','フーリエ共役は D_t の張る空間を E_t の張る空間に移す（補助）','span の像','Submodule.map_span'),
('compatF_of_dind','(ii) の E の側は余分：(i)、(ii) の D の側、(iii) から CompatF が出る（照合 B の指摘で追加）','φ(E_s) = fC(φ(D_s))','fourierConj_mem_spanE'),
('dsub_eq_zero','s ∤ N なら D_s = 0（補助）','Part 228 の dind_eq_zero_of_not_dvd','PAG.Part232.dind_eq_zero_of_not_dvd'),
('esub_eq_zero','s ∤ N なら E_s = 0（補助）','Part 228 の geps_eq_zero_of_not_dvd','PAG.Part232.geps_eq_zero_of_not_dvd'),
('shellLift_fC','shellLift（Part 258）はフーリエと両立する','生成元で：fourierConj が Σ D_{su} と Σ E_{su} を入れ替える','PAG.Part262.shellLift_dind, PAG.Part262.shellLift_geps'),
('compatF_shellLift','shellLift は (i)(ii)(iii) を満たす','Part 258 の shellLift_pull と上','PAG.Part262.shellLift_pull'),
('compatF_iff_eq_shellLift','gcd(a, b) = 1 なら、(i)(ii)(iii) を満たす A_a → A_{ab} は shellLift だけ','一意性と上','—'),
('existsUnique_compatF_iff','一意な存在の二分法：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型がちょうど 1 つ ⇔ gcd(N, M/N) = 1（互いに素でないときは (i)(ii) を満たすものが 1 つもない）','⇒ は Part 258 の二分法、⇐ は shellLift と一意性','PAG.Part262.exists_compatible_hom_iff'),
('map_mem_spanD','D の生成元を D の張る空間に送る準同型は、その空間の元も送る（補助）','span の像','Submodule.map_span'),
('map_mem_spanE','E について同じ（補助）','span の像','Submodule.map_span'),
('compatF_comp','合成：(i)(ii)(iii) は合成で保たれる','引き戻しの合成と span の補題','pull_pull'),
('compatF_id','恒等写像は (i)(ii)(iii) を満たす','pull_self','—'),
('compatF_canon','互いに素な段の標準の写像 canon（def：一意な存在から選んだもの）は (i)(ii)(iii) を満たす','選択の性質','Exists.choose_spec'),
('canon_eq_shellLift','canon は shellLift に等しい','一意性','—'),
('canon_self','φ_{N,N} = id','一意性','—'),
('canon_comp','帰納系：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}','合成と一意性','udvd_trans'),
('esub_mul_esub','E_s E_t = [s = t] E_s（A_N の中で、補助）','Part 89 の結合法則と Part 201 の geps_conv_geps','PAG.Part205.geps_conv_geps'),
('conv_geps_self_const','E_N は定数関数を保つ（補助）','Part 239 の geps_self','PAG.Part243.geps_self'),
('chi2_mul_self','χ(x) = (−1)^x（chi2、def、ℤ/2 上）で χ² = 1（補助）','場合分け','—'),
('chiConj_apply','χ による共役 chiConj（def、chiMul は χ を掛ける線形同型、def）の値（補助）','rfl','LinearEquiv.conjAlgEquiv'),
('chiConj_mulLeft','χ の共役は掛け算の作用素を固定する','可換性と χ² = 1','—'),
('chiConj_chiConj','χ の共役は対合','χ² = 1','—'),
('convL_geps_two_one','E_1 = 1 − E_2（N = 2）','Part 228 の sum_convL_geps','PAG.Part232.sum_convL_geps'),
('sum_zmod2','ℤ/2 上の和は 2 項（補助）','Fin.sum_univ_two','Fin.sum_univ_two'),
('chiConj_geps_two','χ E_2 χ⁻¹ = E_1','ℤ/2 の 2 点で計算（E_2 は定数 1/2 の畳み込み）','PAG.Part243.geps_self'),
('chiConj_geps_one','χ E_1 χ⁻¹ = E_2','共役は対合','—'),
('map_chiConj_le','χ の共役は A_2 を保つ（補助）','生成元の像','AlgHom.map_adjoin'),
('twist2_coe','A_2 の自己準同型 ψ = twist2（def）の値（補助）','rfl','AlgHom.codRestrict'),
('twist2_twist2','ψ は対合（照合 B の指摘で追加）','chiConj_chiConj','—'),
('twist2_bijective','ψ は全単射（A_2 の自己同型）','対合','Function.Involutive.bijective'),
('twist2_dind','ψ(D_s) = D_s','chiConj_mulLeft','—'),
('twist2_geps_one','ψ(E_1) = E_2','chiConj_geps_one','—'),
('twist2_geps_two','ψ(E_2) = E_1','chiConj_geps_two','—'),
('eTop_const','E_b（Part 258 の eTop）は定数を保つ（補助）','conv_geps_self_const','—'),
('one_sub_eTop_const','1 − E_b は定数を 0 に送る（補助）','上','—'),
('one_sub_eTop_eq','1 − E_b = 1 + (−1)·E_b（A_b の中で、補助）','係数への移行','—'),
('twTensLin_apply','線形写像 S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)（twTensLin、def）の値（補助）','rfl','TensorProduct.mk'),
('twTens_apply','代数準同型 twTens（def）の値（補助）','rfl','AlgHom.ofLinearMap'),
('twLift_apply','捩れた写像 twLift（def：φ\'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))、Θ は Part 228）の値（補助）','rfl','—'),
('twLift_pull','φ\' は (i) を満たす','CRT の座標で：E_b は定数を保ち 1 − E_b は消す','PAG.Part232.crtConj_shellAlgTensorEquiv, PAG.Part262.crtLin_pull'),
('twLift_dind','φ\'(D_s) = shellLift(D_s)','ψ(D_s) = D_s','—'),
('twist2_geps','ψ(E_s) はある E_t（補助）','s = 1, 2 とそれ以外（E_s = 0）','—'),
('tensor_eTop_mem_spanE','Θ(E_t ⊗ E_b) は E の張る空間に入る（補助）','Part 228 の shellAlgTensorEquiv_geps','PAG.Part232.shellAlgTensorEquiv_geps'),
('compat_twLift','φ\' は Part 258 の (i)(ii) を満たす','φ\'(E_s) = Θ(E_s ⊗ E_b) + shellLift(E_t) − Θ(E_t ⊗ E_b)','—'),
('convL_geps_one_ne_zero','E_1 ≠ 0（補助）','フーリエ共役で D_1、点 1 で値 1','PAG.Part246.fourierConj_convL_geps'),
('twLift_ne_shellLift','1 < b なら φ\' ≠ shellLift','E_1 ⊗ E_1 を右から掛けると φ\'(E_1) 側は 0、shellLift(E_1) 側は E_1^{(2b)} ≠ 0','esub_mul_esub'),
('not_existsUnique_compat','(iii) を外すと一意でない場合がある（a = 2 の例）：gcd(2, b) = 1、1 < b のとき、(i)(ii) を満たす A_2 → A_{2b} は一意でない（数値では a が奇数なら (i)(ii) だけで一意、Lean にしていない）','shellLift と φ\'','—'),
('pull_injective\'','引き戻しは単射（N ∣ M）','Part 202 の pull_injective（内部照合）','PAG.Part206.pull_injective'),
('compat_injective','(i) を満たす写像は単射','引き戻しの単射性','—'),
('primeProd_pos','素数の有限集合の積 N_S（primeProd、def）は正（補助）','Finset.prod_pos','Finset.prod_pos'),
('primeProd_udvd','S ⊆ T なら N_S → N_T は互いに素な段','N_T = N_{T∖S}·N_S、異なる素数は互いに素','Finset.prod_sdiff, Nat.coprime_primes'),
('sqLim_of_injective','無平方数の段の帰納極限 sqLim（abbrev、ℂ 加群。標準の写像 sqMap（def）による帰納系、DirectedSystem のインスタンス）に各 A_{N_S} は単射で入る','compat_injective','Module.DirectLimit.exists_eq_of_of_eq'),
]
```

### T3-d：PAG263.lean の現在の全文（形式文の正本）

```lean
/-
アーデル射影幾何 — Part 259（PAG 2.0）：互いに素な段の写像の一意性と、帰納系の添字

問いの出所：基礎文書の骨格（著者側、2026-11-15）の第5章と、方向ラウンドの項目 (b) の R1
（互いに素な段だけの帰納系を第5章の材料として確定できるか）。R1 の査定（`pag2_R1_assessment.md`、
数値と手計算）の主張を Lean にした。著者の指示（2026-11-15 07:27「Lean」）。

記号：A_N = `shellAlg N`、D_s = mulLeft(dind N s)、E_s = convL(geps N s)、π^* = `pull`。
Part 258（PAG262）の条件 (i)(ii)（`Compat`）：(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合。
(iii)（`CompatF` で足す）：φ(𝓕 S 𝓕⁻¹) = 𝓕 φ(S) 𝓕⁻¹（`fC` は Part 242 の `fourierConj` を A_N に制限したもの）。

内容：
1. 互いに素な段の順序 `UDvd`（N ∣ M かつ gcd(N, M/N) = 1。古典的な「ユニタリ約数」の関係 N ∥ M。
   E. Cohen, Math. Z. 74 (1960) 66–80）：N > 0 で反射的（`udvd_refl`）、推移的（`udvd_trans`）。Part 216 の層
   `InLayer` で c = d = N とした場合と同じ（`udvd_iff_inLayer`、N > 0）。素数 p について p と p² の共通の上界がなく
   （`not_directed_udvd`）、したがって ℕ の上で有向でない（`not_isDirected_udvd`）。
2. 生成元 D_s・E_s で一致する A_N からの代数準同型は等しい（`shellAlg_hom_ext`）。(i)(ii) の D の側から φ(D_s) は
   一意に決まる（`compat_dind_unique`。文は N ∣ M だけを仮定するが、gcd(N, M/N) ≠ 1 なら Part 258 により (i)(ii) を
   満たす φ はないので、その場合は空虚に真）。
3. 一意性：(i)(ii)(iii) を満たす写像は高々 1 つ（`compatF_unique`）。これは φ(D_s) の一意性を (iii) で E の側へ
   運ぶだけの、ほぼ即座の帰結である（(ii) の E の側も互いに素も使わない）。同じ理由で (ii) の E の側は (i)、(ii) の
   D の側、(iii) から出る（`compatF_of_dind`）。内容があるのは存在の側：`shellLift`（φ(S) = S ⊗ 1）がフーリエと
   両立すること（`shellLift_fC`）。gcd(a, b) = 1 なら (i)(ii)(iii) を満たすのは `shellLift` だけ
   （`compatF_iff_eq_shellLift`）。N ∣ M のとき、(i)(ii)(iii) を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1
   （`existsUnique_compatF_iff`）。互いに素でないときに成り立たないのは、(i)(ii) を満たす写像が 1 つもないから
   （Part 258）で、複数あるからではない。
4. (i)(ii)(iii) は合成で保たれ（`compatF_comp`）、恒等写像は満たす（`compatF_id`）。互いに素な段の標準の写像
   `canon` は `shellLift` に等しく（`canon_eq_shellLift`）、φ_{N,N} = id（`canon_self`）、φ_{M,L} ∘ φ_{N,M} = φ_{N,L}
   （`canon_comp`）。
5. (iii) を外すと一意でない場合がある（a = 2 の例）：gcd(2, b) = 1、1 < b のとき、A_2 の自己同型（対合、
   `twist2_twist2`・`twist2_bijective`）ψ(S) = χ S χ⁻¹（χ(x) = (−1)^x、`twist2`。D_s を固定し E_1 と E_2 を入れ替える）
   を使った φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))（`twLift`、Θ は Part 228 の `shellAlgTensorEquiv`）は (i)(ii) を
   満たし（`compat_twLift`）、`shellLift` と異なる（`twLift_ne_shellLift`）。したがって (i)(ii) を満たす A_2 → A_{2b}
   は一意でない（`not_existsUnique_compat`）。Lean が示すのはこの場合だけ。R1 の査定の数値（9 組）では、a が奇数なら
   (i)(ii) だけで一意で、(iii) が効くのは a が偶数のときだけと見られる（Lean にしていない）。
6. 有向な部分系の例：素数の有限集合 S の積 N_S（無平方数）の段は、包含の順で `canon` により帰納系をなし
   （`DirectedSystem` のインスタンス）、ℂ 加群としての帰納極限 `sqLim` に各 A_{N_S} は単射で入る
   （`sqLim_of_injective`。遷移写像の単射性 `compat_injective` からほぼ自動的に出る）。この系は、極大な有向部分系
   （各素数の指数を 1 つに固定したもの）のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。

Lean にしていないこと：一意でない写像の個数（数値の観察では a が偶数なら 2^{d(b)−1}、奇数なら 1）、a が 2 以外の
偶数の場合の捩れ、a が奇数での (i)(ii) だけによる一意性。`sqLim` の代数の構造と、それが制限テンソル積 ⊗'_p A_p に
同型であること。他の有向な部分系。どの有向な部分系も整除の順序で共終でないこと（初等的）。照合 B が手計算で示した
(iii) の言い換え（𝓕⁻¹ π^* 𝓕 は双対側の部分群の埋め込み ι_* なので、(i)(iii) から φ(S) ι_* = ι_* S。逆向きも
成り立つ見込み。確信度：中）。
-/
import PAG262

open Complex Finset
open PAG.Part205 PAG.Part218 PAG.Part232 PAG.Part246 PAG.Part262
open ZMod (stdAddChar)
open scoped ZMod

namespace PAG.Part263

/-! ### 1. 互いに素な段の順序 -/

/-- 互いに素な段：N ∣ M かつ gcd(N, M/N) = 1。 -/
def UDvd (N M : ℕ) : Prop := N ∣ M ∧ Nat.Coprime N (M / N)

theorem udvd_refl {N : ℕ} (hN : 0 < N) : UDvd N N :=
  ⟨dvd_rfl, by rw [Nat.div_self hN]; exact Nat.coprime_one_right N⟩

theorem udvd_trans {N M L : ℕ} (h1 : UDvd N M) (h2 : UDvd M L) : UDvd N L := by
  obtain ⟨⟨a, rfl⟩, ha⟩ := h1
  obtain ⟨⟨b, rfl⟩, hb⟩ := h2
  refine ⟨⟨a * b, by ring⟩, ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp at ha
  rw [Nat.mul_div_cancel_left a hN] at ha
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    have : N = 1 := by simpa using ha
    subst this; simp
  rw [Nat.mul_div_cancel_left b (Nat.mul_pos hN ha0)] at hb
  rw [mul_assoc, Nat.mul_div_cancel_left _ hN]
  exact Nat.Coprime.mul_right ha (Nat.Coprime.coprime_dvd_left (dvd_mul_right N a) hb)

/-- 内部照合（2026-11-15）：互いに素な段は、Part 216（PAG220）の層 `InLayer`（n = d·e、e は c と互いに素）で
c = d = N とした場合と同じ（N > 0）。 -/
theorem udvd_iff_inLayer {N M : ℕ} (hN : 0 < N) : UDvd N M ↔ PAG.Part220.InLayer N N M := by
  constructor
  · rintro ⟨⟨e, rfl⟩, h⟩
    rw [Nat.mul_div_cancel_left e hN] at h
    exact ⟨e, rfl, h.symm⟩
  · rintro ⟨e, rfl, h⟩
    refine ⟨dvd_mul_right N e, ?_⟩
    rw [Nat.mul_div_cancel_left e hN]
    exact h.symm

/-- p と p² の両方の上に来る段はない（p は素数）。 -/
theorem not_udvd_and_udvd_sq {p M : ℕ} (hp : p.Prime) : ¬ (UDvd p M ∧ UDvd (p ^ 2) M) := by
  rintro ⟨⟨_, h1⟩, ⟨⟨k, rfl⟩, _⟩⟩
  have : p ^ 2 * k / p = p * k := by
    rw [pow_two, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [this] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 (dvd_mul_right p k))

/-- **有向でない**：互いに素な段の順序には、p と p² の共通の上界がない。 -/
theorem not_directed_udvd {p : ℕ} (hp : p.Prime) : ¬ ∃ M, UDvd p M ∧ UDvd (p ^ 2) M :=
  fun ⟨_, h⟩ => not_udvd_and_udvd_sq hp h

/-- **有向でない**（照合 B の指摘で追加）：ℕ の上の UDvd は有向でない（p = 2 の場合）。 -/
theorem not_isDirected_udvd : ¬ IsDirected ℕ UDvd := by
  intro h
  obtain ⟨M, h1, h2⟩ := h.directed 2 (2 ^ 2)
  exact not_udvd_and_udvd_sq Nat.prime_two ⟨h1, h2⟩

/-! ### 2. 生成元での一致と、φ(D_s) の一意性 -/

variable {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L]

/-- 生成元 D_s・E_s で一致する、A_N からの代数準同型は等しい。 -/
theorem shellAlg_hom_ext {B : Type} [Semiring B] [Algebra ℂ B] {φ ψ : shellAlg N →ₐ[ℂ] B}
    (hD : ∀ s, φ ⟨_, mulLeft_dind_mem N s⟩ = ψ ⟨_, mulLeft_dind_mem N s⟩)
    (hE : ∀ s, φ ⟨_, convL_geps_mem N s⟩ = ψ ⟨_, convL_geps_mem N s⟩) : φ = ψ := by
  have key : shellAlg N ≤ (AlgHom.equalizer φ ψ).map (shellAlg N).val := by
    apply Algebra.adjoin_le
    rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Subalgebra.mem_map.mpr ⟨⟨_, convL_geps_mem N s⟩, (AlgHom.mem_equalizer _ _ _).mpr (hE s), rfl⟩
    · exact Subalgebra.mem_map.mpr ⟨⟨_, mulLeft_dind_mem N s⟩, (AlgHom.mem_equalizer _ _ _).mpr (hD s), rfl⟩
  ext S
  obtain ⟨T, hT, hTS⟩ := Subalgebra.mem_map.mp (key S.2)
  have hT' : T = S := Subtype.ext hTS
  rw [← hT']
  exact (AlgHom.mem_equalizer φ ψ T).mp hT

omit [NeZero N] [NeZero M] [NeZero L] in
/-- 引き戻しの合成。
内部照合（2026-11-15）：還元の合成は Part 192（PAG196）の `castHom_castHom`。それを引き戻しに言い直したもの。 -/
theorem pull_pull (hNM : N ∣ M) (hML : M ∣ L) (f : ZMod N → ℂ) :
    PAG.Part201.pull hML (PAG.Part201.pull hNM f) = PAG.Part201.pull (hNM.trans hML) f := by
  funext x
  simp only [PAG.Part201.pull, Function.comp_apply]
  congr 1
  exact PAG.Part196.castHom_castHom hNM hML (hNM.trans hML) x

omit [NeZero N] in
theorem pull_self (f : ZMod N → ℂ) : PAG.Part201.pull (dvd_refl N) f = f := by
  funext x
  simp only [PAG.Part201.pull, Function.comp_apply]
  congr 1
  exact RingHom.congr_fun (ZMod.castHom_self) x

omit [NeZero N] [NeZero M] in
theorem pull_one (hNM : N ∣ M) : PAG.Part201.pull hNM (1 : ZMod N → ℂ) = 1 := rfl

/-- **φ(D_s) は (i)(ii) の D の側から一意に決まる**（N ∣ M。互いに素は要らない）。 -/
theorem compat_dind_unique (hNM : N ∣ M) {φ ψ : shellAlg N →ₐ[ℂ] shellAlg M}
    (hφ1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (hψ1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (ψ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (hφ2 : ∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (hψ2 : ∀ s : ℕ, (ψ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (s : ℕ) : φ ⟨_, mulLeft_dind_mem N s⟩ = ψ ⟨_, mulLeft_dind_mem N s⟩ := by
  obtain ⟨g, hg⟩ := exists_mulLeft_of_mem_span M (hφ2 s)
  obtain ⟨g', hg'⟩ := exists_mulLeft_of_mem_span M (hψ2 s)
  have h1 := hφ1 ⟨_, mulLeft_dind_mem N s⟩ 1
  have h2 := hψ1 ⟨_, mulLeft_dind_mem N s⟩ 1
  rw [hg, pull_one, LinearMap.mulLeft_apply, mul_one] at h1
  rw [hg', pull_one, LinearMap.mulLeft_apply, mul_one] at h2
  apply Subtype.ext
  rw [hg, hg', h1, h2]

/-! ### 3. フーリエとの両立 (iii) と一意性 -/

/-- A_N のフーリエ共役 S ↦ 𝓕 S 𝓕⁻¹（Part 242 の `fourierConj` を A_N に制限したもの）。 -/
noncomputable def fC (N : ℕ) [NeZero N] : shellAlg N ≃ₐ[ℂ] shellAlg N :=
  ((fourierConj N).subalgebraMap (shellAlg N)).trans
    (Subalgebra.equivOfEq _ _ (map_fourierConj_shellAlg N))

theorem fC_coe (S : shellAlg N) :
    (fC N S : Module.End ℂ (ZMod N → ℂ)) = fourierConj N (S : Module.End ℂ (ZMod N → ℂ)) := rfl

theorem fC_dind (s : ℕ) : fC N ⟨_, mulLeft_dind_mem N s⟩ = ⟨_, convL_geps_mem N s⟩ :=
  Subtype.ext (fourierConj_mulLeft_dind N s)

theorem fC_geps (s : ℕ) : fC N ⟨_, convL_geps_mem N s⟩ = ⟨_, mulLeft_dind_mem N s⟩ :=
  Subtype.ext (fourierConj_convL_geps N s)

/-- Part 258 の条件：(i) 引き戻しと両立、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合。 -/
def Compat (hNM : N ∣ M) (φ : shellAlg N →ₐ[ℂ] shellAlg M) : Prop :=
  (∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
    (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
    (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))

/-- (i)(ii) に (iii) フーリエとの両立 φ(𝓕 S 𝓕⁻¹) = 𝓕 φ(S) 𝓕⁻¹ を足した条件。 -/
def CompatF (hNM : N ∣ M) (φ : shellAlg N →ₐ[ℂ] shellAlg M) : Prop :=
  Compat hNM φ ∧ ∀ S : shellAlg N, φ (fC N S) = fC M (φ S)

/-- フーリエ共役は D_t の張る空間を E_t の張る空間に移す（補助）。 -/
theorem fourierConj_mem_spanE {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    fourierConj M T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
  have h : (Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))).map
      (fourierConj M).toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact fourierConj_mulLeft_dind M t
  rw [← h]
  exact Submodule.mem_map_of_mem hT

/-- **(ii) の E の側は余分**（照合 B の指摘で追加）：(i)、(ii) の D の側、(iii) から CompatF が出る。 -/
theorem compatF_of_dind (hNM : N ∣ M) {φ : shellAlg N →ₐ[ℂ] shellAlg M}
    (h1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (h2 : ∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (h3 : ∀ S : shellAlg N, φ (fC N S) = fC M (φ S)) : CompatF hNM φ := by
  refine ⟨⟨h1, h2, fun s => ?_⟩, h3⟩
  rw [← fC_dind, h3, fC_coe]
  exact fourierConj_mem_spanE (h2 s)

/-- **一意性**：(i)(ii)(iii) を満たす代数準同型は高々 1 つ（N ∣ M）。 -/
theorem compatF_unique (hNM : N ∣ M) {φ ψ : shellAlg N →ₐ[ℂ] shellAlg M}
    (hφ : CompatF hNM φ) (hψ : CompatF hNM ψ) : φ = ψ := by
  have hD := compat_dind_unique hNM hφ.1.1 hψ.1.1 hφ.1.2.1 hψ.1.2.1
  apply shellAlg_hom_ext hD
  intro s
  rw [← fC_dind, hφ.2, hψ.2, hD]

theorem dsub_eq_zero {s : ℕ} (hs : ¬ s ∣ N) : (⟨_, mulLeft_dind_mem N s⟩ : shellAlg N) = 0 := by
  apply Subtype.ext
  show LinearMap.mulLeft ℂ (dind N s) = 0
  rw [dind_eq_zero_of_not_dvd hs]; exact LinearMap.mulLeft_zero_eq_zero ℂ _

theorem esub_eq_zero {s : ℕ} (hs : ¬ s ∣ N) : (⟨_, convL_geps_mem N s⟩ : shellAlg N) = 0 := by
  apply Subtype.ext
  show PAG.Part15.convL (geps N s) = 0
  rw [geps_eq_zero_of_not_dvd hs, map_zero]

section lift
variable {a b : ℕ} [NeZero a] [NeZero b]

set_option synthInstance.maxHeartbeats 200000 in
/-- `shellLift`（φ(S) = S ⊗ 1）はフーリエと両立する。 -/
theorem shellLift_fC (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab (fC a S) = fC (a * b) (shellLift hab S) := by
  have h : (shellLift hab).comp (fC a).toAlgHom = (fC (a * b)).toAlgHom.comp (shellLift hab) := by
    apply shellAlg_hom_ext
    · intro s
      show shellLift hab (fC a _) = fC (a * b) (shellLift hab _)
      by_cases hs : s ∣ a
      · rw [fC_dind]
        apply Subtype.ext
        rw [fC_coe, shellLift_geps hab hs, shellLift_dind hab hs, map_sum]
        exact Finset.sum_congr rfl fun u _ => (fourierConj_mulLeft_dind _ _).symm
      · rw [dsub_eq_zero hs, map_zero, map_zero, map_zero]
    · intro s
      show shellLift hab (fC a _) = fC (a * b) (shellLift hab _)
      by_cases hs : s ∣ a
      · rw [fC_geps]
        apply Subtype.ext
        rw [fC_coe, shellLift_geps hab hs, shellLift_dind hab hs, map_sum]
        exact Finset.sum_congr rfl fun u _ => (fourierConj_convL_geps _ _).symm
      · rw [esub_eq_zero hs, map_zero, map_zero, map_zero]
  exact congrArg (fun g : shellAlg a →ₐ[ℂ] shellAlg (a * b) => g S) h

/-- `shellLift` は (i)(ii)(iii) を満たす。 -/
theorem compatF_shellLift (hab : a.Coprime b) : CompatF (dvd_mul_right a b) (shellLift hab) := by
  obtain ⟨-, h2, h3⟩ : Compat (dvd_mul_right a b) (shellLift hab) := by
    refine ⟨shellLift_pull hab, fun s => ?_, fun s => ?_⟩
    · by_cases hs : s ∣ a
      · rw [shellLift_dind hab hs]
        exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
      · rw [dsub_eq_zero hs, map_zero]; exact Submodule.zero_mem _
    · by_cases hs : s ∣ a
      · rw [shellLift_geps hab hs]
        exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
      · rw [esub_eq_zero hs, map_zero]; exact Submodule.zero_mem _
  exact ⟨⟨shellLift_pull hab, h2, h3⟩, shellLift_fC hab⟩

/-- (i)(ii)(iii) を満たす A_a → A_{ab} は `shellLift` だけ（gcd(a, b) = 1）。 -/
theorem compatF_iff_eq_shellLift (hab : a.Coprime b) (φ : shellAlg a →ₐ[ℂ] shellAlg (a * b)) :
    CompatF (dvd_mul_right a b) φ ↔ φ = shellLift hab :=
  ⟨fun h => compatF_unique _ h (compatF_shellLift hab), fun h => h ▸ compatF_shellLift hab⟩

end lift

/-- **一意な存在の二分法**：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型 A_N → A_M が
ちょうど 1 つあるのは gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem existsUnique_compatF_iff (hNM : N ∣ M) :
    (∃! φ : shellAlg N →ₐ[ℂ] shellAlg M, CompatF hNM φ) ↔ Nat.Coprime N (M / N) := by
  constructor
  · rintro ⟨φ, hφ, -⟩
    exact (exists_compatible_hom_iff hNM).mp ⟨φ, hφ.1⟩
  · intro hc
    rcases hNM with ⟨k, rfl⟩
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    rw [Nat.mul_div_cancel_left k hN0] at hc
    have : NeZero k := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
    exact ⟨shellLift hc, compatF_shellLift hc, fun ψ hψ => compatF_unique _ hψ (compatF_shellLift hc)⟩

/-! ### 4. 合成との両立と、標準の写像の系 -/

/-- ψ が D の生成元を D_t の張る空間に送るなら、その空間の元も送る。 -/
theorem map_mem_spanD (ψ : shellAlg M →ₐ[ℂ] shellAlg L)
    (hψ : ∀ t : ℕ, (ψ ⟨_, mulLeft_dind_mem M t⟩ : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind L u)))
    {X : shellAlg M} (hX : (X : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    (ψ X : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind L u)) := by
  set G : Set (shellAlg M) := Set.range fun t : ℕ => (⟨_, mulLeft_dind_mem M t⟩ : shellAlg M)
  set lin : shellAlg M →ₗ[ℂ] Module.End ℂ (ZMod L → ℂ) :=
    (shellAlg L).val.toLinearMap ∘ₗ ψ.toLinearMap
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ (Set.range fun u : ℕ =>
      LinearMap.mulLeft ℂ (dind L u))).comap lin := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hψ t
  have hmap : (Submodule.span ℂ G).map (shellAlg M).val.toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [← hmap] at hX
  obtain ⟨Y, hY, hYX⟩ := Submodule.mem_map.mp hX
  have : Y = X := Subtype.ext hYX
  subst this
  exact hle hY

theorem map_mem_spanE (ψ : shellAlg M →ₐ[ℂ] shellAlg L)
    (hψ : ∀ t : ℕ, (ψ ⟨_, convL_geps_mem M t⟩ : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps L u)))
    {X : shellAlg M} (hX : (X : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :
    (ψ X : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps L u)) := by
  set G : Set (shellAlg M) := Set.range fun t : ℕ => (⟨_, convL_geps_mem M t⟩ : shellAlg M)
  set lin : shellAlg M →ₗ[ℂ] Module.End ℂ (ZMod L → ℂ) :=
    (shellAlg L).val.toLinearMap ∘ₗ ψ.toLinearMap
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ (Set.range fun u : ℕ =>
      PAG.Part15.convL (geps L u))).comap lin := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hψ t
  have hmap : (Submodule.span ℂ G).map (shellAlg M).val.toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [← hmap] at hX
  obtain ⟨Y, hY, hYX⟩ := Submodule.mem_map.mp hX
  have : Y = X := Subtype.ext hYX
  subst this
  exact hle hY

/-- **合成**：(i)(ii)(iii) は合成で保たれる。 -/
theorem compatF_comp (hNM : N ∣ M) (hML : M ∣ L) {φ : shellAlg N →ₐ[ℂ] shellAlg M}
    {ψ : shellAlg M →ₐ[ℂ] shellAlg L} (hφ : CompatF hNM φ) (hψ : CompatF hML ψ) :
    CompatF (hNM.trans hML) (ψ.comp φ) := by
  refine ⟨⟨fun S f => ?_, fun s => ?_, fun s => ?_⟩, fun S => ?_⟩
  · rw [AlgHom.comp_apply, ← pull_pull hNM hML, hψ.1.1, hφ.1.1, pull_pull]
  · exact map_mem_spanD ψ hψ.1.2.1 (hφ.1.2.1 s)
  · exact map_mem_spanE ψ hψ.1.2.2 (hφ.1.2.2 s)
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, hφ.2, hψ.2]

/-- 恒等写像は (i)(ii)(iii) を満たす。 -/
theorem compatF_id : CompatF (dvd_refl N) (AlgHom.id ℂ (shellAlg N)) :=
  ⟨⟨fun S f => by rw [AlgHom.id_apply, pull_self, pull_self],
    fun s => Submodule.subset_span ⟨s, rfl⟩, fun s => Submodule.subset_span ⟨s, rfl⟩⟩,
    fun S => rfl⟩

/-- 互いに素な段の標準の写像（(i)(ii)(iii) を満たす唯一の写像）。 -/
noncomputable def canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : shellAlg N →ₐ[ℂ] shellAlg M :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose

theorem compatF_canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : CompatF hNM (canon hNM hc) :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose_spec

/-- 標準の写像は `shellLift`。 -/
theorem canon_eq_shellLift {a b : ℕ} [NeZero a] [NeZero b] (hab : a.Coprime b)
    (hc : Nat.Coprime a (a * b / a)) : canon (dvd_mul_right a b) hc = shellLift hab :=
  compatF_unique _ (compatF_canon _ hc) (compatF_shellLift hab)

theorem canon_self (hc : Nat.Coprime N (N / N)) : canon (dvd_refl N) hc = AlgHom.id ℂ (shellAlg N) :=
  compatF_unique _ (compatF_canon _ hc) compatF_id

/-- **帰納系**：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem canon_comp (h1 : UDvd N M) (h2 : UDvd M L) :
    (canon h2.1 h2.2).comp (canon h1.1 h1.2) = canon (udvd_trans h1 h2).1 (udvd_trans h1 h2).2 :=
  compatF_unique _ (compatF_comp h1.1 h2.1 (compatF_canon _ _) (compatF_canon _ _)) (compatF_canon _ _)

/-! ### 5. (iii) を外すと一意でない（a = 2） -/

/-- E_s E_t = [s = t] E_s（A_N の中で）。 -/
theorem esub_mul_esub (s t : ℕ) :
    (⟨_, convL_geps_mem N s⟩ : shellAlg N) * ⟨_, convL_geps_mem N t⟩ =
      if s = t then ⟨_, convL_geps_mem N s⟩ else 0 := by
  apply Subtype.ext
  apply LinearMap.ext; intro f
  show PAG.Part15.conv (geps N s) (PAG.Part15.conv (geps N t) f) = _
  rw [← PAG.Part89.conv_assoc', geps_conv_geps]
  split_ifs
  · rfl
  · show PAG.Part15.conv 0 f = 0
    funext x; simp [PAG.Part15.conv]

/-- E_N は定数を保つ。 -/
theorem conv_geps_self_const (c : ℂ) :
    PAG.Part15.conv (geps N N) (fun _ => c) = fun _ => c := by
  funext x
  unfold PAG.Part15.conv
  simp only [PAG.Part243.geps_self]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp

/-- ℤ/2 の指標 χ(x) = (−1)^x。 -/
noncomputable def chi2 : ZMod 2 → ℂ := fun x => if x = 0 then 1 else -1

theorem chi2_mul_self (x : ZMod 2) : chi2 x * chi2 x = 1 := by
  unfold chi2; split_ifs <;> norm_num

/-- χ を掛ける作用素（χ² = 1 なので自分自身が逆）。 -/
noncomputable def chiMul : (ZMod 2 → ℂ) ≃ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun h := chi2 * h
  map_add' f g := mul_add _ _ _
  map_smul' c f := mul_smul_comm c chi2 f
  invFun h := chi2 * h
  left_inv h := by funext x; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
  right_inv h := by funext x; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]

/-- χ による共役 T ↦ χ T χ⁻¹。 -/
noncomputable def chiConj : Module.End ℂ (ZMod 2 → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod 2 → ℂ) :=
  LinearEquiv.conjAlgEquiv ℂ chiMul

theorem chiConj_apply (T : Module.End ℂ (ZMod 2 → ℂ)) (h : ZMod 2 → ℂ) :
    chiConj T h = chi2 * T (chi2 * h) := rfl

theorem chiConj_mulLeft (g : ZMod 2 → ℂ) : chiConj (LinearMap.mulLeft ℂ g) = LinearMap.mulLeft ℂ g := by
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply]
  simp only [Pi.mul_apply, LinearMap.mulLeft_apply]
  linear_combination (g x * h x) * chi2_mul_self x

/-- E_1 = 1 − E_2（N = 2）。 -/
theorem convL_geps_two_one :
    PAG.Part15.convL (geps 2 1) = 1 - PAG.Part15.convL (geps 2 2) := by
  have h := sum_convL_geps 2
  rw [Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num)] at h
  rw [← h]; abel

theorem sum_zmod2 (g : ZMod 2 → ℂ) : ∑ x, g x = g 0 + g 1 := Fin.sum_univ_two g

/-- χ E_2 χ⁻¹ = E_1。 -/
theorem chiConj_geps_two : chiConj (PAG.Part15.convL (geps 2 2)) = PAG.Part15.convL (geps 2 1) := by
  rw [convL_geps_two_one]
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply]
  simp only [Pi.mul_apply, LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
    PAG.Part15.convL_apply, PAG.Part15.conv, PAG.Part243.geps_self, sum_zmod2]
  have e1 : (0 : ZMod 2) - 1 = 1 := rfl
  have e2 : (1 : ZMod 2) - 1 = 0 := rfl
  have e3 : (1 : ZMod 2) - 0 = 1 := rfl
  have e4 : (0 : ZMod 2) - 0 = 0 := rfl
  have e5 : (1 : ZMod 2) ≠ 0 := by decide
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;>
    simp only [chi2, e1, e2, e3, e4, e5, ↓reduceIte] <;> ring

/-- χ の共役は対合。 -/
theorem chiConj_chiConj (T : Module.End ℂ (ZMod 2 → ℂ)) : chiConj (chiConj T) = T := by
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply, chiConj_apply]
  have hc : chi2 * (chi2 * h) = h := by
    funext y; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
  simp only [Pi.mul_apply]
  rw [hc, ← mul_assoc, chi2_mul_self, one_mul]

theorem chiConj_geps_one : chiConj (PAG.Part15.convL (geps 2 1)) = PAG.Part15.convL (geps 2 2) := by
  rw [← chiConj_geps_two, chiConj_chiConj]

theorem map_chiConj_le : (shellAlg 2).map (chiConj : Module.End ℂ (ZMod 2 → ℂ) →ₐ[ℂ] _) ≤ shellAlg 2 := by
  rw [shellAlg_eq_adjoin, AlgHom.map_adjoin]
  apply Algebra.adjoin_le
  rintro _ ⟨T, (⟨s, rfl⟩ | ⟨s, rfl⟩), rfl⟩
  · show chiConj (PAG.Part15.convL (geps 2 s)) ∈ shellAlg 2
    by_cases h1 : s = 1
    · subst h1; rw [chiConj_geps_one]; exact convL_geps_mem 2 2
    by_cases h2 : s = 2
    · subst h2; rw [chiConj_geps_two]; exact convL_geps_mem 2 1
    have hs : ¬ s ∣ 2 := by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> contradiction
    rw [geps_eq_zero_of_not_dvd hs, map_zero, map_zero]; exact Subalgebra.zero_mem _
  · show chiConj (LinearMap.mulLeft ℂ (dind 2 s)) ∈ shellAlg 2
    rw [chiConj_mulLeft]; exact mulLeft_dind_mem 2 s

/-- A_2 の自己同型 ψ(S) = χ S χ⁻¹：D_s を固定し、E_1 と E_2 を入れ替える。 -/
noncomputable def twist2 : shellAlg 2 →ₐ[ℂ] shellAlg 2 :=
  ((chiConj : Module.End ℂ (ZMod 2 → ℂ) →ₐ[ℂ] _).comp (shellAlg 2).val).codRestrict (shellAlg 2)
    (fun S => map_chiConj_le (Subalgebra.mem_map.mpr ⟨S, S.2, rfl⟩))

theorem twist2_coe (S : shellAlg 2) :
    (twist2 S : Module.End ℂ (ZMod 2 → ℂ)) = chiConj (S : Module.End ℂ (ZMod 2 → ℂ)) := rfl

/-- ψ は対合（照合 B の指摘で追加。したがって A_2 の自己同型）。 -/
theorem twist2_twist2 (S : shellAlg 2) : twist2 (twist2 S) = S :=
  Subtype.ext (chiConj_chiConj _)

theorem twist2_bijective : Function.Bijective twist2 :=
  Function.Involutive.bijective twist2_twist2

theorem twist2_dind (s : ℕ) : twist2 ⟨_, mulLeft_dind_mem 2 s⟩ = ⟨_, mulLeft_dind_mem 2 s⟩ :=
  Subtype.ext (chiConj_mulLeft _)

theorem twist2_geps_one : twist2 ⟨_, convL_geps_mem 2 1⟩ = ⟨_, convL_geps_mem 2 2⟩ :=
  Subtype.ext chiConj_geps_one

theorem twist2_geps_two : twist2 ⟨_, convL_geps_mem 2 2⟩ = ⟨_, convL_geps_mem 2 1⟩ :=
  Subtype.ext chiConj_geps_two

section twistLift
variable {b : ℕ} [NeZero b]

theorem eTop_const (c : ℂ) :
    (eTop b : Module.End ℂ (ZMod b → ℂ)) (fun _ => c) = fun _ => c :=
  conv_geps_self_const c

theorem one_sub_eTop_const (c : ℂ) :
    ((1 - eTop b : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) (fun _ => c) = 0 := by
  rw [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply, Module.End.one_apply, eTop_const, sub_self]

theorem one_sub_eTop_eq : (1 - eTop b : shellAlg b) = 1 + (-1 : ℂ) • eTop b :=
  Subtype.ext (by
    rw [Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul, neg_one_smul,
      sub_eq_add_neg])

/-- 線形写像 S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)。 -/
noncomputable def twTensLin : shellAlg 2 →ₗ[ℂ] TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
  (TensorProduct.mk ℂ (shellAlg 2) (shellAlg b)).flip (eTop b) +
    ((TensorProduct.mk ℂ (shellAlg 2) (shellAlg b)).flip (1 - eTop b)) ∘ₗ twist2.toLinearMap

theorem twTensLin_apply (S : shellAlg 2) :
    (twTensLin S : TensorProduct ℂ (shellAlg 2) (shellAlg b)) =
      S ⊗ₜ[ℂ] eTop b + twist2 S ⊗ₜ[ℂ] (1 - eTop b) := rfl

/-- 代数準同型 A_2 → A_2 ⊗ A_b、S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)。 -/
noncomputable def twTens : shellAlg 2 →ₐ[ℂ] TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
  AlgHom.ofLinearMap twTensLin
    (by
      rw [twTensLin_apply, map_one, ← TensorProduct.tmul_add,
        show eTop b + (1 - eTop b) = 1 by abel]
      rfl)
    (fun S T => by
      have he : eTop b * eTop b = eTop b := eTop_mul_self b
      have he' : (eTop b : Module.End ℂ (ZMod b → ℂ)) * eTop b = eTop b := congrArg Subtype.val he
      have h1 : (1 - eTop b) * eTop b = 0 := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, sub_mul, one_mul, he', sub_self,
          ZeroMemClass.coe_zero])
      have h2 : eTop b * (1 - eTop b) = 0 := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, mul_sub, mul_one, he', sub_self,
          ZeroMemClass.coe_zero])
      have h3 : (1 - eTop b) * (1 - eTop b) = 1 - eTop b := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, sub_mul, one_mul, mul_sub, mul_one, he',
          sub_self, sub_zero])
      simp only [twTensLin_apply, map_mul, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        he, h1, h2, h3, TensorProduct.tmul_zero, add_zero, zero_add])

theorem twTens_apply (S : shellAlg 2) :
    (twTens S : TensorProduct ℂ (shellAlg 2) (shellAlg b)) =
      S ⊗ₜ[ℂ] eTop b + twist2 S ⊗ₜ[ℂ] (1 - eTop b) := rfl

/-- **捩れた写像** A_2 → A_{2b}：φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))。 -/
noncomputable def twLift (hab : Nat.Coprime 2 b) : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp twTens

theorem twLift_apply (hab : Nat.Coprime 2 b) (S : shellAlg 2) :
    twLift hab S = shellAlgTensorEquiv hab (twTens S) := rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- φ' は引き戻しと両立する（条件 (i)）。 -/
theorem twLift_pull (hab : Nat.Coprime 2 b) (S : shellAlg 2) (f : ZMod 2 → ℂ) :
    (twLift hab S : Module.End ℂ (ZMod (2 * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right 2 b) f) =
      PAG.Part201.pull (dvd_mul_right 2 b) ((S : Module.End ℂ (ZMod 2 → ℂ)) f) := by
  apply (crtLin hab).injective
  have h1 : ∀ (T : Module.End ℂ (ZMod (2 * b) → ℂ)) (g : ZMod (2 * b) → ℂ),
      crtLin hab (T g) = crtConj hab T (crtLin hab g) := by
    intro T g; rw [crtConj_apply, LinearEquiv.symm_apply_apply]
  rw [h1, twLift_apply, crtConj_shellAlgTensorEquiv, twTens_apply, map_add, tensLift_tmul, tensLift_tmul]
  funext p
  simp only [LinearMap.add_apply, Module.End.mul_apply, leftOp_apply, rightOp_apply, crtLin_pull,
    Pi.add_apply]
  rw [show (fun x : ZMod 2 => (eTop b : Module.End ℂ (ZMod b → ℂ)) (fun _ => f x) p.2) = f from
      funext fun x => congrFun (eTop_const (f x)) p.2,
    show (fun x : ZMod 2 => ((1 - eTop b : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) (fun _ => f x) p.2) = 0 from
      funext fun x => congrFun (one_sub_eTop_const (f x)) p.2,
    map_zero, Pi.zero_apply, add_zero]

set_option synthInstance.maxHeartbeats 200000 in
/-- φ'(D_s) = φ(D_s)（`shellLift` と D の側で一致）。 -/
theorem twLift_dind (hab : Nat.Coprime 2 b) (s : ℕ) :
    twLift hab ⟨_, mulLeft_dind_mem 2 s⟩ = shellLift hab ⟨_, mulLeft_dind_mem 2 s⟩ := by
  rw [twLift_apply, twTens_apply, twist2_dind, ← TensorProduct.tmul_add,
    show eTop b + (1 - eTop b) = 1 by abel, shellLift_apply]

theorem twist2_geps (s : ℕ) : ∃ t, twist2 ⟨_, convL_geps_mem 2 s⟩ = ⟨_, convL_geps_mem 2 t⟩ := by
  by_cases h1 : s = 1
  · subst h1; exact ⟨2, twist2_geps_one⟩
  by_cases h2 : s = 2
  · subst h2; exact ⟨1, twist2_geps_two⟩
  have hs : ¬ s ∣ 2 := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> contradiction
  refine ⟨0, ?_⟩
  rw [esub_eq_zero hs, map_zero, esub_eq_zero (by norm_num : ¬ (0 : ℕ) ∣ 2)]

set_option synthInstance.maxHeartbeats 200000 in
theorem tensor_eTop_mem_spanE (hab : Nat.Coprime 2 b) (t : ℕ) :
    (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 t⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
      Module.End ℂ (ZMod (2 * b) → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps (2 * b) u)) := by
  by_cases ht : t ∣ 2
  · rw [eTop, shellAlgTensorEquiv_geps hab ht dvd_rfl]
    exact Submodule.subset_span ⟨t * b, rfl⟩
  · rw [esub_eq_zero ht, TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _

set_option synthInstance.maxHeartbeats 200000 in
/-- φ' は Part 258 の条件 (i)(ii) を満たす。 -/
theorem compat_twLift (hab : Nat.Coprime 2 b) : Compat (dvd_mul_right 2 b) (twLift hab) := by
  have hL := (compatF_shellLift hab).1
  refine ⟨twLift_pull hab, fun s => ?_, fun s => ?_⟩
  · rw [twLift_dind]; exact hL.2.1 s
  · obtain ⟨t, ht⟩ := twist2_geps s
    have e : (twLift hab ⟨_, convL_geps_mem 2 s⟩ : Module.End ℂ (ZMod (2 * b) → ℂ)) =
        (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 s⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
          Module.End ℂ (ZMod (2 * b) → ℂ)) +
          (shellLift hab ⟨_, convL_geps_mem 2 t⟩ : Module.End ℂ (ZMod (2 * b) → ℂ)) -
          (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 t⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
            Module.End ℂ (ZMod (2 * b) → ℂ)) := by
      rw [twLift_apply, twTens_apply, ht, shellLift_apply, one_sub_eTop_eq, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, map_add, map_add, map_smul, Subalgebra.coe_add, Subalgebra.coe_add,
        Subalgebra.coe_smul, neg_one_smul]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (tensor_eTop_mem_spanE hab s) (hL.2.2 t))
      (tensor_eTop_mem_spanE hab t)

theorem convL_geps_one_ne_zero (M : ℕ) [NeZero M] : PAG.Part15.convL (geps M 1) ≠ 0 := by
  intro h
  have h2 := congrArg (fourierConj M) h
  rw [fourierConj_convL_geps, map_zero] at h2
  have h3 := congrFun (LinearMap.congr_fun h2 1) 1
  rw [LinearMap.mulLeft_apply, LinearMap.zero_apply, Pi.mul_apply, Pi.one_apply, mul_one,
    Pi.zero_apply] at h3
  have hg : Nat.gcd M (1 : ZMod M).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.gcd_comm, ← Nat.gcd_rec]
    exact Nat.gcd_one_right M
  simp [dind, hg] at h3

set_option synthInstance.maxHeartbeats 200000 in
/-- **φ' ≠ `shellLift`**（1 < b）。 -/
theorem twLift_ne_shellLift (hab : Nat.Coprime 2 b) (hb : 1 < b) : twLift hab ≠ shellLift hab := by
  intro heq
  set z : TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
    (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) ⊗ₜ[ℂ] (⟨_, convL_geps_mem b 1⟩ : shellAlg b)
  have h1 : twTens (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) =
      (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) ⊗ₜ[ℂ] (1 : shellAlg b) := by
    apply (shellAlgTensorEquiv hab).injective
    have := congrArg (fun g : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) => g ⟨_, convL_geps_mem 2 1⟩) heq
    simpa only [twLift_apply, shellLift_apply] using this
  have hz0 : twTens (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) * z = 0 := by
    have hb1 : (b : ℕ) ≠ 1 := hb.ne'
    have hebe : eTop b * (⟨_, convL_geps_mem b 1⟩ : shellAlg b) = 0 := by
      rw [eTop, esub_mul_esub, ite_eq_right_iff.mpr (fun h => absurd h hb1)]
    have h21 : (⟨_, convL_geps_mem 2 2⟩ : shellAlg 2) * ⟨_, convL_geps_mem 2 1⟩ = 0 := by
      rw [esub_mul_esub, ite_eq_right_iff.mpr (fun h => absurd h (by norm_num))]
    rw [twTens_apply, twist2_geps_one, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, hebe, h21, TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero]
  have hz : z = 0 := by
    rw [h1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, esub_mul_esub] at hz0
    simpa only [↓reduceIte] using hz0
  have hΘ := congrArg (fun w => (shellAlgTensorEquiv hab w : Module.End ℂ (ZMod (2 * b) → ℂ))) hz
  simp only [z, shellAlgTensorEquiv_geps hab (one_dvd 2) (one_dvd b), mul_one, map_zero,
    ZeroMemClass.coe_zero] at hΘ
  exact convL_geps_one_ne_zero (2 * b) hΘ

/-- **(iii) を外すと一意でない**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) を満たす
A_2 → A_{2b} は少なくとも 2 つある（`shellLift` と φ'）。 -/
theorem not_existsUnique_compat (hab : Nat.Coprime 2 b) (hb : 1 < b) :
    ¬ ∃! φ : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b), Compat (dvd_mul_right 2 b) φ := by
  rintro ⟨φ, -, hu⟩
  exact twLift_ne_shellLift hab hb ((hu _ (compat_twLift hab)).trans (hu _ (compatF_shellLift hab).1).symm)

end twistLift

/-! ### 6. 無平方数の段の帰納系と、その極限（有向な部分系） -/

/-- 引き戻しは単射（N ∣ M）。
内部照合（2026-11-15）：Part 202（PAG206）の `pull_injective`（M = N·t の形）から直ちに出る（Lean で確認）。 -/
theorem pull_injective' (hNM : N ∣ M) : Function.Injective (PAG.Part201.pull hNM) := by
  obtain ⟨t, rfl⟩ := hNM
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  exact PAG.Part206.pull_injective N t

/-- (i) を満たす写像は単射。 -/
theorem compat_injective (hNM : N ∣ M) {φ : shellAlg N →ₐ[ℂ] shellAlg M} (hφ : Compat hNM φ) :
    Function.Injective φ := by
  intro S T h
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply pull_injective' hNM
  rw [← hφ.1, ← hφ.1, h]

/-- 素数の有限集合 S の積 N_S = ∏_{p ∈ S} p（無平方数）。 -/
def primeProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

theorem primeProd_pos (S : Finset Nat.Primes) : 0 < primeProd S :=
  Finset.prod_pos fun p _ => p.2.pos

instance (S : Finset Nat.Primes) : NeZero (primeProd S) := ⟨(primeProd_pos S).ne'⟩

theorem primeProd_udvd {S T : Finset Nat.Primes} (h : S ⊆ T) : UDvd (primeProd S) (primeProd T) := by
  have hmul : primeProd T = primeProd (T \ S) * primeProd S := by
    unfold primeProd; rw [Finset.prod_sdiff h]
  refine ⟨⟨primeProd (T \ S), by rw [hmul, mul_comm]⟩, ?_⟩
  rw [hmul, Nat.mul_div_cancel _ (primeProd_pos S)]
  unfold primeProd
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  rw [Nat.coprime_primes p.2 q.2]
  intro hpq
  have : p = q := Subtype.ext hpq
  subst this
  exact (Finset.mem_sdiff.mp hq).2 hp

/-- 無平方数の段の標準の写像 A_{N_S} → A_{N_T}（S ⊆ T）。 -/
noncomputable def sqMap (S T : Finset Nat.Primes) (h : S ≤ T) :
    shellAlg (primeProd S) →ₐ[ℂ] shellAlg (primeProd T) :=
  canon (primeProd_udvd h).1 (primeProd_udvd h).2

/-- **帰納系**：無平方数の段（素数の有限集合の包含）の上で、標準の写像は帰納系をなす。 -/
instance : DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h : shellAlg (primeProd S) → shellAlg (primeProd T))) where
  map_self S x := by
    show sqMap S S le_rfl x = x
    rw [sqMap, canon_self]; rfl
  map_map {U T S} hST hTU x := by
    show sqMap T U hTU (sqMap S T hST x) = sqMap S U (hST.trans hTU) x
    rw [← AlgHom.comp_apply, sqMap, sqMap, sqMap,
      canon_comp (primeProd_udvd hST) (primeProd_udvd hTU)]

/-- 無平方数の段の帰納極限（ℂ 加群として）。 -/
abbrev sqLim : Type :=
  Module.DirectLimit (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h).toLinearMap)

instance : DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => ((sqMap S T h).toLinearMap : shellAlg (primeProd S) → shellAlg (primeProd T))) :=
  inferInstanceAs (DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h : shellAlg (primeProd S) → shellAlg (primeProd T))))

/-- 各段 A_{N_S} は極限に単射で入る。 -/
theorem sqLim_of_injective (S : Finset Nat.Primes) :
    Function.Injective (Module.DirectLimit.of ℂ (Finset Nat.Primes)
      (fun S : Finset Nat.Primes => shellAlg (primeProd S)) (fun S T h => (sqMap S T h).toLinearMap) S) := by
  intro x y hxy
  obtain ⟨T, hST, hT⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact compat_injective (primeProd_udvd hST).1 (compatF_canon _ (primeProd_udvd hST).2).1 hT

end PAG.Part263


```

## 付録：使う定義 使う定義（前の鎖から、原文）
```lean
noncomputable def dind (N s : ℕ) : ZMod N → ℂ := fun ξ => if Nat.gcd N ξ.val = s then 1 else 0

/-- 双対殻 s のべき等元 ε_s = 𝓕⁻¹(1_{D_s})。 -/
noncomputable def geps (N s : ℕ) [NeZero N] : ZMod N → ℂ := 𝓕⁻ (dind N s)

def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)


noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom

theorem pull_apply {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) (x : ZMod N') :

noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))

/-- **5a.** A の元は U_a と可換。 -/
theorem shellAlg_comm_dil (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N)
    (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : T (dil a f) = dil a (T f) := by
  unfold shellAlg at hT

theorem shellAlg_eq_adjoin (N : ℕ) [NeZero N] : shellAlg N = Algebra.adjoin ℂ
    (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪ Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s))) :=
  rfl


noncomputable def shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (shellAlg a) (shellAlg b) ≃ₐ[ℂ] shellAlg (a * b) :=
  ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))).trans
    (Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective).symm


/-- フーリエ変換による共役 T ↦ 𝓕 T 𝓕⁻¹（End(ℂ^{ℤ/N}) の代数の自己同型）。 -/
noncomputable def fourierConj (N : ℕ) [NeZero N] :
    Module.End ℂ (ZMod N → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  LinearEquiv.conjAlgEquiv ℂ (ZMod.dft : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ))


variable {a b : ℕ} [NeZero a] [NeZero b]

/-- 互いに素な a, b で、A_a → A_{ab}、S ↦ Θ(S ⊗ 1)（Θ は Part 228 の `shellAlgTensorEquiv`）。 -/
noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))

theorem shellLift_apply (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab S = shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] (1 : shellAlg b)) := rfl

/-- C(φ(S)) = L(S)（C は CRT の共役）。
/-- **条件 3（殻と両立、D）**：φ(D_s) = Σ_{u ∣ b} D_{su}（s ∣ a）。 -/
theorem shellLift_dind (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, LinearMap.mulLeft ℂ (dind (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, mulLeft_dind_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_mulLeft_dind b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_dind hab hs (Nat.dvd_of_mem_divisors hu)

set_option synthInstance.maxHeartbeats 200000 in
/-- **条件 3（殻と両立、E）**：φ(E_s) = Σ_{u ∣ b} E_{su}（s ∣ a）。 -/
theorem shellLift_geps (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, PAG.Part15.convL (geps (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, convL_geps_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_convL_geps b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_geps hab hs (Nat.dvd_of_mem_divisors hu)

/-- φ は単射。 -/
theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) := by
  constructor
  · intro hex
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    exact no_compatible_hom hNM hp (hpd.trans (Nat.gcd_dvd_left _ _)) (hpd.trans (Nat.gcd_dvd_right _ _)) hex

    PAG.Part15.conv g (Pi.single 0 1) = g := by
  rw [PAG.Part15.conv_comm]; exact PAG.Part111.conv_single_gen g

/-- A_N の中の D_N（{0} の指示関数の掛け算）。 -/
noncomputable def dTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, mulLeft_dind_mem N N⟩
/-- A_N の中の E_N（定数 1/N の畳み込み）。 -/
noncomputable def eTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, convL_geps_mem N N⟩

```

