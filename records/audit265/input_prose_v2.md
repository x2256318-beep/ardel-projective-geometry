# 入力 2（入力 1 の成果物を書き終えてから読む）：PAG265.lean の冒頭の説明（散文）
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
- `CornerLim`：Mathlib の一般の `DirectLimit`（Mathlib/Algebra/Colimit/DirectLimit.lean）による帰納極限。
  - 遷移写像が非単位的な ℂ 代数準同型なので、Mathlib のインスタンスにより、非単位的な環の構造と ℂ のスカラー倍を持つ。
- `ofCorner a`：標準の写像 A_a → 極限（`DirectLimit.NonUnitalAlgebra.of`、非単位的な ℂ 代数準同型）。

Lean の文：
- 恒等の法則 φ_{a,a} = id（`cornerSys_self`。Part 260 の `cornerOp_self` から）。
- 合成の法則 φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（`cornerSys_comp`。Part 260 の `cornerOp_comp` から）。
- `DirectedSystem` のインスタンス（上の 2 法則）。
- 標準の写像の値（`ofCorner_apply`、rfl）。系の写像との両立 ofCorner_b ∘ φ_{a,b} = ofCorner_a（`ofCorner_cornerSys`）。
- 各 A_a は極限に単射で入る（`ofCorner_injective`）。
  - 遷移写像の単射性（Part 260 の `cornerHom_injective`）を、Mathlib の `DirectLimit.mk_injective` に当てはめた。
- **局所的な単位元**（`exists_local_unit`）：極限のどの元 x にも、ある a があって、e_a = ofCorner_a(1) が e_a x = x = x e_a を満たす。
- **大域の単位元はない**（`not_exists_left_one`）：極限には左単位元がない。
  - 証明：u = ofCorner_c(U) が左単位元なら、d = 2c で φ_{c,d}(U) = 1 となる。
  - それは Part 260 の `cornerOp_one_mul` と `cornerOp_one_ne_one`（c < d）に反する。

補足（照合者の指摘）：
- 恒等と合成の 2 法則は、`End(ℂ^{ℤ/a})` 全体で正規化なしでも成り立ち、殻代数の構造を使わない。
- 正規化 N/M が効くのは、乗法性（局所的な単位元と、単位元がないこと）の側。

対比（前の Part の Lean の文との並置。新しい定理ではない）：
- 引き戻しと両立し、単位元を保ち、殻を混ぜない（強い読み）代数準同型 A_N → A_M があるのは、N ∣ M で gcd(N, M/N) = 1 のときに限る（Part 258（PAG262）の `exists_compatible_hom_iff`）。
- そのような段（a ∣ b かつ gcd(a, b/a) = 1、ユニタリ約数の順序）は有向でない（Part 259（PAG263）の `not_isDirected_udvd`。2 と 4 に共通の上界がない）。
- 単位元を保たず、D 側で殻の span に入らない角の写像（Part 260）は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。

範囲（Lean にしていないもの）：
- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
- 像が角全体であること（Part 260 の範囲）。
- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（§1 の 08:41 の定義）。

位置づけ（ラベル）：
- ［再導出（小さい）］：直極限の一般論（Mathlib）と前の Part の定理の組み合わせ。
- 局所的な単位元を持つ非単位的な環（rings with local units）は標準の概念。
- 新規候補はない。A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った。
- 同じ型の上の別の帰納系との関係：
  - Part 254 には、単数の上の関数の引き戻しの帰納系と ℂ 加群の極限 `Lim`（`ofL_injective`）がある。
  - Part 259 には、無平方数の段の極限 `sqLim`（`sqLim_of_injective`）がある。
  - どちらも `Module.DirectLimit` による別の系で、作りは同じ型（重複ではない）。
- Mathlib の名前の検索（照合者の指摘を受けて）：
  - Mathlib/Algebra/Colimit/DirectLimit.lean に、一般の `DirectLimit` の非単位的な環・代数の構造（`NonUnitalRing` のインスタンス、`DirectLimit.NonUnitalAlgebra.of`）がある。
  - Mathlib/Order/DirectedInverseSystem.lean に `DirectLimit.mk_injective` がある。
  - 最初の版は `Module.DirectLimit`（ℂ 加群）だけで組み、「Mathlib に非単位的な代数の直極限の道具が見当たらない」と書いていた。これは誤りだったので、一般の `DirectLimit` で組み直した。
- 閉じる前の機械的な照合（全宣言 4483 件、対象 11 件、候補上位 20、380 回）：
  - 下書きの `cornerSys_apply` が Part 260（PAG264）の `cornerHom_coe` と、定義を開けば同じ文（A）だったので消した。
  - ほかに一致と出たのは自動生成の congr_simp だけ。
- 独立照合は記録 `records/audit265/`。
-/
```
