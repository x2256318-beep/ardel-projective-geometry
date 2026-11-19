# 入力 2（入力 1 の成果物を書き終えてから読む）：PAG265.lean の冒頭の説明（散文）
```
/-
アーデル射影幾何 — Part 261（PAG265、短期層の小さいノート、2026-11-19）：角の写像の帰納系とその極限（正の整数の整除の順序の上）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §1）の R-d「整除の順序全体での直極限」の残り。
- 2026-11-19 12:51 に著者が採用した（構築側の推薦）。
- 基礎文書の第 5 章（索引 5.2・5.5）の材料。新しい問いではない。

記号：
- `Lvl`（Part 254（PAG258））：正の整数を整除の前順序で並べた型。a ≤ b ⇔ a ∣ b で、有向（`IsDirectedOrder`、上界は積）。
- A_a = `shellAlg a.val`。
- φ = Part 260（PAG264）の `cornerHom`（非単位的な代数準同型）。

定義：
- `cornerSys a b h`（a ≤ b）：φ_{a,b} を線形写像として。
- `CornerLim`：ℂ 加群としての帰納極限 `Module.DirectLimit`。

Lean の文：
- `cornerSys_apply`：値（rfl）。
- 恒等の法則 φ_{a,a} = id（`cornerSys_self`。Part 260 の `cornerOp_self` から）。
- 合成の法則 φ_{b,c} ∘ φ_{a,b} = φ_{a,c}（`cornerSys_comp`。Part 260 の `cornerOp_comp` から）。
- `DirectedSystem` のインスタンス（上の 2 法則）。
- 各 A_a は極限 `CornerLim` に単射で入る（`cornerLim_of_injective`）。遷移写像の単射性（Part 260 の `cornerHom_injective`）から出る。

対比（前の Part の Lean の文との並置。新しい定理ではない）：
- 単位元を保ち殻を混ぜない写像は、互いに素な段にしかない（Part 258（PAG262）の `exists_compatible_hom_iff`）。
- その段の順序は有向でない（Part 259（PAG263）の `not_isDirected_udvd`）。
- 非単位的な角の写像は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなす（この Part）。

範囲（Lean にしていないもの）：
- 極限の代数の構造（掛け算）。極限は ℂ 加群としてだけとった。
  - Mathlib に、非単位的な代数の直極限の道具が見当たらないため。
  - 遷移写像は積を保つ（Part 260 の `cornerHom`）ので代数の構造が入る見込みだが、Lean の外。
- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（§1 の 08:41 の定義）。

位置づけ（ラベル）：
- ［再導出（小さい）］：直極限の一般論（Mathlib）と、前の Part の定理の組み合わせ。
- 新規候補はない。A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：索引の型 `Lvl` は Part 254（PAG258）にあり、それを使った。
- 同じ型の上の別の帰納系との関係：
  - Part 254 には、単数の上の関数の引き戻しの帰納系と極限 `Lim`（`ofL_injective`）がある。
  - Part 259 には、無平方数の段の極限 `sqLim`（`sqLim_of_injective`）がある。
  - どちらも別の系で、作りは同じ型（重複ではない）。
- 閉じる前の機械的な照合は、記録 `records/audit265/`。
-/
```
