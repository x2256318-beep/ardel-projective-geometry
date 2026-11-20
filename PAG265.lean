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
  - 非単位的な環の構造と ℂ のスカラー倍は Mathlib/Algebra/Colimit/DirectLimit.lean のインスタンスによる（`NonUnitalRing`、`Module`、積とスカラー倍の両立 `IsScalarTower`・`SMulCommClass` のインスタンスもある。2026-11-20 に `#synth` で確かめた：`DirectLimit.instIsScalarTower`・`DirectLimit.instSMulCommClass`）。遷移写像が非単位的な ℂ 代数準同型なので入る。
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
  - 局所的な単位元を持つ環の、Ánh–Márki の流儀の定義（有限集合ごとに冪等元 e があって F ⊆ eRe）の条件の形。Abrams の流儀（可換な冪等元の集合を求める）との異同と、文献の本文との照合は未確認（照合者の記憶による、確信度：低〜中）。
- 大域の単位元はない（`not_exists_left_one`）：極限には左単位元がない（したがって両側の単位元もない。右単位元がないことは Lean にしていない）。
  - 証明：u = ofCorner_c(U) が左単位元なら、d = 2c で u e_d = e_d と `ofCorner_cornerSys` から ofCorner_d(φ_{c,d}(U)) = ofCorner_d(1)、`ofCorner_injective` により φ_{c,d}(U) = 1 となる。
  - それは Part 260 の `cornerOp_one_mul` と `cornerOp_one_ne_one`（c < d）に反する。

補足（照合者の指摘）：
- 恒等と合成の 2 法則は殻代数の構造を使わない（Part 260 の `cornerOp_self`・`cornerOp_comp` は End(ℂ^{ℤ/a}) 全体の文）。正規化なしでも成り立つこと（係数の積が合えばよい）は手計算で、Lean の文は正規化つき。
- 正規化 N/M が効くのは φ の乗法性、したがって極限に積の構造があること（正規化なしでは φ'(S)φ'(T) = (M/N)φ'(ST)、手計算）。φ(1) ≠ 1 自体は正規化によらない（階数による手計算）。
- 単位元がないことの証明：Lean の証明は d = 2c をとり、`ofCorner_injective` と `cornerOp_one_ne_one`（N ∣ M、N < M のどの段でも成り立ち、gcd によらない）を使う。c が偶数ならこの段は素数冪の段だが、d を c の倍数で c より大きいレベル（例：c を割らない素数 p で d = pc）に替えても同じ筋が通るので、素数冪の段は要らない見込み（手計算）。無平方数の段だけの部分系（上界は lcm）でもこの取り方で通る見込み（Lean にしていない）。
- 局所的な単位元の 3 つの文（1 元ごと、べき等と順序、有限集合ごと）は、有向な添字の上で単位的な環を乗法的な写像でつないだ直極限ならどれでも成り立つ一般の事実（単射性も φ(1) ≠ 1 も使わない）。「非単位的」という内容を運ぶのは `not_exists_left_one` だけ（照合者の指摘）。

対比（前の Part の Lean の文との並置。新しい定理ではない）：
- N ∣ M のとき、引き戻しと両立し、単位元を保ち、殻を混ぜない（強い読み）代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、そのときに限る（Part 258（PAG262）の `exists_compatible_hom_iff`）。
- そのような段（a ∣ b かつ gcd(a, b/a) = 1、ユニタリ約数の順序）は有向でない（Part 259（PAG263）の `not_isDirected_udvd`。2 と 4 に共通の上界がない）。
- Part 260 の角の写像は、N < M の段で単位元を保たない。D 側は殻の span に入らない（(2,4)・s = 2 は Lean。N < M のすべての s ∣ N で入らないことは数値（M ≤ 30 の 81 組）。Part 260）。
- この写像は、素数冪の段を含む正の整数の整除の順序全体（有向）の上で帰納系をなし、極限は局所的な単位元を持つ非単位的な代数になる（この Part）。

範囲（Lean にしていないもの）：
- 極限の具体形（Ẑ 上の局所定数関数への作用。盲検の手計算）と、Bost–Connes との対応。
- 像が角全体であること（Part 260 でも Lean の外）。
- 右単位元がないこと。部分系（無平方数の段など）での同じ文。
- 完備化（L²(Ẑ)、C* 完備化）はとらない。完備化は解像度が落ちる側の操作と読み、極限は直極限の側でとった（CLAUDE.md §1 の 08:41 の定義）。

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
  - 足した 3 定理：全宣言 4485 件、3·20·2 = 120 回、一致なし。Mathlib の `IsIdempotentElem.one`・`IsIdempotentElem.map` から `ofCorner_one_mul_self` が直ちに出る（照合者の指摘、B。照合者の確信度は中だったが、2026-11-20 に `IsIdempotentElem.one.map (ofCorner a)` の 1 行が通ることを Lean で確かめた。宣言は消していない）。
- 照合は、独立照合 2 回（最初の版、組み直した版。形式文と定義だけ）と、再照合 1 回（足した 3 定理と直した文面）。著者は 2026-11-19 19:58 の判断で、PAG265 はこの照合で条件を満たすとした（引き継ぎメモの記録：「PAG265 は独立照合 2 回と再照合 1 回（形式文が先）で条件を満たす」）。
  - 2 回目の独立照合の指摘を受けて 3 定理（べき等、順序、有限集合版）を足した。
  - 再照合の指摘 11 点（単位元がないことの証明の段の取り方、単射性の段、正規化の効き方、量化など）を直した。
  - 再照合の後の直しは主張を狭めるか明確にするものと申告し、補足8の停止の規約の範囲として尾の台帳は空としたが、2026-11-19 19:58 の著者の規則により台帳 L4 に戻した（未照合）。2026-11-20 の統合照合 II-a（`records/audit266/integrated/`）で照らし、その指摘の直しは台帳 L7。記録 `records/audit265/`。
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

/-- **局所的な単位元**：極限のどの元 x にも、ある a があって、e_a = ofCorner_a(1)（A_a の単位元の像）は x = e_a x = x e_a を満たす。 -/
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

/-- **局所的な単位元（有限集合版）**：極限の有限部分集合 F ごとに、ある a があって、e_a = ofCorner_a(1) が F のどの元も両側から固定する
（e_a のべき等性は `ofCorner_one_mul_self`。F ⊆ e_a·極限·e_a はこの文から直ちに出るが、Lean の文ではない。Ánh–Márki の流儀の条件の形で、文献の本文とは未照合）。 -/
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
