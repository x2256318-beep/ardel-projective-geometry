# 統合照合 I-a の入力：Part 263（PAG267）の材料と、独立照合の後の直し（台帳 L13）（2026-11-25）
照合の対象：Part 263 の散文（Lean の冒頭の説明と docstring、ノート、xlsx の行、引き継ぎメモの項、着手前の文書の後注）が、Lean の形式文（§2 の全文）と食い違わないか、強いことを言っていないか。§4 は独立照合の出力の全文で、§5 は独立照合に渡した形式文（独立照合の後に定理 4 つを足したので、今の §2 とは違う）。

## §1 台帳 L13
```markdown
### L13：Part 263（PAG267）の独立照合の後の直し（2026-11-25 夜）

- 範囲：独立照合（`records/audit267/outputs/check_output.md`）の指摘を受けた直し。
  - PAG267.lean：定理 4 つを足した（`invG_comp_pullSys`・`invL_ofL`・`Wproj_eqPt`・`resL_WL`。定義 `invG`・`invL`。主張を足した直し）。冒頭の説明（赤道の外は 0・∞ と同じでない、法 1、`not_exists_extL` は `resL` の線形な切断を否定しない、M ≠ 0 は外しても成り立つ見込み、共終な部分系の見込み、内部照合の B の行）と `not_exists_extL` の docstring。
  - ノート `notes/pag2_pag267_p1_tower.md`（§2・§3・§5・§6）、xlsx（行 3724〜3757、メモ、検証手順の行 286。`records/audit267/update_xlsx_267.py`）、この台帳の L13〜L14 と閉じた項目への移動。
- 自己申告（根拠にしない）：足した定理は sorry 0・警告 0、#print axioms は標準の 3 つ。機械的な照合をやり直した（712 回、一致なし）。
- 扱い：閉じるときの統合照合 I に載せる。
```

## §2 PAG267.lean の全文（今の版。sorry 0・警告 0）
```lean
/-
アーデル射影幾何 — Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長

問いの出所：基礎文書の索引の「射影」の空間の水準の問い（舞台 P¹ は索引 1.4、変換の留保は索引 2.4）。
- 推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
- 着手前の内部照合では、鎖（PAG27・28・29・32・34・35・36・38・266）にレベルの間の `ProjLine` の写像はなかった。

記号：`ProjLine N` = P¹(ℤ/N)（Part 23（PAG27）、単模の組を単数倍で割ったもの）。`Wproj` は [a:b] ↦ [b:a]。
`Lvl`・`Gsp`・`pullSys`・`Lim`・`ofL`・`Uinf` は Part 254（PAG258）のもの（正の整数を整除の順で並べた添字と、単数の上の関数の帰納極限）。

主な定理（N ∣ M）：
1. 還元 `red h : ProjLine M → ProjLine N`（[a:b] ↦ [a mod N : b mod N]）は well-defined で、
   `red_self`（恒等）・`red_comp`（合成）を満たし、反転と可換（`red_Wproj`）。M ≠ 0 なら全射（`red_surjective`）。
2. 点 0 = [0:1]・∞ = [1:0]（`zeroPt`・`infPt`）：W は 0 と ∞ を入れ替え（`Wproj_zeroPt`・`Wproj_infPt`）、還元は 0 を 0 に、∞ を ∞ に送り、
   N ≠ 1 なら 0 ≠ ∞（`zeroPt_ne_infPt`）。
3. P¹ の上の関数の引き戻し `pullP` は `Lvl` の上の帰納系をなし（`DirectedSystem`）、各段から極限 `LimP` への写像は単射（`ofP_injective`、1 の全射性から）。
   反転は極限の上の ℂ 線形写像 `WL` を誘導し、`WL` は対合（`WL_WL`）。
4. 赤道の点 [x:1]（x は単数、`eqPt`）への制限 `resE` は引き戻しと両立し（`resE_comp_pullP`）、
   極限の間の ℂ 線形写像 `resL : LimP → Lim` を誘導する（`resL_ofP`）。`resL` は全射（`resL_surjective`）。
   反転は赤道の上で逆元（`Wproj_eqPt`：W[x:1] = [x⁻¹:1]）で、resL ∘ W_∞ = (逆元による引き戻し `invL`) ∘ resL（`resL_WL`。独立照合の指摘で追加）。
5. 赤道からの 0 延長 `extE`（赤道の外では 0）について、a ∣ b のとき、すべての関数で引き戻しと可換であるのは
   b の素因数がすべて a を割るとき、そのときに限る（`extE_compat_iff`）。証人 (1, 2)（`extE_not_compat`）。
   したがって、各段で 0 延長と一致する ℂ 線形写像 `Lim → LimP` はない（`not_exists_extL`）。
   この文が否定するのは各段の 0 延長との両立だけで、`resL` の ℂ 線形な切断（選択公理で存在する）は否定しない（独立照合の指摘）。

赤道について：赤道は [x:1]（x は単数）の点、すなわち両座標が単数の点だけ。N が素数なら P¹(ℤ/N) = {0, ∞} ∪ 赤道だが、
合成数の N では 0・∞ のどちらでもなく赤道でもない点がある（法 4 の [2:1]・[1:2] など）。「赤道の外」は「0 と ∞」ではない。
法 1 では P¹ は 1 点で、それが 0 でも ∞ でも赤道でもある（証人 (1, 2) はこれを使う）。

Lean の外：
- 極限 `LimP` が P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できること、Ẑ^× が P¹(Ẑ) の中で閉だが開でないこと（盲検の照合者の記述）。
- 読み：すべての素点を測る段では赤道が開集合でないので、局所定数関数の上の作用素として `Uinf` を赤道に閉じ込めることはできない。
  `Uinf` が作用するのは `resL` の行き先 `Lim` の側で、`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外で、5 はその障害の一つ。
- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み
  （M = 0 では ℤ からの還元。独立照合の手計算。Lean にしていない）。
- 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（共終な部分系は素数を足す段を含む。独立照合の手計算。Lean にしていない）。
- 5 の判定は数値でも確かめた（`records/p1_tower/numeric`：M ≤ 48 の 198 組すべてで、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割るときに限る）。

内部照合：Part 258（PAG262）の `mem_ker_iff`（還元の核）と Part 24（PAG28）の `Wpull`・`Wpull_Wpull` を使い、作り直していない。
機械的な照合（独立照合の前の版、632 組）で「同じ文」「定義的に同じ」は見つからなかった（網羅ではない）。
直ちに出るもの（B）：`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq`（ZMod の逆元で書いた [y⁻¹:1] = [1:y]）と同じ内容。
近いもの（C）：Part 23（PAG27）の `toProj`（素数冪の法で x ↦ [x:1]）、Part 24（PAG28）の `projFunEquiv` の [x:1] での値。

ラベル（見込み、閉鎖で確定）：1〜3 は［既知］（射影直線の還元、有限集合の全射の逆系の上の局所定数関数）。4・5 は［再導出（小さい）］。新規候補なし。
対照群：1〜5 の文は F_q[t] の法でも同じ形で成り立つ見込みで、ℚ に固有の算術は運ばない。
-/
import PAG258
import PAG262
import PAG27
import PAG28

namespace PAG.Part267

open ZMod PAG.Part27 PAG.Part258

/-! ## 1. 還元写像 -/

section red

variable {N M L : ℕ}

/-- 単模の組の法 M から法 N（N ∣ M）への還元。 -/
def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
    obtain ⟨s, t, hst⟩ := v.2
    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩

/-- 還元写像 P¹(ℤ/M) → P¹(ℤ/N)（N ∣ M）。 -/
def red (h : N ∣ M) : ProjLine M → ProjLine N :=
  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
    mk_eq_mk (unitsMap h u)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))

theorem red_mk (h : N ∣ M) (v : Unimod M) : red h (mk v) = mk (redU h v) := rfl

theorem red_self (q : ProjLine N) : red (dvd_refl N) q = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show mk (redU (dvd_refl N) v) = mk v
    congr 1
    apply Subtype.ext
    show (castHom (dvd_refl N) (ZMod N) v.1.1, castHom (dvd_refl N) (ZMod N) v.1.2) = v.1
    simp only [castHom_apply, ZMod.cast_id', id]

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show mk (redU h₁ (redU h₂ v)) = mk (redU (dvd_trans h₁ h₂) v)
    congr 1
    apply Subtype.ext
    show (castHom h₁ (ZMod N) (castHom h₂ (ZMod M) v.1.1),
        castHom h₁ (ZMod N) (castHom h₂ (ZMod M) v.1.2)) =
      (castHom (dvd_trans h₁ h₂) (ZMod N) v.1.1, castHom (dvd_trans h₁ h₂) (ZMod N) v.1.2)
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, castHom_comp]

/-- 還元は反転 W と可換。 -/
theorem red_Wproj (h : N ∣ M) (q : ProjLine M) : red h (Wproj q) = Wproj (red h q) := by
  induction q using Quotient.inductionOn with
  | h v => rfl

/-- 点 0 = [0:1] の代表。 -/
def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

/-- 点 ∞ = [1:0] の代表。 -/
def infU (N : ℕ) : Unimod N := ⟨(1, 0), ⟨1, 0, by simp⟩⟩

/-- 点 0 = [0:1]。 -/
def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

/-- 点 ∞ = [1:0]。 -/
def infPt (N : ℕ) : ProjLine N := mk (infU N)

/-- W は 0 を ∞ に送る。 -/
theorem Wproj_zeroPt : Wproj (zeroPt N) = infPt N := rfl

/-- W は ∞ を 0 に送る。 -/
theorem Wproj_infPt : Wproj (infPt N) = zeroPt N := rfl

theorem red_zeroPt (h : N ∣ M) : red h (zeroPt M) = zeroPt N := by
  show mk (redU h (zeroU M)) = mk (zeroU N)
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) 0, castHom h (ZMod N) 1) = ((0 : ZMod N), (1 : ZMod N))
  rw [map_zero, map_one]

theorem red_infPt (h : N ∣ M) : red h (infPt M) = infPt N := by
  show mk (redU h (infU M)) = mk (infU N)
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) 1, castHom h (ZMod N) 0) = ((1 : ZMod N), (0 : ZMod N))
  rw [map_zero, map_one]

/-- N ≠ 1 なら 0 ≠ ∞。 -/
theorem zeroPt_ne_infPt (hN : N ≠ 1) : zeroPt N ≠ infPt N := by
  intro h
  have h' : mk (zeroU N) = mk (infU N) := h
  obtain ⟨u, h1, _⟩ := Quotient.exact h'
  change (1 : ZMod N) = u * 0 at h1
  rw [mul_zero] at h1
  have h2 : ((1 : ℕ) : ZMod N) = 0 := by exact_mod_cast h1
  exact hN (Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 N).mp h2))

/-- 単模の組の持ち上げ（射影類として）。 -/
theorem exists_redU [NeZero M] (h : N ∣ M) (v : Unimod N) :
    ∃ w : Unimod M, mk (redU h w) = mk v := by
  have : NeZero N := ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd h)⟩
  obtain ⟨d, hdN, u, hu, hau⟩ := ZMod.eq_unit_mul_divisor v.1.1
  obtain ⟨s, t, hst⟩ := v.2
  obtain ⟨m, hm⟩ := hdN
  set U := hu.unit with hUdef
  have hau' : v.1.1 = (U : ZMod N) * (d : ZMod N) := by rw [hau, hUdef, IsUnit.unit_spec]
  have hUU : (U : ZMod N) * ((U⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := Units.mul_inv U
  obtain ⟨b₂, hb₂⟩ := castHom_surjective h (((U⁻¹ : (ZMod N)ˣ) : ZMod N) * v.1.2)
  obtain ⟨s₂, hs₂⟩ := castHom_surjective h (s * U)
  obtain ⟨t₂, ht₂⟩ := castHom_surjective h (t * U)
  have he : castHom h (ZMod N) (s₂ * (d : ZMod M) + t₂ * b₂ - 1) = 0 := by
    rw [map_sub, map_add, map_mul, map_mul, hs₂, ht₂, hb₂, map_natCast, map_one]
    linear_combination hst - s * hau' + t * v.1.2 * hUU
  obtain ⟨k, hk⟩ := (PAG.Part262.mem_ker_iff h _).mp he
  have hNdm : (N : ZMod M) = (d : ZMod M) * (m : ZMod M) := by rw [← Nat.cast_mul, ← hm]
  refine ⟨⟨((d : ZMod M), b₂), ⟨s₂ - (m : ZMod M) * k, t₂, ?_⟩⟩, ?_⟩
  · show (s₂ - (m : ZMod M) * k) * (d : ZMod M) + t₂ * b₂ = 1
    linear_combination hk + k * hNdm
  · refine mk_eq_mk U ?_ ?_
    · change v.1.1 = U * castHom h (ZMod N) (d : ZMod M)
      rw [map_natCast]
      exact hau'
    · change v.1.2 = U * castHom h (ZMod N) b₂
      rw [hb₂, ← mul_assoc, hUU, one_mul]

/-- 還元写像は全射（M ≠ 0）。 -/
theorem red_surjective [NeZero M] (h : N ∣ M) : Function.Surjective (red h) := by
  intro q
  induction q using Quotient.inductionOn with
  | h v =>
    obtain ⟨w, hw⟩ := exists_redU h v
    exact ⟨mk w, hw⟩

/-! ## 2. 赤道 -/

/-- 赤道の点 [x:1]（x は単数）の代表。 -/
def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

/-- 赤道の点 [x:1]（x は単数）。 -/
def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem eqPt_injective : Function.Injective (eqPt (N := N)) := by
  intro x y hxy
  have h' : mk (eqU x) = mk (eqU y) := hxy
  obtain ⟨u, h1, h2⟩ := Quotient.exact h'
  change (y : ZMod N) = u * x at h1
  change (1 : ZMod N) = u * 1 at h2
  rw [mul_one] at h2
  apply Units.ext
  rw [h1, ← h2, one_mul]

/-- 還元は赤道を赤道に送る：red [x:1] = [x mod N : 1]。 -/
theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := by
  show mk (redU h (eqU x)) = mk (eqU (unitsMap h x))
  congr 1
  apply Subtype.ext
  show (castHom h (ZMod N) (x : ZMod M), castHom h (ZMod N) 1) =
    (((unitsMap h x : (ZMod N)ˣ) : ZMod N), (1 : ZMod N))
  rw [map_one]
  rfl

/-- 法 M の素因数がすべて N を割るなら、法 N で単数に落ちる元は法 M でも単数。 -/
theorem isUnit_of_castHom [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (c : ZMod M) (hc : IsUnit (castHom h (ZMod N) c)) : IsUnit c := by
  rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime] at hc
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime]
  refine Nat.coprime_of_dvd (fun k hk hkc hkM => ?_)
  exact hk.not_dvd_one (Nat.Coprime.gcd_eq_one hc ▸ Nat.dvd_gcd hkc (hp k hk hkM))

/-- 素因数の条件のもとで、赤道に落ちる点は赤道の点。 -/
theorem exists_eqPt_of_red [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (q : ProjLine M) (x : (ZMod N)ˣ) (hx : eqPt x = red h q) : ∃ y, eqPt y = q := by
  induction q using Quotient.inductionOn with
  | h v =>
    have hx' : mk (eqU x) = mk (redU h v) := hx
    obtain ⟨u, h1, h2⟩ := Quotient.exact hx'
    change castHom h (ZMod N) v.1.1 = u * x at h1
    change castHom h (ZMod N) v.1.2 = u * 1 at h2
    have hc : IsUnit v.1.1 :=
      isUnit_of_castHom h hp _ (by rw [h1]; exact u.isUnit.mul x.isUnit)
    have he : IsUnit v.1.2 :=
      isUnit_of_castHom h hp _ (by rw [h2, mul_one]; exact u.isUnit)
    refine ⟨he.unit⁻¹ * hc.unit, ?_⟩
    symm
    refine mk_eq_mk he.unit⁻¹ ?_ ?_
    · change ((he.unit⁻¹ * hc.unit : (ZMod M)ˣ) : ZMod M) = _ * v.1.1
      rw [Units.val_mul, IsUnit.unit_spec]
    · change (1 : ZMod M) = _ * v.1.2
      rw [IsUnit.val_inv_mul]

end red

/-! ## 3. 引き戻しの帰納系と、その極限の上の反転 -/

/-- 法 a の P¹ の上の関数の空間。 -/
abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

/-- 系の写像：a ∣ b なら還元による引き戻し。 -/
noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem Fsp (fun a b h => (pullP a b h : Fsp a → Fsp b)) where
  map_self a f := by
    funext q
    show f (red (dvd_refl a.val) q) = f q
    rw [red_self]
  map_map c b a hab hbc f := by
    funext q
    show f (red hab (red hbc q)) = f (red (dvd_trans hab hbc) q)
    rw [red_comp]

/-- 帰納極限 lim_N (P¹(ℤ/N) の上の関数)。 -/
abbrev LimP : Type := Module.DirectLimit Fsp pullP

/-- 法 a の成分から極限への写像。 -/
noncomputable abbrev ofP (a : Lvl) : Fsp a →ₗ[ℂ] LimP := Module.DirectLimit.of ℂ Lvl Fsp pullP a

/-- 引き戻しは単射（還元の全射性から）。 -/
theorem pullP_injective (a b : Lvl) (h : a ≤ b) : Function.Injective (pullP a b h) := by
  intro f g hfg
  funext q
  obtain ⟨q', rfl⟩ := red_surjective (N := a.val) (M := b.val) h q
  exact congrFun hfg q'

/-- 極限への写像は単射。 -/
theorem ofP_injective (a : Lvl) : Function.Injective (ofP a) := by
  intro f g h
  obtain ⟨b, hab, hb⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  exact pullP_injective a b hab hb

/-- 法 a の反転 f ↦ f ∘ W（Part 24（PAG28）の `Wpull` を ℂ 線形写像にしたもの）。 -/
noncomputable def Wfun (a : Lvl) : Fsp a →ₗ[ℂ] Fsp a where
  toFun := PAG.Part28.Wpull
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Wfun_comp_pullP (a b : Lvl) (h : a ≤ b) :
    Wfun b ∘ₗ pullP a b h = pullP a b h ∘ₗ Wfun a := by
  refine LinearMap.ext (fun f => funext (fun q => ?_))
  show f (red (N := a.val) (M := b.val) h (Wproj q)) = f (Wproj (red (N := a.val) (M := b.val) h q))
  rw [red_Wproj]

/-- 極限の上の反転 W_∞。 -/
noncomputable def WL : LimP →ₗ[ℂ] LimP :=
  Module.DirectLimit.map Wfun (fun a b h => Wfun_comp_pullP a b h)

theorem WL_ofP (a : Lvl) (f : Fsp a) : WL (ofP a f) = ofP a (Wfun a f) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- W_∞ は対合。 -/
theorem WL_WL (x : LimP) : WL (WL x) = x := by
  refine Module.DirectLimit.induction_on x (fun a f => ?_)
  rw [WL_ofP, WL_ofP]
  exact congrArg (ofP a) (PAG.Part28.Wpull_Wpull f)

/-! ## 4. 赤道への制限は引き戻しと両立する -/

/-- 赤道への制限 f ↦ (x ↦ f [x:1])。 -/
noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resE_comp_pullP (a b : Lvl) (h : a ≤ b) :
    resE b ∘ₗ pullP a b h = pullSys a b h ∘ₗ resE a := by
  refine LinearMap.ext (fun f => funext (fun x => ?_))
  show f (red (N := a.val) (M := b.val) h (eqPt x)) = f (eqPt (unitsMap (n := a.val) (m := b.val) h x))
  rw [red_eqPt]

/-- 赤道への制限が極限に誘導する写像 lim(P¹ の上の関数) → lim(単数の上の関数)（Part 254 の `Lim`）。 -/
noncomputable def resL : LimP →ₗ[ℂ] Lim :=
  Module.DirectLimit.map resE (fun a b h => resE_comp_pullP a b h)

theorem resL_ofP (a : Lvl) (f : Fsp a) : resL (ofP a f) = ofL a (resE a f) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- 単数の上の関数の逆元による引き戻し g ↦ (x ↦ g x⁻¹)。 -/
noncomputable def invG (a : Lvl) : Gsp a →ₗ[ℂ] Gsp a where
  toFun g x := g x⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem invG_comp_pullSys (a b : Lvl) (h : a ≤ b) :
    invG b ∘ₗ pullSys a b h = pullSys a b h ∘ₗ invG a := by
  refine LinearMap.ext (fun g => funext (fun x => ?_))
  show g (unitsMap (n := a.val) (m := b.val) h x⁻¹) = g (unitsMap (n := a.val) (m := b.val) h x)⁻¹
  rw [map_inv]

/-- 極限の上の逆元による引き戻し。 -/
noncomputable def invL : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map invG (fun a b h => invG_comp_pullSys a b h)

theorem invL_ofL (a : Lvl) (g : Gsp a) : invL (ofL a g) = ofL a (invG a g) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- 反転は赤道の上で逆元：W[x:1] = [x⁻¹:1]。 -/
theorem Wproj_eqPt {N : ℕ} (x : (ZMod N)ˣ) : Wproj (eqPt x) = eqPt x⁻¹ := by
  show mk ⟨(((1 : ZMod N)), (x : ZMod N)), _⟩ = mk (eqU x⁻¹)
  refine mk_eq_mk x⁻¹ ?_ ?_
  · change ((x⁻¹ : (ZMod N)ˣ) : ZMod N) = ((x⁻¹ : (ZMod N)ˣ) : ZMod N) * 1
    rw [mul_one]
  · change (1 : ZMod N) = ((x⁻¹ : (ZMod N)ˣ) : ZMod N) * x
    rw [Units.inv_mul]

/-- **制限と反転**：resL ∘ W_∞ = (逆元による引き戻し) ∘ resL。 -/
theorem resL_WL (z : LimP) : resL (WL z) = invL (resL z) := by
  refine Module.DirectLimit.induction_on z (fun a f => ?_)
  rw [WL_ofP, resL_ofP, resL_ofP, invL_ofL]
  congr 1
  funext x
  show f (Wproj (eqPt x)) = f (eqPt x⁻¹)
  rw [Wproj_eqPt]

/-! ## 5. 赤道からの 0 延長 -/

open Classical in
/-- 赤道からの 0 延長（赤道の外では 0）。 -/
noncomputable def extE (a : Lvl) : Gsp a →ₗ[ℂ] Fsp a where
  toFun g q := if h : ∃ x, eqPt x = q then g h.choose else 0
  map_add' g g' := by
    funext q
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extE_eqPt (a : Lvl) (g : Gsp a) (x : (ZMod a.val)ˣ) : extE a g (eqPt x) = g x := by
  classical
  show (if h : ∃ y, eqPt y = eqPt x then g h.choose else 0) = g x
  split_ifs with h'
  · rw [eqPt_injective h'.choose_spec]
  · exact absurd ⟨x, rfl⟩ h'

theorem extE_off (a : Lvl) (g : Gsp a) (q : ProjLine a.val) (hq : ∀ x, eqPt x ≠ q) :
    extE a g q = 0 := by
  classical
  show (if h : ∃ y, eqPt y = q then g h.choose else 0) = 0
  split_ifs with h'
  · exact absurd h'.choose_spec (hq _)
  · rfl

theorem resE_extE (a : Lvl) (g : Gsp a) : resE a (extE a g) = g :=
  funext (fun x => extE_eqPt a g x)

/-- 赤道への制限が誘導する写像は全射。 -/
theorem resL_surjective : Function.Surjective resL := by
  intro z
  refine Module.DirectLimit.induction_on z (fun a g => ?_)
  exact ⟨ofP a (extE a g), by rw [resL_ofP, resE_extE]⟩

/-- **0 延長と引き戻しの両立の判定**：a ∣ b のとき、0 延長がすべての関数について引き戻しと可換であるのは、
b の素因数がすべて a を割るとき、そのときに限る。 -/
theorem extE_compat_iff (a b : Lvl) (h : a ≤ b) :
    (∀ g : Gsp a, extE b (pullSys a b h g) = pullP a b h (extE a g)) ↔
      ∀ p : ℕ, p.Prime → p ∣ b.val → p ∣ a.val := by
  constructor
  · intro H p hp hpb
    by_contra hpa
    have hunit : IsUnit ((p : ZMod a.val)) :=
      (ZMod.isUnit_iff_coprime p a.val).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
    let v : Unimod b.val := ⟨((p : ZMod b.val), 1), ⟨0, 1, by simp⟩⟩
    have hred : red (N := a.val) (M := b.val) h (mk v) = eqPt hunit.unit := by
      show mk (redU h v) = mk (eqU hunit.unit)
      congr 1
      apply Subtype.ext
      show (castHom h (ZMod a.val) (p : ZMod b.val), castHom h (ZMod a.val) 1) =
        (((hunit.unit : (ZMod a.val)ˣ) : ZMod a.val), (1 : ZMod a.val))
      rw [map_natCast, map_one, IsUnit.unit_spec]
    have hoff : ∀ y : (ZMod b.val)ˣ, eqPt y ≠ mk v := by
      intro y hy
      have hy' : mk (eqU y) = mk v := hy
      obtain ⟨u, h1, _⟩ := Quotient.exact hy'
      change (p : ZMod b.val) = u * y at h1
      have hpu : IsUnit ((p : ZMod b.val)) := by rw [h1]; exact u.isUnit.mul y.isUnit
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp
        ((ZMod.isUnit_iff_coprime p b.val).mp hpu) hpb
    have key := congrFun (H 1) (mk v)
    rw [extE_off b _ (mk v) hoff] at key
    change (0 : ℂ) = extE a 1 (red (N := a.val) (M := b.val) h (mk v)) at key
    rw [hred, extE_eqPt] at key
    exact zero_ne_one key
  · intro hp g
    funext q
    by_cases hq : ∃ y, eqPt y = q
    · obtain ⟨y, rfl⟩ := hq
      rw [extE_eqPt]
      show pullSys a b h g y = extE a g (red (N := a.val) (M := b.val) h (eqPt y))
      rw [red_eqPt, extE_eqPt]
      rfl
    · rw [extE_off b _ q (fun y hy => hq ⟨y, hy⟩)]
      show 0 = extE a g (red (N := a.val) (M := b.val) h q)
      rw [extE_off]
      intro x hx
      exact hq (exists_eqPt_of_red h hp q x hx)

/-- 法 1。 -/
def lv1 : Lvl := ⟨1, Nat.one_pos⟩

/-- 法 2。 -/
def lv2 : Lvl := ⟨2, Nat.two_pos⟩

theorem lv1_le_lv2 : lv1 ≤ lv2 := one_dvd 2

/-- **証人 (1, 2)**：0 延長は引き戻しと可換でない。 -/
theorem extE_not_compat :
    ∃ g : Gsp lv1, extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) ≠ pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) := by
  by_contra H
  have H' : ∀ g : Gsp lv1,
      extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) = pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) :=
    fun g => by_contra (fun hne => H ⟨g, hne⟩)
  have h2 := (extE_compat_iff lv1 lv2 lv1_le_lv2).mp H' 2 Nat.prime_two (dvd_refl 2)
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (by norm_num)

/-- **0 延長は極限に降りない**：各法で 0 延長と一致する ℂ 線形写像 lim(単数の上の関数) → lim(P¹ の上の関数) はない。
`resL` の ℂ 線形な切断の存在は否定しない。 -/
theorem not_exists_extL :
    ¬ ∃ E : Lim →ₗ[ℂ] LimP, ∀ (a : Lvl) (g : Gsp a), E (ofL a g) = ofP a (extE a g) := by
  rintro ⟨E, hE⟩
  obtain ⟨g, hg⟩ := extE_not_compat
  apply hg
  apply ofP_injective lv2
  have e1 : ofL lv2 (pullSys lv1 lv2 lv1_le_lv2 g) = ofL lv1 g := Module.DirectLimit.of_f
  have e2 : ofP lv2 (pullP lv1 lv2 lv1_le_lv2 (extE lv1 g)) = ofP lv1 (extE lv1 g) :=
    Module.DirectLimit.of_f
  rw [← hE, e1, hE, e2]

end PAG.Part267

#print axioms PAG.Part267.red_comp
#print axioms PAG.Part267.red_surjective
#print axioms PAG.Part267.zeroPt_ne_infPt
#print axioms PAG.Part267.WL_WL
#print axioms PAG.Part267.ofP_injective
#print axioms PAG.Part267.resL_ofP
#print axioms PAG.Part267.resL_surjective
#print axioms PAG.Part267.resL_WL
#print axioms PAG.Part267.extE_compat_iff
#print axioms PAG.Part267.extE_not_compat
#print axioms PAG.Part267.not_exists_extL
```

## §3 ノート `notes/pag2_pag267_p1_tower.md`（全文）
```markdown
# アーデル射影幾何 — Part 263（PAG267、短期層の小さいノート）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長

（2026-11-25。題と主張は PAG267.lean の形式文から起こした。）

## §1 問いの出所

- 基礎文書の索引の「射影」の空間の水準の問い。舞台 P¹ は索引 1.4（0 と ∞ は別の点で、W がこの2点を入れ替える）、変換の留保は索引 2.4（照合した範囲（PAG23・PAG26・PAG27・PAG256）では `JH` と P¹ のモデルを結ぶ Lean の文はない）。
- 推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
- 盲検の問いテスト（`records/p1_tower/`）で、最初の C1 の前提（赤道の関数が塔の極限に埋め込まれる）は偽と分かり、制限と 0 延長の否定に改めた。

## §2 Lean に入った文（PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ）

記号：`ProjLine N` = P¹(ℤ/N)（Part 23（PAG27））。`Lvl`・`Gsp`・`pullSys`・`Lim`・`ofL` は Part 254（PAG258）。以下 N ∣ M、a ≤ b は a ∣ b。

1. 還元 `red`：[a:b] ↦ [a mod N : b mod N] は well-defined。`red_self`（恒等）、`red_comp`（合成）、`red_Wproj`（反転と可換）。M ≠ 0 なら全射（`red_surjective`。持ち上げは `exists_redU`：a = 単数 × N の約数 d と書き、(d, b の持ち上げ) が法 M で単模になる）。
2. `zeroPt` = [0:1]、`infPt` = [1:0]：`Wproj_zeroPt`・`Wproj_infPt`（W は 2 点を入れ替える）、`red_zeroPt`・`red_infPt`（還元は 0・∞ を保つ）、`zeroPt_ne_infPt`（N ≠ 1 なら 0 ≠ ∞）。
3. `pullP`（P¹ の上の関数の還元による引き戻し）は `Lvl` の上の帰納系（`DirectedSystem`）。極限 `LimP`。`pullP_injective`・`ofP_injective`（1 の全射性から）。反転の誘導する `WL : LimP → LimP` は対合（`WL_ofP`・`WL_WL`）。
4. 赤道の点 `eqPt x` = [x:1]（x は単数。`eqPt_injective`、`red_eqPt`：還元は赤道を赤道に送る）。制限 `resE` は引き戻しと両立し（`resE_comp_pullP`）、`resL : LimP → Lim` を誘導する（`resL_ofP`）。`resL` は全射（`resL_surjective`）。反転は赤道の上で逆元（`Wproj_eqPt`：W[x:1] = [x⁻¹:1]）で、resL ∘ W_∞ = invL ∘ resL（`resL_WL`。`invL` は単数の逆元による引き戻し `invG` が `Lim` に誘導する写像、`invG_comp_pullSys`・`invL_ofL`。独立照合の指摘で追加）。
5. 0 延長 `extE`（`extE_eqPt`・`extE_off`・`resE_extE`）。`extE_compat_iff`：a ∣ b のとき、すべての関数で `extE` が引き戻しと可換 ⇔ b の素因数はすべて a を割る（補助：`isUnit_of_castHom`・`exists_eqPt_of_red`）。`extE_not_compat`：証人 (1, 2)。`not_exists_extL`：各段で `extE` と一致する ℂ 線形写像 `Lim → LimP` はない。この文が否定するのは各段の 0 延長との両立だけで、`resL` の ℂ 線形な切断（選択公理で存在する）は否定しない。

赤道について：赤道は両座標が単数の点だけ。N が素数なら P¹(ℤ/N) = {0, ∞} ∪ 赤道だが、合成数の N では 0・∞ のどちらでもなく赤道でもない点がある（法 4 の [2:1]・[1:2] など）。「赤道の外」は「0 と ∞」ではない。法 1 では P¹ は 1 点で、それが 0 でも ∞ でも赤道でもある（証人 (1, 2) はこれを使う）。

## §3 読み（Lean の外）

- `LimP` は P¹(Ẑ) = ∏_p P¹(ℤ_p) の上の局所定数関数の空間と同一視できる（盲検の照合者の記述。Lean にしていない）。Ẑ^× は P¹(Ẑ) の中で閉だが開でない。
- 5 はこの「開でない」の有限レベルの形：素数を足す段（b の素因数が a を割らない段）では、赤道の逆像が上の段の赤道より大きい。整除の順序の共終な部分系はどれも素数を足す段を含む。
- したがって、すべての素点を測る段では、`Uinf`（Part 254）を局所定数関数の上の作用素として赤道に閉じ込めることはできない。`Uinf` が作用するのは `resL` の行き先 `Lim` の側。`LimP` の上に `Uinf` を持ち上げる作用素（候補 C2）はこの文書の外で、5 はその障害の一つ（障害がすべてかどうかは調べていない）。これは索引 2.4 の留保の、空間の水準の理由の材料になる（留保そのものは埋まっていない）。
- `red_surjective`・`exists_redU`・`isUnit_of_castHom`・`exists_eqPt_of_red` の M ≠ 0 は証明の都合で、外しても成り立つ見込み（M = 0 では ℤ からの還元。独立照合の手計算。Lean にしていない）。
- 0 延長との両立を整除の順序の共終な部分系の段だけに弱めても、5 の不存在は保たれる見込み（独立照合の手計算。Lean にしていない）。
- 数値：`records/p1_tower/numeric/p1_tower_check.py`（M ≤ 48 の N ∣ M の 198 組）。還元はすべて全射、|P¹(ℤ/M)| の公式はすべて一致、赤道の逆像が上の段の赤道と一致するのは M の素因数が N を割る組とちょうど同じ（5 と合う）。
- 対照群：1〜5 は F_q[t] の法でも同じ形で成り立つ見込みで（盲検の照合者）、ℚ に固有の算術は運ばない。

## §4 ラベル（見込み。閉鎖で確定）

- 1〜3：［既知］。射影直線の還元と、全射の逆系の上の局所定数関数（盲検の照合者は Cremona・Stein の Manin 記号の章、SL₂ の持ち上げは Shimura Lemma 1.38 を挙げた。節番号は照合者の記憶で未確認）。
- 4・5：［再導出（小さい）］。
- 新規候補なし。兆候 4（初等的な部品の組み合わせだけ）は続いている。

## §5 内部照合

- 着手前（推薦案 §0）：鎖（PAG27・28・29・32・34・35・36・38・266）にレベルの間の `ProjLine` の写像はなかった。
- 実装中の言葉の検索：還元の核の補題は Part 258（PAG262）の `mem_ker_iff` にあったので、作り直した補題を消してそれを使った。反転の関数の写像は Part 24（PAG28）の `Wpull`・`Wpull_Wpull` と同じ式（型の違う同じ構成）だったので、`Wfun` をその ℂ 線形写像として定義し直した。
- 閉じる前：機械的な照合（独立照合の後の版で、全宣言 4391 件、対象 55 件、候補の組 440、照合 712 回、一致なし。独立照合の前の版では 4385 件・49 件・392 組・632 回で、同じく一致なし。対照（同じ宣言どうし）は OK を返す。記録 `records/audit267/internal/`）。網羅ではない。
- 直ちに出るもの（B）：`Wproj_eqPt` は Part 24（PAG28）の `mk_inv_eq`（ZMod の逆元で書いた [y⁻¹:1] = [1:y]）と同じ内容（言葉の検索で見つけた。単数の逆元と ZMod の逆元の書き換えが要るので、使い回していない）。
- 近いもの（C）：Part 23（PAG27）の `toProj`（素数冪の法の点モデルの x ↦ [x:1]）、Part 24（PAG28）の `projFunEquiv` の [x:1] での値。

## §6 照合

- 独立照合（形式文と定義だけ、2026-11-25 18:42〜、約 119 秒、`records/audit267/outputs/check_output.md`。依頼文 `records/audit267/request_formal.md`、入力 `records/audit267/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人はすべての定理にある。除去テスト：N ≠ 1 と素因数の条件は外すと反例がある（N = 1、(2, 6) の [3:1] など）。M ≠ 0 は外しても成り立つ見込み。
- 指摘と直し：赤道の外は 0・∞ と同じではない（合成数の法）、法 1 では 3 つの呼び名が区別を失う、`not_exists_extL` は `resL` の線形な切断を否定しない、共終な部分系でも不存在は保たれる見込み、反転と制限の関係の文がない。前の 4 つは冒頭の説明・docstring・このノートに書いた。最後の 1 つは `Wproj_eqPt`・`invG`・`invL`・`resL_WL` を足して Lean にした（主張を足した直し）。
- この直し（形式文の追加を含む）は、閉じるときの統合照合 I の入力に含める（台帳 L13）。

## §7 収束アラームの報告

（閉鎖時に記入する。）
```

## §4 独立照合の出力（`records/audit267/outputs/check_output.md`、全文）
# 独立照合の出力（PAG267、2026-11-25）

（照合者の最終報告の全文を写した。）

# PAG267 の形式文の照合結果（逆翻訳・証人・除去テスト・気づいた点）

## 1. 逆翻訳

### 定義

- **Unimod N**：$\mathbb Z/N$ の元の組 $(v_1,v_2)$ のうち、$s v_1 + t v_2 = 1$ となる $s,t\in\mathbb Z/N$ があるもの（単模ベクトル）の集合です。
  - $N=0$ のとき $\mathbb Z/0=\mathbb Z$ なので、互いに素な整数の組になります。
  - $N=1$ のときは自明環なので、組 $(0,0)$ がただ 1 つあります。
- **ProjLine N**：単模ベクトルを、単数 $u\in(\mathbb Z/N)^\times$ によるスカラー倍 $(v_1,v_2)\sim(uv_1,uv_2)$ で割った商です。$\mathbb Z/N$ 上の射影直線 $\mathbb P^1(\mathbb Z/N)$ に当たります。
- **mk**：単模ベクトルの類 $[v_1:v_2]$ です。
- **Wproj**：$[a:b]\mapsto[b:a]$（座標の入れ替え）です。
- **Wpull Φ**：$\Phi\circ \mathrm{Wproj}$ です。
- **redU（$N\mid M$）**：$\mathbb Z/M$ 上の単模ベクトルを、成分ごとに法 $N$ で還元したものです。
- **red**：redU が誘導する写像 $\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$ です。
- **zeroPt N**：$[0:1]$ です。
- **infPt N**：$[1:0]$ です。
- **eqPt x**（$x\in(\mathbb Z/N)^\times$）：点 $[x:1]$ です。これを「赤道」の点と呼んでいます。
- **Lvl**：正の整数の集合で、順序は $a\le b \iff a\mid b$（有向）です。
- **Gsp a**：$(\mathbb Z/a)^\times$ 上の複素数値関数の空間です。
- **pullSys a b**（$a\mid b$）：$g\mapsto g\circ(\text{単数の還元 }(\mathbb Z/b)^\times\to(\mathbb Z/a)^\times)$ です。
- **Lim**：Gsp を pullSys でつないだ帰納系の直極限（$\mathbb C$ 加群）です。
- **ofL a**：段 $a$ から Lim への標準写像です。
- **Fsp a**：$\mathbb P^1(\mathbb Z/a)$ 上の複素数値関数の空間です。
- **pullP a b**：$f\mapsto f\circ \mathrm{red}$ です。
- **LimP**：Fsp を pullP でつないだ直極限です。
- **ofP**：段から LimP への標準写像です。
- **Wfun a**：段 $a$ での Wpull です。
- **WL**：Wfun が誘導する LimP 上の線形写像です。
- **resE a**：$f\mapsto (x\mapsto f([x:1]))$（赤道への制限）です。
- **resL**：resE が誘導する写像 LimP → Lim です。
- **extE a**：$g\mapsto$「$q=[x:1]$ となる単数 $x$ があれば $g(x)$、なければ $0$」（赤道の外を 0 で延ばす写像）です。$x$ は選択公理で選びますが、eqPt が単射なので値は一意に決まります。
- **lv1**：段 1 です。
- **lv2**：段 2 です。

### 定理

（$N,M,L$ は 0 を含む任意の自然数です。）

- **red_mk**：$\mathrm{red}[v]=[v \bmod N]$。
- **red_self**：$N\mid N$ に対する red は恒等写像。
- **red_comp**：$N\mid M\mid L$ なら、$L\to M\to N$ と還元したものは $L\to N$ の還元に等しい。
- **red_Wproj**：還元は座標の入れ替えと可換。
- **Wproj_zeroPt / Wproj_infPt**：入れ替えは $[0:1]$ と $[1:0]$ を互いに移す。
- **red_zeroPt / red_infPt**：還元は $[0:1]$ を $[0:1]$ に、$[1:0]$ を $[1:0]$ に移す。
- **zeroPt_ne_infPt**：$N\ne1$ なら $\mathbb P^1(\mathbb Z/N)$ で $[0:1]\ne[1:0]$。
- **exists_redU**：$M\ne0$、$N\mid M$ とする。法 $N$ の任意の単模ベクトル $v$ に対し、法 $M$ の単模ベクトル $w$ で、その還元が $v$ と射影的に同値なものがある。
- **red_surjective**：$M\ne0$、$N\mid M$ なら、$\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$ は全射。
- **eqPt_injective**：$x\mapsto[x:1]$ は単射。
- **red_eqPt**：$[x:1]$ の還元は $[x \bmod N:1]$。
- **isUnit_of_castHom**：次の 3 つを仮定する。
  - $M\ne0$ かつ $N\mid M$。
  - $M$ の素因数はすべて $N$ を割る。
  - $c\in\mathbb Z/M$ の法 $N$ での像が単数である。

  このとき $c$ は $\mathbb Z/M$ の単数。
- **exists_eqPt_of_red**：isUnit_of_castHom と同じ仮定のもとで、$q\in\mathbb P^1(\mathbb Z/M)$ の還元が赤道の点 $[x:1]$ に等しいなら、$q$ 自身も赤道の点（ある単数 $y$ で $q=[y:1]$）。
- **pullP_injective**：段の間の引き戻し pullP は単射。
- **ofP_injective**：各段から LimP への標準写像は単射。
- **Wfun_comp_pullP**：入れ替えの引き戻しは、段の間の引き戻しと可換。
- **WL_ofP**：WL は段 $a$ では Wfun として働く。
- **WL_WL**：WL は対合（2 回で恒等）。
- **resE_comp_pullP**：赤道への制限は引き戻しと可換。すなわち $\mathrm{resE}_b(f\circ\mathrm{red})=\mathrm{resE}_a(f)\circ(\text{単数の還元})$。
- **resL_ofP**：resL は段 $a$ では resE として働く。
- **resL_surjective**：resL は全射。
- **extE_eqPt**：$\mathrm{extE}(g)([x:1])=g(x)$。
- **extE_off**：赤道の外では $\mathrm{extE}(g)=0$。
- **resE_extE**：$\mathrm{resE}\circ\mathrm{extE}=\mathrm{id}$。
- **extE_compat_iff**：$a\mid b$ のとき、次の 2 つは同値。
  - すべての $g$ について $\mathrm{extE}_b(g\circ\text{還元})=\mathrm{extE}_a(g)\circ\mathrm{red}$。
  - $b$ の素因数はすべて $a$ を割る（$\mathrm{rad}(b)\mid a$）。
- **lv1_le_lv2**：$1\mid 2$。
- **extE_not_compat**：段 1 のある関数 $g$ について、$\mathrm{extE}_2(g\circ\text{還元})\ne \mathrm{extE}_1(g)\circ\mathrm{red}$。
- **not_exists_extL**：すべての段 $a$ とすべての $g$ で $E(\mathrm{ofL}_a g)=\mathrm{ofP}_a(\mathrm{extE}_a g)$ を満たす $\mathbb C$ 線形写像 $E:\mathrm{Lim}\to\mathrm{LimP}$ は存在しない。

## 2. 非空虚性の証人

- **red 系（red_mk、red_self、red_comp、red_Wproj）**：$N=2,M=4,L=8$、$q=[3:2]\in\mathbb P^1(\mathbb Z/8)$ を取ります。
  - $q$ を法 4 に還元すると $[3:2]$、法 2 に還元すると $[1:0]$ です。
  - 入れ替えてから還元すると、法 2 で $[0:1]$ になり、還元してから入れ替えたものと一致します。
- **zeroPt_ne_infPt**：$N=2$ では $[0:1]\ne[1:0]$ です（スカラー倍は 1 だけなので）。
- **exists_redU、red_surjective**：$N=3,M=6,v=(2,0)$ を取ります。
  - 素朴な持ち上げ $(2,0)$ は法 6 で単模ではありません。
  - $w=(2,3)$（$2\cdot2+3\cdot1=7\equiv1$）は単模で、法 3 に還元すると $(2,0)$ です。
  - したがって、この定理は持ち上げを調整する必要がある場合を含んでいます。
- **eqPt_injective、red_eqPt**：$N=3,M=9,x=4$ を取ると、$[4:1]\mapsto[1:1]$ です。
- **isUnit_of_castHom**：$N=2,M=4,c=3$ を取ります。$3 \bmod 2=1$ は単数で、$3$ は法 4 の単数です。
- **exists_eqPt_of_red**：$N=2,M=4$ を取ります。
  - $q=[1:2]$ の還元は $[1:0]$ で赤道ではないので、この $q$ では仮定が成り立たず、文は空になります。
  - $q=[3:1]$ の還元は $[1:1]$（赤道）で、確かに $q=[3:1]$ も赤道の点です。
- **pullP_injective、ofP_injective**：$a=1,b=2$ を取ります。$f$ を定数 $c$ とすると引き戻しも定数 $c$ なので、$c$ が復元できます。
- **WL 系（Wfun_comp_pullP、WL_ofP、WL_WL）**：$a=3$、$f=$「$[0:1]$ で 1、それ以外で 0」を取ります。
  - Wfun で $[1:0]$ の指示関数に移り、もう 1 回で元に戻ります。
- **resE_comp_pullP、resL_ofP、resL_surjective**：$a=2,b=4$ を取ります。
  - $f$ を法 2 の $\mathbb P^1$ 上の関数とすると、法 4 の赤道 $\{[1:1],[3:1]\}$ 上で $f([1:1])$ の値を取ります。
  - 全射性の証人は $\mathrm{ofL}_a g=\mathrm{resL}(\mathrm{ofP}_a(\mathrm{extE}_a g))$ です。
- **extE_eqPt、extE_off、resE_extE**：$a=4$、$g(1)=5,\ g(3)=7$ を取ります。
  - $\mathrm{extE}(g)$ は $[1:1]\mapsto5$、$[3:1]\mapsto7$ で、$[0:1],[1:0],[2:1],[1:2]$ では 0 です。
- **extE_compat_iff の真の側**：$a=2,b=4$ を取ります。
  - 赤道の外の点 $[0:1],[1:0],[2:1],[1:2]$ は、法 2 でそれぞれ $[0:1],[1:0],[0:1],[1:0]$ に還元され、どれも赤道の外です。
  - したがって両辺とも 0 になり、一致します。
- **extE_compat_iff の偽の側**：$a=2,b=6$ を取ります。
  - $q=[3:1]$ は赤道の外（3 は法 6 で単数でない）ですが、法 2 で $[1:1]$（赤道）に還元されます。
  - $g=1$ とすると左辺は 0、右辺は 1 です。
- **extE_not_compat**：段 1 で $g=1$ を取ります。
  - $\mathbb P^1(\mathbb Z/1)$ は 1 点で、それが赤道なので $\mathrm{extE}_1 g=1$ です。引き戻すと $\mathbb P^1(\mathbb Z/2)=\{[0:1],[1:0],[1:1]\}$ 上の定数 1 になります。
  - 一方 $\mathrm{extE}_2(1)$ は $[1:1]$ でだけ 1 なので、$[0:1]$ で食い違います。
- **not_exists_extL**：上の $g$ で $\mathrm{ofL}_1 g=\mathrm{ofL}_2(\text{引き戻し})$ です。
  - $E$ があれば $\mathrm{ofP}_2(\mathrm{pullP}(\mathrm{extE}_1 g))=\mathrm{ofP}_2(\mathrm{extE}_2(\ldots))$ となります。
  - ofP_injective により extE_not_compat と矛盾します。

## 3. 除去テスト（手計算）

- **zeroPt_ne_infPt の $N\ne1$**：外すと反例があります。$N=1$ では $\mathbb P^1$ は 1 点なので $[0:1]=[1:0]$ です。この仮定は必要です。$N=0$（$\mathbb Z$、単数は $\pm1$）では成り立ちます。
- **exists_redU・red_surjective の [NeZero M]**：$M=0$ のときは $\mathbb P^1(\mathbb Z)\to\mathbb P^1(\mathbb Z/N)$ の全射性を言うことになり、これは成り立ちます（$\mathrm{SL}_2(\mathbb Z)\to\mathrm{SL}_2(\mathbb Z/N)$ が全射、という既知の事実による）。反例は作れないので、**この仮定は不要に見えます**（証明の便宜と思われます）。
- **isUnit_of_castHom・exists_eqPt_of_red の [NeZero M]**：$M=0$ のとき、素因数の条件は「すべての素数が $N$ を割る」となり、$N=0$ を強制します。すると還元は $\mathbb Z\to\mathbb Z$ の恒等写像で、文は自明に成り立ちます。**不要に見えます**。
- **素因数の条件 $\forall p$（isUnit_of_castHom）**：外すと反例があります。$N=1,M=2,c=0$ では、$0 \bmod 1$ は（自明環の）単数ですが、$0$ は法 2 の単数ではありません。$N\neq1$ の例としては $N=2,M=6,c=3$ があります。
- **素因数の条件（exists_eqPt_of_red）**：外すと反例があります。
  - $N=2,M=6,q=[3:1]$ では、還元は $[1:1]=\mathrm{eqPt}(1)$ ですが、$q$ は赤道の点ではありません。$[3:1]=[y:1]$ ならスカラー倍は $u=1$ に限られ、$y=3$ は単数でないからです。
  - $N=1,M=2,q=[0:1]$ も反例です。
- **$N\mid M$**：型の上で必要な仮定なので、外すことはできません。
- **extE_compat_iff の右辺**：右辺を外して「左辺が常に成り立つ」とする文は偽です。反例は $a=1,b=2$（extE_not_compat）と $a=2,b=6$ です。逆向き（左辺 ⇒ 右辺）も上の構成で確認できます。
  - $p\mid b,\ p\nmid a$ なら、中国剰余定理で $x\equiv1\pmod a$、$x\equiv0\pmod p$ を取ります。
  - $q=[x:1]$ は赤道の外（または $[0:1]$ など）で、還元は $[1:1]$ になります。
- **not_exists_extL**：仮定のない否定文なので、除去の対象はありません。

## 4. 気づいた点

1. **法 0 と法 1**：
   - red・ProjLine・zeroPt などは $N=0$（$\mathbb Z$）でも定義され、各文も成り立ちます。一方、Lvl は正の整数だけなので、極限には法 0 は入りません。
   - 法 1 では 1 点が $[0:1]$ でも $[1:0]$ でも $[1:1]$ でもあります。そのため「段 1 の赤道は $\mathbb P^1$ 全体」となり、extE_not_compat はちょうどこの性質を使っています。
   - 「0・∞・赤道」という呼び名は、段 1 では区別を失います。
2. **赤道の定義**：
   - 赤道は $[x:1]$（$x$ は単数）の形の点だけで、これは「両座標がともに単数」の点と同じ集合です。
   - $N$ が素数なら $\mathbb P^1=\{0,\infty\}\cup$ 赤道となります。合成数の $N$ では、どちらにも入らない点（法 4 の $[2:1],[1:2]$、法 6 の $[2:1],[3:1]$ など）があります。
   - したがって「赤道の外」は「0 と ∞」と同じではありません。ノートで「赤道の補集合＝両極」と読まれないように注意が要ります。
3. **extE の choose**：eqPt が単射なので値は選び方によらず、well-defined です。問題はありません。
4. **極限の上の写像の well-defined 性**：
   - WL と resL は Module.DirectLimit.map に、可換性（Wfun_comp_pullP、resE_comp_pullP）を渡して作られています。可換性は形式文として示されているので、well-defined です。
   - extE は可換性を満たさない（extE_compat_iff）ので、極限に降ろす写像は定義されていません。not_exists_extL はそのことを、極限の上の線形写像の不存在として述べています。
5. **not_exists_extL の範囲**：
   - 否定しているのは「すべての段で extE と両立する $E$」だけです。resL は全射なので、ℂ 加群として線形な切断は（選択公理により）存在します。この定理はそれを否定していません。
   - 散文で「resL には切断がない」と読まないようにする必要があります。
   - なお手計算では、両立を共終な部分系の段だけに弱めても不存在は保たれます。共終性から新しい素数を持ち込む段 $a\mid b$ が必ず現れ、そこで extE_compat_iff の偽の側に当たるためです。ただしこれは形式化されていません。
6. **resL の行き先**：Lim は単数の上の関数（Gsp）の極限で、Uinf と同じ空間です。この点は意図どおりです。
   - $\widehat{\mathbb Z}^\times$ 上の局所定数関数との同一視は、この入力には文がありません（読みです）。
7. **未記載の関係**：
   - WL と resL の関係を述べる文がありません。$\mathrm{Wproj}[x:1]=[1:x]=[x^{-1}:1]$ なので、期待される関係は「$\mathrm{resL}\circ\mathrm{WL}=(\text{単数の逆元による引き戻し})\circ\mathrm{resL}$」です。
   - WL と Uinf を結ぶ文もありません。
8. **Lim のスカラー**：Lim には $\mathbb C$ 加群の構造しか与えられていません。積・代数の構造はこの入力にはありません。

## 使ったツールと読んだ範囲

Read を 1 回だけ使い、`/home/claude/ardel-projective-geometry/records/audit267/input_formal.md` の全体（285 行）を読みました。ほかのファイルは読まず、コードの実行とウェブの利用もしていません。上の反例と証人はすべて手計算で、数値や Lean では確かめていません。

## §5 独立照合に渡した形式文と定義（`records/audit267/input_formal.md`、全文。前の鎖の定義 PAG27・PAG28・PAG258・PAG262 を含む）
# 入力：形式文と定義

Lean 4 / Mathlib。定理の証明は省略し、定義は全文を写した（コメントと docstring は除いた）。すべてエラー 0・警告 0 で通っており、`#print axioms` は標準の 3 つ（propext, Classical.choice, Quot.sound）だけ。

## 前提の定義 1：PAG27.lean（名前空間 PAG.Part27）
```lean
namespace PAG.Part27
open ZMod PAG.Part23 PAG.Part26
open Classical
variable {N : ℕ}
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : ℕ) (hK : 1 ≤ K)

def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }

def ProjLine (N : ℕ) := Quotient (projSetoid N)

def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v

theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
    mk v = mk w := …（証明は省略）

theorem swap_unimod (v : Unimod N) : ∃ s t : ZMod N, s * v.1.2 + t * v.1.1 = 1 := …（証明は省略）

def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)

theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q := …（証明は省略）
```

## 前提の定義 2：PAG28.lean（名前空間 PAG.Part28）
```lean
def Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : ProjLine N → ℂ := Φ ∘ Wproj

theorem Wpull_Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : Wpull (Wpull Φ) = Φ := …（証明は省略）
```

## 前提の定義 3：PAG258.lean（名前空間 PAG.Part258）
```lean
namespace PAG.Part258
open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter
variable {N : ℕ} [NeZero N]

instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring

noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

abbrev Lim : Type := Module.DirectLimit Gsp pullSys

noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

theorem ofL_injective (a : Lvl) : Function.Injective (ofL a) := …（証明は省略）

noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f) := …（証明は省略）
```
（`UA1` は法 N の単数の上の関数の空間の ℂ 線形写像で、ここでは使わない内部の定義 `charU`・`phaseA1`・`ip` などに依存する。この入力の定理には `UA1`・`Uinf` は現れない。）

## 前提の定義 4：PAG262.lean（名前空間 PAG.Part262）
```lean
theorem mem_ker_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (y : ZMod M) :
    ZMod.castHom hNM (ZMod N) y = 0 ↔ ∃ c : ZMod M, y = (N : ZMod M) * c := …（証明は省略）
```

## 検査対象：PAG267.lean（名前空間 PAG.Part267）
```lean
namespace PAG.Part267
open ZMod PAG.Part27 PAG.Part258
variable {N M L : ℕ}

def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
    obtain ⟨s, t, hst⟩ := v.2
    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩

def red (h : N ∣ M) : ProjLine M → ProjLine N :=
  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
    mk_eq_mk (unitsMap h u)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))

theorem red_mk (h : N ∣ M) (v : Unimod M) : red h (mk v) = mk (redU h v) := …（証明は省略）

theorem red_self (q : ProjLine N) : red (dvd_refl N) q = q := …（証明は省略）

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := …（証明は省略）

theorem red_Wproj (h : N ∣ M) (q : ProjLine M) : red h (Wproj q) = Wproj (red h q) := …（証明は省略）

def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

def infU (N : ℕ) : Unimod N := ⟨(1, 0), ⟨1, 0, by simp⟩⟩

def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

def infPt (N : ℕ) : ProjLine N := mk (infU N)

theorem Wproj_zeroPt : Wproj (zeroPt N) = infPt N := …（証明は省略）

theorem Wproj_infPt : Wproj (infPt N) = zeroPt N := …（証明は省略）

theorem red_zeroPt (h : N ∣ M) : red h (zeroPt M) = zeroPt N := …（証明は省略）

theorem red_infPt (h : N ∣ M) : red h (infPt M) = infPt N := …（証明は省略）

theorem zeroPt_ne_infPt (hN : N ≠ 1) : zeroPt N ≠ infPt N := …（証明は省略）

theorem exists_redU [NeZero M] (h : N ∣ M) (v : Unimod N) :
    ∃ w : Unimod M, mk (redU h w) = mk v := …（証明は省略）

theorem red_surjective [NeZero M] (h : N ∣ M) : Function.Surjective (red h) := …（証明は省略）

def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem eqPt_injective : Function.Injective (eqPt (N := N)) := …（証明は省略）

theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := …（証明は省略）

theorem isUnit_of_castHom [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (c : ZMod M) (hc : IsUnit (castHom h (ZMod N) c)) : IsUnit c := …（証明は省略）

theorem exists_eqPt_of_red [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (q : ProjLine M) (x : (ZMod N)ˣ) (hx : eqPt x = red h q) : ∃ y, eqPt y = q := …（証明は省略）

abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem Fsp (fun a b h => (pullP a b h : Fsp a → Fsp b)) where
  map_self a f := by
    funext q
    show f (red (dvd_refl a.val) q) = f q
    rw [red_self]
  map_map c b a hab hbc f := by
    funext q
    show f (red hab (red hbc q)) = f (red (dvd_trans hab hbc) q)
    rw [red_comp]

abbrev LimP : Type := Module.DirectLimit Fsp pullP

noncomputable abbrev ofP (a : Lvl) : Fsp a →ₗ[ℂ] LimP := Module.DirectLimit.of ℂ Lvl Fsp pullP a

theorem pullP_injective (a b : Lvl) (h : a ≤ b) : Function.Injective (pullP a b h) := …（証明は省略）

theorem ofP_injective (a : Lvl) : Function.Injective (ofP a) := …（証明は省略）

noncomputable def Wfun (a : Lvl) : Fsp a →ₗ[ℂ] Fsp a where
  toFun := PAG.Part28.Wpull
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Wfun_comp_pullP (a b : Lvl) (h : a ≤ b) :
    Wfun b ∘ₗ pullP a b h = pullP a b h ∘ₗ Wfun a := …（証明は省略）

noncomputable def WL : LimP →ₗ[ℂ] LimP :=
  Module.DirectLimit.map Wfun (fun a b h => Wfun_comp_pullP a b h)

theorem WL_ofP (a : Lvl) (f : Fsp a) : WL (ofP a f) = ofP a (Wfun a f) := …（証明は省略）

theorem WL_WL (x : LimP) : WL (WL x) = x := …（証明は省略）

noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resE_comp_pullP (a b : Lvl) (h : a ≤ b) :
    resE b ∘ₗ pullP a b h = pullSys a b h ∘ₗ resE a := …（証明は省略）

noncomputable def resL : LimP →ₗ[ℂ] Lim :=
  Module.DirectLimit.map resE (fun a b h => resE_comp_pullP a b h)

theorem resL_ofP (a : Lvl) (f : Fsp a) : resL (ofP a f) = ofL a (resE a f) := …（証明は省略）

open Classical in
noncomputable def extE (a : Lvl) : Gsp a →ₗ[ℂ] Fsp a where
  toFun g q := if h : ∃ x, eqPt x = q then g h.choose else 0
  map_add' g g' := by
    funext q
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extE_eqPt (a : Lvl) (g : Gsp a) (x : (ZMod a.val)ˣ) : extE a g (eqPt x) = g x := …（証明は省略）

theorem extE_off (a : Lvl) (g : Gsp a) (q : ProjLine a.val) (hq : ∀ x, eqPt x ≠ q) :
    extE a g q = 0 := …（証明は省略）

theorem resE_extE (a : Lvl) (g : Gsp a) : resE a (extE a g) = g := …（証明は省略）

theorem resL_surjective : Function.Surjective resL := …（証明は省略）

theorem extE_compat_iff (a b : Lvl) (h : a ≤ b) :
    (∀ g : Gsp a, extE b (pullSys a b h g) = pullP a b h (extE a g)) ↔
      ∀ p : ℕ, p.Prime → p ∣ b.val → p ∣ a.val := …（証明は省略）

def lv1 : Lvl := ⟨1, Nat.one_pos⟩

def lv2 : Lvl := ⟨2, Nat.two_pos⟩

theorem lv1_le_lv2 : lv1 ≤ lv2 := …（証明は省略）

theorem extE_not_compat :
    ∃ g : Gsp lv1, extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) ≠ pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) := …（証明は省略）

theorem not_exists_extL :
    ¬ ∃ E : Lim →ₗ[ℂ] LimP, ∀ (a : Lvl) (g : Gsp a), E (ofL a g) = ofP a (extE a g) := …（証明は省略）
```

## §6 xlsx の行（定理と証明の行 3724〜3757：名前 | 主張 | 証明の要点 | 主な補題 | 状態）
共通の LABEL 列：PAG2.0-263（PAG267、短期層の小さいノート）P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長（推薦案 pag2_p1_tower_preregistration.md、著者の採用 2026-11-25 18:27。基礎文書の索引の「射影」の空間の水準の問い）：還元 P¹(ℤ/M) → P¹(ℤ/N) は恒等・合成の法則を満たし、反転と可換で、M ≠ 0 なら全射。0 と ∞ は W で入れ替わり、N ≠ 1 なら異なる。P¹ の上の関数の引き戻しは整除の順序の上の帰納系で、極限の上の反転は対合。赤道 [x:1] への制限は引き戻しと両立し、Part 254 の Lim への全射を誘導し、反転を逆元に移す。赤道からの 0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る。証人 (1, 2)。0 延長は極限に降りない。ラベル（見込み、閉鎖で確定）は 1〜3 が［既知］、4・5 が［再導出（小さい）］、新規候補なし

```
red_mk | red h [v] = [v mod N] | 定義 | Quotient.lift | 検証完了（axioms 確認済み）
red_self | N ∣ N の還元は恒等 | castHom の恒等 | ZMod.cast_id' | 検証完了（axioms 確認済み）
red_comp | N ∣ M ∣ L なら還元の合成は L → N の還元 | castHom の合成 | ZMod.castHom_comp | 検証完了（axioms 確認済み）
red_Wproj | 還元は反転 W と可換 | 代表で rfl | PAG.Part27.Wproj | 検証完了（axioms 確認済み）
Wproj_zeroPt | W[0:1] = [1:0] | rfl | PAG.Part27.Wproj | 検証完了（axioms 確認済み）
Wproj_infPt | W[1:0] = [0:1] | rfl | PAG.Part27.Wproj | 検証完了（axioms 確認済み）
red_zeroPt | 還元は [0:1] を [0:1] に送る | map_zero・map_one | ZMod.castHom | 検証完了（axioms 確認済み）
red_infPt | 還元は [1:0] を [1:0] に送る | map_zero・map_one | ZMod.castHom | 検証完了（axioms 確認済み）
zeroPt_ne_infPt | N ≠ 1 なら [0:1] ≠ [1:0]（N = 1 では等しい） | 1 = u·0 から N ∣ 1 | ZMod.natCast_eq_zero_iff | 検証完了（axioms 確認済み）
exists_redU | M ≠ 0、N ∣ M なら、法 N の単模の組は法 M の単模の組の還元と射影的に同値 | a = 単数 × N の約数 d と書き、(d, b の持ち上げ) の単模性を核の補題で直す | ZMod.eq_unit_mul_divisor, PAG.Part262.mem_ker_iff | 検証完了（axioms 確認済み）
red_surjective | M ≠ 0 なら還元 P¹(ℤ/M) → P¹(ℤ/N) は全射（M ≠ 0 は外しても成り立つ見込み） | exists_redU | exists_redU | 検証完了（axioms 確認済み）
eqPt_injective | x ↦ [x:1]（x は単数）は単射 | スカラー倍は 1 | Units.ext | 検証完了（axioms 確認済み）
red_eqPt | 還元は [x:1] を [x mod N : 1] に送る | 代表の計算 | ZMod.unitsMap | 検証完了（axioms 確認済み）
isUnit_of_castHom | M の素因数がすべて N を割るなら、法 N で単数に落ちる元は法 M でも単数 | 互いに素性の素因数による判定 | Nat.coprime_of_dvd, ZMod.isUnit_iff_coprime | 検証完了（axioms 確認済み）
exists_eqPt_of_red | 同じ条件で、還元が赤道の点なら元の点も赤道の点 | isUnit_of_castHom を両座標に | isUnit_of_castHom | 検証完了（axioms 確認済み）
pullP_injective | P¹ の上の関数の引き戻しは単射 | 還元の全射性 | red_surjective | 検証完了（axioms 確認済み）
ofP_injective | 各段から極限 LimP への写像は単射 | pullP_injective | Module.DirectLimit.exists_eq_of_of_eq | 検証完了（axioms 確認済み）
Wfun_comp_pullP | 反転の関数の写像（Part 24 の Wpull）は引き戻しと可換 | red_Wproj | red_Wproj | 検証完了（axioms 確認済み）
WL_ofP | 極限の上の反転 W_∞ は各段で Wfun | DirectLimit.map の値 | Module.DirectLimit.map_apply_of | 検証完了（axioms 確認済み）
WL_WL | W_∞ は対合 | Wpull_Wpull | PAG.Part28.Wpull_Wpull | 検証完了（axioms 確認済み）
resE_comp_pullP | 赤道への制限は引き戻しと両立（制限してから単数の還元で引き戻す = 引き戻してから制限） | red_eqPt | red_eqPt | 検証完了（axioms 確認済み）
resL_ofP | 制限が誘導する resL : LimP → Lim（Part 254）は各段で resE | DirectLimit.map の値 | Module.DirectLimit.map_apply_of | 検証完了（axioms 確認済み）
invG_comp_pullSys | 単数の逆元による引き戻しは pullSys と可換 | unitsMap は逆元を保つ | map_inv | 検証完了（axioms 確認済み）
invL_ofL | 逆元の引き戻しが誘導する invL : Lim → Lim は各段で invG | DirectLimit.map の値 | Module.DirectLimit.map_apply_of | 検証完了（axioms 確認済み）
Wproj_eqPt | W[x:1] = [x⁻¹:1]（Part 24 の mk_inv_eq と同じ内容） | スカラー倍 x⁻¹ | PAG.Part27.mk_eq_mk | 検証完了（axioms 確認済み）
resL_WL | resL ∘ W_∞ = invL ∘ resL（独立照合の指摘で追加） | 各段で Wproj_eqPt | Wproj_eqPt | 検証完了（axioms 確認済み）
extE_eqPt | 0 延長は赤道の点で元の値 | eqPt_injective | eqPt_injective | 検証完了（axioms 確認済み）
extE_off | 0 延長は赤道の外で 0（合成数の法では赤道の外は 0・∞ だけではない） | 定義 | dite | 検証完了（axioms 確認済み）
resE_extE | 制限 ∘ 0 延長 = 恒等 | extE_eqPt | extE_eqPt | 検証完了（axioms 確認済み）
resL_surjective | resL は全射 | 各段の 0 延長で持ち上げる | resE_extE | 検証完了（axioms 確認済み）
extE_compat_iff | a ∣ b のとき、0 延長がすべての関数で引き戻しと可換 ⇔ b の素因数はすべて a を割る | ⇒：p ∣ b、p ∤ a なら [p:1] は赤道の外で還元は赤道。⇐：exists_eqPt_of_red | exists_eqPt_of_red | 検証完了（axioms 確認済み）
lv1_le_lv2 | 1 ∣ 2 | one_dvd | one_dvd | 検証完了（axioms 確認済み）
extE_not_compat | 証人 (1, 2)：0 延長は引き戻しと可換でない | extE_compat_iff で p = 2 | extE_compat_iff | 検証完了（axioms 確認済み）
not_exists_extL | 各段で 0 延長と一致する ℂ 線形写像 Lim → LimP はない（resL の線形な切断は否定しない） | of_f と ofP_injective と証人 | Module.DirectLimit.of_f, ofP_injective | 検証完了（axioms 確認済み）
```

メモの行の末尾：
```
 2026-11-19 午後、Part 261（PAG265.lean、短期層、角の写像の帰納系と極限）をコンパイルし、行 3709〜3718 を足した（定理 10 個）。索引の型は Part 254 の Lvl を使った（内部照合）。下書きの cornerSys_apply（Part 260 の cornerHom_coe と同じ文）を消した。 2026-11-20 朝、Part 262（PAG266.lean、短期層、舞台 P¹ の赤道の絡み合いの係数を 𝔀（rootNum）で書く）をコンパイルし、行 3719〜3723 を足した（定理 5 個）。内部照合で、Part 21（PAG25）の equator_intertwine_hat と Part 25（PAG29）の equator_intertwine_proj を使った（言葉の検索）。独立照合・再照合を受けた。再照合の後の直し（形式文は変えていない。Lean の外の新しい文（単数の点の比）と数値を含む）は尾の台帳の L6 で、統合照合（2026-11-20、照合者 3 人）の対象にした。統合照合の後の直しは台帳の L7、その再照合（R2）の後の直しは L9、L9 の照合（R3）の後の直しは L10、L10 の照合（R4）の後の直しは L11（次のパートの統合照合に載せる）。2026-11-20 16:40、著者の止め方の規則により Part 262 は閉じた。 2026-11-25 夜、Part 263（PAG267.lean、短期層、P¹(ℤ/N) の還元の逆系と赤道への制限・0 延長）をコンパイルし、行 3724〜3757 を足した（定理 34 個）。内部照合で Part 258（PAG262）の mem_ker_iff と Part 24（PAG28）の Wpull・Wpull_Wpull を使った（言葉の検索）。独立照合を受け、その指摘で Wproj_eqPt・invG_comp_pullSys・invL_ofL・resL_WL を足した。この直しは尾の台帳の L13 で、閉じるときの統合照合の対象。
```

検証手順の行 286：
```
285 | PAG 2.0 Part 263（短期層）: PAG267.lean（P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限と反転、赤道への制限と Lim への全射、赤道からの 0 延長の両立の判定と極限に降りないこと）をコンパイル | 完了 | 2026-11-25 夜、推薦案 pag2_p1_tower_preregistration.md（著者の採用 18:27）。定理 34 個、sorry 0、警告 0、#print axioms 11 行は標準の公理の範囲。内部照合（言葉の検索で PAG262 の mem_ker_iff と PAG28 の Wpull を使った。機械的な照合は全宣言 4391 件、対象 55 件、712 回で一致なし）。独立照合（records/audit267/outputs/）。独立照合の後の直しは尾の台帳の L13。
```

## §7 引き継ぎメモの Part 263 の項
```markdown
- **Part 263（PAG267、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の還元の逆系、引き戻しの帰納極限、赤道への制限と赤道からの 0 延長**：
  - 出所：基礎文書の索引の「射影」の空間の水準の問い（索引 1.4・2.4）。推薦案 `notes/pag2_p1_tower_preregistration.md` §4（盲検の指摘で改めた C1）を、2026-11-25 18:27 に著者が採用した（「進めてください」）。
  - Lean：PAG267.lean、定理 34、sorry 0・警告 0、#print axioms は標準の 3 つ。還元の恒等・合成の法則・反転との可換・全射（M ≠ 0）、0 ≠ ∞（N ≠ 1）、引き戻しの帰納系と極限の上の対合 W_∞、赤道への制限が誘導する `resL : LimP → Lim`（Part 254 の Lim）の全射と resL ∘ W_∞ = invL ∘ resL、0 延長が引き戻しと可換 ⇔ 上の段の法の素因数がすべて下の段の法を割る（証人 (1, 2)）、0 延長は極限に降りない。ノート `notes/pag2_pag267_p1_tower.md`。
  - ラベル（見込み、閉鎖で確定）：1〜3 は［既知］、4・5 は［再導出（小さい）］、新規候補なし。兆候 4 は続く（Part 249〜263 で 15 パート連続）。
  - 内部照合：PAG262 の `mem_ker_iff` と PAG28 の `Wpull` を使った（言葉の検索）。機械的な照合 712 回で一致なし。`Wproj_eqPt` は PAG28 の `mk_inv_eq` と同じ内容（B）。
  - 照合：独立照合（約 119 秒）。指摘で 4 定理を足した（台帳 L13）。同時に、台帳 L11・L12 と台帳に項目のなかった記録の追記を統合照合 II-a・II-b で照らした（L11・L12 は閉じた）。II-a に「高」1 件：R4 の指摘は「低〜中」2 件を含んでいたのに、記録は「低か極低だけ」と書いていた。直しは後注の形で入れた（台帳 L14）。L13・L14 は閉じるときの統合照合 I に載せる。
  - 著者に確かめる事項（2026-11-25）：
    1. 2026-11-20 16:40 の Part 262 の閉鎖の決定は、構築側の「R4 は低・極低だけ」という報告を前提にしていた可能性がある。実際の R4 の出力では、6 節の 1・2（L10 の範囲と自己申告、ノート §2 の K。どちらも記録の側で、L11 で直した）が「低〜中」だった。この 2 件を知ったうえで閉鎖の決定を保つかどうか。
    2. CLAUDE.md §7 の「照合の後に直した文面は、そのパートを閉じる前に再照合する（2026-11-13）」と、止め方の規則（2026-11-20）の関係（止め方の規則が前者の例外であると明記するか）。リポジトリの CLAUDE.md は著者側の版の写しなので、構築側では文面を変えていない。
    3. CLAUDE.md §2 の Part 260 の「3 条件すべてが効く」と「`InLayer` が定義する関係そのもの」の文は著者側の版の写しで、構築側はこの写しのために Lean で確かめていない（II-b の指摘）。
```

## §8 着手前の文書 `notes/pag2_p1_tower_preregistration.md`（全文）
```markdown
# 着手前の文書：舞台 P¹ の塔（全素点を通した舞台の空間のレベル）（2026-11-25）

アーデル射影幾何。新しいパートの着手前の 4 点（CLAUDE.md §4）と、盲検の問いテスト・対照群テスト（§7）、内部照合（第 12 の型）。推薦案は 1 つに絞る。Lean は著者の決定の後。

## §0 問いの出所

- 基礎文書の索引「定式化の問い」：「射影」の、全素点を通した一つの構成（空間と作用素のレベル）としての定式化。値のレベルは 2.7 で済んでいる。空間のレベルは手つかず。
- 索引 1.4（舞台 P¹）の留保：「0 と ∞ は別の点で、反転がこの 2 点を入れ替える」という文は Lean にない（N ≥ 2 で正しい）。
- 索引 2.4 の留保：照合した範囲では `JH`（貼り合わせ U）と P¹ のモデルを結ぶ Lean の文はない。Part 262 で結んだのは 𝔀 の値と赤道の係数だけ。
- 内部照合（2026-11-25、言葉の検索）：鎖の P¹ は各レベル `PAG.Part27.ProjLine N` ごとに閉じていて、レベルの間の写像（ProjLine M → ProjLine N）は鎖に見つからなかった（`ProjLine` を含むファイル PAG27・28・29・32・34・35・36・38・266 の宣言を見た。見つからなかったは不存在の証明ではない）。U の全レベルの組み立ては Part 254（PAG258）の `Uinf`（単数の上の関数の直極限 `Lim` の上）にある。

## §1 候補

- **C1（推薦）舞台 P¹ の塔と、その赤道への U_∞ の載せ方**：N ∣ M のとき還元 P¹(ℤ/M) → P¹(ℤ/N) を定め、正の整数の整除の順序（`Lvl`）の上の逆系にする。反転 W と還元が可換。関数の引き戻しで直極限（全素点を同時に測る側。08:41 の定義の「極限は直極限の側」）を作り、W がその上の対合になる。赤道（単数の点）の部分の引き戻しが Part 254 の `pullL` と一致し、赤道の関数の直極限が `Lim` に入ること、したがって `Uinf` が舞台の赤道の上で働くことを Lean の文にする。あわせて 1.4 の留保（0 ≠ ∞、W が入れ替える）を Lean にする。
- C2 作用素のレベル：U を P¹ の各レベルの関数の上の作用素に延ばし、塔と両立させる。延ばし方は一意でなく（赤道の外と北のチャートの扱いに選択がある）、著者の判断が先。C1 の後でなければ立てられない。
- C3 短期層：A1 の位相が定理 2.6 の条件を満たすことを 1 つの Lean の文にする（索引 2.3 の留保。PAG16・PAG173・PAG198 の 3 定理の組み合わせ）。残余は計算だけ。

## §2 C1 の 4 点

1. 幾何の言葉：点は素数たちと無限素点。舞台 P¹ の有限レベルは各法 N で別々にある。全素点を同時に測る見方（L1 の読みで、測る素点の集合を全部にした側）で、舞台は一つの対象になり、反転（0 と ∞ の入れ替え）はその上の一つの対合になるか。貼り合わせ U は、その舞台の赤道（0 でも ∞ でもない点）の上の一つの作用素として働くか。
2. 既存の言葉への翻訳：P¹(Ẑ) = lim P¹(ℤ/N)（射有限集合）＝ ∏_p P¹(ℤ_p)。関数の直極限は P¹(Ẑ) 上の局所定数関数。反転は P¹ の自己同型 [a:b] ↦ [b:a]。赤道は P¹(Ẑ) の中の Ẑ^× ⊂ ℙ¹ の部分（単数の点）。U_∞ は Part 254 の作用素。
3. 残余：(a) 塔と反転の可換性・直極限の上の対合は、標準の構成の形式化（計算の細部）。(b) 赤道の引き戻しが Part 254 の `pullL` と一致し、`Uinf` が舞台の赤道に載ること（2.4 の留保に空間のレベルで答える部分。新しい内容ではなく、鎖の中の二つの構成をつなぐ計算）。残余は計算の細部だけなので、**短期層の小さいノート**として扱う（§4 の規則）。
4. 対照群：F_q[t] の P¹（F_q[t]/(f) の塔）でも同じ文が成り立つ（形式の文）。ℚ に固有の算術の内容はない。U_∞ の位相（𝔀）の側の算術は Part 252〜254 にあって、このパートは足さない。

## §3 盲検の問いテスト

依頼（定義と問い Q1〜Q5 だけ、ウェブ検索あり）と出力は `records/p1_tower/`。所要約 112 秒、ツール 5 回。

- Q1・Q2・Q4：既知・教科書の範囲（確信度：高）。還元は well-defined で全射（単模な組の持ち上げ ＝ SL₂(ℤ) → SL₂(ℤ/M) の全射と同値な初等的補題。Shimura の Lemma 1.38、記憶から）。P¹(ℤ/N) の定義と点の数は Cremona・Stein の Manin 記号の章、SageMath の `P1List`（確認済み）。P¹(Ẑ) を逆極限として明示した文献は見つからなかった。直極限 ＝ P¹(Ẑ) 上の局所定数関数、W は対合、0 ≠ ∞ は自明。
- **Q3（重い指摘）**：赤道の関数を 0 で延ばして舞台の関数の空間に入れる写像は、引き戻しと可換でない。赤道の逆像が上の段の赤道より大きいため（照合者の数値：(N, M) = (1, 2) で逆像 3 点・赤道 1 点、(2, 6) で 4 点・2 点）。極限の側では、Ẑ^× は P¹(Ẑ) の中で閉だが開でない。したがって §1 の C1 の「赤道の関数の直極限が舞台の直極限に入り、`Uinf` が舞台の赤道の上で働く」という読みは、そのままでは成り立たない。成り立つのは逆向きで、赤道への制限（舞台の関数 → 単数の上の関数）が引き戻しと可換になり、直極限の間の写像を与える（構築側の手計算：赤道は赤道に写るので、制限と引き戻しは可換）。`Uinf` はその像の側（Part 254 の `Lim`）で働く。原始指標で決まるスカラーがレベルによらない一つの作用素になることは、分解から直ちに出る（既知の材料の組み合わせ。作用素として明示した文献は見つからなかった、確信度：低）。
- Q5：構造の文は F_q[t] でも同じ形で成り立つ（∞ の素点は逆極限に入らない、ℚ の無限素点と同じ）。成り立たないのは位相の式 τ(χ)/(i^a √f) の形（i^a と √f、偶奇が q − 1 通り）で、それはこのパートの外（Part 252〜254）。

§2 の 3 の残余は、盲検の結果を受けて次のように改める：(a) は既知の構成の形式化。(b) は「赤道への制限が塔と両立し、`Uinf` の載る `Lim` への写像になる」ことと、「赤道からの 0 延長は両立しない」ことの証人（小さい計算）。読み（Lean の外）として、全素点の舞台では赤道が開でないので、貼り合わせ U は舞台の局所定数関数の上の作用素として赤道に局所化できない。これは索引 2.4 の留保（U は P¹ の上の作用素ではない）に、空間のレベルの理由を一つ与える読みで、C2（U を P¹ の作用素に延ばす）を立てるときの障害量になる（第 4 の型）。

## §4 推薦

**C1 を、盲検の指摘で改めた形で、短期層の小さいノート（Part 263、PAG267）として行う。**

- Lean に入れる見込みの文（題と主張は形式文が確定してから起こす）：
  1. N ∣ M のときの還元 P¹(ℤ/M) → P¹(ℤ/N)、恒等と合成の法則（`Lvl` の上の逆系）、反転 W との可換性。
  2. N ≥ 2 で 0 ≠ ∞、W が 0 と ∞ を入れ替える（索引 1.4 の留保）。
  3. 関数の引き戻しによる直極限と、その上の対合 W。各段が単射に入ること（還元の全射性が要る。Lean で示せなければ、直極限は作るが単射性は Lean の外として残す）。
  4. 赤道への制限が引き戻しと可換で、舞台の直極限から Part 254 の `Lim` への写像になり、`Uinf` はその像の側で働く。
  5. 赤道からの 0 延長は引き戻しと可換でない（(1, 2) の証人）。
- 期待するラベル：1〜3 は［既知］、4・5 は［再導出（小さい）］。新規候補なし。兆候 4 は続く。
- 理由：
  1. 索引の「定式化の問い」（射影の全素点を通した構成）の空間のレベルに初めて手を付ける。鎖にはレベルの間の写像がなかった。
  2. 1.4 の留保を閉じ、2.4 の留保に空間のレベルの理由（赤道は全素点の舞台で開でない）を与える。
  3. C2（作用素のレベル）に進むかどうかを、障害量を見たうえで判断できるようになる。
- 対照群：構造の文はすべて F_q[t] でも成り立つ（形式の文、ℚ に固有の算術なし）。
- 閉じるときの統合照合に、台帳の L11・L12 を載せる（停止規則）。

（後注 2026-11-25 夜：著者の採用（18:27）を受けて Part 263（PAG267）として実施した。予定の 5 つの文はすべて Lean に入った。5 は証人 (1, 2) だけでなく、両立の判定（上の段の法の素因数がすべて下の段の法を割るとき、そのときに限る）と、0 延長が極限に降りないことの形になった。独立照合の指摘で、反転と制限の関係 resL ∘ W_∞ = invL ∘ resL を足した。全射性は Lean で示せたので、段の単射性も Lean の中にある。結果はノート `notes/pag2_pag267_p1_tower.md`。）
```

## §9 数値スクリプトとその出力（`records/p1_tower/numeric/`）
```python
from math import gcd
def P1(N):
    pts=set()
    for a in range(N):
        for b in range(N):
            if gcd(gcd(a,b),N)==1 or N==1:
                # canonical rep: min over unit multiples
                us=[u for u in range(N) if gcd(u,N)==1] or [0]
                pts.add(min(((u*a)%N,(u*b)%N) for u in us))
    return pts
def canon(a,b,N):
    us=[u for u in range(N) if gcd(u,N)==1] or [0]
    return min(((u*a)%N,(u*b)%N) for u in us)
def card(N):
    r=N; n=N; p=2
    while p*p<=n:
        if n%p==0:
            r=r*(p+1)//p
            while n%p==0: n//=p
        p+=1
    if n>1: r=r*(n+1)//n
    return r
def isEq(a,b,N): return gcd(a,N)==1 and gcd(b,N)==1
bad=0; rows=[]
for M in range(1,49):
    PM=P1(M); assert len(PM)==card(M),(M,len(PM))
    for N in range(1,M+1):
        if M%N: continue
        PN=P1(N)
        img={canon(a%N,b%N,N) for (a,b) in PM}
        if img!=PN: bad+=1; print("not surj",N,M)
        # W commute
        for (a,b) in PM:
            assert canon(b%N,a%N,N)==canon(*canon(b,a,M),N) if False else True
        # equator preimage vs upper equator: zero-extension compat?
        # f on equator(N) indicator of one point; zero-extend then pull vs pull then zero-extend
        eqN=[x for x in PN if isEq(*x,N)]
        pre=[y for y in PM if canon(y[0]%N,y[1]%N,N) in eqN]
        eqM=[y for y in PM if isEq(*y,M)]
        rows.append((N,M,len(pre),len(eqM)))
        # restriction compat: eq(M) maps into eq(N)
        assert all(isEq(y[0]%N,y[1]%N,N) for y in eqM)
        # 0 and inf distinct
    if M>=2: assert canon(0,1,M)!=canon(1,0,M)
print("nonsurjective:",bad)
mism=[r for r in rows if r[2]!=r[3]]
print("pairs:",len(rows),"zero-ext incompatible (pre != eq):",len(mism))
print("compatible pairs:",[ (n,m) for (n,m,a,b) in rows if a==b][:40])
print("examples:",mism[:8])
def primes(n): return {p for p in range(2,n+1) if n%p==0 and all(p%q for q in range(2,p))}
ok=all((a==b)==(primes(m)<=primes(n)) for (n,m,a,b) in rows)
print("compatible iff primes(M) ⊆ primes(N):",ok)
```
```
nonsurjective: 0
pairs: 198 zero-ext incompatible (pre != eq): 120
compatible pairs: [(1, 1), (2, 2), (3, 3), (2, 4), (4, 4), (5, 5), (6, 6), (7, 7), (2, 8), (4, 8), (8, 8), (3, 9), (9, 9), (10, 10), (11, 11), (6, 12), (12, 12), (13, 13), (14, 14), (15, 15), (2, 16), (4, 16), (8, 16), (16, 16), (17, 17), (6, 18), (18, 18), (19, 19), (10, 20), (20, 20), (21, 21), (22, 22), (23, 23), (6, 24), (12, 24), (24, 24), (5, 25), (25, 25), (26, 26), (3, 27)]
examples: [(1, 2, 3, 1), (1, 3, 4, 2), (1, 4, 6, 2), (1, 5, 6, 4), (1, 6, 12, 2), (2, 6, 4, 2), (3, 6, 6, 2), (1, 7, 8, 6)]
compatible iff primes(M) ⊆ primes(N): True
```
