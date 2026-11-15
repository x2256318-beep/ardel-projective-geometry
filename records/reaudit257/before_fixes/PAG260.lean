/-
アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法の原始指標の積の上での、貼り合わせ U の固有値 — 交差項の法則

問いの出所：著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の
「無限素点を含む大域対象」と「重なり」。Part 252〜254 の貼り合わせ U（公準 A1 の位相＝ルート数 W を固有値とする）を、
Part 255 の L1（測る素点の集合）とつなぐ問い：互いに素な法 M, N の局所の貼り合わせから、法 M·N の貼り合わせは決まるか。

答え（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）：
1. 中国剰余定理の分解 a = a₁·N + a₂·M（`crtMap`・`crtMap_bijective`）と、加法指標の分解（`stdAddChar_crtMap`）。
2. 指標の積 `prodChar χ₁ χ₂`（法 M·N）とその値（`prodChar_apply`・`charU_prodChar`・`prodChar_neg_one`）。
3. ガウス和の乗法性 τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`。原始性は要らない）。
4. 無限素点の因子のずれ ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)、s = −1（両方が奇）か +1（`crossSign`・`parFac_prodChar`）。
5. 交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項の絶対値は 1
   （`norm_cross`）。
6. 原始指標の積は原始（`isPrimitive_prodChar`）。したがって公準 A1 の位相と貼り合わせ U でも同じ法則
   （`phaseA1_prodChar`・`UA1_charU_prodChar`）。
7. 法 15 = 3·5 で W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（`rootNum_prodChar_ne_mul`・
   `phaseA1_prodChar_ne_mul`）。法 39 = 3·13 で、交差項は 1 だが符号だけで W(χ₁χ₂) = −W(χ₁)·W(χ₂) となる組がある
   （`rootNum_prodChar_eq_neg_mul`。独立照合 B の指摘で追加）。等号になる組もあり、ずれは「一般には」起きる。
8. 3 つの位相がすべて 1 なら交差項は符号で打ち消される（`cross_eq_sign_of_rootNum_one`。条件つきの文。2 次の指標では
   平方剰余の相互法則と同じ形だが、3 つの仮定は外から入れるもので、ここから相互法則が出るのではない）。

言い方の注意（着手前の盲検の問いテストの指摘）：大域の ε 因子は局所の ε 因子の積である（Tate、Deligne）。ここで言う
ずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ のルート数の積と、χ₁χ₂ のルート数との差。交差項は、χ₁ の、
N を割る素点での局所成分（不分岐だが自明でない）から出る。「大域は局所の積ではない」とは書かない。
A1 は公準のまま。ここでの文は、ルート数という量についての恒等式で、A1 から何かを出すものではない。

範囲（独立照合 B の指摘）：ここでの文は、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値の式。法 M·N の
すべての指標が積の形に一意に書けること、作用素全体の式、素数冪ごとの分解は Lean にしていない。互いに素の仮定は、
ガウス和の法則と交差項の法則では外しても成り立つ（両辺 0）が、仮定つきのまま。

Lean にしていないこと：原始でない指標の位相の法則（導手 d₁, d₂ での交差項 χ₁*(d₂)·χ₂*(d₁)。数値 step279 の (4)）、
作用素の形（テンソル積と平行移動。指標の基底の上の文 `UA1_charU_prodChar` まで）、3 つ以上の法（数値 (7)）、
互いに素でない法（両辺が 0 になる。数値 (10)）、対照群 F_q[t]（数値 (5)）、イデール類指標の局所成分と局所の ε 因子。
-/
import PAG259

open DirichletCharacter ZMod Complex

namespace PAG.Part260

variable {M N : ℕ} [NeZero M] [NeZero N]

/-- 法の積は 0 でない。 -/
instance : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩

/-- 互いに素な法 M, N の指標の積（法 M·N の指標）。 -/
noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂

/-- 分解の写像 (a₁, a₂) ↦ a₁·N + a₂·M（mod M·N）。 -/
def crtMap (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))

/-- 分解の写像の法 M への像は a₁·N。 -/
theorem cast_crtMap_fst (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M) := by
  unfold crtMap
  rw [ZMod.cast_natCast (dvd_mul_right M N)]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero]

/-- 分解の写像の法 N への像は a₂·M。 -/
theorem cast_crtMap_snd (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N) := by
  unfold crtMap
  rw [ZMod.cast_natCast (dvd_mul_left N M)]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, zero_add]

/-- 互いに素な法では、分解の写像は全単射（中国剰余定理）。 -/
theorem crtMap_bijective (h : M.Coprime N) : Function.Bijective (crtMap M N) := by
  have hinj : Function.Injective (crtMap M N) := by
    intro x y hxy
    have hN : IsUnit (N : ZMod M) := (ZMod.isUnit_iff_coprime N M).mpr h.symm
    have hM : IsUnit (M : ZMod N) := (ZMod.isUnit_iff_coprime M N).mpr h
    have h1 := congrArg (fun z : ZMod (M * N) => (z.cast : ZMod M)) hxy
    have h2 := congrArg (fun z : ZMod (M * N) => (z.cast : ZMod N)) hxy
    simp only [cast_crtMap_fst, cast_crtMap_snd] at h1 h2
    exact Prod.ext (hN.mul_left_injective h1) (hM.mul_left_injective h2)
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [ZMod.card]

/-- 加法指標は分解の写像で積に分かれる：e((a₁N + a₂M)/(MN)) = e(a₁/M)·e(a₂/N)。 -/
theorem stdAddChar_crtMap (x : ZMod M × ZMod N) :
    stdAddChar (crtMap M N x) = stdAddChar x.1 * stdAddChar x.2 := by
  have e1 : stdAddChar x.1 = exp (2 * Real.pi * I * (x.1.val : ℤ) / M) := by
    rw [← stdAddChar_coe]; simp
  have e2 : stdAddChar x.2 = exp (2 * Real.pi * I * (x.2.val : ℤ) / N) := by
    rw [← stdAddChar_coe]; simp
  have e3 : stdAddChar (crtMap M N x) =
      exp (2 * Real.pi * I * ((x.1.val * N + x.2.val * M : ℕ) : ℤ) / (M * N : ℕ)) := by
    rw [← stdAddChar_coe]; simp [crtMap]
  rw [e1, e2, e3, ← Complex.exp_add]
  congr 1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  push_cast
  field_simp

/-- 積の指標の値：(χ₁χ₂)(a) = χ₁(a mod M)·χ₂(a mod N)（単数でない a では両辺 0）。 -/
theorem prodChar_apply (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    prodChar χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N) := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd]
  · rw [MulChar.map_nonunit _ ha, zero_mul]
    by_contra hne
    apply ha
    have h1 : IsUnit ((a.cast : ZMod M)) := by
      by_contra h1; exact hne (by rw [MulChar.map_nonunit _ h1, zero_mul])
    have h2 : IsUnit ((a.cast : ZMod N)) := by
      by_contra h2; exact hne (by rw [MulChar.map_nonunit _ h2, mul_zero])
    have hc1 : Nat.Coprime a.val M := by
      rw [← ZMod.isUnit_iff_coprime]
      have : ((a.val : ℕ) : ZMod M) = (a.cast : ZMod M) := by
        rw [← ZMod.cast_natCast (dvd_mul_right M N) (a.val), ZMod.natCast_zmod_val]
      rwa [this]
    have hc2 : Nat.Coprime a.val N := by
      rw [← ZMod.isUnit_iff_coprime]
      have : ((a.val : ℕ) : ZMod N) = (a.cast : ZMod N) := by
        rw [← ZMod.cast_natCast (dvd_mul_left N M) (a.val), ZMod.natCast_zmod_val]
      rwa [this]
    have := (ZMod.isUnit_iff_coprime a.val (M * N)).mpr (Nat.Coprime.mul_right hc1 hc2)
    rwa [ZMod.natCast_zmod_val] at this

/-- **互いに素な法でのガウス和の乗法性**：τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)。原始性は要らない。 -/
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar := by
  unfold gaussSum
  rw [← (crtMap_bijective h).sum_comp, Fintype.sum_prod_type, mul_assoc (χ₁ _ * χ₂ _),
    Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [prodChar_apply, cast_crtMap_fst, cast_crtMap_snd, stdAddChar_crtMap, map_mul, map_mul]
  ring

/-- (χ₁χ₂)(−1) = χ₁(−1)·χ₂(−1)。 -/
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1) := by
  rw [prodChar_apply, ZMod.cast_neg (dvd_mul_right M N), ZMod.cast_neg (dvd_mul_left N M),
    ZMod.cast_one (dvd_mul_right M N), ZMod.cast_one (dvd_mul_left N M)]

open Classical in
/-- 交差項の符号：両方が奇のとき −1、それ以外は +1。 -/
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1

omit [NeZero M] [NeZero N] in
/-- 両方が奇なら符号は −1。 -/
theorem crossSign_of_odd {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : crossSign χ₁ χ₂ = -1 := by
  simp [crossSign, h1, h2]

omit [NeZero M] [NeZero N] in
/-- 左が偶なら符号は 1。 -/
theorem crossSign_of_even_left {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : crossSign χ₁ χ₂ = 1 := by
  have hn : ¬χ₁.Odd := fun h => by
    unfold DirichletCharacter.Odd at h; unfold DirichletCharacter.Even at h1
    rw [h1] at h; norm_num at h
  simp [crossSign, hn]

omit [NeZero M] [NeZero N] in
/-- 右が偶なら符号は 1。 -/
theorem crossSign_of_even_right (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : crossSign χ₁ χ₂ = 1 := by
  have hn : ¬χ₂.Odd := fun h => by
    unfold DirichletCharacter.Odd at h; unfold DirichletCharacter.Even at h2
    rw [h2] at h; norm_num at h
  simp [crossSign, hn]

/-- 無限素点の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は 偶で 1、奇で −i）。 -/
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂ := by
  rcases χ₁.even_or_odd with h1 | h1 <;> rcases χ₂.even_or_odd with h2 | h2
  · have h12 : (prodChar χ₁ χ₂).Even := by
      unfold DirichletCharacter.Even; rw [prodChar_neg_one, h1, h2, mul_one]
    rw [crossSign_of_even_left χ₂ h1, PAG.Part256.parFac_of_even h12,
      PAG.Part256.parFac_of_even h1, PAG.Part256.parFac_of_even h2]; ring
  · have h12 : (prodChar χ₁ χ₂).Odd := by
      unfold DirichletCharacter.Odd; rw [prodChar_neg_one, h1, h2, one_mul]
    rw [crossSign_of_even_left χ₂ h1, PAG.Part256.parFac_of_odd h12,
      PAG.Part256.parFac_of_even h1, PAG.Part256.parFac_of_odd h2]; ring
  · have h12 : (prodChar χ₁ χ₂).Odd := by
      unfold DirichletCharacter.Odd; rw [prodChar_neg_one, h1, h2, mul_one]
    rw [crossSign_of_even_right χ₁ h2, PAG.Part256.parFac_of_odd h12,
      PAG.Part256.parFac_of_odd h1, PAG.Part256.parFac_of_even h2]; ring
  · have h12 : (prodChar χ₁ χ₂).Even := by
      unfold DirichletCharacter.Even; rw [prodChar_neg_one, h1, h2]; norm_num
    rw [crossSign_of_odd h1 h2, PAG.Part256.parFac_of_even h12, PAG.Part256.parFac_of_odd h1,
      PAG.Part256.parFac_of_odd h2]
    have : (-1 : ℂ) * -I * -I = -(I * I) := by ring
    rw [this, Complex.I_mul_I]; ring

/-- **交差項の法則**：W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない。 -/
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) := by
  rw [PAG.Part256.rootNum_eq, PAG.Part256.rootNum_eq, PAG.Part256.rootNum_eq, parFac_prodChar,
    gaussSum_prodChar h]
  have hM : (Real.sqrt M : ℂ) ≠ 0 := by
    have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    exact_mod_cast (Real.sqrt_pos.mpr this).ne'
  have hN : (Real.sqrt N : ℂ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast (Real.sqrt_pos.mpr this).ne'
  have hs : (Real.sqrt ((M * N : ℕ) : ℝ) : ℂ) = (Real.sqrt M : ℂ) * (Real.sqrt N : ℂ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg M)]; push_cast; rfl
  rw [hs]
  field_simp

/-- 積の導手：χ₁, χ₂ が原始なら χ₁χ₂ も原始（法 M·N）。 -/
theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (prodChar χ₁ χ₂).IsPrimitive := by
  set χ := prodChar χ₁ χ₂ with hχ
  set ψ₁ := changeLevel (dvd_mul_right M N) χ₁ with hψ₁
  set ψ₂ := changeLevel (dvd_mul_left N M) χ₂ with hψ₂
  have c1 : ψ₁.conductor = M := by rw [hψ₁, conductor_changeLevel]; exact h1
  have c2 : ψ₂.conductor = N := by rw [hψ₂, conductor_changeLevel]; exact h2
  have e1 : ψ₁ = χ * ψ₂⁻¹ := by rw [hχ]; unfold prodChar; rw [mul_inv_cancel_right]
  have e2 : ψ₂ = χ * ψ₁⁻¹ := by
    rw [hχ]; unfold prodChar; rw [mul_comm (changeLevel _ χ₁), mul_inv_cancel_right]
  have d1 : M ∣ Nat.lcm χ.conductor N := by
    have := conductor_mul_dvd_lcm_conductor χ ψ₂⁻¹
    rwa [← e1, c1, conductor_inv, c2] at this
  have d2 : N ∣ Nat.lcm χ.conductor M := by
    have := conductor_mul_dvd_lcm_conductor χ ψ₁⁻¹
    rwa [← e2, c2, conductor_inv, c1] at this
  have hM : M ∣ χ.conductor :=
    h.dvd_of_dvd_mul_right (d1.trans (Nat.lcm_dvd_mul _ _))
  have hN : N ∣ χ.conductor :=
    h.symm.dvd_of_dvd_mul_right (d2.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm χ.conductor_dvd_level (h.mul_dvd_of_dvd_of_dvd hM hN)

/-- 公準 A1 の位相（Part 254 の `phaseA1`）での交差項の法則（原始指標）。 -/
theorem phaseA1_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.phaseA1 (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂) := by
  rw [PAG.Part258.phaseA1_of_isPrimitive (isPrimitive_prodChar h h1 h2),
    PAG.Part258.phaseA1_of_isPrimitive h1, PAG.Part258.phaseA1_of_isPrimitive h2,
    rootNum_prodChar h]

/-- 貼り合わせ U（Part 254 の `UA1`）は、原始指標の積を、局所の位相の積に交差項を掛けた値で動かす。 -/
theorem UA1_charU_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.UA1 (PAG.Part257.charU (prodChar χ₁ χ₂)) =
      (crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)) •
        PAG.Part257.charU (prodChar χ₁ χ₂) := by
  rw [PAG.Part258.UA1_charU, phaseA1_prodChar h h1 h2]

/-- 2 次の指標などで 3 つの位相がすべて 1 なら、交差項は符号で打ち消される（平方剰余の相互法則と同じ形。
3 つの仮定は外から入れるもので、ここからは出ない）。 -/
theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
    (w2 : PAG.Part256.rootNum χ₂ = 1) (w12 : PAG.Part256.rootNum (prodChar χ₁ χ₂) = 1) :
    crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1 := by
  have := rootNum_prodChar h χ₁ χ₂
  rw [w1, w2, w12, mul_one, mul_one] at this
  exact this.symm

/-- 証人：法 5 の奇の原始指標がある。 -/
theorem exists_primitive_odd_five : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd := by
  have hm : (-1 : ZMod 5) ≠ 1 := by decide
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm
  have hodd : χ.Odd := by
    rcases χ.even_or_odd with h | h
    · exact absurd h hχ
    · exact h
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply (isUnit_neg_one))
  exact ⟨χ, PAG.Part256.isPrimitive_of_prime_of_ne_one hne, hodd⟩

/-- **中国剰余定理の成分の積とのずれの例**（法 15 = 3·5）：原始指標 χ₁（法 3）、χ₂（法 5）で
W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となるものがある。 -/
theorem rootNum_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      χ₁.Odd ∧ χ₂.Odd ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) ≠ PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ := by
  obtain ⟨χ₁, hp1, ho1⟩ := PAG.Part256.exists_primitive_odd_three
  obtain ⟨χ₂, hp2, ho2⟩ := exists_primitive_odd_five
  refine ⟨χ₁, χ₂, hp1, hp2, ho1, ho2, ?_⟩
  have hc : Nat.Coprime 3 5 := by decide
  rw [rootNum_prodChar hc, crossSign_of_odd ho1 ho2]
  have e1 : χ₁ ((5 : ℕ) : ZMod 3) = -1 := by
    have : ((5 : ℕ) : ZMod 3) = -1 := by decide
    rw [this]; exact ho1
  have h33 : χ₂ ((3 : ℕ) : ZMod 5) * χ₂ ((3 : ℕ) : ZMod 5) = -1 := by
    rw [← map_mul]
    have : ((3 : ℕ) : ZMod 5) * ((3 : ℕ) : ZMod 5) = -1 := by decide
    rw [this]; exact ho2
  have hne1 : χ₂ ((3 : ℕ) : ZMod 5) ≠ 1 := by
    intro h; rw [h] at h33; norm_num at h33
  have hW : PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ ≠ 0 :=
    mul_ne_zero (PAG.Part257.rootNum_ne_zero hp1) (PAG.Part257.rootNum_ne_zero hp2)
  rw [e1]
  intro heq
  apply hne1
  have h2 : χ₂ ((3 : ℕ) : ZMod 5) * (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) =
      1 * (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) := by
    linear_combination heq
  exact mul_right_cancel₀ hW h2

/-- **符号だけでずれる例**（法 39 = 3·13。独立照合 B の指摘で追加）：奇の原始指標 χ₁（法 3）、χ₂（法 13）で、
交差項 χ₁(13)·χ₂(3) = 1 だが W(χ₁χ₂) = −W(χ₁)·W(χ₂) となるものがある。 -/
theorem rootNum_prodChar_eq_neg_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 13), χ₁.IsPrimitive ∧
      χ₂.IsPrimitive ∧ χ₁.Odd ∧ χ₂.Odd ∧ χ₁ ((13 : ℕ) : ZMod 3) * χ₂ ((3 : ℕ) : ZMod 13) = 1 ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) =
        -(PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) ∧
      PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ ≠ 0 := by
  have hm : (-1 : ZMod 13) ≠ 1 := by decide
  have h27 : ((3 : ℕ) : ZMod 13) * ((3 : ℕ) : ZMod 13) * ((3 : ℕ) : ZMod 13) = 1 := by decide
  have hneg : (-1 : ZMod 13) * (-1) * (-1) = -1 := by decide
  have h13 : ((13 : ℕ) : ZMod 3) = 1 := by decide
  have hp13 : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨χ₁, hp1, ho1⟩ := PAG.Part256.exists_primitive_odd_three
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm
  have hodd : χ.Odd := by
    rcases χ.even_or_odd with h | h
    · exact absurd h hχ
    · exact h
  set χ₂ : DirichletCharacter ℂ 13 := χ * χ * χ with hχ₂
  have ho2 : χ₂.Odd := by
    show χ₂ (-1) = -1
    rw [hχ₂, MulChar.mul_apply, MulChar.mul_apply, show χ (-1) = -1 from hodd]; ring
  have h3 : χ₂ ((3 : ℕ) : ZMod 13) = 1 := by
    rw [hχ₂, MulChar.mul_apply, MulChar.mul_apply, ← map_mul, ← map_mul, h27, map_one]
  have hne : χ₂ ≠ 1 := by
    intro h1
    have := ho2
    rw [h1] at this
    have h2 : (1 : DirichletCharacter ℂ 13) (-1) = 1 := MulChar.one_apply isUnit_neg_one
    unfold DirichletCharacter.Odd at this
    rw [h2] at this; norm_num at this
  have hp2 : χ₂.IsPrimitive := PAG.Part256.isPrimitive_of_prime_of_ne_one hne
  have hcross : χ₁ ((13 : ℕ) : ZMod 3) * χ₂ ((3 : ℕ) : ZMod 13) = 1 := by
    rw [h13, map_one, h3, mul_one]
  refine ⟨χ₁, χ₂, hp1, hp2, ho1, ho2, hcross, ?_,
    mul_ne_zero (PAG.Part257.rootNum_ne_zero hp1) (PAG.Part257.rootNum_ne_zero hp2)⟩
  rw [rootNum_prodChar (by decide), crossSign_of_odd ho1 ho2, hcross]; ring

/-- 同じ例を貼り合わせ U の言葉で：法 15 で、U の固有値（公準 A1 の位相）が局所の位相の積と違う原始指標の組がある。 -/
theorem phaseA1_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      PAG.Part258.phaseA1 (prodChar χ₁ χ₂) ≠ PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂ := by
  obtain ⟨χ₁, χ₂, h1, h2, -, -, hne⟩ := rootNum_prodChar_ne_mul
  refine ⟨χ₁, χ₂, h1, h2, ?_⟩
  rwa [PAG.Part258.phaseA1_of_isPrimitive (isPrimitive_prodChar (by decide) h1 h2),
    PAG.Part258.phaseA1_of_isPrimitive h1, PAG.Part258.phaseA1_of_isPrimitive h2]

/-- 単数での指標の値の絶対値は 1（Mathlib の `DirichletCharacter.unit_norm_eq_one` と同じ証明。そのモジュールは
この環境でビルドしていないので、ここに置く）。 -/
theorem norm_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one,
    norm_one]

omit [NeZero M] [NeZero N] in
/-- 交差項の大きさは 1：互いに素な法では ‖χ₁(N)·χ₂(M)‖ = 1（位相だけのずれ）。 -/
theorem norm_cross (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1 := by
  have hN : IsUnit (N : ZMod M) := (ZMod.isUnit_iff_coprime N M).mpr h.symm
  have hM : IsUnit (M : ZMod N) := (ZMod.isUnit_iff_coprime M N).mpr h
  rw [norm_mul, ← hN.unit_spec, ← hM.unit_spec, norm_char_unit, norm_char_unit, mul_one]

/-- 積の指標は、中国剰余定理の 2 つの成分の関数の積：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)。 -/
theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    PAG.Part257.charU (prodChar χ₁ χ₂) u =
      PAG.Part257.charU χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        PAG.Part257.charU χ₂ (ZMod.unitsMap (dvd_mul_left N M) u) := by
  unfold PAG.Part257.charU
  rw [prodChar_apply]
  rfl

end PAG.Part260

#print axioms PAG.Part260.cast_crtMap_fst
#print axioms PAG.Part260.cast_crtMap_snd
#print axioms PAG.Part260.crtMap_bijective
#print axioms PAG.Part260.stdAddChar_crtMap
#print axioms PAG.Part260.prodChar_apply
#print axioms PAG.Part260.gaussSum_prodChar
#print axioms PAG.Part260.prodChar_neg_one
#print axioms PAG.Part260.crossSign_of_odd
#print axioms PAG.Part260.crossSign_of_even_left
#print axioms PAG.Part260.crossSign_of_even_right
#print axioms PAG.Part260.parFac_prodChar
#print axioms PAG.Part260.rootNum_prodChar
#print axioms PAG.Part260.isPrimitive_prodChar
#print axioms PAG.Part260.phaseA1_prodChar
#print axioms PAG.Part260.UA1_charU_prodChar
#print axioms PAG.Part260.cross_eq_sign_of_rootNum_one
#print axioms PAG.Part260.exists_primitive_odd_five
#print axioms PAG.Part260.rootNum_prodChar_ne_mul
#print axioms PAG.Part260.rootNum_prodChar_eq_neg_mul
#print axioms PAG.Part260.phaseA1_prodChar_ne_mul
#print axioms PAG.Part260.norm_char_unit
#print axioms PAG.Part260.norm_cross
#print axioms PAG.Part260.charU_prodChar
