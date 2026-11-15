/-
  PAG 2.0 Part 27（2026-10-19）
  1. フーリエ側: 𝓕ε_{w0} の値は 0 か 1、𝓕A = λ 𝓕ε ≥ 0（正定値）、𝓕H = χ(−1) 𝓕A（奇指標で ≤ 0）
  2. 反転共役 ~ と W: ε, A, H は ~ で不変。P¹ 上の ~（チャートごとの反転共役）は W と可換で、
     B_S, B_N と可換。~|w,χ⟩_S = χ(−1)|w,χ̄⟩_S、~|−w,χ⟩_N = χ(−1)|−w,χ̄⟩_N
  3. p = 2 の導手降下: 導手 2 の指標はない、法 4 の原始指標の積は自明、
     法 2^(d+2) の原始指標 χ₁, χ₂ について、積が法 2^d を経由 ⇔ χ₂(g) = −χ₁(g)（g = 1 + 2^d, d ≥ 2）、
     そうでなければ導手はちょうど 2^(d+1)
-/
import PAG30

namespace PAG.Part31

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part25 PAG.Part28
  PAG.Part29 PAG.Part30

/-! ## 1. フーリエ側の正定値性 -/

section Fourier

variable {p : ℕ} [hp : Fact p.Prime]

instance (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- **𝓕ε の値は 0 か 1**（a ≤ K）。 -/
theorem dft_eps_zero_or_one (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K)) :
    𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K a) k = 0 ∨
      𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K a) k = 1 := by
  have h := congrArg (fun f => 𝓕 f k) (eps_conv (p := p) K a a ha ha)
  simp only [ite_true, PAG.Part16.dft_conv, Pi.mul_apply] at h
  have : 𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K a) k * (𝓕 (PAG.Part14.epsBall (Pavg (p := p) K) K a) k - 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- λ = p^K/|S_{w0}| > 0。 -/
theorem lam_pos (K u : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K u : ℝ) := by
  have : (0 : ℝ) < sz p K u := by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  exact div_pos (pow_pos (by exact_mod_cast hp.out.pos) K) this

/-- **A は正定値**: 𝓕A(k) は実数で ≥ 0（値は 0 または λ）。 -/
theorem dft_auto_nonneg (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (k : ZMod (p ^ K)) :
    𝓕 (auto K w (n + 1) hK χ) k = 0 ∨
      𝓕 (auto K w (n + 1) hK χ) k = (((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) : ℝ) : ℂ) := by
  rw [auto_eps K w n hK χ hχ, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul]
  rcases dft_eps_zero_or_one K (K - (n + 1) - w) (by omega) k with h | h
  · left; rw [h, mul_zero]
  · right; rw [h, mul_one]; push_cast; rfl

/-- 正定値性（実部 ≥ 0・虚部 0 の形）。 -/
theorem dft_auto_re_nonneg (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (k : ZMod (p ^ K)) :
    0 ≤ (𝓕 (auto K w (n + 1) hK χ) k).re ∧ (𝓕 (auto K w (n + 1) hK χ) k).im = 0 := by
  rcases dft_auto_nonneg K w n hK χ hχ k with h | h <;> rw [h]
  · simp
  · simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]; exact (lam_pos K _).le

/-- **𝓕H = χ(−1)·𝓕A**。 -/
theorem dft_H (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = χ (-1) • 𝓕 (auto K w (n + 1) hK χ) := by
  rw [H_eq_chi_auto, LinearEquiv.map_smul]

/-- **奇指標では H は負定値**: χ(−1) = −1 なら 𝓕H(k) は実数で ≤ 0。 -/
theorem dft_H_odd_nonpos (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (hodd : χ (-1) = -1) (k : ZMod (p ^ K)) :
    (𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) k).re ≤ 0 ∧
    (𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) k).im = 0 := by
  rw [dft_H, Pi.smul_apply, smul_eq_mul, hodd]
  have := dft_auto_re_nonneg K w n hK χ hχ k
  simp only [neg_mul, one_mul, Complex.neg_re, Complex.neg_im, neg_nonpos, this.1, this.2, neg_zero, and_self]

/-- 偶指標では H は正定値。 -/
theorem dft_H_even_nonneg (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) (heven : χ (-1) = 1) (k : ZMod (p ^ K)) :
    0 ≤ (𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) k).re ∧
    (𝓕 (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))) k).im = 0 := by
  rw [dft_H, Pi.smul_apply, smul_eq_mul, heven, one_mul]
  exact dft_auto_re_nonneg K w n hK χ hχ k

end Fourier

/-! ## 2. 反転共役 ~ の不変性と W との関係 -/

section TildeW

variable {p : ℕ} [hp : Fact p.Prime]

/-- 球の指示関数は反転で不変（j ≤ K）。 -/
theorem ball_neg (K j : ℕ) (hj : j ≤ K) (x : ZMod (p ^ K)) : ball (p := p) K j (-x) = ball (p := p) K j x := by
  have e := indH_Hs (p := p) K (K - j)
  rw [Nat.sub_sub_self hj] at e
  rw [← e]
  simp only [indH]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (neg_mem_iff.mp h1) h2
  · exact absurd (neg_mem_iff.mpr h2) h1
  · rfl

theorem tilde_Pavg (K u : ℕ) : tilde (Pavg (p := p) K u) = Pavg (p := p) K u := by
  funext x
  simp only [tilde, Pavg, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_pow, Complex.conj_natCast,
    ball_neg K (K - u) (Nat.sub_le K u)]
  congr 1
  unfold ball; split_ifs <;> simp

omit hp in
theorem tilde_sub {N : ℕ} (f g : ZMod N → ℂ) : tilde (f - g) = tilde f - tilde g := by
  funext x; simp [tilde]

omit hp in
theorem tilde_smul {N : ℕ} (a : ℂ) (f : ZMod N → ℂ) : tilde (a • f) = starRingEnd ℂ a • tilde f := by
  funext x; simp [tilde]

/-- **ε~ = ε**。 -/
theorem tilde_eps (K a : ℕ) :
    tilde (PAG.Part14.epsBall (Pavg (p := p) K) K a) = PAG.Part14.epsBall (Pavg (p := p) K) K a := by
  unfold PAG.Part14.epsBall
  split_ifs
  · rw [tilde_sub, tilde_Pavg, tilde_Pavg]
  · rw [tilde_Pavg]

/-- **A~ = A**。 -/
theorem tilde_auto (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    tilde (auto K w (n + 1) hK χ) = auto K w (n + 1) hK χ := by
  rw [auto_eps K w n hK χ hχ, tilde_smul, tilde_eps]
  congr 1
  rw [map_div₀, map_pow, Complex.conj_natCast, Complex.conj_natCast]

/-- **H~ = H**。 -/
theorem tilde_H (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    tilde (conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)))
      = conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ)) := by
  rw [H_eq_chi_auto, tilde_smul, tilde_auto K w n hK χ hχ, star_chi_neg_one]

omit hp in
/-- ~ と畳み込みの可換性: conv f~ g~ = (conv f g)~。 -/
theorem conv_tilde {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : conv (tilde f) (tilde g) = tilde (conv f g) := by
  funext x
  simp only [conv, tilde, map_sum, map_mul]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun y => by
    simp only [Equiv.neg_apply]; rw [show -(x - y) = -x - -y by ring])

/-- P¹ 上の反転共役（チャートごと）。 -/
noncomputable def tildeP1 {N : ℕ} (F : P1F N) : P1F N := (tilde F.1, tilde F.2)

omit hp in
/-- **~ と W は可換**。 -/
theorem tildeP1_W {N : ℕ} (F : P1F N) : tildeP1 (W F) = W (tildeP1 F) := rfl

omit hp in
theorem neg_inv_of_unit {N : ℕ} {y : ZMod N} (hy : IsUnit y) : (-y)⁻¹ = -y⁻¹ := by
  obtain ⟨u, rfl⟩ := hy
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_neg, Units.val_neg]

omit hp in
/-- ~ は貼り合わせ条件を保つ。 -/
theorem compat_tildeP1 {N : ℕ} {F : P1F N} (hF : Compat F) : Compat (tildeP1 F) := by
  intro y hy
  simp only [tildeP1, tilde]
  rw [hF (-y) hy.neg, neg_inv_of_unit hy]

omit hp in
theorem tildeP1_extS {N : ℕ} (h : ZMod N → ℂ) : tildeP1 (extS h) = extS (tilde h) := by
  ext y
  · rfl
  · simp only [tildeP1, extS, tilde]
    by_cases hy : IsUnit y
    · simp [hy, hy.neg, neg_inv_of_unit hy]
    · have : ¬ IsUnit (-y) := fun h => hy (by simpa using h.neg)
      simp [hy, this]

omit hp in
theorem tildeP1_extN {N : ℕ} (h : ZMod N → ℂ) : tildeP1 (extN h) = extN (tilde h) := by
  have := congrArg W (tildeP1_extS (N := N) h)
  rw [W_extS, ← tildeP1_W, W_extS] at this
  exact this

omit hp in
/-- **B_S と ~ の可換性**。 -/
theorem BS_tilde {N : ℕ} [NeZero N] (F G : P1F N) : BS (tildeP1 F) (tildeP1 G) = tildeP1 (BS F G) := by
  unfold BS
  rw [tildeP1_extS, ← conv_tilde]
  rfl

omit hp in
/-- **B_N と ~ の可換性**。 -/
theorem BN_tilde {N : ℕ} [NeZero N] (F G : P1F N) : BN (tildeP1 F) (tildeP1 G) = tildeP1 (BN F G) := by
  unfold BN
  rw [← tildeP1_W, ← tildeP1_W, BS_tilde, tildeP1_W]

theorem tilde_ket (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    tilde (ket K w c h χ) = χ (-1) • ket K w c h ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ) := by
  rw [ket_inv_eq_tilde, smul_smul, PAG.Part9.chi_neg_one_sq, one_smul]

/-- **~|w,χ⟩_S = χ(−1)|w,χ̄⟩_S**。 -/
theorem tildeP1_kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    tildeP1 (kS K w c h χ) = χ (-1) • kS K w c h χ⁻¹ := by
  rw [kS, tildeP1_extS, tilde_ket, kS, extS_smul]

/-- **~|−w,χ⟩_N = χ(−1)|−w,χ̄⟩_N**。 -/
theorem tildeP1_kN (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    tildeP1 (kN K w c h χ) = χ (-1) • kN K w c h χ⁻¹ := by
  rw [kN, tildeP1_extN, tilde_ket, kN, extN_smul, chi_inv_neg_one, inv_inv]

/-- **W∘~ は南ケットを北ケットへ、位相 χ(−1) で**: W ~|w,χ⟩_S = χ(−1)|−w,χ⟩_N。 -/
theorem W_tilde_kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    W (tildeP1 (kS K w c h χ)) = χ (-1) • kN K w c h χ := by
  rw [tildeP1_kS, show W (χ (-1) • kS K w c h χ⁻¹) = χ (-1) • W (kS K w c h χ⁻¹) from rfl, W_kS, inv_inv]

/-- **定理 B の像 ε^S, ε^N は ~ で不変**、W は ε^S ↔ ε^N を入れ替える。 -/
theorem tildeP1_epsS (K a : ℕ) :
    tildeP1 (extS (PAG.Part14.epsBall (Pavg (p := p) K) K a)) = extS (PAG.Part14.epsBall (Pavg (p := p) K) K a) := by
  rw [tildeP1_extS, tilde_eps]

theorem tildeP1_epsN (K a : ℕ) :
    tildeP1 (extN (PAG.Part14.epsBall (Pavg (p := p) K) K a)) = extN (PAG.Part14.epsBall (Pavg (p := p) K) K a) := by
  rw [tildeP1_extN, tilde_eps]

end TildeW

/-! ## 3. p = 2 の導手降下 -/

section TwoDescent

/-- 導手 2 の指標は存在しない。 -/
theorem conductor_ne_two {N : ℕ} (χ : DirichletCharacter ℂ N) : χ.conductor ≠ 2 := by
  intro hc
  have key : ∀ m (hm : m = 2) (ψ : DirichletCharacter ℂ m), ψ.IsPrimitive → False := by
    intro m hm ψ hψ; subst hm; exact no_prim_mod_two ψ hψ
  exact key _ hc _ χ.primitiveCharacter_isPrimitive

/-- **法 4 の原始指標の積は自明指標**。 -/
theorem mod4_mul_trivial (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (1 + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : χ₁ * χ₂ = 1 := by
  have hnp := two_mul_not_prim (c := 1) le_rfl χ₁ χ₂ h₁ h₂
  have hdvd : (χ₁ * χ₂).conductor ∣ 4 := by
    have := (χ₁ * χ₂).conductor_dvd_level; norm_num at this; exact this
  have hne2 := conductor_ne_two (χ₁ * χ₂)
  have hne4 : (χ₁ * χ₂).conductor ≠ 4 := fun h => hnp (by rw [DirichletCharacter.isPrimitive_def, h]; norm_num)
  have h1 : (χ₁ * χ₂).conductor = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hcc : (χ₁ * χ₂).conductor
    · exact absurd hdvd (by norm_num)
    · rfl
    · exact absurd rfl hne2
    · exact absurd hdvd (by norm_num)
    · exact absurd rfl hne4
  exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1

variable {d : ℕ}

/-- 核の生成元 g = 1 + 2^d ∈ Z/2^(d+2)。 -/
def gg (d : ℕ) : ZMod (2 ^ (d + 2)) := 1 + ((2 ^ d : ℕ) : ZMod (2 ^ (d + 2)))

/-- g² = k（= 1 + 2^(d+1)）、d ≥ 2。 -/
theorem gg_sq (hd : 2 ≤ d) : gg d * gg d = kk (d + 1) := by
  unfold gg kk
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  have e : ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2 + 2))) * ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2 + 2))) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨2 ^ m, by ring⟩
  have e2 : ((2 ^ (m + 2 + 1) : ℕ) : ZMod (2 ^ (m + 2 + 2))) = 2 * ((2 ^ (m + 2) : ℕ) : ZMod (2 ^ (m + 2 + 2))) := by
    push_cast; ring
  rw [e2]
  linear_combination e

/-- g·k = 1 + 3·2^d（d ≥ 1）。 -/
theorem gg_mul_kk (hd : 1 ≤ d) :
    gg d * kk (d + 1) = 1 + 3 * ((2 ^ d : ℕ) : ZMod (2 ^ (d + 2))) := by
  unfold gg kk
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have e : ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 2))) * ((2 ^ (m + 1 + 1) : ℕ) : ZMod (2 ^ (m + 1 + 2))) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨2 ^ m, by ring⟩
  have e2 : ((2 ^ (m + 1 + 1) : ℕ) : ZMod (2 ^ (m + 1 + 2))) = 2 * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 2))) := by
    push_cast; ring
  rw [e2] at e ⊢
  linear_combination e

/-- Z/2^(d+2) → Z/2^d の単数の核 = {1, g, k, gk}。 -/
theorem ker4_cases (hd : 1 ≤ d) (u : (ZMod (2 ^ (d + 2)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow 2 (by omega : d ≤ d + 2))).ker) :
    (u : ZMod (2 ^ (d + 2))) = 1 ∨ (u : ZMod (2 ^ (d + 2))) = gg d ∨
      (u : ZMod (2 ^ (d + 2))) = kk (d + 1) ∨ (u : ZMod (2 ^ (d + 2))) = gg d * kk (d + 1) := by
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.cast_eq_val] at hu
  have hpd : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
  have h1 : (u : ZMod (2 ^ (d + 2))).val % 2 ^ d = 1 := by
    have := congrArg ZMod.val hu
    rwa [ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hpd] at this
  have hlt : (u : ZMod (2 ^ (d + 2))).val < 4 * 2 ^ d := by
    have := ZMod.val_lt (u : ZMod (2 ^ (d + 2)))
    have e2 : (2 : ℕ) ^ (d + 2) = 4 * 2 ^ d := by ring
    omega
  have hdm := Nat.div_add_mod (u : ZMod (2 ^ (d + 2))).val (2 ^ d)
  have hq : (u : ZMod (2 ^ (d + 2))).val / 2 ^ d < 4 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have back : ∀ t : ℕ, (u : ZMod (2 ^ (d + 2))).val = 1 + t * 2 ^ d →
      (u : ZMod (2 ^ (d + 2))) = 1 + (t : ZMod (2 ^ (d + 2))) * ((2 ^ d : ℕ) : ZMod (2 ^ (d + 2))) := by
    intro t ht
    rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ (d + 2))), ht]; push_cast; ring
  generalize hqq : (u : ZMod (2 ^ (d + 2))).val / 2 ^ d = q at hq hdm
  rw [h1] at hdm
  rcases q with _ | _ | _ | _ | q
  · left; have := back 0 (by simp at hdm; omega); simpa using this
  · right; left; have := back 1 (by simp at hdm; omega); rw [this, gg]; push_cast; ring
  · right; right; left
    have := back 2 (by simp at hdm; omega); rw [this, kk]
    push_cast; ring
  · right; right; right
    have := back 3 (by simp at hdm; omega); rw [this, gg_mul_kk hd]; push_cast; ring
  · omega

theorem gg_natCast : gg d = ((1 + 2 ^ d : ℕ) : ZMod (2 ^ (d + 2))) := by
  unfold gg; push_cast; ring

theorem isUnit_gg (hd : 1 ≤ d) : IsUnit (gg d) := by
  rw [gg_natCast, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro h
  have : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
  omega

/-- **一段降下の判定**: ψ(k) = 1（法 2^(d+1) を経由）のとき、ψ が法 2^d を経由 ⇔ ψ(g) = 1。 -/
theorem factors_two_step (hd : 1 ≤ d) (ψ : DirichletCharacter ℂ (2 ^ (d + 2))) (hk : ψ (kk (d + 1)) = 1) :
    ψ.FactorsThrough (2 ^ d) ↔ ψ (gg d) = 1 := by
  have : NeZero (2 ^ (d + 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow 2 (by omega : d ≤ d + 2))]
  constructor
  · intro h
    have hmem : (isUnit_gg hd).unit ∈ (ZMod.unitsMap (pow_dvd_pow 2 (by omega : d ≤ d + 2))).ker := by
      rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, IsUnit.unit_spec, Units.val_one, gg_natCast,
        ZMod.cast_natCast (pow_dvd_pow 2 (by omega : d ≤ d + 2))]
      have h0 : ((2 : ZMod (2 ^ d))) ^ d = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ d)
      push_cast
      rw [h0, add_zero]
    have := congrArg Units.val (h hmem)
    rwa [MulChar.coe_toUnitHom, IsUnit.unit_spec, Units.val_one] at this
  · intro hg u hu
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
    rcases ker4_cases hd u hu with e | e | e | e <;> rw [e]
    · exact map_one ψ
    · exact hg
    · exact hk
    · rw [map_mul, hg, hk, one_mul]

/-- 原始指標（法 2^(d+2)、d ≥ 2）は χ(g)² = −1（χ(g) = ±i）。 -/
theorem prim_gg_sq (hd : 2 ≤ d) (χ : DirichletCharacter ℂ (2 ^ (d + 2))) (hχ : χ.IsPrimitive) :
    χ (gg d) * χ (gg d) = -1 := by
  rw [← map_mul, gg_sq hd]
  exact prim_kk (c := d + 1) (by omega) χ hχ

/-- **p = 2 の導手降下の判定**（法 2^(d+2)、d ≥ 2）: 積 χ₁χ₂ が法 2^d を経由 ⇔ χ₂(g) = −χ₁(g)。 -/
theorem two_descent_iff (hd : 2 ≤ d) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (d + 2)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁ * χ₂).FactorsThrough (2 ^ d) ↔ χ₂ (gg d) = -χ₁ (gg d) := by
  have hk : (χ₁ * χ₂) (kk (d + 1)) = 1 := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, prim_kk (c := d + 1) (by omega) χ₁ h₁,
      prim_kk (c := d + 1) (by omega) χ₂ h₂]
    norm_num
  rw [factors_two_step (by omega) _ hk, MulChar.coeToFun_mul, Pi.mul_apply]
  have hs := prim_gg_sq hd χ₁ h₁
  constructor
  · intro h; linear_combination (-χ₁ (gg d)) * h + χ₂ (gg d) * hs
  · intro h; rw [h]; linear_combination -hs

/-- **一段で止まる場合**: χ₂(g) = χ₁(g) なら 積の導手はちょうど 2^(d+1)。 -/
theorem conductor_eq_of_stop (hd : 2 ≤ d) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (d + 2)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (hstop : χ₂ (gg d) = χ₁ (gg d)) :
    (χ₁ * χ₂).conductor = 2 ^ (d + 1) := by
  have : NeZero (2 ^ (d + 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hk : (χ₁ * χ₂) (kk (d + 1)) = 1 := by
    rw [MulChar.coeToFun_mul, Pi.mul_apply, prim_kk (c := d + 1) (by omega) χ₁ h₁,
      prim_kk (c := d + 1) (by omega) χ₂ h₂]
    norm_num
  have hf1 := factors_of_kk (c := d + 1) (by omega) (χ₁ * χ₂) hk
  have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet (χ₁ * χ₂)
    ((DirichletCharacter.mem_conductorSet_iff _).mpr hf1)
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases (by omega : i = d + 1 ∨ i ≤ d) with h | h
  · rw [he, h]
  · exfalso
    have hmem : 2 ^ d ∈ (χ₁ * χ₂).conductorSet :=
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (pow_dvd_pow 2 (by omega))).mpr
        (by rw [he]; exact pow_dvd_pow 2 h)
    have hneg := (two_descent_iff hd χ₁ χ₂ h₁ h₂).mp ((DirichletCharacter.mem_conductorSet_iff _).mp hmem)
    have hs := prim_gg_sq hd χ₁ h₁
    have h0 : χ₁ (gg d) = 0 := by linear_combination (hneg - hstop) / 2
    rw [h0, mul_zero] at hs
    norm_num at hs

end TwoDescent

end PAG.Part31

#print axioms PAG.Part31.dft_eps_zero_or_one
#print axioms PAG.Part31.lam_pos
#print axioms PAG.Part31.dft_auto_nonneg
#print axioms PAG.Part31.dft_auto_re_nonneg
#print axioms PAG.Part31.dft_H
#print axioms PAG.Part31.dft_H_odd_nonpos
#print axioms PAG.Part31.dft_H_even_nonneg
#print axioms PAG.Part31.ball_neg
#print axioms PAG.Part31.tilde_Pavg
#print axioms PAG.Part31.tilde_sub
#print axioms PAG.Part31.tilde_smul
#print axioms PAG.Part31.tilde_eps
#print axioms PAG.Part31.tilde_auto
#print axioms PAG.Part31.tilde_H
#print axioms PAG.Part31.conv_tilde
#print axioms PAG.Part31.tildeP1
#print axioms PAG.Part31.tildeP1_W
#print axioms PAG.Part31.neg_inv_of_unit
#print axioms PAG.Part31.compat_tildeP1
#print axioms PAG.Part31.tildeP1_extS
#print axioms PAG.Part31.tildeP1_extN
#print axioms PAG.Part31.BS_tilde
#print axioms PAG.Part31.BN_tilde
#print axioms PAG.Part31.tilde_ket
#print axioms PAG.Part31.tildeP1_kS
#print axioms PAG.Part31.tildeP1_kN
#print axioms PAG.Part31.W_tilde_kS
#print axioms PAG.Part31.tildeP1_epsS
#print axioms PAG.Part31.tildeP1_epsN
#print axioms PAG.Part31.conductor_ne_two
#print axioms PAG.Part31.mod4_mul_trivial
#print axioms PAG.Part31.gg
#print axioms PAG.Part31.gg_sq
#print axioms PAG.Part31.gg_mul_kk
#print axioms PAG.Part31.ker4_cases
#print axioms PAG.Part31.gg_natCast
#print axioms PAG.Part31.isUnit_gg
#print axioms PAG.Part31.factors_two_step
#print axioms PAG.Part31.prim_gg_sq
#print axioms PAG.Part31.two_descent_iff
#print axioms PAG.Part31.conductor_eq_of_stop
