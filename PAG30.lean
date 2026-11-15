/-
  PAG 2.0 Part 26（2026-10-19）
  1. 符号の意味: 反転 f ↦ f̃（f̃(x) = conj f(−x)）について |w,χ̄⟩ = χ(−1)·|w,χ⟩~。
     自己相関 A = |w,χ⟩ ⋆ |w,χ⟩~ は χ によらず A = (p^K/|S_{w0}|) ε_{w0}、A ⋆ A = (p^K/|S_{w0}|) A、A(0) = 1。
     定理 B の像は H = χ(−1)·A（奇指標の符号は反転 x ↦ −x から来る）。
  2. p = 2: 法 2^(c+1)（c ≥ 1）の原始指標は χ(1 + 2^c) = −1。二つの原始指標の積は原始的でない。
     法 2 の原始指標は存在しない。
-/
import PAG29

namespace PAG.Part30

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part25 PAG.Part28 PAG.Part29

/-! ## 1. 反転と自己相関 -/

section Tilde

variable {p : ℕ} [hp : Fact p.Prime]

/-- 反転共役 f̃(x) = conj f(−x)。 -/
noncomputable def tilde {N : ℕ} (f : ZMod N → ℂ) : ZMod N → ℂ := fun x => starRingEnd ℂ (f (-x))

omit hp in
theorem tilde_tilde {N : ℕ} (f : ZMod N → ℂ) : tilde (tilde f) = f := by
  funext x; simp [tilde]

omit hp in
theorem star_chi_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : starRingEnd ℂ (χ (-1)) = χ (-1) := by
  rw [starRingEnd_apply, MulChar.star_apply', chi_inv_neg_one]

omit hp in
theorem push_neg_apply {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G)
    (hι : Function.Injective ι) (f : H → ℂ) (y : H) : push ι f (-(ι y)) = f (-y) := by
  rw [← map_neg, push_apply_emb _ hι]

/-- **|w, χ̄⟩ = χ(−1)·|w, χ⟩~**。 -/
theorem ket_inv_eq_tilde (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ket K w c h ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ) = χ (-1) • tilde (ket K w c h χ) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hinj := shellEmb_injective (p := p) K w (by omega)
  funext x
  rw [Pi.smul_apply, smul_eq_mul, tilde]
  by_cases hx : ∃ y, shellEmb (p := p) K w (by omega) y = x
  · obtain ⟨y, rfl⟩ := hx
    unfold ket
    simp only [Pi.smul_apply, smul_eq_mul, push_apply_emb _ hinj, push_neg_apply _ hinj, Function.comp_apply, map_neg, map_mul,
      Complex.conj_ofReal]
    set z := (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c))).toAddMonoidHom y
    have hz : χ (-z) = χ (-1) * χ z := by rw [← map_mul, neg_one_mul]
    rw [hz, map_mul, star_chi_neg_one, starRingEnd_apply (χ z), MulChar.star_apply']
    have h1 := PAG.Part9.chi_neg_one_sq χ
    linear_combination (-(((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) * χ⁻¹ z) * h1
  · have hx' : ¬ ∃ y, shellEmb (p := p) K w (by omega) y = -x := by
      rintro ⟨y, hy⟩; exact hx ⟨-y, by rw [map_neg, hy, neg_neg]⟩
    unfold ket
    simp only [Pi.smul_apply, smul_eq_mul, push_apply_not _ _ _ hx, push_apply_not _ _ _ hx', mul_zero,
      map_zero]

/-- 自己相関 A = |w,χ⟩ ⋆ |w,χ⟩~。 -/
noncomputable def auto (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : ZMod (p ^ K) → ℂ :=
  conv (ket K w c h χ) (tilde (ket K w c h χ))

/-- **定理 B の像 = χ(−1) × 自己相関**: H = χ(−1)·A。 -/
theorem H_eq_chi_auto (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    conv (ket K w c h χ) (ket K w c h ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = χ (-1) • auto K w c h χ := by
  rw [ket_inv_eq_tilde, auto]
  have e := conv_smul_smul (1 : ℂ) (χ (-1)) (ket K w c h χ) (tilde (ket K w c h χ))
  rw [one_smul, one_mul] at e
  exact e

/-- **自己相関は χ によらない正のべき等元倍**: A = (p^K/|S_{w0}|) ε_{w0}。 -/
theorem auto_eps (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    auto K w (n + 1) hK χ
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) •
          PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w) := by
  have e := H_eq_chi_auto K w (n + 1) hK χ
  rw [thmB_eps K w n hK χ hχ, cB] at e
  have h1 := PAG.Part9.chi_neg_one_sq χ
  have e2 := congrArg (fun f => χ (-1) • f) e
  simp only [smul_smul, ← mul_assoc, h1, one_mul, one_smul] at e2
  exact e2.symm

/-- **A ⋆ A = (p^K/|S_{w0}|) A**（指示書 Part 25 の形は自己相関について正しい）。 -/
theorem auto_self (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (auto K w (n + 1) hK χ) (auto K w (n + 1) hK χ)
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) • auto K w (n + 1) hK χ := by
  rw [auto_eps K w n hK χ hχ, conv_smul_smul, eps_conv K _ _ (by omega) (by omega),
    ite_eq_left_of_eq_true _ _ (eq_true rfl), smul_smul]

/-- **A(0) = 1**（‖|w,χ⟩‖² = 1 と整合）。 -/
theorem auto_zero (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    auto K w (n + 1) hK χ 0 = 1 := by
  rw [auto_eps K w n hK χ hχ, Pi.smul_apply, PAG.Part14.epsBall,
    ite_eq_left_of_eq_true _ _ (eq_true (by omega : K - (n + 1) - w < K))]
  simp only [Pi.sub_apply, Pavg, Pi.smul_apply, ball, ZMod.val_zero, dvd_zero, ↓reduceIte, smul_eq_mul,
    mul_one]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    intro h; apply this.ne'; exact_mod_cast (sub_eq_zero.mp h)
  have hsz : (sz p K (K - (n + 1) - w) : ℂ) = (p : ℂ) ^ (w + n) * ((p : ℂ) - 1) := by
    unfold sz
    rw [show K - 1 - (K - (n + 1) - w) = w + n by omega]
    push_cast [Nat.cast_sub hp.out.one_lt.le]
    ring
  have hpK : (p : ℂ) ^ K = (p : ℂ) ^ (K - (n + 1) - w) * (p : ℂ) ^ (w + n) * p := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [hsz, hpK]
  field_simp
  ring

end Tilde

/-! ## 2. p = 2: 原始指標の積は原始的でない -/

section Two

variable {c : ℕ}

theorem fourLe (hc : 1 ≤ c) : 1 < 2 ^ c := Nat.one_lt_two_pow (by omega)

/-- 法 2^(c+1) の元 k = 1 + 2^c。 -/
def kk (c : ℕ) : ZMod (2 ^ (c + 1)) := 1 + ((2 ^ c : ℕ) : ZMod (2 ^ (c + 1)))

theorem kk_sq (hc : 1 ≤ c) : kk c * kk c = 1 := by
  unfold kk
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  have h : ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1)))
      + 2 * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1))) = 0 := by
    have e : ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1))) * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1)))
        + 2 * ((2 ^ (m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1)))
        = ((2 ^ (m + 1 + 1) * (2 ^ m + 1) : ℕ) : ZMod (2 ^ (m + 1 + 1))) := by
      push_cast; ring
    rw [e, ZMod.natCast_eq_zero_iff]
    exact dvd_mul_right _ _
  linear_combination h

theorem isUnit_kk (hc : 1 ≤ c) : IsUnit (kk c) := ⟨⟨kk c, kk c, kk_sq hc, kk_sq hc⟩, rfl⟩

/-- 核 {u ≡ 1 mod 2^c} = {1, k}。 -/
theorem ker_cases (hc : 1 ≤ c) (u : (ZMod (2 ^ (c + 1)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow 2 (Nat.le_succ c))).ker) :
    (u : ZMod (2 ^ (c + 1))) = 1 ∨ (u : ZMod (2 ^ (c + 1))) = kk c := by
  have : NeZero (2 ^ (c + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, Units.val_one,
    ZMod.cast_eq_val] at hu
  have h1 : (u : ZMod (2 ^ (c + 1))).val % 2 ^ c = 1 := by
    have := congrArg ZMod.val hu
    rwa [ZMod.val_natCast, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (fourLe hc)] at this
  have hlt : (u : ZMod (2 ^ (c + 1))).val < 2 * 2 ^ c := by
    have := ZMod.val_lt (u : ZMod (2 ^ (c + 1)))
    have e2 : (2 : ℕ) ^ (c + 1) = 2 * 2 ^ c := by ring
    omega
  have hc2 : 2 ≤ 2 ^ c := fourLe hc
  have hd := Nat.div_add_mod (u : ZMod (2 ^ (c + 1))).val (2 ^ c)
  have hq : (u : ZMod (2 ^ (c + 1))).val / 2 ^ c < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  have key : (u : ZMod (2 ^ (c + 1))).val = 1 ∨ (u : ZMod (2 ^ (c + 1))).val = 1 + 2 ^ c := by
    generalize hqq : (u : ZMod (2 ^ (c + 1))).val / 2 ^ c = q at hq hd
    rw [h1] at hd
    rcases q with _ | _ | q
    · left; simp at hd; omega
    · right; simp at hd; omega
    · omega
  rcases key with e | e
  · left; rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ (c + 1))), e, Nat.cast_one]
  · right; rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ (c + 1))), e, kk, Nat.cast_add, Nat.cast_one]

/-- χ が法 2^c を経由すれば原始的でない。 -/
theorem not_prim_of_factors (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1)))
    (hf : χ.FactorsThrough (2 ^ c)) : ¬ χ.IsPrimitive := by
  intro hp
  have hle : χ.conductor ≤ 2 ^ c := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hf)
  rw [DirichletCharacter.isPrimitive_def] at hp
  rw [hp, pow_succ] at hle
  have := fourLe hc
  omega

/-- 核上で χ(k) = 1 なら 法 2^c を経由する。 -/
theorem factors_of_kk (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1))) (hk : χ (kk c) = 1) :
    χ.FactorsThrough (2 ^ c) := by
  have : NeZero (2 ^ (c + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow 2 (Nat.le_succ c))]
  intro u hu
  rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  rcases ker_cases hc u hu with e | e
  · rw [e, map_one]
  · rw [e, hk]

/-- **p = 2 の原始指標は χ(1 + 2^c) = −1**（法 2^(c+1)、c ≥ 1）。 -/
theorem prim_kk (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1))) (hχ : χ.IsPrimitive) :
    χ (kk c) = -1 := by
  have hsq : χ (kk c) * χ (kk c) = 1 := by rw [← map_mul, kk_sq hc, map_one]
  have hne : χ (kk c) ≠ 1 := fun h => not_prim_of_factors hc χ (factors_of_kk hc χ h) hχ
  have : (χ (kk c) - 1) * (χ (kk c) + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact eq_neg_of_add_eq_zero_left h

/-- **p = 2 では二つの原始指標の積は原始的でない**（法 2^(c+1)、c ≥ 1）。 -/
theorem two_mul_not_prim (hc : 1 ≤ c) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (c + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : ¬ (χ₁ * χ₂).IsPrimitive := by
  apply not_prim_of_factors hc
  apply factors_of_kk hc
  rw [MulChar.coeToFun_mul, Pi.mul_apply, prim_kk hc χ₁ h₁, prim_kk hc χ₂ h₂]
  norm_num

/-- 法 2 の原始指標は存在しない。 -/
theorem no_prim_mod_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive := by
  have hχ : χ = 1 := by
    ext u
    have : u = 1 := by
      have hc : Fintype.card (ZMod 2)ˣ = 1 := by rw [ZMod.card_units_eq_totient]; rfl
      exact Fintype.card_le_one_iff_subsingleton.mp hc.le |>.elim _ _
    simp [this]
  intro hp
  rw [DirichletCharacter.isPrimitive_def, hχ, DirichletCharacter.conductor_one (n := 2)] at hp
  exact absurd hp (by norm_num)

/-- 系: p = 2 では赤道絡み合い（積が原始的という仮定）に当てはまる組はない。 -/
theorem two_equator_vacuous (n : ℕ) (hn : 1 ≤ n + 1) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : ¬ (χ₁ * χ₂).IsPrimitive := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact fun _ => no_prim_mod_two χ₁ h₁
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact two_mul_not_prim (c := m + 1) (by omega) χ₁ χ₂ h₁ h₂

end Two

end PAG.Part30

#print axioms PAG.Part30.tilde
#print axioms PAG.Part30.tilde_tilde
#print axioms PAG.Part30.star_chi_neg_one
#print axioms PAG.Part30.push_neg_apply
#print axioms PAG.Part30.ket_inv_eq_tilde
#print axioms PAG.Part30.auto
#print axioms PAG.Part30.H_eq_chi_auto
#print axioms PAG.Part30.auto_eps
#print axioms PAG.Part30.auto_self
#print axioms PAG.Part30.auto_zero
#print axioms PAG.Part30.fourLe
#print axioms PAG.Part30.kk
#print axioms PAG.Part30.kk_sq
#print axioms PAG.Part30.isUnit_kk
#print axioms PAG.Part30.ker_cases
#print axioms PAG.Part30.not_prim_of_factors
#print axioms PAG.Part30.factors_of_kk
#print axioms PAG.Part30.prim_kk
#print axioms PAG.Part30.two_mul_not_prim
#print axioms PAG.Part30.no_prim_mod_two
#print axioms PAG.Part30.two_equator_vacuous
