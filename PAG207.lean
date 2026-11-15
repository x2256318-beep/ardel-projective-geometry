/-
  PAG 2.0 Part 203（2026-10-24）— ℤ/N の動径関数の代数と、ケットの同時固有ベクトル性
  動径関数：単数倍で不変な関数 f(a·x) = f(x)（def Radial）。局所の Part 54・55 の大域版
  1. 軌道：ξ = a·gcd(N, ξ)（a は単数）、gcd(N, a·ξ) = gcd(N, ξ)
  2. f が動径的 ⇔ 𝓕f が動径的。1_{D_s}、ε_s、球 1_{vℤ} は動径的
  3. 動径的 ⇔ ε_s の一次結合：f = Σ_{s ∣ N} 𝓕f(s)·ε_s。ε_s は一次独立で、張る空間の次元は d(N)
  4. 動径関数は畳み込みで閉じる（可換な部分代数）
  5. ケット |u, χ⟩（s₀ = M/c）：u の素因数がすべて c を割るなら、動径的な f について k ⋆ f = 𝓕f(s₀)·k。
     逆に、すべての動径関数の同時固有ベクトルなら u の素因数はすべて c を割る（gket_eigen_iff）
  6. 例：(R) のもとで k ⋆ 1_{vℤ} = [W ∣ s₀]·W·k（vW = N。局所の Part 54 の k ⋆ ball_j の大域版）
-/
import PAG206

namespace PAG.Part207

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205
open ZMod (stdAddChar)
open scoped ZMod

/-- 動径関数：単数倍で不変。 -/
def Radial {N : ℕ} (f : ZMod N → ℂ) : Prop := ∀ (a : (ZMod N)ˣ) (x : ZMod N), f ((a : ZMod N) * x) = f x

/-! ### 1. 軌道 -/

/-- **1a.** gcd(N, (a·x).val) = gcd(N, x.val)（a は単数）。 -/
theorem gcd_val_unit_mul (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (x : ZMod N) :
    Nat.gcd N ((a : ZMod N) * x).val = Nat.gcd N x.val := by
  rw [ZMod.val_mul, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm,
    Nat.Coprime.gcd_mul_left_cancel _ (ZMod.val_coe_unit_coprime a), Nat.gcd_comm]

/-- **1b. 軌道**：ξ = a·gcd(N, ξ) となる単数 a がある。 -/
theorem exists_unit_mul_gcd (N : ℕ) [NeZero N] (ξ : ZMod N) :
    ∃ a : (ZMod N)ˣ, (a : ZMod N) * ((Nat.gcd N ξ.val : ℕ) : ZMod N) = ξ := by
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd N ξ.val := ⟨_, rfl⟩
  rw [← hg]
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_left _ hN0
  have hgN : g ∣ N := by rw [hg]; exact Nat.gcd_dvd_left N ξ.val
  have hgξ : g ∣ ξ.val := by rw [hg]; exact Nat.gcd_dvd_right N ξ.val
  obtain ⟨y, hy⟩ := hgξ
  obtain ⟨n, hNn⟩ := hgN
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, mul_zero] at hNn; exact absurd hNn (NeZero.ne N)
    · exact h0
  have : NeZero n := ⟨hn0.ne'⟩
  -- y は n と互いに素：gcd(N, ξ) = g·gcd(n, y)
  have hyn : Nat.Coprime y n := by
    have e : Nat.gcd N ξ.val = g * Nat.gcd n y := by rw [hy, hNn, Nat.gcd_mul_left]
    rw [← hg] at e
    have e2 : g * Nat.gcd n y = g * 1 := by rw [← e, mul_one]
    exact Nat.Coprime.symm (Nat.eq_of_mul_eq_mul_left hg0 e2)
  have hnN : n ∣ N := Dvd.intro_left g hNn.symm
  obtain ⟨a, ha⟩ := ZMod.unitsMap_surjective (m := N) hnN (ZMod.unitOfCoprime y hyn)
  refine ⟨a, ?_⟩
  have h1 : (((a : ZMod N).val : ℕ) : ZMod n) = (y : ZMod n) := by
    have e := congrArg Units.val ha
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.coe_unitOfCoprime] at e
    exact e
  have h2 : (a : ZMod N).val * g ≡ y * g [MOD n * g] :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).mul_right' g
  rw [show n * g = N by rw [hNn, mul_comm]] at h2
  have h3 : (((a : ZMod N).val * g : ℕ) : ZMod N) = ((y * g : ℕ) : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
  rw [Nat.cast_mul, Nat.cast_mul, ZMod.natCast_zmod_val] at h3
  rw [h3, ← Nat.cast_mul, mul_comm y g, ← hy, ZMod.natCast_zmod_val]

/-- gcd(N, (s : ZMod N).val) = s（s ∣ N）。 -/
theorem gcd_natCast_self (N s : ℕ) [NeZero N] (hs : s ∣ N) : Nat.gcd N (s : ZMod N).val = s := by
  rw [ZMod.val_natCast]
  rcases Nat.lt_or_ge s N with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, Nat.gcd_eq_right hs]
  · have e : s = N := le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hs) hge
    rw [e, Nat.mod_self, Nat.gcd_zero_right]

/-! ### 2. 動径関数とフーリエ変換 -/

/-- **2a.** f が動径的なら 𝓕f も動径的。 -/
theorem dft_radial {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (hf : Radial f) : Radial (𝓕 f) := by
  intro a k
  have e := ZMod.dft_comp_unitMul f a⁻¹ k
  rw [inv_inv] at e
  have hfun : (fun j => f (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * j)) = f := funext (fun j => hf a⁻¹ j)
  rw [hfun] at e
  exact e.symm

/-- **2b.** 𝓕f が動径的なら f も動径的（𝓕𝓕f(x) = N·f(−x)）。 -/
theorem radial_of_dft_radial {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (hf : Radial (𝓕 f)) : Radial f := by
  have h2 := dft_radial (𝓕 f) hf
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ y, (N : ℂ) * f y = 𝓕 (𝓕 f) (-y) := fun y => by
    rw [ZMod.dft_dft]; simp
  intro a x
  have e := key ((a : ZMod N) * x)
  rw [show -((a : ZMod N) * x) = (a : ZMod N) * (-x) by ring, h2 a (-x), ← key x] at e
  exact mul_left_cancel₀ hN e

/-- **2c.** f が動径的 ⇔ 𝓕f が動径的。 -/
theorem radial_iff_dft {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : Radial f ↔ Radial (𝓕 f) :=
  ⟨dft_radial f, radial_of_dft_radial f⟩

/-- 1_{D_s} は動径的。 -/
theorem dind_radial (N s : ℕ) [NeZero N] : Radial (dind N s) := by
  intro a x
  simp only [dind, gcd_val_unit_mul]

/-- **2d.** ε_s は動径的。 -/
theorem geps_radial (N s : ℕ) [NeZero N] : Radial (geps N s) :=
  radial_of_dft_radial _ (by rw [dft_geps]; exact dind_radial N s)

/-- **2e.** 球 1_{vℤ}（v ∣ N）は動径的。 -/
theorem ball_radial (v N : ℕ) [NeZero N] (hv : v ∣ N) : Radial (rk (N := N) v 1 (fun _ => 1)) := by
  have key : ∀ y : ZMod N, v ∣ y.val ↔ v ∣ Nat.gcd N y.val := fun y =>
    ⟨fun hy => Nat.dvd_gcd hv hy, fun hy => hy.trans (Nat.gcd_dvd_right _ _)⟩
  intro a x
  have e : v ∣ ((a : ZMod N) * x).val ↔ v ∣ x.val := by
    rw [key, key x, gcd_val_unit_mul]
  simp only [rk]
  by_cases hx : v ∣ x.val
  · rw [ite_eq_left (e.mpr hx), ite_eq_left hx]
  · rw [ite_eq_right (fun h' => hx (e.mp h')), ite_eq_right hx]

/-! ### 3. 動径関数は ε_s の一次結合 -/

/-- 動径的な F は D_s の上で一定：F(ξ) = F(gcd(N, ξ))。 -/
theorem radial_apply_gcd {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (hF : Radial F) (ξ : ZMod N) :
    F ξ = F ((Nat.gcd N ξ.val : ℕ) : ZMod N) := by
  obtain ⟨a, ha⟩ := exists_unit_mul_gcd N ξ
  conv_lhs => rw [← ha]
  exact hF a _

/-- **3a.** 動径的な f は f = Σ_{s ∣ N} 𝓕f(s)·ε_s。 -/
theorem radial_eq_sum_geps {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (hf : Radial f) :
    f = ∑ s ∈ N.divisors, (𝓕 f (s : ZMod N)) • geps N s := by
  have hF := dft_radial f hf
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, dft_geps, dind, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq]
  rw [ite_eq_left (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne N⟩)]
  exact radial_apply_gcd _ hF ξ

/-- **3b.** 動径的 ⇔ ε_s（s ∣ N）の一次結合。 -/
theorem radial_iff {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    Radial f ↔ ∃ c : ℕ → ℂ, f = ∑ s ∈ N.divisors, c s • geps N s := by
  constructor
  · intro hf
    exact ⟨fun s => 𝓕 f (s : ZMod N), radial_eq_sum_geps f hf⟩
  · rintro ⟨c, rfl⟩ a x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun s _ => by rw [geps_radial N s a x])

/-- 1_{D_s}(s) = 1（s ∣ N）。 -/
theorem dind_self (N s : ℕ) [NeZero N] (hs : s ∣ N) : dind N s (s : ZMod N) = 1 := by
  simp only [dind]
  rw [ite_eq_left (gcd_natCast_self N s hs)]

/-- ε_s ≠ 0（s ∣ N）。 -/
theorem geps_ne_zero (N s : ℕ) [NeZero N] (hs : s ∣ N) : geps N s ≠ 0 := by
  intro h
  have e := congrFun (congrArg (ZMod.dft (N := N) (E := ℂ)) h) (s : ZMod N)
  rw [dft_geps, map_zero, Pi.zero_apply, dind_self N s hs] at e
  exact one_ne_zero e

/-- **3c.** ε_s（s ∣ N）は一次独立。 -/
theorem geps_linearIndependent (N : ℕ) [NeZero N] :
    LinearIndependent ℂ (fun s : N.divisors => geps N (s : ℕ)) := by
  rw [linearIndependent_iff']
  intro S g hsum i hi
  have e := congrFun (congrArg (ZMod.dft (N := N) (E := ℂ)) hsum) (((i : ℕ) : ZMod N))
  rw [map_sum, map_zero, Finset.sum_apply, Pi.zero_apply] at e
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, dft_geps] at e
  have hiN : (i : ℕ) ∣ N := (Nat.mem_divisors.mp i.2).1
  rw [Finset.sum_eq_single i (fun j _ hji => by
      have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Subtype.ext h)
      simp only [dind]
      rw [ite_eq_right (fun h => hne (h.symm.trans (gcd_natCast_self N i hiN))), mul_zero])
    (fun hi' => absurd hi hi'), dind_self N i hiN, mul_one] at e
  exact e

/-- **3d.** ε_s が張る空間（= 動径関数の空間）の次元は d(N)。 -/
theorem finrank_span_geps (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun s : N.divisors => geps N (s : ℕ)))) =
      N.divisors.card := by
  rw [finrank_span_eq_card (geps_linearIndependent N), Fintype.card_coe]

/-! ### 4. 畳み込みで閉じる -/

/-- **4.** 動径関数の畳み込みは動径的。 -/
theorem radial_conv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) (hf : Radial f) (hg : Radial g) :
    Radial (PAG.Part15.conv f g) := by
  apply radial_of_dft_radial
  intro a k
  rw [PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_radial f hf a k, dft_radial g hg a k]

/-! ### 5. ケットは動径関数の同時固有ベクトル -/

/-- **5a.** u の素因数がすべて c を割るなら、動径的な f について |u, χ⟩ ⋆ f = 𝓕f(s₀)·|u, χ⟩（s₀ = M/c）。 -/
theorem gket_conv_radial (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (f : ZMod N → ℂ) (hf : Radial f) :
    PAG.Part15.conv (gket u M N h c hc χ) f = (𝓕 f ((M / c : ℕ) : ZMod N)) • gket u M N h c hc χ := by
  have hF := dft_radial f hf
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  by_cases h0 : 𝓕 (gket u M N h c hc χ) ξ = 0
  · rw [h0, zero_mul, mul_zero]
  · have hg := (dft_gket_ne_zero_iff u M N h c hc χ hχ hrad ξ).mp h0
    have e : 𝓕 f ξ = 𝓕 f ((M / c : ℕ) : ZMod N) := by
      rw [radial_apply_gcd _ hF ξ, hg]
    rw [e]; ring

/-- 𝓕|u, χ⟩(s₀) ≠ 0（条件なし）。 -/
theorem dft_gket_dual_ne_zero (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    𝓕 (gket u M N h c hc χ) ((M / c : ℕ) : ZMod N) ≠ 0 := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd hM0 hc) hc0
  have hsN : M / c ∣ N := Dvd.intro _ (dual_eq h hc)
  have hφ : (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hM0)
    exact_mod_cast (inv_pos.mpr this).ne'
  have hsC : ((M / c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hneg : χ⁻¹ (-1) ≠ 0 := ((isUnit_one.neg : IsUnit (-1 : ZMod c)).map χ⁻¹).ne_zero
  rw [dft_gket_apply u M N h c hc χ hχ, ZMod.val_natCast]
  have hdvd : M / c ∣ M / c % N := (Nat.dvd_mod_iff hsN).mpr dvd_rfl
  rw [ite_eq_left hdvd]
  have hcop : (M / c % N / (M / c)).Coprime c := by
    rcases Nat.lt_or_ge (M / c) N with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt, Nat.div_self hs0]
      exact Nat.coprime_one_left c
    · -- M/c = N なら M = N、c = 1
      have hMN : M ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Dvd.intro_left u h)
      have heq : M / c = M := le_antisymm (Nat.div_le_self M c) (hMN.trans hge)
      have hc1 : c = 1 := by
        rcases Nat.div_eq_self.mp heq with h0 | h1
        · exact absurd h0 hM0.ne'
        · exact h1
      rw [hc1]
      exact Nat.coprime_one_right _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hφ hsC) hneg) (PAG.Part16.gaussSum_ne_zero hχ))
    (chi_natCast_ne_zero χ⁻¹ _ hcop)

/-- **5b. 同時固有ベクトルの判定**：すべての動径関数 f で |u, χ⟩ ⋆ f ∈ ℂ·|u, χ⟩ ⇔ u の素因数がすべて c を割る。 -/
theorem gket_eigen_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    (∀ f : ZMod N → ℂ, Radial f → ∃ μ : ℂ, PAG.Part15.conv (gket u M N h c hc χ) f = μ • gket u M N h c hc χ) ↔
      ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c := by
  constructor
  · intro H
    obtain ⟨μ, hμ⟩ := H (geps N (M / c)) (geps_radial N (M / c))
    have hsN : M / c ∣ N := Dvd.intro _ (dual_eq h hc)
    have hk0 := dft_gket_dual_ne_zero u M N h c hc χ hχ
    have e := congrFun (congrArg (ZMod.dft (N := N) (E := ℂ)) hμ) ((M / c : ℕ) : ZMod N)
    rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps, dind_self N (M / c) hsN, map_smul, Pi.smul_apply,
      smul_eq_mul] at e
    have hμ1 : μ = 1 := mul_right_cancel₀ hk0 (e.symm.trans (by ring))
    rw [← gket_mem_iff u M N h c hc χ hχ, PAG.Part15.conv_comm, hμ, hμ1, one_smul]
  · intro hrad f hf
    exact ⟨_, gket_conv_radial u M N h c hc χ hχ hrad f hf⟩

/-- **6. 例：球**。u の素因数がすべて c を割るなら |u, χ⟩ ⋆ 1_{vℤ} = [W ∣ s₀]·W·|u, χ⟩（vW = N）。 -/
theorem gket_conv_ball (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c)
    (v W : ℕ) (hvW : v * W = N) :
    PAG.Part15.conv (gket u M N h c hc χ) (rk (N := N) v 1 (fun _ => 1)) =
      (if W ∣ M / c then (W : ℂ) else 0) • gket u M N h c hc χ := by
  have hsN : M / c ∣ N := Dvd.intro _ (dual_eq h hc)
  have hWN : W ∣ N := Dvd.intro_left v hvW
  rw [gket_conv_radial u M N h c hc χ hχ hrad _ (ball_radial v N (Dvd.intro W hvW)),
    dft_ball v W N hvW, ZMod.val_natCast]
  congr 1
  by_cases hW : W ∣ M / c
  · rw [ite_eq_left ((Nat.dvd_mod_iff hWN).mpr hW), ite_eq_left hW]
  · rw [ite_eq_right (fun h' => hW ((Nat.dvd_mod_iff hWN).mp h')), ite_eq_right hW]

end PAG.Part207

#print axioms PAG.Part207.gcd_val_unit_mul
#print axioms PAG.Part207.exists_unit_mul_gcd
#print axioms PAG.Part207.gcd_natCast_self
#print axioms PAG.Part207.dft_radial
#print axioms PAG.Part207.radial_of_dft_radial
#print axioms PAG.Part207.radial_iff_dft
#print axioms PAG.Part207.dind_radial
#print axioms PAG.Part207.geps_radial
#print axioms PAG.Part207.ball_radial
#print axioms PAG.Part207.radial_apply_gcd
#print axioms PAG.Part207.radial_eq_sum_geps
#print axioms PAG.Part207.radial_iff
#print axioms PAG.Part207.dind_self
#print axioms PAG.Part207.geps_ne_zero
#print axioms PAG.Part207.geps_linearIndependent
#print axioms PAG.Part207.finrank_span_geps
#print axioms PAG.Part207.radial_conv
#print axioms PAG.Part207.gket_conv_radial
#print axioms PAG.Part207.dft_gket_dual_ne_zero
#print axioms PAG.Part207.gket_eigen_iff
#print axioms PAG.Part207.gket_conv_ball
