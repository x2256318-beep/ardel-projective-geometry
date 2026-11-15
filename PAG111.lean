/-
  PAG 2.0 Part 107（2026-10-19）— 積の巡回構造: (k₁ ⊗ k₂)^m がスカラー ⟺ lcm(ord χ₁, ord χ₂) ∣ m
  1. 作用素の冪 cpow k m = k^{⋆m}（k^{⋆0} = δ）と、(k₁ ⊗ k₂)^{⋆m} = k₁^{⋆m} ⊗ k₂^{⋆m}
  2. 「e で固定される空間の上でスカラー」Scalar e k := ∃ c, ∀ f, e⋆f = f → k⋆f = c f
  3. 積のスカラー性: 各因子が V 上で単射、V ≠ 0 なら Scalar (e₁⊗e₂) (A⊗B) ⟺ Scalar e₁ A ∧ Scalar e₂ B
  4. 単一素数（作用素の形）: Scalar ε_a (k^{⋆m}) ⟺ χ^m = 1（m ≥ 1）
  5. 系: Scalar (ε_{a₁}⊗ε_{a₂}) ((k₁⊗k₂)^{⋆m}) ⟺ lcm(orderOf χ₁, orderOf χ₂) ∣ m
-/
import PAG110

namespace PAG.Part111

open ZMod Finset PAG.Part15 PAG.Part108 PAG.Part109

section Generic

variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [DecidableEq G] in
theorem conv_smul_gen (f g : G → ℂ) (c : ℂ) : conv f (c • g) = c • conv f g := by
  funext x; simp only [conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply sum_congr rfl; intro _ _; ring

theorem conv_single_gen (g : G → ℂ) : conv (Pi.single 0 1) g = g := by
  funext x
  simp only [conv]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- 作用素の冪 k^{⋆m}。 -/
noncomputable def cpow (k : G → ℂ) : ℕ → G → ℂ
  | 0 => Pi.single 0 1
  | m + 1 => conv k (cpow k m)

theorem cpow_tens (k₁ : G → ℂ) (k₂ : H → ℂ) (m : ℕ) :
    cpow (tens k₁ k₂) m = tens (cpow k₁ m) (cpow k₂ m) := by
  induction m with
  | zero => exact (tens_single 0 0).symm
  | succ m ih => simp only [cpow]; rw [ih, conv_tens]

omit [DecidableEq G] in
/-- e で固定される関数は、畳み込みの後も固定される。 -/
theorem fix_conv (e k f : G → ℂ) (hf : conv e f = f) : conv e (conv k f) = conv k f := by
  rw [← conv_assoc_gen, conv_comm e k, conv_assoc_gen, hf]

theorem isoOn_cpow (e k : G → ℂ) (l : ℝ) (hk : IsoOn e k l) (m : ℕ) : IsoOn e (cpow k m) (l ^ m) := by
  induction m with
  | zero => intro f _; simp [cpow, conv_single_gen]
  | succ m ih =>
    intro f hf
    simp only [cpow]
    rw [conv_assoc_gen, hk _ (fix_conv e _ f hf), ih f hf, pow_succ]; ring

/-- 「e で固定される空間の上でスカラー」。 -/
def Scalar {X : Type*} [AddCommGroup X] [Fintype X] (e k : X → ℂ) : Prop :=
  ∃ c : ℂ, ∀ f, conv e f = f → conv k f = c • f

omit [DecidableEq G] [DecidableEq H] in
/-- **3. 積のスカラー性**。 -/
theorem scalar_tens_iff (e₁ A : G → ℂ) (e₂ B : H → ℂ) (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂)
    (hA : ∀ f, conv e₁ f = f → conv A f = 0 → f = 0) (hB : ∀ f, conv e₂ f = f → conv B f = 0 → f = 0)
    (f₁ : G → ℂ) (hf₁ : conv e₁ f₁ = f₁) (hf₁0 : f₁ ≠ 0) (f₂ : H → ℂ) (hf₂ : conv e₂ f₂ = f₂) (hf₂0 : f₂ ≠ 0) :
    Scalar (tens e₁ e₂) (tens A B) ↔ Scalar e₁ A ∧ Scalar e₂ B := by
  constructor
  · rintro ⟨c, hc⟩
    have key : ∀ g₁ g₂, conv e₁ g₁ = g₁ → conv e₂ g₂ = g₂ →
        tens (conv A g₁) (conv B g₂) = c • tens g₁ g₂ := by
      intro g₁ g₂ hg₁ hg₂
      rw [← conv_tens]
      exact hc _ (by rw [conv_tens, hg₁, hg₂])
    constructor
    · have hB0 : conv B f₂ ≠ 0 := fun h => hf₂0 (hB f₂ hf₂ h)
      obtain ⟨y, hy⟩ : ∃ y, conv B f₂ y ≠ 0 := by
        by_contra H; push Not at H; exact hB0 (funext H)
      refine ⟨c * f₂ y / conv B f₂ y, fun f hf => ?_⟩
      funext x
      have := congrFun (key f f₂ hf hf₂) (x, y)
      simp only [tens, Pi.smul_apply, smul_eq_mul] at this ⊢
      field_simp
      linear_combination this
    · have hA0 : conv A f₁ ≠ 0 := fun h => hf₁0 (hA f₁ hf₁ h)
      obtain ⟨x, hx⟩ : ∃ x, conv A f₁ x ≠ 0 := by
        by_contra H; push Not at H; exact hA0 (funext H)
      refine ⟨c * f₁ x / conv A f₁ x, fun f hf => ?_⟩
      funext y
      have := congrFun (key f₁ f hf₁ hf) (x, y)
      simp only [tens, Pi.smul_apply, smul_eq_mul] at this ⊢
      field_simp
      linear_combination this
  · rintro ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩
    refine ⟨c₁ * c₂, fun g hg => ?_⟩
    obtain ⟨hs₁, hs₂⟩ := (tens_fix_iff e₁ e₂ h₁ h₂ g).mp hg
    funext z
    obtain ⟨x, y⟩ := z
    rw [conv_tens_apply]
    have e1 : (fun x' => conv B (fun y' => g (x', y')) y) = c₂ • (fun x' => g (x', y)) := by
      funext x'; rw [hc₂ _ (hs₂ x')]; rfl
    rw [e1, conv_smul_gen, hc₁ _ (hs₁ y)]
    simp only [Pi.smul_apply, smul_eq_mul]; ring

end Generic

/-! ## 4. 単一素数: 作用素の形の巡回構造 -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime]

theorem dft_cpow (K : ℕ) (k : ZMod (p ^ K) → ℂ) (m : ℕ) (t : ZMod (p ^ K)) :
    𝓕 (cpow k m) t = 𝓕 k t ^ m := by
  induction m with
  | zero => simp [cpow, ZMod.dft_apply, Pi.single_apply]
  | succ m ih => simp only [cpow]; rw [PAG.Part16.dft_conv, Pi.mul_apply, ih, pow_succ]; ring

theorem Tset_nonempty (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : (Tset (p := p) K (K - (n + 1) - w)).Nonempty := by
  rw [← Finset.card_pos, card_Tset K _ _ ⟨w, n, h, χ, hχ, rfl, rfl⟩]
  unfold sz
  exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)

/-- **4. 単一素数**: Scalar ε_a (k^{⋆(m+1)}) ⟺ χ^{m+1} = 1。 -/
theorem scalar_cpow_iff (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) :
    Scalar (eps (p := p) K (K - (n + 1) - w)) (cpow (ket K w (n + 1) h χ) (m + 1)) ↔ χ ^ (m + 1) = 1 := by
  set a := K - (n + 1) - w with ha
  set k := ket K w (n + 1) h χ
  have haK : a ≤ K := by omega
  constructor
  · rintro ⟨c, hc⟩
    by_contra hne
    obtain ⟨t, ht, t', ht', hneq⟩ := PAG.Part99.pow_eigen_nonconst K w n h χ hχ m hne
    have hval : ∀ s ∈ Tset (p := p) K a, 𝓕 k s ^ (m + 1) = c := by
      intro s hs
      have h1 : 𝓕 (eps (p := p) K a) s = 1 := by simpa [Tset] using hs
      have := congrArg (fun F => 𝓕 F s) (hc _ (PAG.Part109.eps_idem K a haK))
      simp only [PAG.Part16.dft_conv, Pi.mul_apply, _root_.map_smul, Pi.smul_apply, smul_eq_mul, h1, mul_one] at this
      rw [dft_cpow] at this
      exact this
    exact hneq ((hval t ht).trans (hval t' ht').symm)
  · intro ho
    obtain ⟨t₀, ht₀⟩ := Tset_nonempty K w n h χ hχ
    refine ⟨𝓕 k t₀ ^ (m + 1), fun f hf => ?_⟩
    apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
    funext t
    rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_cpow, _root_.map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases ht : t ∈ Tset (p := p) K a
    · rw [PAG.Part98.pow_eigen_const K w (n + 1) h (by omega) χ hχ m ho t t₀ ht ht₀]
    · have h0 : 𝓕 (eps (p := p) K a) t = 0 := by
        rcases PAG.Part31.dft_eps_zero_or_one K a haK t with h0 | h1
        · exact h0
        · exact absurd (by simpa [Tset] using h1) ht
      have hft : 𝓕 f t = 0 := by
        have := congrArg (fun F => 𝓕 F t) hf
        simp only [PAG.Part16.dft_conv, Pi.mul_apply, h0, zero_mul] at this
        exact this.symm
      rw [hft, mul_zero, mul_zero]

/-- V_a 上で k^{⋆m} は単射（λ^m > 0 倍の等長）。 -/
theorem cpow_inj (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (m : ℕ) (f : ZMod (p ^ K) → ℂ) (hf : conv (eps (p := p) K (K - (n + 1) - w)) f = f)
    (h0 : conv (cpow (ket K w (n + 1) h χ) m) f = 0) : f = 0 := by
  have hiso := isoOn_cpow _ _ _ (PAG.Part109.isoOn_ket K w n h χ hχ) m f hf
  rw [h0] at hiso
  simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero] at hiso
  have hl : (0 : ℝ) < ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) ^ m := by
    apply pow_pos
    apply div_pos (pow_pos (by exact_mod_cast hp.out.pos) _)
    have : 0 < sz p K (K - (n + 1) - w) := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    exact_mod_cast this
  have hs : ∑ x, Complex.normSq (f x) = 0 := by
    rcases mul_eq_zero.mp hiso.symm with h' | h'
    · exact absurd h' hl.ne'
    · exact h'
  funext x
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => Complex.normSq_nonneg (f y))).mp hs x (mem_univ x)
  simpa using this

theorem eps_ne_zero (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : eps (p := p) K (K - (n + 1) - w) ≠ 0 := by
  intro h0
  obtain ⟨t, ht⟩ := Tset_nonempty K w n h χ hχ
  have h1 : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 := by simpa [Tset] using ht
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

end Ket

/-! ## 5. 系: 積の巡回構造は lcm -/

section Lcm

open PAG.Part21 PAG.Part59

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **5. (k₁ ⊗ k₂)^{⋆m} が V_{a₁} ⊗ V_{a₂} 上でスカラー ⟺ lcm(ord χ₁, ord χ₂) ∣ m**（m ≥ 1）。 -/
theorem scalar_tens_lcm (K w₁ n₁ L w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (m : ℕ) :
    Scalar (tens (eps (p := p) K (K - (n₁ + 1) - w₁)) (eps (p := q) L (L - (n₂ + 1) - w₂)))
        (cpow (tens (ket K w₁ (n₁ + 1) h₁ χ₁) (ket L w₂ (n₂ + 1) h₂ χ₂)) (m + 1))
      ↔ Nat.lcm (orderOf χ₁) (orderOf χ₂) ∣ m + 1 := by
  rw [cpow_tens, scalar_tens_iff _ _ _ _ (PAG.Part109.eps_idem K _ (by omega)) (PAG.Part109.eps_idem L _ (by omega))
      (fun f hf h0 => cpow_inj K w₁ n₁ h₁ χ₁ hχ₁ (m + 1) f hf h0)
      (fun f hf h0 => cpow_inj L w₂ n₂ h₂ χ₂ hχ₂ (m + 1) f hf h0)
      _ (PAG.Part109.eps_idem K _ (by omega)) (eps_ne_zero K w₁ n₁ h₁ χ₁ hχ₁)
      _ (PAG.Part109.eps_idem L _ (by omega)) (eps_ne_zero L w₂ n₂ h₂ χ₂ hχ₂),
    scalar_cpow_iff K w₁ n₁ h₁ χ₁ hχ₁, scalar_cpow_iff L w₂ n₂ h₂ χ₂ hχ₂, Nat.lcm_dvd_iff, orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

end Lcm

end PAG.Part111

#print axioms PAG.Part111.conv_smul_gen
#print axioms PAG.Part111.conv_single_gen
#print axioms PAG.Part111.cpow_tens
#print axioms PAG.Part111.fix_conv
#print axioms PAG.Part111.isoOn_cpow
#print axioms PAG.Part111.scalar_tens_iff
#print axioms PAG.Part111.dft_cpow
#print axioms PAG.Part111.Tset_nonempty
#print axioms PAG.Part111.scalar_cpow_iff
#print axioms PAG.Part111.cpow_inj
#print axioms PAG.Part111.eps_ne_zero
#print axioms PAG.Part111.scalar_tens_lcm
