/-
  PAG 2.0 Part 119（2026-10-20）— 一様分布の積: Unif は直積で lcm に閉じる
  1. Unif T₁ F₁ t₁ o₁、Unif T₂ F₂ t₂ o₂ ⇒ Unif (T₁ × T₂) (F₁ F₂) (t₁, t₂) (lcm o₁ o₂)
  2. 系: 積のケットのスペクトル {𝓕k₁(s)𝓕k₂(t)} は z₁z₂ μ_ℓ に一様（Part 118 の閉じた形の別証明の素材）
  3. 系: 三つの因子でも Unif（lcm(lcm o₁ o₂) o₃）
-/
import PAG122

namespace PAG.Part123

open ZMod Finset Polynomial PAG.Part122

section Mul

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq β] in
/-- **1. 一様分布の積**。 -/
theorem unif_mul {T₁ : Finset α} {T₂ : Finset β} {F₁ : α → ℂ} {F₂ : β → ℂ} {t₁ : α} {t₂ : β} {o₁ o₂ : ℕ}
    (h₁ : Unif T₁ F₁ t₁ o₁) (h₂ : Unif T₂ F₂ t₂ o₂) :
    Unif (T₁ ×ˢ T₂) (fun z => F₁ z.1 * F₂ z.2) (t₁, t₂) (Nat.lcm o₁ o₂) := by
  classical
  have hu1 := h₁; have hu2 := h₂
  obtain ⟨h0₁, ho₁, hF₁, hpow₁, hfib₁⟩ := h₁
  obtain ⟨h0₂, ho₂, hF₂, hpow₂, hfib₂⟩ := h₂
  set ℓ := Nat.lcm o₁ o₂
  have hℓ : 0 < ℓ := Nat.lcm_pos ho₁ ho₂
  obtain ⟨k₁, hk₁⟩ := Nat.dvd_lcm_left o₁ o₂
  obtain ⟨k₂, hk₂⟩ := Nat.dvd_lcm_right o₁ o₂
  refine ⟨Finset.mem_product.mpr ⟨h0₁, h0₂⟩, hℓ, mul_ne_zero hF₁ hF₂, fun z hz => ?_, fun ξ hξ => ?_⟩
  · obtain ⟨hs, ht⟩ := Finset.mem_product.mp hz
    simp only
    rw [mul_div_mul_comm, mul_pow, show ℓ = o₁ * k₁ from hk₁, pow_mul, hpow₁ _ hs, one_pow, one_mul,
      ← show ℓ = o₁ * k₁ from hk₁, show ℓ = o₂ * k₂ from hk₂, pow_mul, hpow₂ _ ht, one_pow]
  -- ファイバー
  simp only
  set g := Nat.gcd o₁ o₂
  set o' := o₁ / g
  have hl : o₂ * o' = ℓ := by
    simp only [o', g, ℓ, Nat.lcm]
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left o₁ o₂), mul_comm]
  -- 各 s で t の数
  have hinner : ∀ s ∈ T₁, (T₂.filter (fun t => F₁ s * F₂ t = F₁ t₁ * F₂ t₂ * ξ)).card
      = if F₁ s ^ o₂ = F₁ t₁ ^ o₂ * ξ ^ o₂ then T₂.card / o₂ else 0 := by
    intro s hs
    have hFs : F₁ s ≠ 0 := unif_ne_zero hu1 s hs
    set η := ξ * F₁ t₁ / F₁ s
    have hiff : ∀ t, (F₁ s * F₂ t = F₁ t₁ * F₂ t₂ * ξ ↔ F₂ t = F₂ t₂ * η) := by
      intro t
      simp only [η]
      constructor
      · intro e; field_simp; linear_combination e
      · intro e; rw [e]; field_simp
    rw [Finset.filter_congr (fun t _ => hiff t)]
    have hηiff : η ^ o₂ = 1 ↔ F₁ s ^ o₂ = F₁ t₁ ^ o₂ * ξ ^ o₂ := by
      simp only [η]
      rw [div_pow, mul_pow, div_eq_one_iff_eq (pow_ne_zero _ hFs)]
      constructor <;> intro e <;> linear_combination -e
    split_ifs with hc
    · have := hfib₂ η (hηiff.mpr hc)
      rw [← this, Nat.mul_div_cancel_left _ ho₂]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro t ht e
      apply hc
      apply hηiff.mp
      have := hpow₂ t ht
      rw [e, mul_div_cancel_left₀ _ hF₂] at this
      exact this
  -- 合計
  have hcount : ((T₁ ×ˢ T₂).filter (fun z => F₁ z.1 * F₂ z.2 = F₁ t₁ * F₂ t₂ * ξ)).card
      = (T₁.filter (fun s => F₁ s ^ o₂ = F₁ t₁ ^ o₂ * ξ ^ o₂)).card * (T₂.card / o₂) := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [← Finset.card_filter]
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hP := unif_pow hu1 o₂
  have hξ' : (ξ ^ o₂) ^ o' = 1 := by rw [← pow_mul, hl, hξ]
  have hfibP := hP.2.2.2.2 (ξ ^ o₂) hξ'
  simp only at hfibP
  rw [hcount, Finset.card_product, ← hl]
  have h1 : o' ∣ T₁.card := dvd_card hP
  have h2 : o₂ ∣ T₂.card := dvd_card hu2
  calc o₂ * o' * ((T₁.filter (fun s => F₁ s ^ o₂ = F₁ t₁ ^ o₂ * ξ ^ o₂)).card * (T₂.card / o₂))
      = (o' * (T₁.filter (fun s => F₁ s ^ o₂ = F₁ t₁ ^ o₂ * ξ ^ o₂)).card) * (o₂ * (T₂.card / o₂)) := by ring
    _ = T₁.card * T₂.card := by rw [hfibP, Nat.mul_div_cancel' h2]

end Mul

/-! ## 2. 積のケットのスペクトル -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95

variable {p q r : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] [hr : Fact r.Prime]

theorem ket_spec_unif (K L w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (t₁ : ZMod (p ^ K)) (ht₁ : t₁ ∈ Tset (p := p) K (K - (c₁ + 1) - w₁))
    (t₂ : ZMod (q ^ L)) (ht₂ : t₂ ∈ Tset (p := q) L (L - (c₂ + 1) - w₂)) :
    Unif (Tset (p := p) K (K - (c₁ + 1) - w₁) ×ˢ Tset (p := q) L (L - (c₂ + 1) - w₂))
      (fun z => 𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) z.1 * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) z.2) (t₁, t₂)
      (Nat.lcm (orderOf χ₁) (orderOf χ₂)) :=
  unif_mul (ket_unif K w₁ c₁ h₁ χ₁ hχ₁ t₁ ht₁) (ket_unif L w₂ c₂ h₂ χ₂ hχ₂ t₂ ht₂)

/-- **3. 三つの因子**。 -/
theorem ket_spec_unif3 (K L M w₁ c₁ w₂ c₂ w₃ c₃ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (h₃ : w₃ + (c₃ + 1) ≤ M)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (χ₃ : DirichletCharacter ℂ (r ^ (c₃ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hχ₃ : χ₃.IsPrimitive)
    (t₁ : ZMod (p ^ K)) (ht₁ : t₁ ∈ Tset (p := p) K (K - (c₁ + 1) - w₁))
    (t₂ : ZMod (q ^ L)) (ht₂ : t₂ ∈ Tset (p := q) L (L - (c₂ + 1) - w₂))
    (t₃ : ZMod (r ^ M)) (ht₃ : t₃ ∈ Tset (p := r) M (M - (c₃ + 1) - w₃)) :
    Unif ((Tset (p := p) K (K - (c₁ + 1) - w₁) ×ˢ Tset (p := q) L (L - (c₂ + 1) - w₂)) ×ˢ
        Tset (p := r) M (M - (c₃ + 1) - w₃))
      (fun z => 𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) z.1.1 * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) z.1.2
        * 𝓕 (ket M w₃ (c₃ + 1) h₃ χ₃) z.2) ((t₁, t₂), t₃)
      (Nat.lcm (Nat.lcm (orderOf χ₁) (orderOf χ₂)) (orderOf χ₃)) :=
  unif_mul (ket_spec_unif K L w₁ c₁ w₂ c₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ t₁ ht₁ t₂ ht₂) (ket_unif M w₃ c₃ h₃ χ₃ hχ₃ t₃ ht₃)

/-- 系: 積のスペクトルの「根の多項式」の閉じた形（三つの因子）。 -/
theorem spec_poly3 (K L M w₁ c₁ w₂ c₂ w₃ c₃ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (h₃ : w₃ + (c₃ + 1) ≤ M)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (χ₃ : DirichletCharacter ℂ (r ^ (c₃ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hχ₃ : χ₃.IsPrimitive)
    (t₁ : ZMod (p ^ K)) (ht₁ : t₁ ∈ Tset (p := p) K (K - (c₁ + 1) - w₁))
    (t₂ : ZMod (q ^ L)) (ht₂ : t₂ ∈ Tset (p := q) L (L - (c₂ + 1) - w₂))
    (t₃ : ZMod (r ^ M)) (ht₃ : t₃ ∈ Tset (p := r) M (M - (c₃ + 1) - w₃)) :
    ∏ z ∈ (Tset (p := p) K (K - (c₁ + 1) - w₁) ×ˢ Tset (p := q) L (L - (c₂ + 1) - w₂)) ×ˢ
        Tset (p := r) M (M - (c₃ + 1) - w₃),
      (X - C (𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) z.1.1 * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) z.1.2
        * 𝓕 (ket M w₃ (c₃ + 1) h₃ χ₃) z.2))
      = (X ^ Nat.lcm (Nat.lcm (orderOf χ₁) (orderOf χ₂)) (orderOf χ₃)
          - C ((𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) t₁ * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) t₂ * 𝓕 (ket M w₃ (c₃ + 1) h₃ χ₃) t₃)
            ^ Nat.lcm (Nat.lcm (orderOf χ₁) (orderOf χ₂)) (orderOf χ₃)))
        ^ (sz p K (K - (c₁ + 1) - w₁) * sz q L (L - (c₂ + 1) - w₂) * sz r M (M - (c₃ + 1) - w₃)
            / Nat.lcm (Nat.lcm (orderOf χ₁) (orderOf χ₂)) (orderOf χ₃)) := by
  rw [closed_of_unif (ket_spec_unif3 K L M w₁ c₁ w₂ c₂ w₃ c₃ h₁ h₂ h₃ χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ t₁ ht₁ t₂ ht₂ t₃ ht₃),
    Finset.card_product, Finset.card_product, card_Tset K _ _ ⟨w₁, c₁, h₁, χ₁, hχ₁, rfl, rfl⟩,
    card_Tset L _ _ ⟨w₂, c₂, h₂, χ₂, hχ₂, rfl, rfl⟩, card_Tset M _ _ ⟨w₃, c₃, h₃, χ₃, hχ₃, rfl, rfl⟩]

end Ket

end PAG.Part123

#print axioms PAG.Part123.unif_mul
#print axioms PAG.Part123.ket_spec_unif
#print axioms PAG.Part123.ket_spec_unif3
#print axioms PAG.Part123.spec_poly3
