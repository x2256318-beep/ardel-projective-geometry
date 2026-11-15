/-
  PAG 2.0 Part 29（2026-10-19）— 積の導手分布の数え上げ（一般の素数、p = 2 を含む）
  法 p^(c+1)（c ≥ 1）、χ₁ を原始指標とする。
  1. {ψ | ψ が法 d を経由} ≃ (法 d の指標)、個数 φ(d)
  2. 原始指標の個数 = φ(p^(c+1)) − φ(p^c)
  3. χ₂ ↦ χ₁χ₂ により {χ₂ 原始 | χ₁χ₂ が法 p^m を経由} ≃ {ψ | ψ が法 p^m を経由}（m ≤ c）、個数 φ(p^m)
  4. 積が原始的な χ₂ の個数 = φ(p^(c+1)) − 2φ(p^c)、積の導手がちょうど p^m の個数 = φ(p^m) − φ(p^(m−1))
  （p = 2 では φ(2^(c+1)) = 2φ(2^c) より原始的な積は 0、φ(2) − φ(1) = 0 より導手 2 は 0）
-/
import PAG32

namespace PAG.Part33

open ZMod Finset PAG.Part32

open Classical

/-! ## 1. 法 d を経由する指標の個数 -/

section Factor

variable {N : ℕ} [NeZero N]

/-- 法 d の指標 → 法 N を経由する指標（changeLevel）は全単射。 -/
noncomputable def factorsEquiv {d : ℕ} [NeZero d] (hd : d ∣ N) :
    DirichletCharacter ℂ d ≃ {ψ : DirichletCharacter ℂ N // ψ.FactorsThrough d} :=
  Equiv.ofBijective (fun χ₀ => ⟨DirichletCharacter.changeLevel hd χ₀, ⟨hd, χ₀, rfl⟩⟩)
    ⟨fun a b h => DirichletCharacter.changeLevel_injective hd (congrArg Subtype.val h),
     fun ⟨ψ, hψ⟩ => by
       obtain ⟨h', χ₀, e⟩ := hψ
       exact ⟨χ₀, Subtype.ext e.symm⟩⟩

theorem card_chars (N : ℕ) [NeZero N] : Fintype.card (DirichletCharacter ℂ N) = N.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ N

/-- **法 d を経由する指標は φ(d) 個**。 -/
theorem card_factors {d : ℕ} [NeZero d] (hd : d ∣ N) :
    Fintype.card {ψ : DirichletCharacter ℂ N // ψ.FactorsThrough d} = d.totient := by
  rw [← Fintype.card_congr (factorsEquiv hd), card_chars]

end Factor

/-! ## 2. 原始指標と積の数え上げ -/

section Count

variable {p : ℕ} [hp : Fact p.Prime] {c : ℕ}

instance (k : ℕ) : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- **原始指標の個数** = φ(p^(c+1)) − φ(p^c)。 -/
theorem card_prim (hc : 1 ≤ c) :
    Fintype.card {χ : DirichletCharacter ℂ (p ^ (c + 1)) // χ.IsPrimitive}
      = (p ^ (c + 1)).totient - (p ^ c).totient := by
  have h1 : Fintype.card {χ : DirichletCharacter ℂ (p ^ (c + 1)) // ¬ χ.IsPrimitive} = (p ^ c).totient := by
    rw [← card_factors (N := p ^ (c + 1)) (pow_dvd_pow p (Nat.le_succ c))]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => not_prim_iff_factors hc χ))
  have h2 := Fintype.card_subtype_compl (fun χ : DirichletCharacter ℂ (p ^ (c + 1)) => χ.IsPrimitive)
  have h3 := Fintype.card_subtype_le (fun χ : DirichletCharacter ℂ (p ^ (c + 1)) => χ.IsPrimitive)
  rw [card_chars] at h2 h3
  omega

/-- 法 p^m（m ≤ c）を経由する ψ について χ₁⁻¹ψ は原始的（χ₁ 原始的）。 -/
theorem inv_mul_prim (hc : 1 ≤ c) {m : ℕ} (hm : m ≤ c) (χ₁ ψ : DirichletCharacter ℂ (p ^ (c + 1)))
    (h₁ : χ₁.IsPrimitive) (hψ : ψ.FactorsThrough (p ^ m)) : (χ₁⁻¹ * ψ).IsPrimitive := by
  have hψc : ψ.FactorsThrough (p ^ c) :=
    DirichletCharacter.FactorsThrough.mono ψ hψ (pow_dvd_pow p hm) (pow_dvd_pow p (Nat.le_succ c))
  have hg := (factors_iff_gp hc ψ).mp hψc
  have hg1 := (prim_iff_gp hc χ₁).mp h₁
  rw [prim_iff_gp hc, MulChar.coeToFun_mul, Pi.mul_apply, hg, mul_one, MulChar.inv_apply_eq_inv']
  intro h
  exact hg1 (inv_eq_one.mp h)

/-- **ずらしの全単射**: {χ₂ 原始 | χ₁χ₂ が法 p^m を経由} ≃ {ψ | ψ が法 p^m を経由}（m ≤ c）。 -/
noncomputable def shiftEquiv (hc : 1 ≤ c) {m : ℕ} (hm : m ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1)))
    (h₁ : χ₁.IsPrimitive) :
    {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ m)}
      ≃ {ψ : DirichletCharacter ℂ (p ^ (c + 1)) // ψ.FactorsThrough (p ^ m)} where
  toFun χ₂ := ⟨χ₁ * χ₂.1, χ₂.2.2⟩
  invFun ψ := ⟨χ₁⁻¹ * ψ.1, inv_mul_prim hc hm χ₁ ψ.1 h₁ ψ.2, by rw [mul_inv_cancel_left]; exact ψ.2⟩
  left_inv χ₂ := Subtype.ext (inv_mul_cancel_left χ₁ χ₂.1)
  right_inv ψ := Subtype.ext (mul_inv_cancel_left χ₁ ψ.1)

/-- **積が法 p^m を経由する原始 χ₂ は φ(p^m) 個**（m ≤ c、χ₁ によらない）。 -/
theorem card_mul_factors (hc : 1 ≤ c) {m : ℕ} (hm : m ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1)))
    (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ m)}
      = (p ^ m).totient := by
  rw [Fintype.card_congr (shiftEquiv hc hm χ₁ h₁), card_factors (pow_dvd_pow p (by omega))]

/-- 部分集合の数え上げ: #{P ∧ Q} + #{P ∧ ¬Q} = #{P}。 -/
theorem card_split {α : Type*} [Fintype α] (P Q : α → Prop) :
    Fintype.card {x // P x ∧ Q x} + Fintype.card {x // P x ∧ ¬ Q x} = Fintype.card {x // P x} := by
  simp only [Fintype.card_subtype]
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.card_filter_add_card_filter_not _

/-- **積が非原始な原始 χ₂ は φ(p^c) 個**。 -/
theorem card_mul_not_prim (hc : 1 ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1))) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ ¬ (χ₁ * χ₂).IsPrimitive}
      = (p ^ c).totient := by
  rw [← card_mul_factors hc le_rfl χ₁ h₁]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun χ₂ => and_congr_right (fun _ => not_prim_iff_factors hc _)))

/-- **積が原始的な原始 χ₂ は φ(p^(c+1)) − 2φ(p^c) 個**。 -/
theorem card_mul_prim (hc : 1 ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1))) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).IsPrimitive}
      = (p ^ (c + 1)).totient - (p ^ c).totient - (p ^ c).totient := by
  have h := card_split (fun χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) => χ₂.IsPrimitive) (fun χ₂ => (χ₁ * χ₂).IsPrimitive)
  rw [card_mul_not_prim hc χ₁ h₁, card_prim hc] at h
  omega

/-- 素数冪の導手: conductor = p^m ⇔ 法 p^m を経由し法 p^(m−1) を経由しない（1 ≤ m ≤ c+1）。 -/
theorem conductor_eq_iff {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ c + 1) (ψ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ψ.conductor = p ^ m ↔ ψ.FactorsThrough (p ^ m) ∧ ¬ ψ.FactorsThrough (p ^ (m - 1)) := by
  have hdm : ∀ k, k ≤ c + 1 → (ψ.FactorsThrough (p ^ k) ↔ ψ.conductor ∣ p ^ k) := fun k hk =>
    (DirichletCharacter.mem_conductorSet_iff _).symm.trans
      (DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ (pow_dvd_pow p hk))
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp.out).mp ψ.conductor_dvd_level
  rw [hdm m hm, hdm (m - 1) (by omega), he, Nat.pow_dvd_pow_iff_le_right hp.out.one_lt,
    Nat.pow_dvd_pow_iff_le_right hp.out.one_lt, Nat.pow_right_inj hp.out.one_lt]
  omega

/-- **導手がちょうど p^m の積は φ(p^m) − φ(p^(m−1)) 個**（1 ≤ m ≤ c）。 -/
theorem card_mul_conductor (hc : 1 ≤ c) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ c)
    (χ₁ : DirichletCharacter ℂ (p ^ (c + 1))) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).conductor = p ^ m}
      = (p ^ m).totient - (p ^ (m - 1)).totient := by
  have hsub : ∀ ψ : DirichletCharacter ℂ (p ^ (c + 1)), ψ.FactorsThrough (p ^ (m - 1)) → ψ.FactorsThrough (p ^ m) :=
    fun ψ h => DirichletCharacter.FactorsThrough.mono ψ h (pow_dvd_pow p (by omega)) (pow_dvd_pow p (by omega))
  have h := card_split (fun χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) => χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ m))
    (fun χ₂ => (χ₁ * χ₂).FactorsThrough (p ^ (m - 1)))
  have e1 : Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) //
      (χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ m)) ∧ (χ₁ * χ₂).FactorsThrough (p ^ (m - 1))}
      = (p ^ (m - 1)).totient := by
    rw [← card_mul_factors hc (m := m - 1) (by omega) χ₁ h₁]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun χ₂ =>
      ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hsub _ h.2⟩, h.2⟩⟩))
  have e2 : Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) //
      (χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ m)) ∧ ¬ (χ₁ * χ₂).FactorsThrough (p ^ (m - 1))}
      = Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).conductor = p ^ m} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun χ₂ => by
      rw [conductor_eq_iff hm1 (by omega)]; tauto))
  have h' : (p ^ (m - 1)).totient
      + Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).conductor = p ^ m}
      = (p ^ m).totient := by
    rw [← e1, ← e2, ← card_mul_factors hc hm χ₁ h₁]
    convert h
  omega

/-- 導手 1 の積（χ₂ = χ₁⁻¹）はちょうど 1 個。 -/
theorem card_mul_trivial (hc : 1 ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1))) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).FactorsThrough (p ^ 0)} = 1 := by
  rw [card_mul_factors hc (Nat.zero_le c) χ₁ h₁, pow_zero, Nat.totient_one]

/-- φ(p^(c+1)) = p·φ(p^c)（c ≥ 1）。 -/
theorem totient_succ (hc : 1 ≤ c) : (p ^ (c + 1)).totient = p * (p ^ c).totient := by
  rw [Nat.totient_prime_pow hp.out (by omega), Nat.totient_prime_pow hp.out (by omega),
    show c + 1 - 1 = (c - 1) + 1 by omega, pow_succ]
  ring

/-- **原始的な積の割合**: #{積が原始的} · (p − 1) = #{原始的} · (p − 2)（χ₁ によらない）。 -/
theorem ratio_mul_prim (hc : 1 ≤ c) (χ₁ : DirichletCharacter ℂ (p ^ (c + 1))) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ (p ^ (c + 1)) // χ₂.IsPrimitive ∧ (χ₁ * χ₂).IsPrimitive} * (p - 1)
      = Fintype.card {χ : DirichletCharacter ℂ (p ^ (c + 1)) // χ.IsPrimitive} * (p - 2) := by
  rw [card_mul_prim hc χ₁ h₁, card_prim hc, totient_succ hc]
  generalize (p ^ c).totient = t
  rw [Nat.sub_sub, ← two_mul, ← Nat.sub_mul, ← Nat.sub_one_mul]
  ring

end Count

end PAG.Part33

#print axioms PAG.Part33.factorsEquiv
#print axioms PAG.Part33.card_chars
#print axioms PAG.Part33.card_factors
#print axioms PAG.Part33.card_prim
#print axioms PAG.Part33.inv_mul_prim
#print axioms PAG.Part33.shiftEquiv
#print axioms PAG.Part33.card_mul_factors
#print axioms PAG.Part33.card_split
#print axioms PAG.Part33.card_mul_not_prim
#print axioms PAG.Part33.card_mul_prim
#print axioms PAG.Part33.conductor_eq_iff
#print axioms PAG.Part33.card_mul_conductor
#print axioms PAG.Part33.card_mul_trivial
#print axioms PAG.Part33.totient_succ
#print axioms PAG.Part33.ratio_mul_prim
