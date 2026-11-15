/-
  PAG 2.0 Part 138（2026-10-22）— 野性部分の周波数: 原始性と停留点の明示
  P = p^k（k < c ≤ 2k）。χ の周波数 δ_χ: ∀ y, χ(1 + P y) = e(P δ_χ y)
  1. 周波数は積で足される: δ_{χψ} = δ_χ + δ_ψ
  2. u ∈ S_P(χ) ↔ P (u + δ_χ) = 0（停留集合は −δ_χ + Ann(P)）
  3. 停留点は u₀ ≡ −δ_χ (mod p)
  4. χ 原始 ↔ δ_χ 単元
  5. χψ 原始 ↔ δ_χ + δ_ψ 単元
-/
import PAG141

namespace PAG.Part142

open ZMod Finset PAG.Part120

variable {p : ℕ} [hp : Fact p.Prime]

section Freq

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

/-- **1. 周波数の加法性**。 -/
theorem freq_mul (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ₁ δ₂ : ZMod (p ^ c))
    (h₁ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₁ * y))
    (h₂ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₂ * y)) :
    ∀ y, (χ * ψ) (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * (δ₁ + δ₂) * y) := by
  intro y
  rw [MulChar.mul_apply, h₁, h₂, ← AddChar.map_add_eq_mul]
  congr 1; ring

/-- **2. 停留集合の明示**。 -/
theorem mem_SP_iff_freq (χ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) (u : ZMod (p ^ c)) :
    (∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u * y) = 1) ↔
      (p : ZMod (p ^ c)) ^ k * (u + δ) = 0 := by
  have key : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u * y)
      = stdAddChar ((p : ZMod (p ^ c)) ^ k * (u + δ) * y) := by
    intro y; simp only [phiP, hδ]; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp only [key]
  constructor
  · intro h
    have h1 := h 1; rw [mul_one] at h1
    exact ZMod.injective_stdAddChar (h1.trans (AddChar.map_zero_eq_one _).symm)
  · intro h y; rw [h, zero_mul, AddChar.map_zero_eq_one]

include hkc in
/-- **3. 停留点は u₀ ≡ −δ (mod p)**。 -/
theorem stationary_cast (χ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) (u₀ : ZMod (p ^ c))
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1) :
    ((u₀ : ZMod (p ^ c)).cast : ZMod p) = ((-δ : ZMod (p ^ c)).cast : ZMod p) := by
  apply PAG.Part139.cast_eq_of_P (p := p) hkc
  have := (mem_SP_iff_freq χ δ hδ u₀).mp hS₀
  linear_combination this

include hkc h2k in
/-- **4. χ 原始 ↔ δ_χ 単元**。 -/
theorem primitive_iff_freq (χ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) :
    χ.IsPrimitive ↔ IsUnit δ := by
  have hP : (p : ZMod (p ^ c)) ^ k * (p : ZMod (p ^ c)) ^ k = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  have hS₀ : ∀ y, phiP (1 : DirichletCharacter ℂ (p ^ c)) ((p : ZMod (p ^ c)) ^ k) y
      * stdAddChar ((p : ZMod (p ^ c)) ^ k * 0 * y) = 1 := by
    intro y
    simp only [phiP, mul_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.one_apply (one_add_unit _ hP y)
  have h := PAG.Part141.primitive_iff_unit hkc h2k 1 χ δ hδ 0 hS₀
  rw [one_mul, zero_sub, IsUnit.neg_iff] at h
  exact h

include hkc h2k in
/-- **5. χψ 原始 ↔ δ_χ + δ_ψ 単元**。 -/
theorem primitive_mul_iff (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ₁ δ₂ : ZMod (p ^ c))
    (h₁ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₁ * y))
    (h₂ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₂ * y)) :
    (χ * ψ).IsPrimitive ↔ IsUnit (δ₁ + δ₂) :=
  primitive_iff_freq hkc h2k (χ * ψ) (δ₁ + δ₂) (freq_mul χ ψ δ₁ δ₂ h₁ h₂)

end Freq

end PAG.Part142

#print axioms PAG.Part142.freq_mul
#print axioms PAG.Part142.mem_SP_iff_freq
#print axioms PAG.Part142.stationary_cast
#print axioms PAG.Part142.primitive_iff_freq
#print axioms PAG.Part142.primitive_mul_iff
