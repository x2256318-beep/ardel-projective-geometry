/-
  PAG 2.0 Part 60（2026-10-19）— 導手による統一的な分類（任意の素数 p）
  同じ殻 w・同じ導手 p^(n+1) の原始ケットの組について、積 χ₁χ₂ の導手を p^i とすると
  (B) i = 0：conv = χ₁(−1)·ballB
  (A) i ≥ 1：conv = C·|w + (n+1−i), ψ⟩、ψ は導手 p^i の原始指標、|C|² = λ
  すなわち「降下量 = (n+1) − log_p cond(χ₁χ₂)」。p = 2（PAG53）と奇素数（PAG63）はこの系であり、
  違いは cond(χ₁χ₂) の公式（ν₂(j+j') と s+s'、または ν_p(j+j') と φ）だけにある。
-/
import PAG63

namespace PAG.Part64

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part47 PAG.Part48 PAG.Part50

variable {p : ℕ} [hp : Fact p.Prime]

/-- **導手による統一的な分類**。 -/
theorem unified_classification (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (i : ℕ) (hi : (χ₁ * χ₂).conductor = p ^ i) :
    (i = 0 ∧ conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = χ₁ (-1) • ballB (p := p) K w n) ∨
    (1 ≤ i ∧ i ≤ n + 1 ∧ ∃ h : w + (n + 1 - i) + i ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ i), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = C • ket K (w + (n + 1 - i)) i h ψ) := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hin : i ≤ n + 1 := by
    have hd := DirichletCharacter.conductor_dvd_level (χ₁ * χ₂)
    rw [hi] at hd
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hd
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · left
    subst h0
    refine ⟨rfl, ?_⟩
    have h1 : χ₁ * χ₂ = 1 := by
      rw [DirichletCharacter.eq_one_iff_conductor_eq_one, hi, pow_zero]
    exact thmB_of_mul_eq_one K w n hK χ₁ χ₂ h₁ h1
  · right
    refine ⟨hpos, hin, by omega, ?_⟩
    exact thmA_of_conductor K w n (w + (n + 1 - i)) i hK hpos hin (by omega) (by omega) χ₁ χ₂ h₁ h₂ hi

/-- 導手は必ず p の冪（統一分類の前提はいつも満たされる）。 -/
theorem exists_conductor_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ∃ i, χ.conductor = p ^ i :=
  let ⟨i, _, h⟩ := conductor_eq_pow χ
  ⟨i, h⟩

/-- 系（p = 2）: ν₂(j+j') = d+3−m（3 ≤ m）なら積の導手は 2^m、降下量は d+3−m。 -/
theorem p2_instance {d : ℕ} (s j s' j' : ℕ) {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3)
    (hν : 2 ^ (d + 3 - m) ∣ (j + j') ∧ ¬ 2 ^ (d + 4 - m) ∣ (j + j')) :
    (PAG.Part44.chiSJ d s j * PAG.Part44.chiSJ d s' j').conductor = 2 ^ m :=
  (PAG.Part44.chiSJ_mul_conductor_iff s j s' j' hm3 hm).mpr hν

/-- 系（奇素数）: ν_p(j+j') = n−m（2 ≤ m）なら積の導手は p^m、降下量は n−m。 -/
theorem odd_instance (c : ℕ) (hp2 : p ≠ 2) {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ c + 1) (j j' : ℕ)
    (hν : p ^ (c + 1 - m) ∣ (j + j') ∧ ¬ p ^ (c + 1 - m + 1) ∣ (j + j')) :
    (PAG.Part61.omega c hp2 ^ j * PAG.Part61.omega c hp2 ^ j').conductor = p ^ m :=
  (PAG.Part62.omega_mul_conductor_iff c hp2 m hm2 hm j j').mpr hν

end PAG.Part64

#print axioms PAG.Part64.unified_classification
#print axioms PAG.Part64.exists_conductor_pow
#print axioms PAG.Part64.p2_instance
#print axioms PAG.Part64.odd_instance
