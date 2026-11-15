/-
  PAG 2.0 Part 135（2026-10-22）— ひねり公式をすべての導手 p^c（c ≥ 2）へ
  P = p^k（1 ≤ k < c ≤ 2k）について
  1. P u = P u₀ ⇒ u ≡ u₀ (mod p)
  2. ψ = 法 p の指標 ψ₀ の持ち上げ、u₀ ∈ S_P 単元 ⇒ τ(χψ) = ψ(u₀) τ(χ)
  3. χ 原始なら S_P に単元がある
  4. 統一形（c ≥ 2、偶奇を問わない）: ∃ u₀ 単元、∀ ψ₀, τ(χ·ψ₀↑) = ψ₀↑(u₀) τ(χ)
-/
import PAG138

namespace PAG.Part139

open ZMod Finset PAG.Part120

variable {p : ℕ} [hp : Fact p.Prime]

section Gen

variable {c k : ℕ} (hk1 : 1 ≤ k) (hkc : k < c) (h2k : c ≤ 2 * k)

include hkc in
/-- **1. P u = P u₀ ⇒ u ≡ u₀ (mod p)**。 -/
theorem cast_eq_of_P (u u₀ : ZMod (p ^ c)) (h : (p : ZMod (p ^ c)) ^ k * u = (p : ZMod (p ^ c)) ^ k * u₀) :
    ((u : ZMod (p ^ c)).cast : ZMod p) = (u₀.cast : ZMod p) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpc : p ∣ p ^ c := dvd_pow_self p (by omega)
  set w := u - u₀
  have hw : (p : ZMod (p ^ c)) ^ k * w = 0 := by simp only [w]; rw [mul_sub, h, sub_self]
  rw [← ZMod.natCast_zmod_val w, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hw
  have hsplit : p ^ k * p ^ (c - k) = p ^ c := by rw [← pow_add]; congr 1; omega
  have h1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos k) ((dvd_of_eq hsplit).trans hw)
  have h2 : p ∣ w.val := (dvd_pow_self p (by omega)).trans h1
  have h3 : ((w.cast : ZMod p)) = 0 := by
    rw [ZMod.cast_eq_val]; exact (ZMod.natCast_eq_zero_iff _ _).mpr h2
  simp only [w] at h3
  rw [ZMod.cast_sub hpc] at h3
  exact sub_eq_zero.mp h3

include hk1 hkc h2k in
/-- **2. 一般のひねり公式**。 -/
theorem gauss_twist_gen (χ : DirichletCharacter ℂ (p ^ c)) (ψ₀ : DirichletCharacter ℂ p) (hpc : p ∣ p ^ c)
    (u₀ : ZMod (p ^ c)) (hu₀ : IsUnit u₀)
    (hS₀ : ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1) :
    gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar
      = DirichletCharacter.changeLevel hpc ψ₀ u₀ * gaussSum χ stdAddChar := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P : ZMod (p ^ c) := (p : ZMod (p ^ c)) ^ k
  set ψ := DirichletCharacter.changeLevel hpc ψ₀
  have hP : P * P = 0 := by
    simp only [P]; rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  have hψ1 : ∀ y, ψ (1 + P * y) = 1 := by
    intro y
    have hu := one_add_unit P hP y
    have e := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hpc hu.unit
    rw [IsUnit.unit_spec] at e
    simp only [ψ]
    rw [e, ZMod.cast_add hpc, ZMod.cast_one hpc, ZMod.cast_mul hpc]
    simp only [P]
    rw [ZMod.cast_pow hpc, ZMod.cast_natCast hpc, ZMod.natCast_self, zero_pow (by omega), zero_mul, add_zero,
      map_one]
  have hphi : ∀ y, phiP (χ * ψ) P y = phiP χ P y := by
    intro y; simp only [phiP, MulChar.mul_apply, hψ1, mul_one]
  rw [gauss_eq_sum_SP (χ * ψ) P hP, gauss_eq_sum_SP χ P hP]
  simp only [hphi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hS := (Finset.mem_filter.mp hu).2
  rw [MulChar.mul_apply]
  by_cases hun : IsUnit u
  · have hPu : P * u = P * u₀ := by
      have h1 := hS 1; have h2 := hS₀ 1
      rw [mul_one] at h1 h2
      have hφ : phiP χ P 1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
      exact ZMod.injective_stdAddChar (mul_left_cancel₀ hφ (h1.trans h2.symm))
    have hc := cast_eq_of_P (p := p) hkc u u₀ hPu
    have e1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hpc hun.unit
    have e2 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ₀ hpc hu₀.unit
    rw [IsUnit.unit_spec] at e1 e2
    have : ψ u = ψ u₀ := by simp only [ψ]; rw [e1, e2, hc]
    rw [this]; ring
  · rw [MulChar.map_nonunit χ hun]; ring

include h2k in
/-- **3. χ 原始なら S_P に単元がある**。 -/
theorem exists_unit_SP (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧
      ∀ y, phiP χ ((p : ZMod (p ^ c)) ^ k) y * stdAddChar ((p : ZMod (p ^ c)) ^ k * u₀ * y) = 1 := by
  classical
  have hP : (p : ZMod (p ^ c)) ^ k * (p : ZMod (p ^ c)) ^ k = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  have hτ := gauss_eq_sum_SP χ _ hP
  have hτ0 := PAG.Part16.gaussSum_ne_zero hχ
  rw [hτ] at hτ0
  obtain ⟨u₀, hu₀S, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ0
  have hχu₀ : χ u₀ ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
  exact ⟨u₀, by by_contra hn; exact hχu₀ (MulChar.map_nonunit χ hn), (Finset.mem_filter.mp hu₀S).2⟩

end Gen

/-- **4. 統一形**（c ≥ 2）: u₀ は ψ₀ によらない。 -/
theorem gauss_twist_all (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive)
    (hpc : p ∣ p ^ c) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∀ ψ₀ : DirichletCharacter ℂ p,
      gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar
        = DirichletCharacter.changeLevel hpc ψ₀ u₀ * gaussSum χ stdAddChar := by
  obtain ⟨u₀, hu, hS⟩ := exists_unit_SP (p := p) (k := (c + 1) / 2) (by omega) χ hχ
  exact ⟨u₀, hu, fun ψ₀ => gauss_twist_gen (by omega) (by omega) (by omega) χ ψ₀ hpc u₀ hu hS⟩

end PAG.Part139

#print axioms PAG.Part139.cast_eq_of_P
#print axioms PAG.Part139.gauss_twist_gen
#print axioms PAG.Part139.exists_unit_SP
#print axioms PAG.Part139.gauss_twist_all
