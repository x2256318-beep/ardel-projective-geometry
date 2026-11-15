/-
  PAG 2.0 Part 145（2026-10-22）— 打ち消しの割合の統合定理
  A_ψ = ψ(a) A₀（ψ は法 q の指標、a ∈ (ℤ/q)ˣ）、B 固定、素数 p、E ≥ 1、p ∤ M'
  ∀ ψ, ord(A_ψ B) ∣ p^E M' のとき、N = p^{E−1} M' として
  1. 判定式の一般形: p^E ∣ ord(AB) ↔ (AB)^N ≠ 1（ord(AB) ∣ p^E M' だけを仮定）
  2. 桁の準同型のファイバー: 像の元 x について #{ψ | ψ(a)^N = x} · (ord a / gcd(ord a, N)) = q − 1
  3. 打ち消し（p^E ∤ ord(A_ψ B)）の個数 K は 0 か、K · (ord a / gcd(ord a, N)) = q − 1
-/
import PAG148

namespace PAG.Part149

open ZMod Finset

/-- **1. 判定式の一般形**。 -/
theorem criterion_gen {p : ℕ} [hp : Fact p.Prime] (X : ℂ) (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M')
    (hdvd : orderOf X ∣ p ^ E * M') :
    p ^ E ∣ orderOf X ↔ X ^ (p ^ (E - 1) * M') ≠ 1 := by
  have hM0 : M' ≠ 0 := fun h0 => hM' (h0 ▸ dvd_zero p)
  have hN0 : p ^ E * M' ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hM0
  have ho0 : orderOf X ≠ 0 := fun h0 => hN0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  constructor
  · intro h h1
    have h2 := h.trans (orderOf_dvd_of_pow_eq_one h1)
    have hcop : Nat.Coprime (p ^ E) M' := Nat.Coprime.pow_left E ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hM')
    have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp (hcop.dvd_of_dvd_mul_right h2)
    omega
  · intro h
    by_contra hn
    exact h (orderOf_dvd_iff_pow_eq_one.mp (PAG.Part137.dvd_pred_of_not _ E M' hE ho0 hM' hdvd hn))

variable {q : ℕ} [hq : Fact q.Prime]

/-- **2. 桁の準同型のファイバーの大きさ**。 -/
theorem fiber_digit (a : (ZMod q)ˣ) (N : ℕ) (x : ℂ)
    (hx : x ∈ Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N) :
    #{ψ : DirichletCharacter ℂ q | ψ (a : ZMod q) ^ N = x} * (orderOf a / Nat.gcd (orderOf a) N) = q - 1 := by
  classical
  set D := PAG.Part146.digitHom (a : ZMod q) a.isUnit N
  have hD : ∀ ψ, D ψ = ψ (a : ZMod q) ^ N := fun ψ => rfl
  have htot := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Nat.totient_prime hq.out] at htot
  rw [← htot, Finset.card_eq_sum_card_image D univ]
  have hfib : ∀ y ∈ univ.image D, #{ψ ∈ (univ : Finset (DirichletCharacter ℂ q)) | D ψ = y}
      = #{ψ : DirichletCharacter ℂ q | ψ (a : ZMod q) ^ N = x} := by
    intro y hy
    obtain ⟨ψ₁, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨ψ₂, hψ₂⟩ := hx
    have := MonoidHom.card_fiber_eq_of_mem_range D (x := D ψ₁) (y := x) ⟨ψ₁, rfl⟩ ⟨ψ₂, by rw [hD]; exact hψ₂⟩
    rw [this]; simp only [hD]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  congr 1
  rw [← PAG.Part148.ncard_range_digit a N, ← Set.ncard_coe_finset, Finset.coe_image, Finset.coe_univ,
    Set.image_univ]
  rfl

/-- **3. 打ち消しの個数**。 -/
theorem cancel_count {p : ℕ} [hp : Fact p.Prime] (a : (ZMod q)ˣ) (A₀ B : ℂ) (hAB : A₀ * B ≠ 0)
    (E M' : ℕ) (hE : 1 ≤ E) (hM' : ¬ p ∣ M')
    (hdvd : ∀ ψ : DirichletCharacter ℂ q, orderOf (ψ (a : ZMod q) * A₀ * B) ∣ p ^ E * M') :
    let K := #{ψ : DirichletCharacter ℂ q | ¬ p ^ E ∣ orderOf (ψ (a : ZMod q) * A₀ * B)}
    K = 0 ∨ K * (orderOf a / Nat.gcd (orderOf a) (p ^ (E - 1) * M')) = q - 1 := by
  classical
  intro K
  set N := p ^ (E - 1) * M'
  set w := ((A₀ * B) ^ N)⁻¹
  have hw0 : (A₀ * B) ^ N ≠ 0 := pow_ne_zero _ hAB
  have hK : K = #{ψ : DirichletCharacter ℂ q | ψ (a : ZMod q) ^ N = w} := by
    simp only [K]
    congr 1; ext ψ
    simp only [Finset.mem_filter, mem_univ, true_and]
    rw [criterion_gen _ E M' hE hM' (hdvd ψ), not_not, mul_assoc, mul_pow]
    constructor
    · intro h; exact eq_inv_of_mul_eq_one_left h
    · intro h; rw [h, inv_mul_cancel₀ hw0]
  by_cases hx : w ∈ Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N
  · right; rw [hK]; exact fiber_digit a N w hx
  · left; rw [hK]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro ψ _ h; exact hx ⟨ψ, h⟩

end PAG.Part149

#print axioms PAG.Part149.criterion_gen
#print axioms PAG.Part149.fiber_digit
#print axioms PAG.Part149.cancel_count
