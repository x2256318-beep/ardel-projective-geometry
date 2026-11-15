/-
  PAG 2.0 Part 128（2026-10-21）— 積のケットの位相 ζ とガウス和の位相の積 w の関係
  ζ = (∏ λ_i^{-1/2} 𝓕k_i(t_i))^L、L = lcmF(ord χ_i)、w = ∏ τ(χ_i)/√(p_i^{c_i+1}) について
  1. ζ = w^L（各因子で Part 113 の zeta_eq_gauss）
  2. ord ζ = ord w / gcd(ord w, L)
  3. p^e ∣ a、p^e ∤ b ⇒ p ∣ a / gcd(a, b)
  4. p_i^{c_i+1} ∤ ∏_{j≠i} ord z_j かつ p_i^{c_i+1} ∤ L なら p_i ∣ ord ζ（ζ の位数に各素数が現れる）
-/
import PAG131

namespace PAG.Part132

open ZMod Finset PAG.Part125 PAG.Part126

theorem lcmF_ne_zero : ∀ (n : ℕ) (o : Fin n → ℕ), (∀ i, o i ≠ 0) → lcmF n o ≠ 0 := by
  intro n
  induction n with
  | zero => intro o _; exact one_ne_zero
  | succ n ih => intro o h; exact Nat.lcm_ne_zero (h 0) (ih _ (fun j => h j.succ))

/-- **3. p^e ∣ a、p^e ∤ b ⇒ p ∣ a / gcd(a, b)**。 -/
theorem p_dvd_div_gcd (p : ℕ) (hp : p.Prime) (e a b : ℕ) (ha : p ^ e ∣ a) (hb : ¬ p ^ e ∣ b) :
    p ∣ a / Nat.gcd a b := by
  by_contra hn
  have hcop : Nat.Coprime (p ^ e) (a / Nat.gcd a b) :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
  have hsplit : a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
  have h1 : p ^ e ∣ Nat.gcd a b * (a / Nat.gcd a b) := hsplit ▸ ha
  exact hb ((hcop.dvd_of_dvd_mul_right h1).trans (Nat.gcd_dvd_right a b))

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **1. ζ = w^L**。 -/
theorem zeta_prod_eq_pow (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    (∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i))
      = (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ))
        ^ lcmF n (fun i => orderOf (χ i)) := by
  rw [← Finset.prod_pow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  obtain ⟨q, hq⟩ := dvd_lcmF n (fun i => orderOf (χ i)) i
  rw [hq, pow_mul, pow_mul, zeta_eq_gauss (K i) (w i) (c i) (h i) (χ i) (hχ i) (t i) (ht i)]

/-- **2. ord ζ = ord w / gcd(ord w, L)**。 -/
theorem orderOf_zeta_prod (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i) * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i))
        ^ lcmF n (fun i => orderOf (χ i)))
      = orderOf (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ))
        / Nat.gcd (orderOf (∏ i, gaussSum (χ i) stdAddChar / ((Real.sqrt ((p i : ℝ) ^ (c i + 1)) : ℝ) : ℂ)))
          (lcmF n (fun i => orderOf (χ i))) := by
  rw [zeta_prod_eq_pow p K w c h χ hχ t ht]
  exact orderOf_pow' _ (lcmF_ne_zero n _ (fun i => (orderOf_pos (χ i)).ne'))

/-- **4. ζ の位数に各素数が現れる十分条件**。 -/
theorem p_dvd_orderOf_zeta_prod (hp2 : ∀ i, p i ≠ 2) (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hcond : ¬ p i ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)))
    (hL : ¬ p i ^ (c i + 1) ∣ lcmF n (fun i => orderOf (χ i))) :
    p i ∣ orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) := by
  rw [orderOf_zeta_prod p K w c h χ hχ t ht]
  apply p_dvd_div_gcd (p i) (hp i).out (c i + 1) _ _ _ hL
  exact PAG.Part131.gauss_prod_pdvd_sharp p (fun j => c j + 1) hp2 (fun j => by have := hc j; omega) χ hχ i hcond

end Ket

end PAG.Part132

#print axioms PAG.Part132.lcmF_ne_zero
#print axioms PAG.Part132.p_dvd_div_gcd
#print axioms PAG.Part132.zeta_prod_eq_pow
#print axioms PAG.Part132.orderOf_zeta_prod
#print axioms PAG.Part132.p_dvd_orderOf_zeta_prod
