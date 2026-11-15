/-
  PAG 2.0 Part 16（2026-10-18）— 正規化ケットでの定理 A の最終形（Part 5 の式そのもの）
  |w, χ⟩ := |S_w|^(−1/2) ι_{w,*}π^*χ として
    B_cv(|w,χ₁⟩, |w,χ₂⟩) = √(p^K/|S_{w0}|) · J̃ · |S_{w+v}|^(−1/2) ι_{w,*}π^*(ι_{v,*}ψ)
    J̃ = τ(χ₁)τ(χ₂) / (τ(ψ) √(p^(c+v)))、|J̃| = 1、w0 = K − c − w
  v = 0（積が原始的）と v ≥ 1（導手降下）を一つの式で扱う。
-/
import PAG19

namespace PAG.Part20

open ZMod Finset PAG.Part17 PAG.Part18 PAG.Part19

/-! ## 1. 規格化係数（平方根つき） -/

/-- **√ つきの係数の一致**: q √(p^(c+v)) / |S_w| = √(p^K/|S_{w0}|) / √|S_{w+v}|。 -/
theorem coef_sqrt (p K c w v c'' a : ℕ) (hp : 2 ≤ p) (hc : c = v + c'' + 1) (hK : K = w + c + a) :
    ((p : ℝ) ^ (K - w - c)) * Real.sqrt ((p : ℝ) ^ (c + v)) / (sz p K w : ℝ)
      = Real.sqrt ((p : ℝ) ^ K / (sz p K (K - c - w) : ℝ)) / Real.sqrt (sz p K (w + v) : ℝ) := by
  have hpos : ∀ u, (0 : ℝ) < sz p K u := fun u => by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hL : 0 ≤ ((p : ℝ) ^ (K - w - c)) * Real.sqrt ((p : ℝ) ^ (c + v)) / (sz p K w : ℝ) := by positivity
  have hR : 0 ≤ Real.sqrt ((p : ℝ) ^ K / (sz p K (K - c - w) : ℝ)) / Real.sqrt (sz p K (w + v) : ℝ) := by
    positivity
  rw [← sq_eq_sq₀ hL hR, div_pow, div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (hpos _).le]
  have key := coef_identity_real p K c w v c'' a hp hc hK
  have hw := (hpos w).ne'
  have hwv := (hpos (w + v)).ne'
  have h0 := (hpos (K - c - w)).ne'
  field_simp
  field_simp at key
  linear_combination key

/-! ## 2. 正規化ケットでの定理 A -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- **定理 A（正規化ケット、最終形）**: c = n+1、v ≤ n、w + c ≤ K、χ₁, χ₂ 原始的（法 p^c）、
χ₁χ₂ = ψ ∘ π（ψ 原始的・法 p^(c−v)）。a_u := |S_u|^(−1/2)、
ket_w(χ) := a_w · ι_{w,*}π^*χ とおくと
ket_w(χ₁) ⋆ ket_w(χ₂) = (√(p^K/|S_{w0}|) · J̃) · (a_{w+v} · ι_{w,*}π^*(ι_{v,*}ψ))、
J̃ = τ₁τ₂ / (τ(ψ) √(p^(c+v)))。 -/
theorem thmA_normalized (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    let ι := shellEmb (p := p) K w (by omega)
    let π := (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K - w)) (ZMod (p ^ (n + 1)))).toAddMonoidHom
    let a : ℕ → ℂ := fun u => ((Real.sqrt (sz p K u))⁻¹ : ℝ)
    let Jt : ℂ := gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
      (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))
    PAG.Part15.conv (a w • push ι ((χ₁ : ZMod (p ^ (n + 1)) → ℂ) ∘ π))
        (a w • push ι ((χ₂ : ZMod (p ^ (n + 1)) → ℂ) ∘ π))
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) * Jt : ℂ) •
          (a (w + v) • push ι (push (shellEmb (p := p) (n + 1) v (by omega))
            (ψ : ZMod (p ^ (n + 1 - v)) → ℂ) ∘ π)) := by
  intro _ ι π a Jt
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hp2 := hp.out.two_le
  rw [PAG.Part15.conv_smul_smul,
    conv_shell_descent ι (shellEmb_injective K w (by omega)) n v hv π (ZMod.ringHom_surjective _)
      χ₁ χ₂ h₁ h₂ ψ hψ hprod, smul_smul, smul_smul]
  congr 1
  -- q = p^(K−w−(n+1))
  have hq := card_ker_castHom p (K - w) (n + 1) (by omega)
  simp only at hq
  rw [show (univ.filter (fun z : ZMod (p ^ (K - w)) => π z = 0)).card = p ^ (K - w - (n + 1)) from hq]
  -- 実数の係数の恒等式
  have hR := coef_sqrt p K (n + 1) w v (n - v) (K - w - (n + 1)) hp2 (by omega) (by omega)
  have hpos : ∀ u, (0 : ℝ) < sz p K u := fun u => by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have hsq : ∀ u, Real.sqrt (sz p K u : ℝ) ≠ 0 := fun u => (Real.sqrt_pos.mpr (hpos u)).ne'
  have hX : Real.sqrt ((p : ℝ) ^ (n + 1 + v)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hS2 : ∀ u, Real.sqrt (sz p K u : ℝ) ^ 2 = sz p K u := fun u => Real.sq_sqrt (hpos u).le
  have hτ := PAG.Part16.gaussSum_ne_zero hψ
  have hRw : ((p : ℝ) ^ (K - w - (n + 1))) / (Real.sqrt (sz p K w : ℝ) ^ 2)
      = Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) / Real.sqrt ((p : ℝ) ^ (n + 1 + v))
        * (Real.sqrt (sz p K (w + v) : ℝ))⁻¹ := by
    rw [hS2]
    field_simp
    field_simp at hR
    linear_combination hR
  have hC := congrArg (fun r : ℝ => (r : ℂ)) hRw
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow,
    Complex.ofReal_natCast] at hC
  simp only [a, Jt, Complex.ofReal_inv]
  push_cast
  have hXc : ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hX
  have hwc : ((Real.sqrt (sz p K w : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq w
  have hwvc : ((Real.sqrt (sz p K (w + v) : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq (w + v)
  field_simp
  field_simp at hC
  linear_combination (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar) * hC

/-- |J̃| = 1: |τ₁τ₂/(τ(ψ)√(p^(c+v)))|² = 1。 -/
theorem normSq_Jt (n v : ℕ) (hv : v ≤ n) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
      (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) = 1 := by
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, PAG.Part16.normSq_gaussSum h₁,
    PAG.Part16.normSq_gaussSum h₂, PAG.Part16.normSq_gaussSum hψ, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by positivity)]
  have hpv : (p : ℝ) ^ (n + 1) * (p : ℝ) ^ (n + 1) = (p : ℝ) ^ (n + 1 - v) * (p : ℝ) ^ (n + 1 + v) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  push_cast
  rw [hpv, div_self (by positivity)]

/-- **定理 B（正規化ケット）**: ket_w(χ) ⋆ ket_w(χ⁻¹) = (p^(K−w−c)/|S_w| · χ(−1)) · ι_{w,*}π^*(c_{p^c})。
c_{p^c} の値は PAG19.ram_eq（p^c·[球 p^c] − p^(c−1)·[球 p^(c−1)]）。 -/
theorem thmB_normalized (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    let ι := shellEmb (p := p) K w (by omega)
    let π := (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K - w)) (ZMod (p ^ (n + 1)))).toAddMonoidHom
    let a : ℂ := ((Real.sqrt (sz p K w))⁻¹ : ℝ)
    PAG.Part15.conv (a • push ι ((χ : ZMod (p ^ (n + 1)) → ℂ) ∘ π))
        (a • push ι (((χ⁻¹ : DirichletCharacter ℂ _) : ZMod (p ^ (n + 1)) → ℂ) ∘ π))
      = (((p : ℂ) ^ (K - w - (n + 1)) / (sz p K w : ℂ)) * χ (-1)) • push ι (ram ∘ π) := by
  intro _ ι π a
  rw [PAG.Part15.conv_smul_smul,
    conv_shell_inv ι (shellEmb_injective K w (by omega)) π (ZMod.ringHom_surjective _) χ hχ, smul_smul]
  congr 1
  have hq := card_ker_castHom p (K - w) (n + 1) (by omega)
  simp only at hq
  rw [show (univ.filter (fun z : ZMod (p ^ (K - w)) => π z = 0)).card = p ^ (K - w - (n + 1)) from hq]
  have hpos : (0 : ℝ) < sz p K w := by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  have hS2 : ((Real.sqrt (sz p K w : ℝ) : ℝ) : ℂ) * ((Real.sqrt (sz p K w : ℝ) : ℝ) : ℂ) = (sz p K w : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]; push_cast; rfl
  have hne : ((Real.sqrt (sz p K w : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hne2 : (sz p K w : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  simp only [a, Complex.ofReal_inv]
  push_cast
  rw [← hS2]
  field_simp

end PAG.Part20

#print axioms PAG.Part20.coef_sqrt
#print axioms PAG.Part20.thmA_normalized
#print axioms PAG.Part20.normSq_Jt
#print axioms PAG.Part20.thmB_normalized
