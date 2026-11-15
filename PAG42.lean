/-
  PAG 2.0 Part 38（2026-10-19）— 同じ双対殻・異なる導手の畳み込みの閉じた形（混合定理 A）
  χ₁ 原始（法 p^(n+1)）、χ₂ 原始（法 p^(n+1−v)）、ψ = χ₁·(χ₂ ∘ π) が原始（法 p^(n+1)）のとき
  1. 頂上: χ₁ ⋆ ι_{v,*}χ₂ = (τ₁τ₂/τ_ψ) · ψ（Z/p^(n+1) 上）
  2. ケット: |w,χ₁⟩ ⋆ |w+v,χ₂⟩ = (|S_{w+v}|^(−1/2) · q · τ₁τ₂/τ_ψ) · |w,ψ⟩、q = p^(K−w−(n+1))
  （殻 w+v・導手 n+1−v のケットは殻 w・導手 n+1 のケットと同じ双対殻 K−w−(n+1) をもつ）
-/
import PAG41

namespace PAG.Part42

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part18 PAG.Part19 PAG.Part21

variable {p : ℕ} [hp : Fact p.Prime]

/-- **混合定理 A（頂上）**: χ₁ ⋆ ι_{v,*}χ₂ = (τ₁τ₂/τ_ψ)·ψ。 -/
theorem conv_mixed_top (n v : ℕ) (hv : v ≤ n)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    conv (χ₁ : ZMod (p ^ (n + 1)) → ℂ) (push (shellEmb (p := p) (n + 1) v (by omega)) (χ₂ : ZMod (p ^ (n + 1 - v)) → ℂ))
      = (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) • (ψ : ZMod (p ^ (n + 1)) → ℂ) := by
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set π := ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) with hπ
  have hτ := PAG.Part16.gaussSum_ne_zero hψ
  apply (dft (N := p ^ (n + 1)) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, _root_.map_smul]
  funext k
  rw [Pi.mul_apply, Pi.smul_apply, dft_push (n + 1) v (by omega), h₁.fourierTransform_eq_inv_mul_gaussSum,
    h₂.fourierTransform_eq_inv_mul_gaussSum, hψ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul]
  have hinv : χ₁⁻¹ (-k) * χ₂⁻¹ (-(π k)) = ψ⁻¹ (-k) := by
    rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hprod, ← map_neg,
      mul_inv]
  rw [← hπ]
  field_simp
  linear_combination (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar) * hinv

/-- **混合定理 A（ケット）**: |w,χ₁⟩ ⋆ |w+v,χ₂⟩ = (|S_{w+v}|^(−1/2)·q·τ₁τ₂/τ_ψ)·|w,ψ⟩。 -/
theorem conv_ket_mixed (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    conv (ket K w (n + 1) hK χ₁) (ket K (w + v) (n + 1 - v) (by omega) χ₂)
      = (((Real.sqrt (sz p K (w + v)))⁻¹ : ℝ) * (((p ^ (K - w - (n + 1)) : ℕ) : ℂ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)) : ℂ) •
        ket K w (n + 1) hK ψ := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  unfold ket
  rw [← push_comp K w (n + 1) v hK (by omega) (χ₂ : ZMod (p ^ (n + 1 - v)) → ℂ)]
  rw [conv_smul_smul, conv_shell_general (shellEmb (p := p) K w (by omega)) (shellEmb_injective K w (by omega))
    _ (ZMod.ringHom_surjective _), conv_mixed_top n v hv χ₁ h₁ χ₂ h₂ ψ hψ hprod]
  have hq := card_ker_castHom p (K - w) (n + 1) (by omega)
  simp only at hq
  rw [hq, show K - w - (n + 1) = K - w - (n + 1) from rfl]
  rw [show ((gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) • (ψ : ZMod (p ^ (n + 1)) → ℂ))
      ∘ (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K - w)) (ZMod (p ^ (n + 1)))).toAddMonoidHom
      = (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) •
        ((ψ : ZMod (p ^ (n + 1)) → ℂ) ∘ (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K - w)) (ZMod (p ^ (n + 1)))).toAddMonoidHom)
      from rfl, push_smul _ (shellEmb_injective K w (by omega)), smul_smul, smul_smul, smul_smul]
  congr 1
  ring


/-- ψ = χ₁·(χ₂ ∘ π) は自動的に原始的（χ₁ 原始的、1 ≤ v）。 -/
theorem mixed_prim (n v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ n)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v)))
    (ψ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprod : ∀ x, ψ x = χ₁ x * χ₂ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    ψ.IsPrimitive := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hn : 1 ≤ n := by omega
  rw [PAG.Part32.prim_iff_gp hn, hprod]
  have hg : ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) (PAG.Part32.gp p n) = 1 := by
    rw [PAG.Part32.gp, map_add, map_one, map_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p (by omega)), add_zero]
  rw [hg, map_one, mul_one]
  exact (PAG.Part32.prim_iff_gp hn χ₁).mp h₁

/-- 係数の大きさ: |係数|² = λ = p^K/|S_{w0}|（PAG41 の飽和から）。 -/
theorem normSq_mixed_coef (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive) :
    Complex.normSq ((((Real.sqrt (sz p K (w + v)))⁻¹ : ℝ) * (((p ^ (K - w - (n + 1)) : ℕ) : ℂ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)) : ℂ))
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) := by
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  obtain ⟨A, hA⟩ : ∃ A, K = w + (n + 1) + A := ⟨K - w - (n + 1), by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, n = v + d := ⟨n - v, by omega⟩
  have e1 : (sz p K (w + v) : ℝ) = (p : ℝ) ^ (d + A) * ((p : ℝ) - 1) := by
    unfold sz; rw [show K - 1 - (w + v) = d + A by omega]; push_cast [Nat.cast_sub hp.out.one_lt.le]; ring
  have e2 : (sz p K (K - (n + 1) - w) : ℝ) = (p : ℝ) ^ (w + n) * ((p : ℝ) - 1) := by
    unfold sz; rw [show K - 1 - (K - (n + 1) - w) = w + n by omega]; push_cast [Nat.cast_sub hp.out.one_lt.le]; ring
  have hsz : (0 : ℝ) < sz p K (w + v) := by rw [e1]; positivity
  rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_mul, Complex.normSq_natCast, Complex.normSq_div,
    Complex.normSq_mul, PAG.Part16.normSq_gaussSum h₁, PAG.Part16.normSq_gaussSum h₂, PAG.Part16.normSq_gaussSum hψ,
    ← mul_inv, Real.mul_self_sqrt hsz.le, e1, e2]
  rw [show K - w - (n + 1) = A by omega, show n + 1 - v = d + 1 by omega, hA, hd]
  push_cast
  field_simp
  ring

end PAG.Part42

#print axioms PAG.Part42.conv_mixed_top
#print axioms PAG.Part42.conv_ket_mixed
#print axioms PAG.Part42.mixed_prim
#print axioms PAG.Part42.normSq_mixed_coef
