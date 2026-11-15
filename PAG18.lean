/-
  PAG 2.0 Part 14（2026-10-18）— 頂上殻の非原始的な積（Part 5 定理 A の導手降下）
  χ₁, χ₂ が法 p^K（K = n+1）で原始的、χ₁χ₂ = ψ ∘ π（ψ は法 p^(K−v) の原始指標、π は射影）のとき
    χ₁ ⋆ χ₂ = (τ(χ₁)τ(χ₂)/τ(ψ)) · ι_{v,*} ψ        （殻 v = c − c' への内向きシフト）
  鍵: 𝓕(ι_{v,*} f) = π^*(𝓕 f)（押し出しのフーリエ変換は引き戻し）
-/
import PAG17

namespace PAG.Part18

open ZMod Finset PAG.Part17

variable {p : ℕ} [hp : Fact p.Prime]

/-- 加法指標のスケーリング: N = M d なら ψ_N(d j) = ψ_M(j)（整数 j）。 -/
theorem stdAddChar_scale (N M d : ℕ) [NeZero N] [NeZero M] (hN : N = M * d) (hd : d ≠ 0) (j : ℤ) :
    stdAddChar (((d : ℤ) * j : ℤ) : ZMod N) = stdAddChar ((j : ℤ) : ZMod M) := by
  rw [stdAddChar_coe, stdAddChar_coe]
  congr 1
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  rw [hN]
  push_cast
  field_simp

/-- **押し出しのフーリエ変換は引き戻し**: 𝓕_{p^K}(ι_{v,*} f)(k) = 𝓕_{p^(K−v)} f(π k)。 -/
theorem dft_push (K v : ℕ) (hv : v ≤ K) (f : ZMod (p ^ (K - v)) → ℂ) (k : ZMod (p ^ K)) :
    have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    𝓕 (push (shellEmb (p := p) K v hv) f) k
      = 𝓕 f (ZMod.castHom (pow_dvd_pow p (Nat.sub_le K v)) (ZMod (p ^ (K - v))) k) := by
  intro _ _
  rw [dft_apply, dft_apply]
  simp_rw [smul_eq_mul]
  rw [show (∑ z, stdAddChar (-(z * k)) * push (shellEmb K v hv) f z)
      = ∑ z, push (shellEmb K v hv) f z * stdAddChar (-(z * k)) from
      sum_congr rfl (fun _ _ => mul_comm _ _), sum_push_mul _ (shellEmb_injective K v hv)]
  refine sum_congr rfl (fun y _ => ?_)
  rw [mul_comm]
  congr 1
  -- ψ_{p^K}(−(p^v y k)) = ψ_{p^(K−v)}(−(y π k))
  have hK : p ^ K = p ^ (K - v) * p ^ v := by rw [← pow_add, Nat.sub_add_cancel hv]
  have e1 : -(shellEmb (p := p) K v hv y * k)
      = ((((p ^ v : ℕ) : ℤ) * (-(y.val * k.val : ℕ) : ℤ) : ℤ) : ZMod (p ^ K)) := by
    rw [shellEmb_apply]
    conv_lhs => rw [← ZMod.natCast_zmod_val k]
    push_cast; ring
  have e2 : -(y * ZMod.castHom (pow_dvd_pow p (Nat.sub_le K v)) (ZMod (p ^ (K - v))) k)
      = (((-(y.val * k.val : ℕ) : ℤ)) : ZMod (p ^ (K - v))) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val k, ← ZMod.natCast_zmod_val y]
    rw [map_natCast]; push_cast; ring
  rw [e1, e2]
  exact stdAddChar_scale (p ^ K) (p ^ (K - v)) (p ^ v) hK (pow_ne_zero _ hp.out.ne_zero) _

/-- 引き戻し指標の逆: χ = ψ ∘ π なら χ⁻¹ = ψ⁻¹ ∘ π。 -/
theorem inv_pullback {N M : ℕ} (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ M)
    (π : ZMod N →+* ZMod M) (h : ∀ x, χ x = ψ (π x)) (x : ZMod N) : χ⁻¹ x = ψ⁻¹ (π x) := by
  rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', h]

/-- **頂上殻の導手降下（Part 5 定理 A、K = c）**: χ₁, χ₂ 原始的（法 p^(n+1)）、
χ₁χ₂ = ψ ∘ π（ψ 原始的、法 p^(n+1−v)、v ≤ n）なら
χ₁ ⋆ χ₂ = (τ(χ₁)τ(χ₂)/τ(ψ)) · ι_{v,*} ψ。 -/
theorem conv_chars_descent (n v : ℕ) (hv : v ≤ n)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    PAG.Part15.conv (χ₁ : ZMod (p ^ (n + 1)) → ℂ) χ₂
      = (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) •
          push (shellEmb (p := p) (n + 1) v (by omega)) (ψ : ZMod (p ^ (n + 1 - v)) → ℂ) := by
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set π := ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) (ZMod (p ^ (n + 1 - v))) with hπ
  have hτ := PAG.Part16.gaussSum_ne_zero hψ
  apply (dft (N := p ^ (n + 1)) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, _root_.map_smul]
  funext k
  rw [Pi.mul_apply, Pi.smul_apply, dft_push (n + 1) v (by omega), h₁.fourierTransform_eq_inv_mul_gaussSum,
    h₂.fourierTransform_eq_inv_mul_gaussSum, hψ.fourierTransform_eq_inv_mul_gaussSum, smul_eq_mul]
  have hinv : χ₁⁻¹ (-k) * χ₂⁻¹ (-k) = ψ⁻¹ (-(π k)) := by
    rw [← map_neg, ← inv_pullback (χ₁ * χ₂) ψ π hprod, mul_inv, MulChar.coeToFun_mul, Pi.mul_apply]
  rw [← hπ]
  field_simp
  linear_combination (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar) * hinv

/-- 係数の大きさ: |τ₁τ₂/τ(ψ)|² = p^(2(n+1)) / p^(n+1−v)、すなわち |J̃| = 1 の正規化と整合。 -/
theorem normSq_descent_coef (n v : ℕ) (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive) :
    Complex.normSq (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)
      = ((p ^ (n + 1) : ℕ) : ℝ) ^ 2 / ((p ^ (n + 1 - v) : ℕ) : ℝ) := by
  have : NeZero (p ^ (n + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Complex.normSq_div, Complex.normSq_mul, PAG.Part16.normSq_gaussSum h₁,
    PAG.Part16.normSq_gaussSum h₂, PAG.Part16.normSq_gaussSum hψ, sq]

/-- 押し出しはスカラー倍と可換。 -/
theorem push_smul {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G)
    (hι : Function.Injective ι) (a : ℂ) (f : H → ℂ) : push ι (a • f) = a • push ι f := by
  funext x
  by_cases hx : ∃ y, ι y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [push, hι.extend_apply, Pi.smul_apply]
  · simp [push, Function.extend_apply' _ _ _ hx]

/-- **一般殻の畳み込みの還元**（原始性によらない）: ι_*π^*f ⋆ ι_*π^*g = q · ι_*π^*(f ⋆ g)。 -/
theorem conv_shell_general {G L H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup L] [Fintype L]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ι : L →+ G) (hι : Function.Injective ι) (π : L →+ H) (hπ : Function.Surjective π) (f g : H → ℂ) :
    PAG.Part15.conv (push ι (f ∘ π)) (push ι (g ∘ π))
      = ((univ.filter (fun z : L => π z = 0)).card : ℂ) • push ι (PAG.Part15.conv f g ∘ π) := by
  rw [push_conv ι hι, conv_pullback π hπ, push_smul ι hι]

/-- **一般殻の導手降下**: 殻 w の引き戻し・押し出しに、頂上殻の導手降下を代入した形。 -/
theorem conv_shell_descent {G L : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup L] [Fintype L]
    (ι : L →+ G) (hι : Function.Injective ι) (n v : ℕ) (hv : v ≤ n)
    (π : L →+ ZMod (p ^ (n + 1))) (hπ : Function.Surjective π)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    PAG.Part15.conv (push ι ((χ₁ : ZMod (p ^ (n + 1)) → ℂ) ∘ π)) (push ι ((χ₂ : ZMod (p ^ (n + 1)) → ℂ) ∘ π))
      = (((univ.filter (fun z : L => π z = 0)).card : ℂ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)) •
        push ι (push (shellEmb (p := p) (n + 1) v (by omega)) (ψ : ZMod (p ^ (n + 1 - v)) → ℂ) ∘ π) := by
  classical
  rw [conv_shell_general ι hι π hπ, conv_chars_descent n v hv χ₁ χ₂ h₁ h₂ ψ hψ hprod]
  rw [show ((gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) •
      push (shellEmb (p := p) (n + 1) v (by omega)) (ψ : ZMod (p ^ (n + 1 - v)) → ℂ)) ∘ π
      = (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar) •
      (push (shellEmb (p := p) (n + 1) v (by omega)) (ψ : ZMod (p ^ (n + 1 - v)) → ℂ) ∘ π) from rfl,
    push_smul ι hι, smul_smul]

end PAG.Part18

#print axioms PAG.Part18.stdAddChar_scale
#print axioms PAG.Part18.dft_push
#print axioms PAG.Part18.inv_pullback
#print axioms PAG.Part18.conv_chars_descent
#print axioms PAG.Part18.normSq_descent_coef
#print axioms PAG.Part18.push_smul
#print axioms PAG.Part18.conv_shell_general
#print axioms PAG.Part18.conv_shell_descent
