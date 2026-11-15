/-
  PAG 2.0 Part 104（2026-10-19）— 複数の素数: 中国剰余定理による積構造
  有限加法群 G, H と、テンソル (f ⊗ g)(x, y) = f x · g y について
  1. (f₁ ⊗ f₂) ⋆ (g₁ ⊗ g₂) = (f₁ ⋆ g₁) ⊗ (f₂ ⋆ g₂)
  2. ‖f ⊗ g‖² = ‖f‖²‖g‖²、δ ⊗ δ = δ
  3. (k₁ ⊗ k₂) ⋆ g は「左の切り口に k₁、右の切り口に k₂」を順に作用させたもの
  4. 積の等長性: k_i が V_i 上で λ_i 倍の等長なら、k₁ ⊗ k₂ は V₁ ⊗ V₂（切り口の条件）上で λ₁λ₂ 倍
  5. 加法同型との整合（ZMod (p^K q^L) ≃ ZMod p^K × ZMod q^L）
  6. 双対殻の対 (a, b) ごとの直交べき等分解 δ = Σ ε_a ⊗ ε_b
-/
import PAG107

namespace PAG.Part108

open Finset PAG.Part15

section Generic

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

/-- テンソル (f ⊗ g)(x, y) = f x · g y。 -/
def tens (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun z => f z.1 * g z.2

/-- **1. 畳み込みの積への分解**。 -/
theorem conv_tens (f₁ g₁ : G → ℂ) (f₂ g₂ : H → ℂ) :
    conv (tens f₁ f₂) (tens g₁ g₂) = tens (conv f₁ g₁) (conv f₂ g₂) := by
  funext z
  simp only [conv, tens, Fintype.sum_prod_type, Prod.fst_sub, Prod.snd_sub, Finset.sum_mul_sum]
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring

omit [AddCommGroup G] [AddCommGroup H] in
/-- **2a. ノルムの積**。 -/
theorem normSq_tens (f : G → ℂ) (g : H → ℂ) :
    ∑ z, Complex.normSq (tens f g z) = (∑ x, Complex.normSq (f x)) * ∑ y, Complex.normSq (g y) := by
  simp only [tens, Complex.normSq_mul, Fintype.sum_prod_type, Finset.sum_mul_sum]

omit [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] in
/-- **2b. δ ⊗ δ = δ**。 -/
theorem tens_single [DecidableEq G] [DecidableEq H] (a : G) (b : H) :
    tens (Pi.single a (1 : ℂ)) (Pi.single b (1 : ℂ)) = Pi.single (a, b) 1 := by
  funext z
  obtain ⟨x, y⟩ := z
  simp only [tens, Pi.single_apply, Prod.mk.injEq]
  by_cases hx : x = a <;> by_cases hy : y = b <;> simp [hx, hy]

omit [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] in
theorem tens_add_left (f₁ f₂ : G → ℂ) (g : H → ℂ) : tens (f₁ + f₂) g = tens f₁ g + tens f₂ g := by
  funext z; simp [tens, add_mul]

omit [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] in
theorem tens_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → G → ℂ) (g : κ → H → ℂ) :
    ∑ i ∈ s, ∑ j ∈ t, tens (f i) (g j) = tens (∑ i ∈ s, f i) (∑ j ∈ t, g j) := by
  funext z
  simp only [tens, Finset.sum_apply, Finset.sum_mul_sum]

/-- **3. 切り口による表示**: ((k₁ ⊗ k₂) ⋆ g)(x, y) = (k₁ ⋆ h(·, y))(x)、h(x', ·) = k₂ ⋆ g(x', ·)。 -/
theorem conv_tens_apply (k₁ : G → ℂ) (k₂ : H → ℂ) (g : G × H → ℂ) (x : G) (y : H) :
    conv (tens k₁ k₂) g (x, y) = conv k₁ (fun x' => conv k₂ (fun y' => g (x', y')) y) x := by
  simp only [conv, tens, Fintype.sum_prod_type, Prod.mk_sub_mk, Finset.mul_sum]
  apply sum_congr rfl; intro x' _; apply sum_congr rfl; intro y' _; ring

/-- 右の切り口への畳み込みは、左の切り口の条件を保つ。 -/
theorem slice_preserved (e₁ : G → ℂ) (k₂ : H → ℂ) (g : G × H → ℂ)
    (hg : ∀ y, conv e₁ (fun x => g (x, y)) = fun x => g (x, y)) (y : H) :
    conv e₁ (fun x' => conv k₂ (fun y' => g (x', y')) y) = fun x' => conv k₂ (fun y' => g (x', y')) y := by
  funext x
  have h : ∀ y', ∑ x', e₁ x' * g (x - x', y') = g (x, y') := fun y' => congrFun (hg y') x
  simp only [conv]
  calc ∑ x', e₁ x' * ∑ y', k₂ y' * g (x - x', y - y')
      = ∑ y', k₂ y' * ∑ x', e₁ x' * g (x - x', y - y') := by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        apply sum_congr rfl; intro _ _; apply sum_congr rfl; intro _ _; ring
    _ = ∑ y', k₂ y' * g (x, y - y') := by simp only [h]

/-- 切り口の条件のもとで、ε₁ ⊗ ε₂ は g を固定する。 -/
theorem tens_fix (e₁ : G → ℂ) (e₂ : H → ℂ) (g : G × H → ℂ)
    (h₁ : ∀ y, conv e₁ (fun x => g (x, y)) = fun x => g (x, y))
    (h₂ : ∀ x, conv e₂ (fun y => g (x, y)) = fun y => g (x, y)) :
    conv (tens e₁ e₂) g = g := by
  funext z
  obtain ⟨x, y⟩ := z
  rw [conv_tens_apply]
  simp only [h₂]
  exact congrFun (h₁ y) x

/-- **4. 積の等長性**。 -/
theorem norm_conv_tens (e₁ k₁ : G → ℂ) (e₂ k₂ : H → ℂ) (l₁ l₂ : ℝ)
    (hk₁ : ∀ f, conv e₁ f = f → ∑ x, Complex.normSq (conv k₁ f x) = l₁ * ∑ x, Complex.normSq (f x))
    (hk₂ : ∀ f, conv e₂ f = f → ∑ y, Complex.normSq (conv k₂ f y) = l₂ * ∑ y, Complex.normSq (f y))
    (g : G × H → ℂ)
    (h₁ : ∀ y, conv e₁ (fun x => g (x, y)) = fun x => g (x, y))
    (h₂ : ∀ x, conv e₂ (fun y => g (x, y)) = fun y => g (x, y)) :
    ∑ z, Complex.normSq (conv (tens k₁ k₂) g z) = l₁ * l₂ * ∑ z, Complex.normSq (g z) := by
  rw [Fintype.sum_prod_type_right]
  simp only [conv_tens_apply]
  have e1 : ∀ y, ∑ x, Complex.normSq (conv k₁ (fun x' => conv k₂ (fun y' => g (x', y')) y) x)
      = l₁ * ∑ x, Complex.normSq (conv k₂ (fun y' => g (x, y')) y) :=
    fun y => hk₁ _ (slice_preserved e₁ k₂ g h₁ y)
  simp only [e1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [fun x => hk₂ _ (h₂ x)]
  rw [← Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]

/-- **5. 加法同型との整合**: (f ∘ φ) ⋆ (g ∘ φ) = (f ⋆ g) ∘ φ。 -/
theorem conv_comp_equiv (φ : G ≃+ H) (f g : H → ℂ) :
    conv (f ∘ φ) (g ∘ φ) = conv f g ∘ φ := by
  funext x
  simp only [conv, Function.comp, map_sub]
  exact Fintype.sum_equiv φ.toEquiv _ _ (fun _ => rfl)

theorem normSq_comp_equiv (φ : G ≃+ H) (f : H → ℂ) :
    ∑ x, Complex.normSq ((f ∘ φ) x) = ∑ y, Complex.normSq (f y) :=
  Fintype.sum_equiv φ.toEquiv _ _ (fun _ => rfl)

end Generic

/-! ## 6. 二つの素数での具体化 -/

section TwoPrimes

open PAG.Part59 PAG.Part89

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- 中国剰余定理の加法同型 ZMod (p^K q^L) ≃+ ZMod p^K × ZMod q^L（p ≠ q）。 -/
noncomputable def crt (K L : ℕ) (hpq : p ≠ q) : ZMod (p ^ K * q ^ L) ≃+ ZMod (p ^ K) × ZMod (q ^ L) :=
  (ZMod.chineseRemainder (Nat.Coprime.pow K L ((Nat.coprime_primes hp.out hq.out).mpr hpq))).toAddEquiv

/-- 双対殻の対ごとの分解: Σ_{a,b} ε_a ⊗ ε_b = δ。 -/
theorem sum_tens_eps (K L : ℕ) :
    ∑ a ∈ range (K + 1), ∑ b ∈ range (L + 1), tens (eps (p := p) K a) (eps (p := q) L b) = Pi.single 0 1 := by
  rw [tens_sum, PAG.Part94.sum_eps, PAG.Part94.sum_eps, tens_single]
  rfl

/-- 直交べき等性: (ε_a ⊗ ε_b) ⋆ (ε_{a'} ⊗ ε_{b'}) = [a = a' ∧ b = b'] ε_a ⊗ ε_b。 -/
theorem tens_eps_conv (K L a b a' b' : ℕ) (ha : a ≤ K) (ha' : a' ≤ K) (hb : b ≤ L) (hb' : b' ≤ L) :
    conv (tens (eps (p := p) K a) (eps (p := q) L b)) (tens (eps (p := p) K a') (eps (p := q) L b'))
      = if a = a' ∧ b = b' then tens (eps (p := p) K a) (eps (p := q) L b) else 0 := by
  rw [conv_tens, eps_conv_eps K a a' ha ha', eps_conv_eps L b b' hb hb']
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp only [h1, h2, and_self, and_false, false_and, ↓reduceIte] <;>
    (funext z; simp [tens])

/-- **積の等長性（二つの素数）**: 原始ケット k₁（法 p^K）、k₂（法 q^L）について、
  切り口がそれぞれ V_{a₁}, V_{a₂} に入る g で ‖(k₁ ⊗ k₂) ⋆ g‖² = λ₁λ₂‖g‖²。 -/
theorem norm_conv_tens_ket (K w₁ n₁ L w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (g : ZMod (p ^ K) × ZMod (q ^ L) → ℂ)
    (hg₁ : ∀ y, conv (eps (p := p) K (K - (n₁ + 1) - w₁)) (fun x => g (x, y)) = fun x => g (x, y))
    (hg₂ : ∀ x, conv (eps (p := q) L (L - (n₂ + 1) - w₂)) (fun y => g (x, y)) = fun y => g (x, y)) :
    ∑ z, Complex.normSq (conv (tens (PAG.Part21.ket K w₁ (n₁ + 1) h₁ χ₁) (PAG.Part21.ket L w₂ (n₂ + 1) h₂ χ₂)) g z)
      = (p : ℝ) ^ K / (PAG.Part19.sz p K (K - (n₁ + 1) - w₁) : ℝ)
        * ((q : ℝ) ^ L / (PAG.Part19.sz q L (L - (n₂ + 1) - w₂) : ℝ)) * ∑ z, Complex.normSq (g z) :=
  norm_conv_tens _ _ _ _ _ _ (fun f hf => norm_conv_eq_of_mem K w₁ n₁ h₁ χ₁ hχ₁ f hf)
    (fun f hf => norm_conv_eq_of_mem L w₂ n₂ h₂ χ₂ hχ₂ f hf) g hg₁ hg₂

/-- 法 p^K q^L への持ち上げ: k̃ = (k₁ ⊗ k₂) ∘ crt について k̃ ⋆ (g ∘ crt) = ((k₁ ⊗ k₂) ⋆ g) ∘ crt。 -/
theorem conv_crt (K L : ℕ) (hpq : p ≠ q) (k g : ZMod (p ^ K) × ZMod (q ^ L) → ℂ) :
    conv (k ∘ crt (p := p) (q := q) K L hpq) (g ∘ crt K L hpq) = conv k g ∘ crt K L hpq :=
  conv_comp_equiv _ k g

end TwoPrimes

end PAG.Part108

#print axioms PAG.Part108.conv_tens
#print axioms PAG.Part108.normSq_tens
#print axioms PAG.Part108.tens_single
#print axioms PAG.Part108.tens_sum
#print axioms PAG.Part108.conv_tens_apply
#print axioms PAG.Part108.slice_preserved
#print axioms PAG.Part108.tens_fix
#print axioms PAG.Part108.norm_conv_tens
#print axioms PAG.Part108.conv_comp_equiv
#print axioms PAG.Part108.normSq_comp_equiv
#print axioms PAG.Part108.sum_tens_eps
#print axioms PAG.Part108.tens_eps_conv
#print axioms PAG.Part108.norm_conv_tens_ket
#print axioms PAG.Part108.conv_crt
