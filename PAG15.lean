/-
  PAG 2.0 Part 11（2026-10-18）
  1. 部分群の指示関数の畳み込み吸収律と、球平均の入れ子から直交べき等元（PAG14.epsBall の具体化）
  2. 殻サイズ比の K 非依存性（|F_{v,K−1−v}| = 1/√p）と、動径列のユニタリ性
  3. 関数空間上の定理 A の骨格（ガウス和比 → ヤコビ和）
-/
import PAG14

namespace PAG.Part15

open Finset PAG.Part14

/-! ## 1. 部分群の吸収律 -/

section Subgroup

variable {G : Type*} [AddCommGroup G] [Fintype G] {K : Type*} [Field K]

/-- 加法畳み込み (f ⋆ g)(x) = Σ_y f(y) g(x − y)。 -/
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)

theorem conv_comm (f g : G → K) : conv f g = conv g f := by
  funext x
  unfold conv
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y => by
    simp only [Equiv.subLeft_apply, sub_sub_cancel]; ring)

/-- 畳み込みは双線形写像。 -/
def convL : (G → K) →ₗ[K] (G → K) →ₗ[K] (G → K) :=
  LinearMap.mk₂ K conv
    (fun f₁ f₂ g => by funext x; simp [conv, add_mul, sum_add_distrib])
    (fun c f g => by funext x; simp [conv, mul_sum, mul_assoc])
    (fun f g₁ g₂ => by funext x; simp [conv, mul_add, sum_add_distrib])
    (fun c f g => by funext x; simp [conv, mul_sum, mul_left_comm])

theorem convL_apply (f g : G → K) : convL f g = conv f g := rfl

theorem conv_smul_smul (a b : K) (f g : G → K) : conv (a • f) (b • g) = (a * b) • conv f g := by
  funext x
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl (fun y _ => by ring)

open Classical in
/-- 部分群の指示関数。 -/
noncomputable def indH (H : AddSubgroup G) : G → K := fun x => if x ∈ H then 1 else 0

open Classical in
/-- |H|（Finset 版）。 -/
noncomputable def cardH (H : AddSubgroup G) : ℕ := (univ.filter (fun y => y ∈ H)).card

theorem cardH_pos (H : AddSubgroup G) : 0 < cardH H := by
  classical
  unfold cardH
  exact Finset.card_pos.mpr ⟨0, by simp [H.zero_mem]⟩

/-- **部分群指示関数の畳み込み吸収律**: H₁ ≤ H₂ ⇒ 1_{H₁} ⋆ 1_{H₂} = |H₁| · 1_{H₂}。 -/
theorem conv_ind_addSubgroup {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) (x : G) :
    conv (indH (K := K) H₁) (indH H₂) x = (cardH H₁ : K) * indH H₂ x := by
  classical
  unfold conv
  have key : ∀ y, indH (K := K) H₁ y * indH H₂ (x - y) = indH H₁ y * indH H₂ x := by
    intro y
    by_cases hy : y ∈ H₁
    · have hy2 : y ∈ H₂ := h hy
      have hiff : x - y ∈ H₂ ↔ x ∈ H₂ := by
        rw [sub_eq_add_neg]; exact H₂.add_mem_cancel_right (H₂.neg_mem hy2)
      simp only [indH, hiff]
    · simp [indH, hy]
  simp_rw [key]
  rw [← sum_mul]
  congr 1
  simp only [indH, cardH]
  rw [Finset.sum_boole]

/-- 正規化球平均 P_H = |H|⁻¹ 1_H。 -/
noncomputable def ballAvg (H : AddSubgroup G) : G → K := ((cardH H : K))⁻¹ • indH H

/-- **球平均の吸収律**: 標数 0 で H₁ ≤ H₂ ⇒ P_{H₁} ⋆ P_{H₂} = P_{H₂}。 -/
theorem ball_avg_absorb [CharZero K] {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) :
    conv (ballAvg (K := K) H₁) (ballAvg H₂) = ballAvg H₂ := by
  have h1 : (cardH H₁ : K) ≠ 0 := Nat.cast_ne_zero.mpr (cardH_pos H₁).ne'
  rw [ballAvg, ballAvg, conv_smul_smul]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, conv_ind_addSubgroup h x]
  field_simp

/-- 反対順（畳み込みの可換性）。 -/
theorem ball_avg_absorb' [CharZero K] {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) :
    conv (ballAvg (K := K) H₂) (ballAvg H₁) = ballAvg H₂ := by
  rw [conv_comm]; exact ball_avg_absorb h

/-- 双線形版の直交べき等性: μ(P_a, P_b) = μ(P_b, P_a) = P_b（a ≤ b ≤ K）なら
μ(ε_a, ε_b) = δ_ab ε_a（ε = PAG14.epsBall）。 -/
theorem epsBall_bilin {M : Type*} [CommRing M] [Module K M] (μ : M →ₗ[K] M →ₗ[K] M)
    (P : ℕ → M) (Kc : ℕ) (habs : ∀ a b, a ≤ b → b ≤ Kc → μ (P a) (P b) = P b ∧ μ (P b) (P a) = P b)
    {a b : ℕ} (ha : a ≤ Kc) (hb : b ≤ Kc) :
    μ (epsBall P Kc a) (epsBall P Kc b) = if a = b then epsBall P Kc a else 0 := by
  unfold epsBall
  rcases lt_trichotomy a b with h | h | h
  · have haK : a < Kc := lt_of_lt_of_le h hb
    rw [ite_eq_right_of_eq_false _ _ (eq_false h.ne), ite_eq_left_of_eq_true _ _ (eq_true haK)]
    by_cases hbK : b < Kc
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hbK)]
      simp only [map_sub, LinearMap.sub_apply, (habs a b h.le hb).1, (habs a (b + 1) (by omega) (by omega)).1,
        (habs (a + 1) b (by omega) hb).1, (habs (a + 1) (b + 1) (by omega) (by omega)).1]
      abel
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hbK)]
      simp only [map_sub, LinearMap.sub_apply, (habs a Kc (by omega) le_rfl).1,
        (habs (a + 1) Kc (by omega) le_rfl).1]
      abel
  · subst h
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    by_cases haK : a < Kc
    · rw [ite_eq_left_of_eq_true _ _ (eq_true haK)]
      simp only [map_sub, LinearMap.sub_apply, (habs a a le_rfl ha).1, (habs a (a + 1) (by omega) (by omega)).1,
        (habs a (a + 1) (by omega) (by omega)).2, (habs (a + 1) (a + 1) le_rfl (by omega)).1]
      abel
    · rw [ite_eq_right_of_eq_false _ _ (eq_false haK)]
      exact (habs Kc Kc le_rfl le_rfl).1
  · have hbK : b < Kc := lt_of_lt_of_le h ha
    rw [ite_eq_right_of_eq_false _ _ (eq_false h.ne'), ite_eq_left_of_eq_true _ _ (eq_true hbK)]
    by_cases haK : a < Kc
    · rw [ite_eq_left_of_eq_true _ _ (eq_true haK)]
      simp only [map_sub, LinearMap.sub_apply, (habs b a h.le ha).2, (habs (b + 1) a (by omega) ha).2,
        (habs b (a + 1) (by omega) (by omega)).2, (habs (b + 1) (a + 1) (by omega) (by omega)).2]
      abel
    · rw [ite_eq_right_of_eq_false _ _ (eq_false haK)]
      simp only [map_sub, (habs b Kc (by omega) le_rfl).2,
        (habs (b + 1) Kc (by omega) le_rfl).2]
      abel

/-- **具体化**: 単調な部分群の列 H_0 ≤ H_1 ≤ … の球平均 P_w = P_{H_w} から作った ε_w は
畳み込みに関して直交べき等。 -/
theorem ballEps_conv [CharZero K] (H : ℕ → AddSubgroup G) (hH : Monotone H) (Kc : ℕ)
    {a b : ℕ} (ha : a ≤ Kc) (hb : b ≤ Kc) :
    conv (epsBall (fun w => ballAvg (K := K) (H w)) Kc a) (epsBall (fun w => ballAvg (H w)) Kc b)
      = if a = b then epsBall (fun w => ballAvg (H w)) Kc a else 0 := by
  rw [← convL_apply]
  exact epsBall_bilin convL (fun w => ballAvg (K := K) (H w)) Kc (fun a b hab _ =>
    ⟨ball_avg_absorb (hH hab), ball_avg_absorb' (hH hab)⟩) ha hb

/-- H_0 = ⊥ なら P_0 = δ₀ は畳み込みの単位元。 -/
theorem ballAvg_bot_conv [CharZero K] (f : G → K) : conv (ballAvg (K := K) ⊥) f = f := by
  classical
  funext x
  have hc : cardH (⊥ : AddSubgroup G) = 1 := by
    unfold cardH
    rw [Finset.card_eq_one]; exact ⟨0, by ext y; simp [AddSubgroup.mem_bot]⟩
  simp [conv, ballAvg, indH, hc, AddSubgroup.mem_bot]

end Subgroup

/-! ## 2. 殻サイズ比の K 非依存性 -/

section Shell

/-- 殻 v のサイズ |S_v| = p^(K−1−v) (p − 1)（v < K）。 -/
def shellSize (p K v : ℕ) : ℕ := p ^ (K - 1 - v) * (p - 1)

theorem shellSize_eq (p K v : ℕ) : shellSize p K v = p ^ (K - 1 - v) * shellSize p K (K - 1) := by
  simp [shellSize]

/-- |S_0| · p = p^K · (p − 1)（K ≥ 1）。 -/
theorem shellSize_zero_mul (p K : ℕ) (hK : 1 ≤ K) : shellSize p K 0 * p = p ^ K * (p - 1) := by
  unfold shellSize
  rw [Nat.sub_zero, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hK]

/-- 一般の v: |S_v| · p^(2v) · p = p^K · |S_{K−1−v}|（v < K）。 -/
theorem shellSize_ratio (p K v : ℕ) (hv : v < K) :
    shellSize p K v * p ^ (2 * v) * p = p ^ K * shellSize p K (K - 1 - v) := by
  unfold shellSize
  rw [show K - 1 - (K - 1 - v) = v by omega]
  have : K - 1 - v + 2 * v + 1 = K + v := by omega
  calc p ^ (K - 1 - v) * (p - 1) * p ^ (2 * v) * p = p ^ (K - 1 - v + 2 * v + 1) * (p - 1) := by ring
    _ = p ^ K * (p ^ v * (p - 1)) := by rw [this, pow_add]; ring

/-- **|F_{v,K−1−v}|² = 1/p（K, v に依存しない）**:
(|S_v| / |S_{K−1−v}|) · p^(2v) / p^K = 1/p（実数）。 -/
theorem F_sq_eq_inv_p (p K v : ℕ) (hp : 2 ≤ p) (hv : v < K) :
    ((shellSize p K v : ℝ) / shellSize p K (K - 1 - v)) * (p : ℝ) ^ (2 * v) / (p : ℝ) ^ K = 1 / p := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hS : (shellSize p K (K - 1 - v) : ℝ) ≠ 0 := by
    unfold shellSize; push_cast
    have : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [Nat.cast_sub (by omega)]; push_cast
    exact mul_ne_zero (pow_ne_zero _ hp0) h1
  have key := shellSize_ratio p K v hv
  have keyR : (shellSize p K v : ℝ) * (p : ℝ) ^ (2 * v) * p = (p : ℝ) ^ K * shellSize p K (K - 1 - v) := by
    exact_mod_cast key
  field_simp
  linear_combination keyR

/-- 系: F_{v,K−1−v} = −(√p)⁻¹ の大きさ: √((|S_v|/|S_{K−1−v}|)·p^(2v)/p^K) = (√p)⁻¹。 -/
theorem abs_F_eq (p K v : ℕ) (hp : 2 ≤ p) (hv : v < K) :
    Real.sqrt (((shellSize p K v : ℝ) / shellSize p K (K - 1 - v)) * (p : ℝ) ^ (2 * v) / (p : ℝ) ^ K)
      = (Real.sqrt p)⁻¹ := by
  rw [F_sq_eq_inv_p p K v hp hv, one_div, Real.sqrt_inv]

/-- **動径列のユニタリ性**: 1/p + Σ_{k<L} (p−1)²/p^(k+2) + (p−1)/p^(L+1) = 1。 -/
theorem radial_column_unitary (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    (1 : ℝ) / p + ∑ k ∈ range L, ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ (k + 2) + ((p : ℝ) - 1) / (p : ℝ) ^ (L + 1) = 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  induction L with
  | zero => simp; field_simp; ring
  | succ L ih =>
    rw [sum_range_succ]
    have : ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ (L + 2) + ((p : ℝ) - 1) / (p : ℝ) ^ (L + 1 + 1)
        = ((p : ℝ) - 1) / (p : ℝ) ^ (L + 1) := by
      rw [show L + 1 + 1 = L + 2 by ring, pow_succ (p : ℝ) (L + 1)]
      field_simp; ring
    linear_combination ih + this

end Shell

/-! ## 3. 定理 A の骨格 -/

section ThmA

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- **畳み込みスケーリング**: F f_i = τ_i g_i、g₁ g₂ = c g₁₂、F f₁₂ = τ₁₂ g₁₂（τ₁₂ ≠ 0）なら
B(f₁, f₂) = (α c τ₁τ₂/τ₁₂) f₁₂。 -/
theorem Bcv_shift (F : A ≃ₗ[ℂ] A) (α c τ₁ τ₂ τ₁₂ : ℂ) (f₁ f₂ f₁₂ g₁ g₂ g₁₂ : A)
    (h₁ : F f₁ = τ₁ • g₁) (h₂ : F f₂ = τ₂ • g₂) (hg : g₁ * g₂ = c • g₁₂)
    (h₁₂ : F f₁₂ = τ₁₂ • g₁₂) (hτ : τ₁₂ ≠ 0) :
    PAG.Part10.Bcv F α f₁ f₂ = (α * c * (τ₁ * τ₂ / τ₁₂)) • f₁₂ := by
  have hg12 : g₁₂ = τ₁₂⁻¹ • F f₁₂ := by rw [h₁₂, smul_smul, inv_mul_cancel₀ hτ, one_smul]
  unfold PAG.Part10.Bcv
  rw [h₁, h₂, smul_mul_smul_comm, hg, smul_smul, hg12, smul_smul, map_smul,
    LinearEquiv.symm_apply_apply, smul_smul]
  congr 1
  field_simp

variable {p n : ℕ} [hp : Fact p.Prime]

/-- ガウス和比はヤコビ和: χ₁χ₂ 原始的・τ(χ₁χ₂) ≠ 0 ⇒ τ₁τ₂/τ₁₂ = J(χ₁, χ₂)。 -/
theorem gauss_ratio_eq_jacobi (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprim : (χ₁ * χ₂).IsPrimitive) (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ)
    (h12 : gaussSum (χ₁ * χ₂) ψ ≠ 0) :
    gaussSum χ₁ ψ * gaussSum χ₂ ψ / gaussSum (χ₁ * χ₂) ψ = PAG.Part7.J χ₁ χ₂ := by
  rw [PAG.Part8.gauss_mul_gauss_eq_jacobi_mul_primitive χ₁ χ₂ hprim ψ, mul_div_assoc, div_self h12,
    mul_one]

/-- **定理 A（原始的な積）の関数空間上の骨格**: B(f₁, f₂) = (α c J(χ₁, χ₂)) f₁₂。 -/
theorem Bcv_shift_jacobi (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hprim : (χ₁ * χ₂).IsPrimitive) (ψ : AddChar (ZMod (p ^ (n + 1))) ℂ)
    (h12 : gaussSum (χ₁ * χ₂) ψ ≠ 0) (F : A ≃ₗ[ℂ] A) (α c : ℂ) (f₁ f₂ f₁₂ g₁ g₂ g₁₂ : A)
    (h₁ : F f₁ = gaussSum χ₁ ψ • g₁) (h₂ : F f₂ = gaussSum χ₂ ψ • g₂) (hg : g₁ * g₂ = c • g₁₂)
    (h₁₂ : F f₁₂ = gaussSum (χ₁ * χ₂) ψ • g₁₂) :
    PAG.Part10.Bcv F α f₁ f₂ = (α * c * PAG.Part7.J χ₁ χ₂) • f₁₂ := by
  rw [Bcv_shift F α c _ _ _ f₁ f₂ f₁₂ g₁ g₂ g₁₂ h₁ h₂ hg h₁₂ h12,
    gauss_ratio_eq_jacobi χ₁ χ₂ hprim ψ h12]

end ThmA

end PAG.Part15

#print axioms PAG.Part15.conv_comm
#print axioms PAG.Part15.convL_apply
#print axioms PAG.Part15.conv_smul_smul
#print axioms PAG.Part15.cardH_pos
#print axioms PAG.Part15.conv_ind_addSubgroup
#print axioms PAG.Part15.ball_avg_absorb
#print axioms PAG.Part15.ball_avg_absorb'
#print axioms PAG.Part15.epsBall_bilin
#print axioms PAG.Part15.ballEps_conv
#print axioms PAG.Part15.ballAvg_bot_conv
#print axioms PAG.Part15.shellSize_eq
#print axioms PAG.Part15.shellSize_zero_mul
#print axioms PAG.Part15.shellSize_ratio
#print axioms PAG.Part15.F_sq_eq_inv_p
#print axioms PAG.Part15.abs_F_eq
#print axioms PAG.Part15.radial_column_unitary
#print axioms PAG.Part15.Bcv_shift
#print axioms PAG.Part15.gauss_ratio_eq_jacobi
#print axioms PAG.Part15.Bcv_shift_jacobi
