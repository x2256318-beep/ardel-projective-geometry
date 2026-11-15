/-
  PAG 2.0 Part 117（2026-10-20）— 積のケットの特性多項式
  1. 加法指標 ψ_s(x) = e(s x) は畳み込みの固有ベクトル: k ⋆ ψ_s = 𝓕k(s) ψ_s
  2. 直交性 Σ_x ψ_s(x) ψ_{−s'}(x) = N [s = s']、積でも同様 ⇒ {ψ_s ⊗ ψ_t} は線形独立
  3. {ψ_s ⊗ ψ_t : s ∈ T_{a₁}, t ∈ T_{a₂}} は V_{a₁} ⊗ V_{a₂} の基底（次元は Part 109）
  4. 積の作用素 T = (k₁ ⊗ k₂) ⋆ · の V_{a₁} ⊗ V_{a₂} 上の特性多項式
     charpoly T = ∏_{s ∈ T_{a₁}} ∏_{t ∈ T_{a₂}} (X − 𝓕k₁(s) 𝓕k₂(t))
-/
import PAG120

namespace PAG.Part121

open ZMod Finset Polynomial PAG.Part15 PAG.Part108 PAG.Part109 PAG.Part113

section Char

variable {N : ℕ} [NeZero N]

/-- 加法指標 ψ_s(x) = e(s x)。 -/
noncomputable def chr (s : ZMod N) : ZMod N → ℂ := fun x => stdAddChar (s * x)

/-- **1. 固有ベクトル**。 -/
theorem conv_chr (k : ZMod N → ℂ) (s : ZMod N) : conv k (chr s) = 𝓕 k s • chr s := by
  funext x
  simp only [conv, chr, Pi.smul_apply, smul_eq_mul, dft_apply, Finset.sum_mul]
  apply sum_congr rfl; intro y _
  rw [show s * (x - y) = -(y * s) + s * x by ring, AddChar.map_add_eq_mul]
  ring

/-- **2a. 直交性**。 -/
theorem sum_chr_mul (s s' : ZMod N) :
    ∑ x, chr s x * chr (-s') x = if s = s' then (N : ℂ) else 0 := by
  have e : ∀ x, chr s x * chr (-s') x = stdAddChar ((s - s') * x) := by
    intro x; simp only [chr]; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp only [e]
  split_ifs with h
  · subst h; simp
  · have h' : s - s' ≠ 0 := sub_ne_zero.mpr h
    have := AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar N) h')
    simpa [AddChar.mulShift_apply] using this

end Char

section Prod

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- Ψ_{s,t} = ψ_s ⊗ ψ_t。 -/
noncomputable def Psi (st : ZMod N₁ × ZMod N₂) : ZMod N₁ × ZMod N₂ → ℂ := tens (chr st.1) (chr st.2)

theorem sum_Psi_mul (st st' : ZMod N₁ × ZMod N₂) :
    ∑ z, Psi st z * Psi (-st') z = if st = st' then ((N₁ * N₂ : ℕ) : ℂ) else 0 := by
  have e : ∀ z : ZMod N₁ × ZMod N₂, Psi st z * Psi (-st') z
      = (chr st.1 z.1 * chr (-st'.1) z.1) * (chr st.2 z.2 * chr (-st'.2) z.2) := by
    intro z; simp only [Psi, tens, Prod.fst_neg, Prod.snd_neg]; ring
  simp only [e]
  rw [Fintype.sum_prod_type]
  simp only []
  rw [← Finset.sum_mul_sum]
  simp only [sum_chr_mul]
  obtain ⟨s, t⟩ := st; obtain ⟨s', t'⟩ := st'
  by_cases h1 : s = s' <;> by_cases h2 : t = t' <;> simp [h1, h2]

/-- **2b. 線形独立**。 -/
theorem Psi_linearIndependent {ι : Type*} [Fintype ι] (v : ι → ZMod N₁ × ZMod N₂) (hv : Function.Injective v) :
    LinearIndependent ℂ (fun i => Psi (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun F => ∑ z, F z * Psi (-(v j)) z) hg
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
  simp only [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  simp only [mul_assoc, ← Finset.mul_sum, sum_Psi_mul, hv.eq_iff, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  have hN : ((N₁ * N₂ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)
  exact (mul_eq_zero.mp h).resolve_right hN

theorem conv_tens_Psi (k₁ : ZMod N₁ → ℂ) (k₂ : ZMod N₂ → ℂ) (st : ZMod N₁ × ZMod N₂) :
    conv (tens k₁ k₂) (Psi st) = (𝓕 k₁ st.1 * 𝓕 k₂ st.2) • Psi st := by
  simp only [Psi]
  rw [conv_tens, conv_chr, conv_chr]
  funext z; simp [tens]; ring

end Prod

/-! ## 3–4. 素数 p, q の双対殻 a₁, a₂ -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part90 PAG.Part95

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- V_{a₁} ⊗ V_{a₂}。 -/
noncomputable abbrev V12 (K L a b : ℕ) : Submodule ℂ (ZMod (p ^ K) × ZMod (q ^ L) → ℂ) :=
  LinearMap.range (convL (tens (eps (p := p) K a) (eps (p := q) L b)))

/-- 添字 T_{a₁} × T_{a₂}。 -/
abbrev Idx (K L a b : ℕ) := (Tset (p := p) K a) × (Tset (p := q) L b)

theorem Psi_mem (K L a b : ℕ) (ha : a ≤ K) (hb : b ≤ L) (i : Idx (p := p) (q := q) K L a b) :
    Psi ((i.1 : ZMod (p ^ K)), (i.2 : ZMod (q ^ L))) ∈ V12 (p := p) (q := q) K L a b := by
  rw [mem_range_convL _ (tens_idem _ _ (eps_idem K a ha) (eps_idem L b hb)), conv_tens_Psi]
  have h1 : 𝓕 (eps (p := p) K a) (i.1 : ZMod (p ^ K)) = 1 := (Finset.mem_filter.mp i.1.2).2
  have h2 : 𝓕 (eps (p := q) L b) (i.2 : ZMod (q ^ L)) = 1 := (Finset.mem_filter.mp i.2.2).2
  simp only [h1, h2, mul_one, one_smul]

/-- 基底。 -/
noncomputable def basis12 (K L a b : ℕ) (ha : a ≤ K) (hb : b ≤ L)
    (hcard : Fintype.card (Idx (p := p) (q := q) K L a b) = Module.finrank ℂ (V12 (p := p) (q := q) K L a b)) :
    Module.Basis (Idx (p := p) (q := q) K L a b) ℂ (V12 (p := p) (q := q) K L a b) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => ⟨Psi ((i.1 : ZMod (p ^ K)), (i.2 : ZMod (q ^ L))), Psi_mem K L a b ha hb i⟩)
    (by
      apply LinearIndependent.of_comp (V12 (p := p) (q := q) K L a b).subtype
      exact Psi_linearIndependent (fun i : Idx (p := p) (q := q) K L a b => ((i.1 : ZMod (p ^ K)), (i.2 : ZMod (q ^ L))))
        (fun i j h => by
          obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := i; obtain ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ := j
          simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl))
    hcard

/-- 次元の一致（原始ケットがある双対殻）。 -/
theorem card_Idx (K L w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    Fintype.card (Idx (p := p) (q := q) K L (K - (c₁ + 1) - w₁) (L - (c₂ + 1) - w₂))
      = Module.finrank ℂ (V12 (p := p) (q := q) K L (K - (c₁ + 1) - w₁) (L - (c₂ + 1) - w₂)) := by
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, V12,
    finrank_tens _ _ (eps_idem K _ (by omega)) (eps_idem L _ (by omega)),
    finrank_eps_ket K w₁ c₁ h₁ χ₁ hχ₁, finrank_eps_ket L w₂ c₂ h₂ χ₂ hχ₂,
    card_Tset K _ _ ⟨w₁, c₁, h₁, χ₁, hχ₁, rfl, rfl⟩, card_Tset L _ _ ⟨w₂, c₂, h₂, χ₂, hχ₂, rfl, rfl⟩]

/-- 積の作用素の制限。 -/
noncomputable def T12 (K L a b : ℕ) (ha : a ≤ K) (hb : b ≤ L) (k₁ : ZMod (p ^ K) → ℂ) (k₂ : ZMod (q ^ L) → ℂ) :
    Module.End ℂ (V12 (p := p) (q := q) K L a b) :=
  (convL (tens k₁ k₂)).restrict (fun f hf => by
    have hi := tens_idem _ _ (eps_idem (p := p) K a ha) (eps_idem (p := q) L b hb)
    exact (mem_range_convL _ hi _).mpr (PAG.Part111.fix_conv _ _ f ((mem_range_convL _ hi f).mp hf)))

/-- **4. 積のケットの特性多項式**。 -/
theorem charpoly_T12 (K L w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    (T12 (p := p) (q := q) K L (K - (c₁ + 1) - w₁) (L - (c₂ + 1) - w₂) (by omega) (by omega)
        (ket K w₁ (c₁ + 1) h₁ χ₁) (ket L w₂ (c₂ + 1) h₂ χ₂)).charpoly
      = ∏ s ∈ Tset (p := p) K (K - (c₁ + 1) - w₁), ∏ t ∈ Tset (p := q) L (L - (c₂ + 1) - w₂),
          (X - C (𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) s * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) t)) := by
  classical
  set a := K - (c₁ + 1) - w₁
  set b := L - (c₂ + 1) - w₂
  set k₁ := ket K w₁ (c₁ + 1) h₁ χ₁
  set k₂ := ket L w₂ (c₂ + 1) h₂ χ₂
  set B := basis12 (p := p) (q := q) K L a b (by omega) (by omega) (card_Idx K L w₁ c₁ w₂ c₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂)
  set lam : Idx (p := p) (q := q) K L a b → ℂ := fun i => 𝓕 k₁ (i.1 : ZMod (p ^ K)) * 𝓕 k₂ (i.2 : ZMod (q ^ L))
  have hB : ∀ i, (B i : ZMod (p ^ K) × ZMod (q ^ L) → ℂ) = Psi ((i.1 : ZMod (p ^ K)), (i.2 : ZMod (q ^ L))) := by
    intro i; simp [B, basis12]
  have hT : ∀ i, T12 (p := p) (q := q) K L a b (by omega) (by omega) k₁ k₂ (B i) = lam i • B i := by
    intro i
    apply Subtype.ext
    show conv (tens k₁ k₂) (B i : ZMod (p ^ K) × ZMod (q ^ L) → ℂ) = lam i • (B i : ZMod (p ^ K) × ZMod (q ^ L) → ℂ)
    rw [hB, conv_tens_Psi]
  have hmat : LinearMap.toMatrix B B (T12 (p := p) (q := q) K L a b (by omega) (by omega) k₁ k₂)
      = Matrix.diagonal lam := by
    ext i j
    rw [LinearMap.toMatrix_apply, hT, _root_.map_smul, B.repr_self, Finsupp.smul_apply, Matrix.diagonal_apply,
      Finsupp.single_apply]
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [← LinearMap.charpoly_toMatrix _ B, hmat, Matrix.charpoly_diagonal, Fintype.prod_prod_type]
  rw [← Finset.prod_coe_sort (Tset (p := p) K a)]
  apply Finset.prod_congr rfl; intro s _
  exact Finset.prod_coe_sort (Tset (p := q) L b) (fun t => X - C (𝓕 k₁ (s : ZMod (p ^ K)) * 𝓕 k₂ t))

end Ket

end PAG.Part121

#print axioms PAG.Part121.conv_chr
#print axioms PAG.Part121.sum_chr_mul
#print axioms PAG.Part121.sum_Psi_mul
#print axioms PAG.Part121.Psi_linearIndependent
#print axioms PAG.Part121.conv_tens_Psi
#print axioms PAG.Part121.Psi_mem
#print axioms PAG.Part121.card_Idx
#print axioms PAG.Part121.charpoly_T12
