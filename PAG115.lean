/-
  PAG 2.0 Part 111（2026-10-19）— 特性多項式: T_k|_{V_a} の charpoly
  原始ケット k = |w, χ⟩（双対殻 a）、T_k = k ⋆ · を V_a に制限した自己準同型について
  1. V_a は k⋆ で不変、Φ : V_a ≃ (T_a → ℂ)（フーリエ制限）で T_k は対角作用素 diag(𝓕k|_{T_a}) と共役
  2. charpoly T_k = ∏_{t ∈ T_a} (X − 𝓕k(t))
  3. 閉じた形: charpoly T_k = (X^o − 𝓕k(t₀)^o)^{|S_a|/o}（o = ord χ、t₀ ∈ T_a は任意）
-/
import PAG114
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.FieldTheory.KummerExtension

namespace PAG.Part115

open ZMod Finset Polynomial PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime]

theorem conv_mem_Va (K a : ℕ) (ha : a ≤ K) (k f : ZMod (p ^ K) → ℂ) (hf : f ∈ Va (p := p) K a) :
    conv k f ∈ Va (p := p) K a :=
  (Va_eq_span K a ha _).mp (PAG.Part111.fix_conv _ k f ((Va_eq_span K a ha f).mpr hf))

/-- T_k を V_a に制限した自己準同型。 -/
noncomputable def Tk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) : Module.End ℂ (Va (p := p) K a) :=
  (convL k).restrict (fun f hf => conv_mem_Va K a ha k f hf)

/-- Φ の線形同型。 -/
noncomputable def PhiE (K a : ℕ) (ha : a ≤ K) : Va (p := p) K a ≃ₗ[ℂ] (Tset (p := p) K a → ℂ) :=
  LinearEquiv.ofBijective (Phi K a) (Phi_bijective K a ha)

/-- **1. 対角化**: Φ T_k Φ⁻¹ = diag(𝓕k|_{T_a})。 -/
theorem conj_Tk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) :
    (PhiE (p := p) K a ha).conj (Tk K a ha k)
      = Matrix.toLin' (Matrix.diagonal (fun t : Tset (p := p) K a => 𝓕 k (t : ZMod (p ^ K)))) := by
  apply LinearMap.ext; intro g
  obtain ⟨f, rfl⟩ := (PhiE (p := p) K a ha).surjective g
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, Matrix.toLin'_apply]
  funext t
  rw [Matrix.mulVec_diagonal]
  show 𝓕 (conv k (f : ZMod (p ^ K) → ℂ)) (t : ZMod (p ^ K)) = 𝓕 k t * 𝓕 (f : ZMod (p ^ K) → ℂ) t
  rw [PAG.Part16.dft_conv, Pi.mul_apply]

/-- **2. 特性多項式**: charpoly T_k = ∏_{t ∈ T_a} (X − 𝓕k(t))。 -/
theorem charpoly_Tk (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) :
    (Tk (p := p) K a ha k).charpoly = ∏ t ∈ Tset (p := p) K a, (X - C (𝓕 k t)) := by
  rw [← LinearEquiv.charpoly_conj (PhiE (p := p) K a ha), conj_Tk, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
  exact Finset.prod_coe_sort (Tset (p := p) K a) (fun t => X - C (𝓕 k t))

/-- **3. 閉じた形**: charpoly T_k = (X^o − 𝓕k(t₀)^o)^{|S_a|/o}。 -/
theorem charpoly_Tk_closed (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    (Tk (p := p) K (K - (n + 1) - w) (by omega) (ket K w (n + 1) h χ)).charpoly
      = (X ^ orderOf χ - C (𝓕 (ket K w (n + 1) h χ) t₀ ^ orderOf χ)) ^ (sz p K (K - (n + 1) - w) / orderOf χ) := by
  classical
  set a := K - (n + 1) - w
  set k := ket K w (n + 1) h χ
  set T := Tset (p := p) K a
  set F := fun t => 𝓕 k t
  set o := orderOf χ
  have ho : 0 < o := orderOf_pos χ
  have : NeZero o := ⟨ho.ne'⟩
  have hkd : KetDual (p := p) K a k := ⟨w, n, h, χ, hχ, rfl, rfl⟩
  -- F(t₀) ≠ 0
  have hF0 : F t₀ ≠ 0 := by
    intro h0
    have := (PAG.Part97.eigen_abs K a k hkd t₀).1 ht₀
    simp only [F] at h0
    rw [h0, map_zero] at this
    have hpos : (0 : ℝ) < (p : ℝ) ^ K / (sz p K a : ℝ) := by
      apply div_pos (pow_pos (by exact_mod_cast hp.out.pos) _)
      have : 0 < sz p K a := by
        unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
      exact_mod_cast this
    linarith
  -- F(t)/F(t₀) は 1 の o 乗根
  have hpow : ∀ t ∈ T, (F t / F t₀) ^ o = 1 := by
    intro t ht
    obtain ⟨m, hm⟩ : ∃ m, o = m + 1 := ⟨o - 1, by omega⟩
    have hχo : χ ^ (m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one χ
    have := PAG.Part98.pow_eigen_const K w (n + 1) h (by omega) χ hχ m hχo t t₀ ht ht₀
    rw [div_pow, hm]
    simp only [F]
    rw [this, div_self (pow_ne_zero _ hF0)]
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / o)
  have hω : IsPrimitiveRoot ω o := Complex.isPrimitiveRoot_exp o ho.ne'
  have hex : ∀ t ∈ T, ∃ j < o, ω ^ j = F t / F t₀ := fun t ht => hω.eq_pow_of_pow_eq_one (hpow t ht)
  let g : ZMod (p ^ K) → ℕ := fun t => if ht : t ∈ T then Classical.choose (hex t ht) else 0
  have hg : ∀ t ∈ T, g t < o ∧ F t = F t₀ * ω ^ g t := by
    intro t ht
    have hs := Classical.choose_spec (hex t ht)
    simp only [g, ht, ↓reduceDIte]
    refine ⟨hs.1, ?_⟩
    rw [hs.2]; field_simp
  have hmaps : ∀ t ∈ T, g t ∈ range o := fun t ht => mem_range.mpr (hg t ht).1
  -- ファイバーの大きさ
  have hfib : ∀ j ∈ range o, (T.filter (fun t => g t = j)).card = sz p K a / o := by
    intro j hj
    have hfilt : T.filter (fun t => g t = j) = T.filter (fun t => F t = F t₀ * ω ^ j) := by
      apply Finset.filter_congr
      intro t ht
      constructor
      · intro e; rw [← e]; exact (hg t ht).2
      · intro e
        have e2 : ω ^ g t = ω ^ j := by
          have := (hg t ht).2
          rw [this] at e
          exact mul_left_cancel₀ hF0 e
        exact hω.pow_inj (hg t ht).1 (mem_range.mp hj) e2
    rw [hfilt]
    have hm := PAG.Part103.eigen_multiplicity K w n h χ hχ t₀ ht₀ (ω ^ j)
      (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow])
    have hcard : T.card = sz p K a := card_Tset K a k hkd
    have hnat : o * (T.filter (fun t => F t = F t₀ * ω ^ j)).card = T.card := by
      exact_mod_cast hm
    rw [← hcard, ← hnat, Nat.mul_div_cancel_left _ ho]
  rw [charpoly_Tk]
  have e1 : ∏ t ∈ T, (X - C (F t)) = ∏ t ∈ T, (fun j => X - C (ω ^ j * F t₀)) (g t) := by
    apply Finset.prod_congr rfl; intro t ht
    simp only
    rw [(hg t ht).2, mul_comm]
  show ∏ t ∈ T, (X - C (F t)) = _
  rw [e1, ← Finset.prod_fiberwise_of_maps_to' hmaps (fun j => X - C (ω ^ j * F t₀))]
  simp only [Finset.prod_const]
  rw [Finset.prod_congr rfl (fun j hj => by rw [hfib j hj]), Finset.prod_pow,
    ← X_pow_sub_C_eq_prod hω ho rfl]

end PAG.Part115

#print axioms PAG.Part115.conv_mem_Va
#print axioms PAG.Part115.conj_Tk
#print axioms PAG.Part115.charpoly_Tk
#print axioms PAG.Part115.charpoly_Tk_closed
