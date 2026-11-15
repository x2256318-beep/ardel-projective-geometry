/-
  PAG 2.0 Part 83（2026-10-19）— 奇素数の乗積表の完全形（全原始指標、添字によらない形）
  1. 忠実な指標 χ₀（法 p^(c'+1)）について、任意の指標は χ₀^j と書ける
  2. 奇素数の混合（全原始指標、法 p を含む）: w₁ < w₂（双対殻共通）なら F = C·|w₁, ψ⟩
  3. 奇素数の乗積表（一つの選言）: (0) ∨ (M) ∨ (M') ∨ (同じ殻・同じレベル)
  4. 同じ殻・同じレベル: (χ₂ = χ₁⁻¹ ∧ F = χ₁(−1)·ballB) ∨ (χ₂ ≠ χ₁⁻¹ ∧ F = C·|u,m,ψ⟩、u+m = w+c)
-/
import PAG86

namespace PAG.Part87

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part48 PAG.Part61 PAG.Part67 PAG.Part68
  PAG.Part69 PAG.Part70 PAG.Part73 PAG.Part82 PAG.Part86

variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
include hp2

/-- **忠実な指標は指標群を生成する**。 -/
theorem faithful_generates (c' : ℕ) (χ₀ : DirichletCharacter ℂ (p ^ (c' + 1))) (hf : Faithful χ₀)
    (χ : DirichletCharacter ℂ (p ^ (c' + 1))) : ∃ j, χ = χ₀ ^ j := by
  have hζ : IsPrimitiveRoot (χ₀ (gen c' hp2)) (phi (p := p) c') := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, ← orderOf_gen c' hp2, pow_orderOf_eq_one, Units.val_one, map_one]
    · intro l hl
      rw [← map_pow, ← Units.val_pow_eq_pow_val] at hl
      rw [← orderOf_gen c' hp2]
      exact orderOf_dvd_of_pow_eq_one (hf _ hl)
  have h1 : χ (gen c' hp2) ^ phi (p := p) c' = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← orderOf_gen c' hp2, pow_orderOf_eq_one, Units.val_one, map_one]
  have : NeZero (phi (p := p) c') := ⟨(phi_pos (p := p) c').ne'⟩
  obtain ⟨j, -, hz⟩ := hζ.eq_pow_of_pow_eq_one h1
  exact ⟨j, char_ext_gen c' hp2 _ _ (by rw [MulChar.pow_apply_coe, hz])⟩

/-- **奇素数の混合（全原始指標）**。 -/
theorem odd_mixed_general (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (hw : w₁ < w₂) :
    ∃ ψ : DirichletCharacter ℂ (p ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) ∧
      conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • ket K w₁ (n₁ + 1) h₁ ψ := by
  have hlt : n₂ < n₁ := by omega
  have hn₁ : 1 ≤ n₁ := by omega
  have hf₁ := omegaLow_isFaithful hp2 n₁ n₁ le_rfl
  have hf₂ := omegaLow_isFaithful hp2 n₁ n₂ hlt.le
  obtain ⟨j₁, rfl⟩ := faithful_generates hp2 n₁ _ hf₁ χ₁
  obtain ⟨j₂, rfl⟩ := faithful_generates hp2 n₂ _ hf₂ χ₂
  have hj₁ : ¬ p ∣ j₁ := (faithful_pow_prim_iff hn₁ _ hf₁ j₁).mp hχ₁
  obtain rfl : w₂ = w₁ + (n₁ - n₂) := by omega
  obtain ⟨C, hC, e⟩ := table_mixed hp2 n₁ K w₁ n₁ n₂ hn₁ hlt le_rfl h₁ h₂ j₁ j₂ hj₁ hχ₂
  refine ⟨_, ?_, C, hC, e⟩
  rw [faithful_pow_prim_iff hn₁ _ hf₁]
  intro h
  apply hj₁
  have hpr : p ∣ p ^ (n₁ - n₂) * j₂ := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
  exact (Nat.dvd_add_right hpr).mp (by rwa [add_comm] at h)

/-- **奇素数の乗積表（全原始指標、一つの選言）**。 -/
theorem odd_table_general (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂)
    (K - (n₁ + 1) - w₁ ≠ K - (n₂ + 1) - w₂ ∧ F = 0) ∨
    (w₁ < w₂ ∧ ∃ ψ : DirichletCharacter ℂ (p ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₁ + 1) - w₁) : ℝ) ∧ F = C • ket K w₁ (n₁ + 1) h₁ ψ) ∨
    (w₂ < w₁ ∧ ∃ ψ : DirichletCharacter ℂ (p ^ (n₂ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n₂ + 1) - w₂) : ℝ) ∧ F = C • ket K w₂ (n₂ + 1) h₂ ψ) ∨
    (w₁ = w₂ ∧ n₁ = n₂) := by
  intro F
  by_cases hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂
  swap
  · exact Or.inl ⟨hab, conv_ket_eq_zero K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab⟩
  rcases lt_trichotomy w₁ w₂ with hw | hw | hw
  · exact Or.inr (Or.inl ⟨hw, odd_mixed_general hp2 K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ hab hw⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨hw, by omega⟩))
  · refine Or.inr (Or.inr (Or.inl ⟨hw, ?_⟩))
    obtain ⟨ψ, hψ, C, hC, e⟩ := odd_mixed_general hp2 K w₂ n₂ w₁ n₁ h₂ h₁ χ₂ χ₁ hχ₂ hχ₁ hab.symm hw
    exact ⟨ψ, hψ, C, hC, by rw [show F = _ from conv_comm _ _]; exact e⟩

/-- **奇素数・同じ殻・同じレベル（全原始指標）**。 -/
theorem odd_same_shell_general (K w n : ℕ) (h : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    let F := conv (ket K w (n + 1) h χ₁) (ket K w (n + 1) h χ₂)
    (χ₂ = χ₁⁻¹ ∧ F = χ₁ (-1) • ballB (p := p) K w n) ∨
    (χ₂ ≠ χ₁⁻¹ ∧ ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        F = C • ket K u (m + 1) hu ψ ∧ u + (m + 1) = w + (n + 1)) := by
  intro F
  by_cases hinv : χ₂ = χ₁⁻¹
  · exact Or.inl ⟨hinv, inv_pair_ballB K w n h χ₁ χ₂ hχ₁ hinv⟩
  refine Or.inr ⟨hinv, ?_⟩
  suffices H : ∃ u m : ℕ, ∃ hu : u + (m + 1) ≤ K, ∃ ψ : DirichletCharacter ℂ (p ^ (m + 1)), ψ.IsPrimitive ∧
      ∃ C : ℂ, Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
        F = C • ket K u (m + 1) hu ψ by
    obtain ⟨u, m, hu, ψ, hψ, C, hC, e⟩ := H
    exact ⟨u, m, hu, ψ, hψ, C, hC, e,
      PAG.Part78.dual_shell_conservation_add K w n w n h h χ₁ χ₂ hχ₁ hχ₂ rfl u m hu ψ hψ C e⟩
  rcases Nat.lt_or_ge n 1 with hn | hn
  · -- レベル 1（法 p）
    obtain rfl : n = 0 := by omega
    have hf := omegaLow_isFaithful hp2 0 0 le_rfl
    obtain ⟨j₁, rfl⟩ := faithful_generates hp2 0 _ hf χ₁
    obtain ⟨j₂, rfl⟩ := faithful_generates hp2 0 _ hf χ₂
    have hj₁ := (PAG.Part74.levelp_prim_iff hp2 0 j₁).mp hχ₁
    have hj₂ := (PAG.Part74.levelp_prim_iff hp2 0 j₂).mp hχ₂
    have hφ : ¬ phi (p := p) 0 ∣ j₁ + j₂ := fun hB =>
      hinv ((PAG.Part84.levelp_three_equiv hp2 0 K w h j₁ j₂ hj₁ hj₂).2.mp hB)
    obtain ⟨C, hC, e⟩ := PAG.Part74.levelp_A hp2 0 K w h j₁ j₂ hj₁ hj₂ hφ
    exact ⟨w, 0, h, _, (PAG.Part74.levelp_prim_iff hp2 0 _).mpr hφ, C, hC, e⟩
  · -- レベル 2 以上（塔）
    have hf := omegaLow_isFaithful hp2 n n le_rfl
    obtain ⟨j₁, rfl⟩ := faithful_generates hp2 n _ hf χ₁
    obtain ⟨j₂, rfl⟩ := faithful_generates hp2 n _ hf χ₂
    have hj₁ : ¬ p ∣ j₁ := (faithful_pow_prim_iff hn _ hf j₁).mp hχ₁
    have hj₂ : ¬ p ∣ j₂ := (faithful_pow_prim_iff hn _ hf j₂).mp hχ₂
    have hT := odd_same_shell_table hp2 n K w n hn le_rfl h j₁ j₂ hj₁ hj₂
    simp only at hT
    rcases hT with ⟨hD, h', C, hC, e⟩ | ⟨hL, hφ, h', C, hC, e⟩ | ⟨hB, -⟩
    · have hψ' := (faithful_pow_prim_iff (c := n - padicValNat p (j₁ + j₂)) (by omega) _
        (omegaLow_isFaithful hp2 n _ (by omega)) ((j₁ + j₂) / p ^ padicValNat p (j₁ + j₂))).mpr (by
          intro hq
          have hJ : j₁ + j₂ ≠ 0 := by intro h0; apply hj₁; rw [show j₁ = 0 by omega]; exact dvd_zero p
          apply pow_succ_padicValNat_not_dvd (p := p) hJ
          have hJq := (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := j₁ + j₂))).symm
          have key : p ^ (padicValNat p (j₁ + j₂) + 1) ∣
              p ^ padicValNat p (j₁ + j₂) * ((j₁ + j₂) / p ^ padicValNat p (j₁ + j₂)) := by
            rw [pow_succ]; exact Nat.mul_dvd_mul_left _ hq
          exact dvd_trans key (dvd_of_eq hJq.symm))
      exact ⟨_, _, h', _, hψ', C, hC, e⟩
    · have hψ' := (faithful_level_p_prim_iff hp2 _ (omegaLow_isFaithful hp2 n 0 (Nat.zero_le _))
        ((j₁ + j₂) / p ^ n)).mpr (by
          intro hq
          apply hφ
          have hdvd : p ^ n ∣ j₁ + j₂ := dvd_trans (pow_dvd_pow p hL) pow_padicValNat_dvd
          rw [phi_eq n, ← Nat.mul_div_cancel' hdvd]
          exact Nat.mul_dvd_mul_left _ hq)
      exact ⟨_, 0, h', _, hψ', C, hC, e⟩
    · exfalso
      exact hinv ((odd_three_equiv hp2 n K w n hn le_rfl h j₁ j₂ hj₁ hj₂).2.mp hB)

end PAG.Part87

#print axioms PAG.Part87.faithful_generates
#print axioms PAG.Part87.odd_mixed_general
#print axioms PAG.Part87.odd_table_general
#print axioms PAG.Part87.odd_same_shell_general
