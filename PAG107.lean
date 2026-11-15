/-
  PAG 2.0 Part 103（2026-10-19）— L²(ℤ/p^{K+1}) = π^* L²(ℤ/p^K) ⊕ V_0^{(K+1)}、および J : V_a ≅ V_{a+1}
  任意の素数で
  1. ε_0^{(K+1)} ⋆ π^* f = 0（引き戻しは双対殻 0 の成分をもたない）
  2. g が引き戻し ⟺ ε_0^{(K+1)} ⋆ g = 0（次元の比較: p^K = p^{K+1} − |S_0^{(K+1)}|）
  3. V_{a+1}^{(K+1)} = π^* V_a^{(K)}（任意の a ≤ K。J は同型）
-/
import PAG106

namespace PAG.Part107

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part58 PAG.Part59 PAG.Part89 PAG.Part93 PAG.Part95
  PAG.Part105

variable {p : ℕ} [hp : Fact p.Prime]

/-- 引き戻しの線形写像。 -/
noncomputable def pullL (K : ℕ) : (ZMod (p ^ K) → ℂ) →ₗ[ℂ] (ZMod (p ^ (K + 1)) → ℂ) where
  toFun := pull (p := p) K
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pull_injective (K : ℕ) : Function.Injective (pull (p := p) K) := by
  intro f g h
  funext x
  obtain ⟨y, rfl⟩ := proj_surjective (p := p) K x
  exact congrFun h y

/-- δ₀ の引き戻し = p·P_1^{(K+1)}。 -/
theorem pull_delta (K : ℕ) :
    pull (p := p) K (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) = (p : ℂ) • PAG.Part28.Pavg (p := p) (K + 1) 1 := by
  rw [delta_eq_ball, pull_ball K K le_rfl, ball_eq_Pavg (K + 1) K (by omega), show K + 1 - K = 1 by omega, pow_one]

/-- **1. 引き戻しは双対殻 0 の成分をもたない**。 -/
theorem eps0_pull (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    conv (eps (p := p) (K + 1) 0) (pull (p := p) K f) = 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e := conv_pull (p := p) K (Pi.single 0 1) f
  rw [PAG.Part57.conv_delta, pull_delta, conv_comm, PAG.Part58.conv_smul_right', conv_comm] at e
  have e' : conv (PAG.Part28.Pavg (p := p) (K + 1) 1) (pull (p := p) K f) = pull (p := p) K f :=
    smul_right_injective _ hp0 e
  rw [← e', ← conv_assoc', Pavg_eq_sum_eps (K + 1) 1 (by omega), conv_sum_right]
  have hz : ∀ b ∈ Ico 1 (K + 1 + 1), conv (eps (p := p) (K + 1) 0)
      (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) (K + 1)) (K + 1) b) = 0 := by
    intro b hb
    have := eps_conv_eps (p := p) (K + 1) 0 b (by omega) (by have := (mem_Ico.mp hb).2; omega)
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := (mem_Ico.mp hb).1; omega))] at this
    exact this
  rw [Finset.sum_eq_zero hz]
  funext x; simp [conv]

/-- 射影 E_0 = ε_0 ⋆ ・。 -/
noncomputable def E0 (K : ℕ) : (ZMod (p ^ (K + 1)) → ℂ) →ₗ[ℂ] (ZMod (p ^ (K + 1)) → ℂ) :=
  convL (eps (p := p) (K + 1) 0)

theorem range_E0 (K : ℕ) : LinearMap.range (E0 (p := p) K) = Va (p := p) (K + 1) 0 := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (Va_eq_span (K + 1) 0 (by omega) _).mp (PAG.Part94.comp_mem (K + 1) 0 (by omega) g)
  · intro hf
    exact ⟨f, (Va_eq_span (K + 1) 0 (by omega) f).mpr hf⟩

/-- **2. 引き戻しの像 = ker E_0**。 -/
theorem range_pull_eq_ker (K : ℕ) (hK : 1 ≤ K) : LinearMap.range (pullL (p := p) K) = LinearMap.ker (E0 (p := p) K) := by
  have hle : LinearMap.range (pullL (p := p) K) ≤ LinearMap.ker (E0 (p := p) K) := by
    rintro g ⟨f, rfl⟩
    exact eps0_pull K f
  apply Submodule.eq_of_le_of_finrank_eq hle
  -- 次元: finrank range pull = p^K、finrank ker E0 = p^{K+1} − |S_0|
  have h1 : Module.finrank ℂ (LinearMap.range (pullL (p := p) K)) = p ^ K := by
    rw [LinearMap.finrank_range_of_inj (pull_injective K), Module.finrank_fintype_fun_eq_card, ZMod.card]
  have h2 := LinearMap.finrank_range_add_finrank_ker (E0 (p := p) K)
  rw [range_E0, Module.finrank_fintype_fun_eq_card, ZMod.card] at h2
  have hdim : Module.finrank ℂ (Va (p := p) (K + 1) 0) = sz p (K + 1) 0 := by
    rw [finrank_Va (K + 1) 0 (by omega)]
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨k, hk⟩ := PAG.Part96.exists_ket_two (K + 1) 0 (by omega)
      exact card_Tset (K + 1) 0 k hk
    · obtain ⟨k, hk⟩ := PAG.Part96.exists_ket_odd hp2 (K + 1) 0 (by omega)
      exact card_Tset (K + 1) 0 k hk
  rw [hdim] at h2
  rw [h1]
  unfold sz at h2
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  rw [show K + 1 - 1 - 0 = K by omega] at h2
  have : p ^ (K + 1) = p ^ K * (p - 1) + p ^ K := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  omega

/-- π^*(ε_a ⋆ f) = ε_{a+1} ⋆ π^* f。 -/
theorem pull_eps_conv (K a : ℕ) (ha : a ≤ K) (f : ZMod (p ^ K) → ℂ) :
    pull (p := p) K (conv (eps (p := p) K a) f) = conv (eps (p := p) (K + 1) (a + 1)) (pull (p := p) K f) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e := conv_pull (p := p) K (eps (p := p) K a) f
  rw [pull_eps K a ha, conv_comm, PAG.Part58.conv_smul_right', conv_comm] at e
  exact (smul_right_injective _ hp0 e).symm

/-- **3. V_{a+1}^{(K+1)} = π^* V_a^{(K)}**（J は同型）。 -/
theorem Va_succ_eq_pull (K a : ℕ) (hK : 1 ≤ K) (ha : a ≤ K) (g : ZMod (p ^ (K + 1)) → ℂ) :
    conv (eps (p := p) (K + 1) (a + 1)) g = g ↔
      ∃ f, conv (eps (p := p) K a) f = f ∧ pull (p := p) K f = g := by
  constructor
  · intro hg
    have h0 : g ∈ LinearMap.ker (E0 (p := p) K) := by
      show conv (eps (p := p) (K + 1) 0) g = 0
      rw [← hg, ← conv_assoc', eps_conv_eps (K + 1) 0 (a + 1) (by omega) (by omega),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      funext x; simp [conv]
    rw [← range_pull_eq_ker K hK] at h0
    obtain ⟨f, hf⟩ := h0
    have hf' : pull (p := p) K f = g := hf
    refine ⟨conv (eps (p := p) K a) f, PAG.Part94.comp_mem K a ha f, ?_⟩
    rw [pull_eps_conv K a ha, hf', hg]
  · rintro ⟨f, hf, rfl⟩
    exact pull_Va K a ha f hf

end PAG.Part107

#print axioms PAG.Part107.pull_injective
#print axioms PAG.Part107.pull_delta
#print axioms PAG.Part107.eps0_pull
#print axioms PAG.Part107.range_E0
#print axioms PAG.Part107.range_pull_eq_ker
#print axioms PAG.Part107.pull_eps_conv
#print axioms PAG.Part107.Va_succ_eq_pull
