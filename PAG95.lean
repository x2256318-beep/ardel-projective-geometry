/-
  PAG 2.0 Part 91（2026-10-19）— 次元の数え上げ: #{双対殻 a の原始ケット} + 1 = |S_a|
  任意の素数、a ≤ K、双対殻 a の原始ケットが少なくとも一つあるとき
  1. 台 T_a = {t | 𝓕ε_a(t) = 1} の大きさは |S_a|
  2. finrank V_a = |S_a|（𝓕 による V_a ≃ (T_a → ℂ)）
  3. B_a は線形独立（直交性から）、finrank V_a = #B_a
  4. 系: Σ_{c=1}^{K−a} #{法 p^c の原始指標} + 1 = |S_a| = p^(K−1−a)(p−1)（原始指標の個数の幾何的導出）
-/
import PAG94

namespace PAG.Part95

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part59
  PAG.Part89 PAG.Part90 PAG.Part93

variable {p : ℕ} [hp : Fact p.Prime]

/-- 台 T_a。 -/
noncomputable def Tset (K a : ℕ) : Finset (ZMod (p ^ K)) :=
  Finset.univ.filter (fun t => 𝓕 (eps (p := p) K a) t = 1)

/-- **台の大きさ**: #T_a = |S_a|。 -/
theorem card_Tset (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    (Tset (p := p) K a).card = sz p K a := by
  obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hk
  have hsz : (sz p K (K - (n + 1) - w) : ℝ) ≠ 0 := by
    have : 0 < sz p K (K - (n + 1) - w) := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    exact_mod_cast this.ne'
  have hpK : (p : ℝ) ^ K ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hk2 : ∀ t, Complex.normSq (𝓕 (ket K w (n + 1) h χ) t)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) *
          (if 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 then 1 else 0) := by
    intro t
    rcases normSq_dft_ket_cases K w n h χ hχ t with ⟨h0e, h0⟩ | ⟨h1e, h1⟩
    · have h0' : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 0 := h0e
      rw [h0]; simp [h0']
    · have h1' : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 := h1e
      rw [h1]; simp [h1']
  have P2 := PAG.Part39.plancherel_normSq (ket K w (n + 1) h χ)
  rw [PAG.Part39.norm_ket K w n h χ hχ, mul_one] at P2
  simp_rw [hk2] at P2
  rw [← Finset.mul_sum, Finset.sum_boole] at P2
  have hc : ((Tset (p := p) K (K - (n + 1) - w)).card : ℝ) = (sz p K (K - (n + 1) - w) : ℝ) := by
    unfold Tset
    push_cast at P2
    rw [div_mul_eq_mul_div, div_eq_iff hsz] at P2
    exact mul_left_cancel₀ hpK (by rw [P2])
  exact_mod_cast hc

/-- V_a（span B_a）。 -/
noncomputable abbrev Va (K a : ℕ) : Submodule ℂ (ZMod (p ^ K) → ℂ) := Submodule.span ℂ (Bset (p := p) K a)

/-- 𝓕 の T_a への制限（V_a 上）。 -/
noncomputable def Phi (K a : ℕ) : Va (p := p) K a →ₗ[ℂ] (Tset (p := p) K a → ℂ) where
  toFun f := fun t => 𝓕 (f : ZMod (p ^ K) → ℂ) t
  map_add' f g := by funext t; simp [map_add]
  map_smul' c f := by funext t; simp

theorem dft_eps_conv (K a : ℕ) (f : ZMod (p ^ K) → ℂ) (t : ZMod (p ^ K)) :
    𝓕 (conv (eps (p := p) K a) f) t = 𝓕 (eps (p := p) K a) t * 𝓕 f t := by
  rw [PAG.Part16.dft_conv, Pi.mul_apply]

theorem Phi_bijective (K a : ℕ) (ha : a ≤ K) : Function.Bijective (Phi (p := p) K a) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rcases f with ⟨f, hfm⟩
    have hfix := (Va_eq_span K a ha f).mpr hfm
    have h0 : 𝓕 f = 0 := by
      funext t
      rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a ha t with h0 | h1
      · have := congrArg (fun g => 𝓕 g t) hfix
        simp only [dft_eps_conv] at this
        rw [h0, zero_mul] at this
        exact this.symm
      · have := congrFun (LinearMap.mem_ker.mp hf) ⟨t, by simp [Tset, h1]⟩
        exact this
    have : f = 0 := (ZMod.dft (N := p ^ K) (E := ℂ)).injective (by rw [h0, map_zero])
    simp [this]
  · intro g
    classical
    let F : ZMod (p ^ K) → ℂ := fun t => if h : t ∈ Tset (p := p) K a then g ⟨t, h⟩ else 0
    let f := (ZMod.dft (N := p ^ K) (E := ℂ)).symm F
    have hfF : 𝓕 f = F := by simp [f]
    have hfix : conv (eps (p := p) K a) f = f := by
      apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
      funext t
      rw [dft_eps_conv, hfF]
      by_cases ht : t ∈ Tset (p := p) K a
      · have h1 : 𝓕 (eps (p := p) K a) t = 1 := by simpa [Tset] using ht
        rw [h1, one_mul]
      · simp only [F, dite_eq_right_iff.mpr (fun h => absurd h ht), mul_zero]
    refine ⟨⟨f, (Va_eq_span K a ha f).mp hfix⟩, ?_⟩
    funext t
    show 𝓕 f t = g t
    rw [hfF]
    simp only [F]
    exact dite_eq_left_of_eq_true (eq_true t.2)

/-- **finrank V_a = #T_a**。 -/
theorem finrank_Va (K a : ℕ) (ha : a ≤ K) :
    Module.finrank ℂ (Va (p := p) K a) = (Tset (p := p) K a).card := by
  rw [(LinearEquiv.ofBijective _ (Phi_bijective (p := p) K a ha)).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]

/-! ## B_a の添字付けと線形独立性 -/

/-- 双対殻 a の原始ケットの添字（レベル n+1 と原始指標）。 -/
def J (K a : ℕ) := {x : (n : Fin K) × DirichletCharacter ℂ (p ^ ((n : ℕ) + 1)) // x.2.IsPrimitive ∧ (x.1 : ℕ) + 1 ≤ K - a}

noncomputable instance (K a : ℕ) : Fintype (J (p := p) K a) := by
  unfold J
  exact Fintype.ofFinite _

/-- 添字に対応するケット（殻 w = K − a − (n+1)）。 -/
noncomputable def ketJ (K a : ℕ) (x : J (p := p) K a) : ZMod (p ^ K) → ℂ :=
  ket K (K - a - ((x.1.1 : ℕ) + 1)) ((x.1.1 : ℕ) + 1) (by have := x.1.1.2; omega) x.1.2

/-- B_a の族（none ↦ ε_a）。 -/
noncomputable def fam (K a : ℕ) : Option (J (p := p) K a) → ZMod (p ^ K) → ℂ
  | none => eps (p := p) K a
  | some x => ketJ K a x

theorem ketJ_dual (K a : ℕ) (ha : a ≤ K) (x : J (p := p) K a) : KetDual (p := p) K a (ketJ K a x) :=
  ⟨_, _, _, x.1.2, x.2.1, by have := x.2.2; omega, rfl⟩

theorem fam_orth (K a : ℕ) (ha : a ≤ K) (i j : Option (J (p := p) K a)) (hij : i ≠ j) :
    ip (fam K a i) (fam K a j) = 0 := by
  rcases i with _ | x <;> rcases j with _ | y
  · exact absurd rfl hij
  · exact PAG.Part91.ip_eps_ket K a _ (ketJ_dual K a ha y)
  · rw [ip_conj]; simp only [fam]; rw [PAG.Part91.ip_eps_ket K a _ (ketJ_dual K a ha x), map_zero]
  · simp only [fam, ketJ]
    rcases x with ⟨⟨n, χ⟩, hχ, hn⟩
    rcases y with ⟨⟨n', χ'⟩, hχ', hn'⟩
    by_cases hnn : n = n'
    · subst hnn
      have hc : χ ≠ χ' := by
        intro e; subst e; exact hij rfl
      exact ip_ket_eq_zero_of_char_ne K _ (n : ℕ) _ χ χ' hχ hχ' hc
    · apply ip_ket_eq_zero_of_ne K _ (n : ℕ) _ (n' : ℕ) _ _ χ χ' hχ hχ'
      right; intro e; exact hnn (Fin.ext e)

theorem fam_ne_zero (K a : ℕ) (ha : a ≤ K) (i : Option (J (p := p) K a)) : fam K a i ≠ 0 := by
  rcases i with _ | x
  · exact eps_ne_zero K a
  · intro h0
    have := (ketJ_dual K a ha x).norm
    simp only [fam] at h0
    rw [h0] at this
    simp at this

theorem fam_linIndep (K a : ℕ) (ha : a ≤ K) : LinearIndependent ℂ (fam (p := p) K a) := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have e : ip (fam K a i) (∑ j ∈ s, g j • fam K a j) = ip (fam K a i) 0 := by rw [hs]
  rw [ip_sum_right, Finset.sum_eq_single i] at e
  · have hz : ip (fam K a i) (0 : ZMod (p ^ K) → ℂ) = 0 := by simp [ip]
    rw [hz] at e
    have e : g i * ip (fam K a i) (fam K a i) = 0 := e
    exact (mul_eq_zero.mp e).resolve_right (ip_self_ne_zero _ (fam_ne_zero K a ha i))
  · intro j _ hji; rw [fam_orth K a ha i j (Ne.symm hji), mul_zero]
  · intro h; exact absurd hi h

theorem range_fam (K a : ℕ) (ha : a ≤ K) : Set.range (fam (p := p) K a) = Bset (p := p) K a := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    rcases i with _ | x
    · exact Or.inr rfl
    · exact Or.inl (ketJ_dual K a ha x)
  · rintro (⟨w, n, h, χ, hχ, hd, rfl⟩ | hf)
    · refine ⟨some ⟨⟨⟨n, by omega⟩, χ⟩, hχ, by simp only; omega⟩, ?_⟩
      simp only [fam, ketJ]
      obtain rfl : w = K - a - (n + 1) := by omega
      rfl
    · exact ⟨none, (Set.mem_singleton_iff.mp hf).symm⟩

/-- **次元の数え上げ**: #J_a + 1 = |S_a|。 -/
theorem card_J_add_one (K a : ℕ) (ha : a ≤ K) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    Fintype.card (J (p := p) K a) + 1 = sz p K a := by
  have h1 := finrank_span_eq_card (fam_linIndep (p := p) K a ha)
  rw [range_fam K a ha, Fintype.card_option] at h1
  rw [← h1, finrank_Va K a ha, card_Tset K a k hk]

end PAG.Part95

#print axioms PAG.Part95.card_Tset
#print axioms PAG.Part95.Phi_bijective
#print axioms PAG.Part95.finrank_Va
#print axioms PAG.Part95.fam_orth
#print axioms PAG.Part95.fam_linIndep
#print axioms PAG.Part95.range_fam
#print axioms PAG.Part95.card_J_add_one
