/-
  PAG 2.0 Part 54（2026-10-19）— 指示関数との畳み込みと、族 S 全体での畳み込みの作用
  原始ケット k = |w,χ⟩（導手 p^(n+1)）、双対殻 a = K−(n+1)−w について
  1. k ⋆ ε_a = k、k ⋆ ε_b = 0（b ≠ a）
  2. P_u = Σ_{u ≤ b ≤ K} ε_b、k ⋆ P_u = [u ≤ a]·k
  3. k ⋆ ball_j = [w+n+1 ≤ j]·p^(K−j)·k
  4. 1_{S_v} = ball_v − ball_{v+1}、k ⋆ 1_{S_v} = ([w+n+1 ≤ v]p^(K−v) − [w+n+1 ≤ v+1]p^(K−v−1))·k
  5. ball_i ⋆ ball_j ∈ IndSpan、1_{S_v} ⋆ 1_{S_u} ∈ IndSpan
  6. 族 S の任意の 2 元の畳み込みは 0、S の一つの元の 0 でない定数倍、または IndSpan の元
-/
import PAG57

namespace PAG.Part58

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57

variable {p : ℕ} [hp : Fact p.Prime]

local notation "ε" => PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) _)

/-! ## 畳み込みの線形性 -/

theorem conv_sum_right {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (f : ZMod N → ℂ) (g : ι → ZMod N → ℂ) :
    conv f (∑ i ∈ s, g i) = ∑ i ∈ s, conv f (g i) := by
  rw [← convL_apply, map_sum]; rfl

theorem conv_sub_right {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv f (g - h) = conv f g - conv f h := by
  rw [← convL_apply, map_sub]; rfl

theorem conv_smul_right' {N : ℕ} [NeZero N] (a : ℂ) (f g : ZMod N → ℂ) : conv f (a • g) = a • conv f g :=
  PAG.Part52.conv_smul_right a g f

/-! ## ケットと ε・球平均の畳み込み -/

/-- k ⋆ ε_a = k（a はケットの双対殻）。 -/
theorem ket_conv_eps_self (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w))
      = ket K w (n + 1) hK χ := by
  apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv]
  funext k
  rw [Pi.mul_apply]
  rcases PAG.Part31.dft_eps_zero_or_one (p := p) K (K - (n + 1) - w) (by omega) k with h0 | h1
  · have e := PAG.Part41.normSq_dft_ket_eq K w n hK χ hχ k
    rw [h0, mul_zero] at e
    have : 𝓕 (ket K w (n + 1) hK χ) k = 0 := Complex.normSq_eq_zero.mp (by exact_mod_cast e)
    rw [this, zero_mul]
  · rw [h1, mul_one]

/-- k ⋆ ε_b = 0（b ≠ a）。 -/
theorem ket_conv_eps_ne (K w n b : ℕ) (hK : w + (n + 1) ≤ K) (hb : b ≤ K) (hne : b ≠ K - (n + 1) - w)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K b) = 0 := by
  apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, map_zero]
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  rcases PAG.Part31.dft_eps_zero_or_one (p := p) K (K - (n + 1) - w) (by omega) k with h0 | h1
  · have e := PAG.Part41.normSq_dft_ket_eq K w n hK χ hχ k
    rw [h0, mul_zero] at e
    have : 𝓕 (ket K w (n + 1) hK χ) k = 0 := Complex.normSq_eq_zero.mp (by exact_mod_cast e)
    rw [this, zero_mul]
  · have e := PAG.Part41.dft_eps_mul_eq_zero (p := p) K _ _ (by omega) hb (Ne.symm hne) k
    rw [h1, one_mul] at e
    rw [e, mul_zero]

omit hp in
/-- 球平均は ε の和: P_u = Σ_{u ≤ b ≤ K} ε_b。 -/
theorem Pavg_eq_sum_eps (K u : ℕ) (hu : u ≤ K) :
    PAG.Part28.Pavg (p := p) K u = ∑ b ∈ Ico u (K + 1), PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K b := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, t ≤ K ∧ u = K - t := ⟨K - u, by omega, by omega⟩
  clear hu
  induction t with
  | zero =>
    rw [Nat.sub_zero, Nat.Ico_succ_singleton, Finset.sum_singleton]
    unfold PAG.Part14.epsBall; rw [ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl K))]
  | succ t ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show K - (t + 1) + 1 = K - t by omega, ← ih (by omega)]
    unfold PAG.Part14.epsBall
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), show K - (t + 1) + 1 = K - t by omega, sub_add_cancel]

/-- **k ⋆ P_u = [u ≤ a]·k**。 -/
theorem ket_conv_Pavg (K w n u : ℕ) (hK : w + (n + 1) ≤ K) (hu : u ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (PAG.Part28.Pavg (p := p) K u)
      = if u ≤ K - (n + 1) - w then ket K w (n + 1) hK χ else 0 := by
  rw [Pavg_eq_sum_eps K u hu, conv_sum_right]
  rw [Finset.sum_congr rfl (fun b hb => (show conv (ket K w (n + 1) hK χ)
      (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K b)
      = if K - (n + 1) - w = b then ket K w (n + 1) hK χ else 0 from by
        split_ifs with h
        · subst h; exact ket_conv_eps_self K w n hK χ hχ
        · exact ket_conv_eps_ne K w n b hK (by have := (mem_Ico.mp hb).2; omega) (Ne.symm h) χ hχ))]
  rw [Finset.sum_ite_eq]
  congr 1
  simp only [mem_Ico]
  apply propext
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega⟩

/-- ball_j = p^(K−j)·P_(K−j)。 -/
theorem ball_eq_Pavg (K j : ℕ) (hj : j ≤ K) :
    PAG.Part22.ball (p := p) K j = ((p : ℂ) ^ (K - j)) • PAG.Part28.Pavg (p := p) K (K - j) := by
  unfold PAG.Part28.Pavg
  rw [show K - (K - j) = j by omega, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)),
    one_smul]

/-- **k ⋆ ball_j = [w+n+1 ≤ j]·p^(K−j)·k**。 -/
theorem ket_conv_ball (K w n j : ℕ) (hK : w + (n + 1) ≤ K) (hj : j ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (PAG.Part22.ball (p := p) K j)
      = (if w + (n + 1) ≤ j then (p : ℂ) ^ (K - j) else 0) • ket K w (n + 1) hK χ := by
  rw [ball_eq_Pavg K j hj, conv_smul_right', ket_conv_Pavg K w n (K - j) hK (by omega) χ hχ]
  by_cases h : w + (n + 1) ≤ j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false h), smul_zero, zero_smul]

/-- 1_{S_v} = ball_v − ball_{v+1}（v < K）。 -/
theorem shellInd_eq_ball_sub (K v : ℕ) (hv : v < K) :
    shellInd (p := p) K v hv = PAG.Part22.ball (p := p) K v - PAG.Part22.ball (p := p) K (v + 1) := by
  funext x
  rw [Pi.sub_apply]
  by_cases hx : x = 0
  · subst hx; rw [shellInd_zero, PAG.Part49.ball_apply_zero, PAG.Part49.ball_apply_zero, sub_self]
  · obtain ⟨t, ht, y, hy, rfl⟩ := exists_shell K x hx
    rw [shellInd_apply K v t hv ht y hy, ball_apply_shell K v t ht y hy, ball_apply_shell K (v + 1) t ht y hy]
    by_cases h1 : v = t
    · subst h1; simp
    · by_cases h2 : v ≤ t
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_left_of_eq_true _ _ (eq_true (by omega)), sub_self]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false (by omega)), sub_self]

/-- **k ⋆ 1_{S_v} はケットの定数倍**。 -/
theorem ket_conv_shellInd (K w n v : ℕ) (hK : w + (n + 1) ≤ K) (hv : v < K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    conv (ket K w (n + 1) hK χ) (shellInd (p := p) K v hv)
      = ((if w + (n + 1) ≤ v then (p : ℂ) ^ (K - v) else 0)
          - (if w + (n + 1) ≤ v + 1 then (p : ℂ) ^ (K - (v + 1)) else 0)) • ket K w (n + 1) hK χ := by
  rw [shellInd_eq_ball_sub K v hv, conv_sub_right, ket_conv_ball K w n v hK hv.le χ hχ,
    ket_conv_ball K w n (v + 1) hK hv χ hχ, sub_smul]

/-! ## 指示関数同士 -/

/-- ball_i ⋆ ball_j は球の定数倍、とくに IndSpan に入る。 -/
theorem ball_conv_ball_mem (K i j : ℕ) (hi : i ≤ K) (hj : j ≤ K) :
    conv (PAG.Part22.ball (p := p) K i) (PAG.Part22.ball (p := p) K j) ∈ IndSpan (p := p) K := by
  rw [ball_eq_Pavg K i hi, ball_eq_Pavg K j hj, conv_smul_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases le_total (K - i) (K - j) with h | h
  · rw [PAG.Part29.Pavg_absorb K _ _ h (by omega), ← inv_smul_smul₀ (pow_ne_zero (K - j)
      (by exact_mod_cast hp.out.ne_zero : (p : ℂ) ≠ 0)) (PAG.Part28.Pavg (p := p) K (K - j)), ← ball_eq_Pavg K j hj]
    exact Submodule.smul_mem _ _ (ball_mem K j)
  · rw [conv_comm, PAG.Part29.Pavg_absorb K _ _ h (by omega), ← inv_smul_smul₀ (pow_ne_zero (K - i)
      (by exact_mod_cast hp.out.ne_zero : (p : ℂ) ≠ 0)) (PAG.Part28.Pavg (p := p) K (K - i)), ← ball_eq_Pavg K i hi]
    exact Submodule.smul_mem _ _ (ball_mem K i)

/-- 1_{S_v} ⋆ 1_{S_u} ∈ IndSpan。 -/
theorem shellInd_conv_mem (K v u : ℕ) (hv : v < K) (hu : u < K) :
    conv (shellInd (p := p) K v hv) (shellInd (p := p) K u hu) ∈ IndSpan (p := p) K := by
  rw [shellInd_eq_ball_sub K v hv, shellInd_eq_ball_sub K u hu, conv_sub_right, conv_comm (_ - _), conv_sub_right,
    conv_comm (_ - _), conv_sub_right]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ (ball_conv_ball_mem K u v hu.le hv.le)
    (ball_conv_ball_mem K u (v + 1) hu.le hv)) (Submodule.sub_mem _ (ball_conv_ball_mem K (u + 1) v hu hv.le)
    (ball_conv_ball_mem K (u + 1) (v + 1) hu hv))

/-! ## 族 S 全体での畳み込みの作用 -/

/-- 「0、S の一つの元の 0 でない定数倍、または IndSpan の元」という性質。 -/
def Good (K : ℕ) (F : ZMod (p ^ K) → ℂ) : Prop :=
  F = 0 ∨ (∃ b ∈ family (p := p) K, ∃ C : ℂ, C ≠ 0 ∧ F = C • b) ∨ F ∈ IndSpan (p := p) K

theorem good_smul_ket (K w c : ℕ) (h : w + c ≤ K) (hc : 1 ≤ c) (ψ : DirichletCharacter ℂ (p ^ c))
    (hψ : ψ.IsPrimitive) (C : ℂ) : Good (p := p) K (C • ket K w c h ψ) := by
  by_cases hC : C = 0
  · left; rw [hC, zero_smul]
  · right; left; exact ⟨_, Or.inl ⟨w, c, h, hc, ψ, hψ, rfl⟩, C, hC, rfl⟩

theorem good_of_mem_family (K : ℕ) (b : ZMod (p ^ K) → ℂ) (hb : b ∈ family (p := p) K) : Good (p := p) K b := by
  right; left; exact ⟨b, hb, 1, one_ne_zero, (one_smul _ _).symm⟩

theorem good_ket_ket (K w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + c₁ ≤ K) (h₂ : w₂ + c₂ ≤ K) (hc₁ : 1 ≤ c₁) (hc₂ : 1 ≤ c₂)
    (χ₁ : DirichletCharacter ℂ (p ^ c₁)) (χ₂ : DirichletCharacter ℂ (p ^ c₂))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    Good (p := p) K (conv (ket K w₁ c₁ h₁ χ₁) (ket K w₂ c₂ h₂ χ₂)) := by
  obtain ⟨n₁, rfl⟩ : ∃ n, c₁ = n + 1 := ⟨c₁ - 1, by omega⟩
  obtain ⟨n₂, rfl⟩ : ∃ n, c₂ = n + 1 := ⟨c₂ - 1, by omega⟩
  exact conv_ket_action K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂

theorem good_ket_shellInd (K w c v : ℕ) (h : w + c ≤ K) (hc : 1 ≤ c) (hv : v < K)
    (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    Good (p := p) K (conv (ket K w c h χ) (shellInd (p := p) K v hv)) := by
  obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
  rw [ket_conv_shellInd K w n v h hv χ hχ]
  exact good_smul_ket K w (n + 1) h hc χ hχ _

/-- **族 S の任意の 2 元の畳み込みは Good**。 -/
theorem conv_family_good (K : ℕ) (f g : ZMod (p ^ K) → ℂ) (hf : f ∈ family (p := p) K) (hg : g ∈ family (p := p) K) :
    Good (p := p) K (conv f g) := by
  rcases hf with ⟨w, c, h, hc, ψ, hψ, rfl⟩ | ⟨v, hv, rfl⟩ | rfl
  · rcases hg with ⟨w', c', h', hc', ψ', hψ', rfl⟩ | ⟨v', hv', rfl⟩ | rfl
    · exact good_ket_ket K w c w' c' h h' hc hc' ψ ψ' hψ hψ'
    · exact good_ket_shellInd K w c v' h hc hv' ψ hψ
    · rw [conv_comm, conv_delta]; exact good_of_mem_family K _ (Or.inl ⟨w, c, h, hc, ψ, hψ, rfl⟩)
  · rcases hg with ⟨w', c', h', hc', ψ', hψ', rfl⟩ | ⟨v', hv', rfl⟩ | rfl
    · rw [conv_comm]; exact good_ket_shellInd K w' c' v h' hc' hv ψ' hψ'
    · right; right; exact shellInd_conv_mem K v v' hv hv'
    · rw [conv_comm, conv_delta]; exact good_of_mem_family K _ (Or.inr (Or.inl ⟨v, hv, rfl⟩))
  · rw [conv_delta]; exact good_of_mem_family K g hg

end PAG.Part58

#print axioms PAG.Part58.conv_sum_right
#print axioms PAG.Part58.conv_sub_right
#print axioms PAG.Part58.conv_smul_right'
#print axioms PAG.Part58.ket_conv_eps_self
#print axioms PAG.Part58.ket_conv_eps_ne
#print axioms PAG.Part58.Pavg_eq_sum_eps
#print axioms PAG.Part58.ket_conv_Pavg
#print axioms PAG.Part58.ball_eq_Pavg
#print axioms PAG.Part58.ket_conv_ball
#print axioms PAG.Part58.shellInd_eq_ball_sub
#print axioms PAG.Part58.ket_conv_shellInd
#print axioms PAG.Part58.ball_conv_ball_mem
#print axioms PAG.Part58.shellInd_conv_mem
#print axioms PAG.Part58.Good
#print axioms PAG.Part58.good_smul_ket
#print axioms PAG.Part58.good_of_mem_family
#print axioms PAG.Part58.good_ket_ket
#print axioms PAG.Part58.good_ket_shellInd
#print axioms PAG.Part58.conv_family_good
