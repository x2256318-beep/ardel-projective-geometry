/-
  PAG 2.0 Part 53（2026-10-19）— 球の分解と、原始ケットの畳み込みの基底上の作用
  1. 殻の指示関数の値: 1_{S_w}(ι_v y) = [w = v]（y 単数）
  2. 球の分解: ball_j = Σ_{j ≤ w < K} 1_{S_w} + δ₀（j ≤ K）
  3. 球の差 ballB は「指示関数と δ₀ の張る空間」IndSpan に入る
  4. 原始ケットの組の畳み込みは 0、一つの原始ケット（∈ S）の定数倍、または IndSpan の元
  5. δ₀ は畳み込みの単位元
-/
import PAG56

namespace PAG.Part57

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part48 PAG.Part49 PAG.Part52 PAG.Part54 PAG.Part55

variable {p : ℕ} [hp : Fact p.Prime]

/-- 単数 y の val は p で割れない。 -/
theorem not_dvd_val_of_unit {m : ℕ} (hm : 1 ≤ m) (y : ZMod (p ^ m)) (hy : IsUnit y) : ¬ p ∣ y.val := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)] at hy
  intro hd
  have := Nat.Coprime.coprime_dvd_left hd hy
  rw [Nat.coprime_self] at this
  exact hp.out.one_lt.ne' this

/-- **指示関数の値**: 1_{S_w}(ι_v y) = [w = v]（y 単数）。 -/
theorem shellInd_apply (K w v : ℕ) (hw : w < K) (hv : v < K) (y : ZMod (p ^ (K - v))) (hy : IsUnit y) :
    shellInd (p := p) K w hw (shellEmb (p := p) K v hv.le y) = if w = v then 1 else 0 := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  split_ifs with h
  · subst h
    rw [shellInd, push_apply_emb _ (shellEmb_injective K w hw.le), MulChar.one_apply hy]
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · rw [shellInd, shellEmb_lower K v w hlt hv y, push_apply_emb _ (shellEmb_injective K w hw.le)]
      apply vanish_one K w hw
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_left]
      rintro ⟨h1, -⟩
      rw [Nat.coprime_pow_left_iff (by omega), Nat.coprime_pow_right_iff (by omega), Nat.coprime_self] at h1
      exact hp.out.one_lt.ne' h1
    · rw [shellInd]
      apply push_apply_not
      rintro ⟨z, hz⟩
      rw [shellEmb_lower K w v hgt hw z] at hz
      have e := shellEmb_injective (p := p) K v hv.le hz
      apply not_dvd_val_of_unit (m := K - v) (by omega) y hy
      rw [← e, ZMod.val_natCast]
      have hlt : p ^ (w - v) * z.val < p ^ (K - v) := by
        have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
        calc p ^ (w - v) * z.val < p ^ (w - v) * p ^ (K - w) :=
              Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) (pow_pos hp.out.pos _)
          _ = p ^ (K - v) := by rw [← pow_add]; congr 1; omega
      rw [Nat.mod_eq_of_lt hlt]
      exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _

/-- 球の値: ball_j(ι_v y) = [j ≤ v]（y 単数）。 -/
theorem ball_apply_shell (K j v : ℕ) (hv : v < K) (y : ZMod (p ^ (K - v))) (hy : IsUnit y) :
    PAG.Part22.ball (p := p) K j (shellEmb (p := p) K v hv.le y) = if j ≤ v then 1 else 0 := by
  have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hlt : p ^ v * y.val < p ^ K := by
    calc p ^ v * y.val < p ^ v * p ^ (K - v) := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt y) (pow_pos hp.out.pos _)
      _ = p ^ K := by rw [← pow_add]; congr 1; omega
  unfold PAG.Part22.ball
  rw [PAG.Part22.val_shellEmb, Nat.mod_eq_of_lt hlt]
  have hnd := not_dvd_val_of_unit (m := K - v) (by omega) y hy
  by_cases hj : j ≤ v
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (Dvd.dvd.mul_right (pow_dvd_pow p hj) _)), ite_eq_left_of_eq_true _ _ (eq_true hj)]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj)]
    apply ite_eq_right_of_eq_false
    apply eq_false
    intro hd
    have h1 : p ^ (v + 1) ∣ p ^ v * y.val := dvd_trans (pow_dvd_pow p (by omega)) hd
    rw [pow_succ] at h1
    exact hnd (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos _) h1)

/-- 球の分解に現れる和（Fin K 上、j ≤ w の殻だけ）。 -/
noncomputable def shellSum (K j : ℕ) : ZMod (p ^ K) → ℂ :=
  ∑ w : Fin K, if j ≤ (w : ℕ) then shellInd (p := p) K w w.2 else 0

/-- **球の分解**: ball_j = Σ_{j ≤ w < K} 1_{S_w} + δ₀。 -/
theorem ball_decomp (K j : ℕ) :
    PAG.Part22.ball (p := p) K j = shellSum (p := p) K j + Pi.single 0 1 := by
  funext x
  rw [Pi.add_apply, shellSum, Finset.sum_apply]
  by_cases hx : x = 0
  · subst hx
    rw [PAG.Part49.ball_apply_zero, Pi.single_eq_same]
    have : ∀ w : Fin K, (if j ≤ (w : ℕ) then shellInd (p := p) K w w.2 else 0) 0 = 0 := by
      intro w; split_ifs
      · exact shellInd_zero K w w.2
      · rfl
    simp only [this, Finset.sum_const_zero, zero_add]
  · obtain ⟨v, hv, y, hy, rfl⟩ := exists_shell K x hx
    rw [ball_apply_shell K j v hv y hy, Pi.single_apply, ite_eq_right_of_eq_false _ _ (eq_false hx), add_zero]
    rw [Finset.sum_eq_single ⟨v, hv⟩]
    · simp only
      split_ifs with h
      · rw [shellInd_apply K v v hv hv y hy, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      · rfl
    · intro w _ hw
      split_ifs
      · rw [shellInd_apply K w v w.2 hv y hy, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hw (Fin.ext h)))]
      · rfl
    · intro h; exact absurd (mem_univ _) h

/-- 指示関数と δ₀ の張る空間。 -/
def IndSpan (K : ℕ) : Submodule ℂ (ZMod (p ^ K) → ℂ) :=
  Submodule.span ℂ {f | (∃ w, ∃ hw : w < K, f = shellInd (p := p) K w hw) ∨ f = Pi.single 0 1}

theorem ball_mem (K j : ℕ) : PAG.Part22.ball (p := p) K j ∈ IndSpan (p := p) K := by
  rw [ball_decomp]
  refine Submodule.add_mem _ (Submodule.sum_mem _ (fun w _ => ?_)) (Submodule.subset_span (Or.inr rfl))
  split_ifs
  · exact Submodule.subset_span (Or.inl ⟨w, w.2, rfl⟩)
  · exact Submodule.zero_mem _

/-- 球の差 ballB は IndSpan に入る。 -/
theorem ballB_mem (K w n : ℕ) : ballB (p := p) K w n ∈ IndSpan (p := p) K := by
  unfold ballB
  exact Submodule.sub_mem _ (ball_mem K _) (Submodule.smul_mem _ _ (Submodule.sub_mem _ (ball_mem K _) (ball_mem K _)))

/-- **畳み込みの基底上の作用**: 原始ケットの組の畳み込みは 0、S の一つの原始ケットの定数倍、または IndSpan の元。 -/
theorem conv_ket_action (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (p ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) :
    conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = 0 ∨
    (∃ b ∈ family (p := p) K, ∃ C : ℂ, C ≠ 0 ∧
      conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) = C • b) ∨
    conv (ket K w₁ (n₁ + 1) h₁ χ₁) (ket K w₂ (n₂ + 1) h₂ χ₂) ∈ IndSpan (p := p) K := by
  rcases classification K w₁ n₁ w₂ n₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂ with hI | hII | hIII
  · exact Or.inl hI.2
  · obtain ⟨hab, w, c, h, hc, ψ, hψ, C, hC, hconv⟩ := hII
    refine Or.inr (Or.inl ⟨ket K w c h ψ, Or.inl ⟨w, c, h, hc, ψ, hψ, rfl⟩, C, ?_, hconv⟩)
    rintro rfl
    rw [map_zero] at hC
    exact (PAG.Part46.lam_pos (p := p) K _).ne hC
  · obtain ⟨-, -, hconv⟩ := hIII
    right; right
    rw [hconv]
    exact Submodule.smul_mem _ _ (ballB_mem K w₁ n₁)

/-- **δ₀ は畳み込みの単位元**。 -/
theorem conv_delta (K : ℕ) (g : ZMod (p ^ K) → ℂ) : conv (Pi.single 0 1) g = g := by
  funext x
  unfold conv
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_univ _) h

end PAG.Part57

#print axioms PAG.Part57.not_dvd_val_of_unit
#print axioms PAG.Part57.shellInd_apply
#print axioms PAG.Part57.ball_apply_shell
#print axioms PAG.Part57.shellSum
#print axioms PAG.Part57.ball_decomp
#print axioms PAG.Part57.IndSpan
#print axioms PAG.Part57.ball_mem
#print axioms PAG.Part57.ballB_mem
#print axioms PAG.Part57.conv_ket_action
#print axioms PAG.Part57.conv_delta
