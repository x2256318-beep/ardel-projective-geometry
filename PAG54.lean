/-
  PAG 2.0 Part 50（2026-10-19）— 原始ケット・殻の指示関数・δ₀ は ℂ^(Z/p^K) を張る
  族 S = {原始ケット |w,ψ⟩（c ≥ 1）} ∪ {殻の指示関数 1_{S_w}（w < K）} ∪ {δ₀} について span S = ⊤。
  1. 0 でない x は x = ι_w(y)（w < K、y 単数）と書ける
  2. δ_{ι y} = φ(p^(K−w))⁻¹ Σ_χ χ(y⁻¹)·ι_*χ（指標の直交関係、Mathlib の sum_char_inv_mul_char_eq）
  3. ι_*χ は、導手 1 なら殻の指示関数、導手 p^c（c ≥ 1）なら原始ケットの定数倍
-/
import PAG53

namespace PAG.Part54

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part47

variable {p : ℕ} [hp : Fact p.Prime]

/-- 殻 w の指示関数（自明な指標の押し出し）。 -/
noncomputable def shellInd (K w : ℕ) (hw : w < K) : ZMod (p ^ K) → ℂ :=
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  push (shellEmb (p := p) K w hw.le) ((1 : DirichletCharacter ℂ (p ^ (K - w))) : ZMod (p ^ (K - w)) → ℂ)

/-- 族 S。 -/
def family (K : ℕ) : Set (ZMod (p ^ K) → ℂ) :=
  {f | (∃ w c, ∃ h : w + c ≤ K, 1 ≤ c ∧ ∃ ψ : DirichletCharacter ℂ (p ^ c), ψ.IsPrimitive ∧ f = ket K w c h ψ) ∨
    (∃ w, ∃ hw : w < K, f = shellInd K w hw) ∨ f = Pi.single 0 1}

/-- **殻への分解**: 0 でない x は x = ι_w(y)（w < K、y 単数）。 -/
theorem exists_shell (K : ℕ) (x : ZMod (p ^ K)) (hx : x ≠ 0) :
    ∃ w, ∃ hw : w < K, ∃ y : ZMod (p ^ (K - w)), IsUnit y ∧ shellEmb (p := p) K w hw.le y = x := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hn : x.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  have hlt : x.val < p ^ K := ZMod.val_lt x
  obtain ⟨e, m, hpm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.one_lt.ne'
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at he; exact hn he
  have heK : e < K := by
    by_contra hge
    have h1 : p ^ K ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h2 : p ^ e ≤ x.val := by rw [he]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm0)
    omega
  have hmlt : m < p ^ (K - e) := by
    have : p ^ e * m < p ^ e * p ^ (K - e) := by rw [← pow_add, Nat.add_sub_cancel' heK.le, ← he]; exact hlt
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨e, heK, (m : ZMod (p ^ (K - e))), ?_, ?_⟩
  · rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm))
  · rw [shellEmb_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hmlt, ← he, ZMod.natCast_zmod_val]

/-- **デルタの指標展開**: δ_{ι y} = φ⁻¹ Σ_χ χ(y⁻¹)·ι_*χ。 -/
theorem delta_expand (K w : ℕ) (hw : w < K) (y : ZMod (p ^ (K - w))) (hy : IsUnit y) :
    have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    Pi.single (shellEmb (p := p) K w hw.le y) (1 : ℂ)
      = ((p ^ (K - w)).totient : ℂ)⁻¹ • ∑ χ : DirichletCharacter ℂ (p ^ (K - w)),
          χ y⁻¹ • push (shellEmb (p := p) K w hw.le) (χ : ZMod (p ^ (K - w)) → ℂ) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hinj := shellEmb_injective (p := p) K w hw.le
  have hφ : ((p ^ (K - w)).totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos hp.out.pos _)).ne'
  funext z
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  by_cases hz : ∃ b, shellEmb (p := p) K w hw.le b = z
  · obtain ⟨b, rfl⟩ := hz
    simp only [push_apply_emb _ hinj]
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy b, Pi.single_apply]
    by_cases hb : b = y
    · subst hb; simp [hφ]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hb (hinj h))),
        ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm hb)), mul_zero]
  · simp only [push_apply_not _ _ _ hz, mul_zero, Finset.sum_const_zero]
    rw [Pi.single_apply, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hz ⟨y, h.symm⟩))]

/-- ι_*χ は族 S の張る空間に入る。 -/
theorem push_char_mem (K w : ℕ) (hw : w < K) (χ : DirichletCharacter ℂ (p ^ (K - w))) :
    push (shellEmb (p := p) K w hw.le) (χ : ZMod (p ^ (K - w)) → ℂ) ∈ Submodule.span ℂ (family (p := p) K) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow hp.out).1 (DirichletCharacter.conductor_dvd_level χ)
  rcases Nat.eq_zero_or_pos i with h0 | hi1
  · subst h0
    rw [pow_zero, ← DirichletCharacter.eq_one_iff_conductor_eq_one] at hc
    subst hc
    exact Submodule.subset_span (Or.inr (Or.inl ⟨w, hw, rfl⟩))
  · obtain ⟨ψ, hψ, hdvd, hcl⟩ := exists_prim_of_conductor χ hc
    have hfun : (χ : ZMod (p ^ (K - w)) → ℂ) = (ψ : ZMod (p ^ i) → ℂ) ∘
        (ZMod.castHom (pow_dvd_pow p hi) (ZMod (p ^ i))).toAddMonoidHom := by
      funext b
      rw [← hcl]
      exact changeLevel_apply_cast (K := K - w) hi1 hi ψ b
    have hket : ket K w i (by omega) ψ = (((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) •
        push (shellEmb (p := p) K w hw.le) (χ : ZMod (p ^ (K - w)) → ℂ) := by
      rw [hfun]; rfl
    have ha := PAG.Part51.coef_ne_zero (p := p) K w
    have e : push (shellEmb (p := p) K w hw.le) (χ : ZMod (p ^ (K - w)) → ℂ)
        = ((((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ))⁻¹ • ket K w i (by omega) ψ := by
      rw [hket, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨w, i, by omega, hi1, ψ, hψ, rfl⟩))

/-- **完全性**: 族 S は ℂ^(Z/p^K) を張る。 -/
theorem span_family_eq_top (K : ℕ) : Submodule.span ℂ (family (p := p) K) = ⊤ := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Submodule.eq_top_iff']
  intro f
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ (fun x _ => ?_)
  have hs : Pi.single x (f x) = f x • Pi.single x (1 : ℂ) := by
    funext z; simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
  rw [hs]
  refine Submodule.smul_mem _ _ ?_
  by_cases hx : x = 0
  · subst hx; exact Submodule.subset_span (Or.inr (Or.inr rfl))
  · obtain ⟨w, hw, y, hy, rfl⟩ := exists_shell K x hx
    rw [delta_expand K w hw y hy]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun χ _ => Submodule.smul_mem _ _ ?_))
    exact push_char_mem K w hw χ

end PAG.Part54

#print axioms PAG.Part54.shellInd
#print axioms PAG.Part54.family
#print axioms PAG.Part54.exists_shell
#print axioms PAG.Part54.delta_expand
#print axioms PAG.Part54.push_char_mem
#print axioms PAG.Part54.span_family_eq_top
