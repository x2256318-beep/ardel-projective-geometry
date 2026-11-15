/-
  PAG 2.0 Part 248（2026-11-07）— 除いた 2 種類の組 (p³, p)・(16, 2) で B_s ≠ A_N。B_s = A_N の分類の完成
  A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg。ℤ/N の円分スキームの Terwilliger 代数 T(0)）、B_s = ⟨D_u, E_N, E_s⟩（Part 246 の addEAlg）、
  S′ = {t ∣ N : φ(N/t) ≠ 1}。
  1. 新しい証拠 q = δ_1 − (1/p)·1_{1+(N/p)ℤ} = (1/p)·Σ_{c < p}(δ_1 − δ_{1+c(N/p)})（levelWit）：p² ∣ N なら単数の殻に載り、
     P q = 0。𝓕q(k) = e(−k)（(N/p)k ≠ 0）、0（(N/p)k = 0）。p ∣ s なら E_s q = 0
  2. 主補題：p 素数、p^{m+1} ∣ N、p ∣ s、p^m ∤ s、N ∤ 2p^m なら E_1 ∉ B_s（convL_geps_one_not_mem_addEAlg_of_level）。
     f = q + h（h は Part 247 の unitWit）は U_s^⊥ に入り単数の殻に載るので、E_1 ∈ B_s なら E_1 f = c·f。
     𝓕f(1) = e(−1) から c = 1、𝓕f(p^m) = p^m(e(−p^m) − e(p^m)) ≠ 0 なのに p^m ∉ D_1 で 𝓕(E_1 f)(p^m) = 0、で矛盾
  3. 除いた組：N = p³（p は奇素数）で B_p ≠ A_N、B_2 ≠ A_16（m = 2）。どちらも |S′| = 3 で平方因子をもつ
  4. 分類の完成：s ∈ S′ なら B_s = A_N ⇔ |S′| ≤ 2 ∨（N が平方因子なし ∧ s ∈ {1, 2}）（addEAlg_eq_shellAlg_iff_all、除外なし）。
     素冪 N = p^k では B_s = A_N ⇔ k ≤ 2 ∨ N = 8、s = p^j ∈ S′ で E_1 ∈ B_s ⇔ j = 0 ∨ k ≤ 2 ∨ N = 8
  5. フーリエ双対：同じ仮定で D_1 ∉ ⟨E_u, D_N, D_s⟩、⟨E_u, D_N, D_s⟩ = A_N も 4 と同じ条件
  6. 追補（同じ日の夜、著者の選択）：同じ証拠と同じ仮定で E_{p^m} ∉ B_s（convL_geps_primePow_not_mem_addEAlg_of_level）。
     E_{p^m} f = c·f とすると、1 ∉ D_{p^m} で c = 0、p^m ∈ D_{p^m} で 𝓕f(p^m) = 0 となり矛盾。
     除いた組では E_{p²} ∉ B_p（N = p³、p は奇素数）、E_4 ∉ B_2（N = 16）。フーリエ双対 D_{p^m} ∉ ⟨E_u, D_N, D_s⟩ も
-/
import PAG251

namespace PAG.Part252

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246 PAG.Part247 PAG.Part248 PAG.Part249 PAG.Part250 PAG.Part251
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 新しい証拠 q = δ_1 − (1/p)·1_{1+(N/p)ℤ} -/

/-- q = (1/p)·Σ_{c < p} (δ_1 − δ_{1+c(N/p)})（= δ_1 − (1/p)·1_{1+(N/p)ℤ}）。 -/
noncomputable def levelWit (N p : ℕ) : ZMod N → ℂ :=
  ((p : ℂ)⁻¹) • ∑ c ∈ Finset.range p, twoPt N (1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N))

/-- **1a.** p² ∣ N なら 1 + c·(N/p) は単数。 -/
theorem isUnit_one_add_mul_div {N p : ℕ} [NeZero N] (hp : p.Prime) (hpp : p * p ∣ N) (c : ℕ) :
    IsUnit (1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N)) := by
  have hpp' : p ^ (1 + 1) ∣ N := by rw [show p ^ (1 + 1) = p * p by ring]; exact hpp
  have h := isUnit_one_add_mul (N := N) (m := 1) hp hpp' c
  rwa [pow_one] at h

/-- **1b.** P q = 0。 -/
theorem shellAvg_levelWit {N p : ℕ} [NeZero N] (hp : p.Prime) (hpp : p * p ∣ N) :
    shellAvg N (levelWit N p) = 0 := by
  rw [levelWit, map_smul, map_sum, Finset.sum_eq_zero (fun c _ => shellAvg_twoPt (isUnit_one_add_mul_div hp hpp c)),
    smul_zero]

/-- **1c.** q は単数の殻に載る：1_{D_1}·q = q。 -/
theorem dind_one_mul_levelWit {N p : ℕ} [NeZero N] (hp : p.Prime) (hpp : p * p ∣ N) :
    dind N 1 * levelWit N p = levelWit N p := by
  rw [levelWit, mul_smul_comm, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun c _ => dind_one_mul_twoPt (isUnit_one_add_mul_div hp hpp c))

/-- **1d.** (N/p)·k = 0 なら 𝓕q(k) = 0。 -/
theorem dft_levelWit_of_mul_eq_zero {N p : ℕ} [NeZero N] {k : ZMod N}
    (hk : ((N / p : ℕ) : ZMod N) * k = 0) : 𝓕 (levelWit N p) k = 0 := by
  rw [levelWit, map_smul, Pi.smul_apply, map_sum, Finset.sum_apply]
  have h : ∀ c ∈ Finset.range p, 𝓕 (twoPt N (1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N))) k = 0 := by
    intro c _
    rw [twoPt, map_sub, Pi.sub_apply, dft_single, dft_single]
    have e : (1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N)) * k = 1 * k := by
      rw [add_mul, one_mul, mul_assoc, hk, mul_zero, add_zero]
    rw [e, sub_self]
  rw [Finset.sum_eq_zero h, smul_zero]

/-- **1e.** (N/p)·k ≠ 0 なら 𝓕q(k) = e(−k)（ζ = e(−(N/p)k) は 1 でない p 乗根）。 -/
theorem dft_levelWit_of_mul_ne_zero {N p : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N) {k : ZMod N}
    (hk : ((N / p : ℕ) : ZMod N) * k ≠ 0) : 𝓕 (levelWit N p) k = stdAddChar (-k) := by
  rw [levelWit, map_smul, Pi.smul_apply, map_sum, Finset.sum_apply]
  have hterm : ∀ c : ℕ, 𝓕 (twoPt N (1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N))) k =
      stdAddChar (-k) - stdAddChar (-k) * stdAddChar (-(((N / p : ℕ) : ZMod N) * k)) ^ c := by
    intro c
    rw [twoPt, map_sub, Pi.sub_apply, dft_single, dft_single, one_mul]
    have e : -((1 + (c : ZMod N) * ((N / p : ℕ) : ZMod N)) * k) = -k + c • (-(((N / p : ℕ) : ZMod N) * k)) := by
      rw [nsmul_eq_mul]
      ring
    rw [e, AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  simp only [hterm]
  have hpw : (p : ℕ) • (-(((N / p : ℕ) : ZMod N) * k)) = 0 := by
    rw [smul_neg, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hpN, ZMod.natCast_self, zero_mul,
      neg_zero]
  have hgeo : ∑ c ∈ Finset.range p, stdAddChar (-(((N / p : ℕ) : ZMod N) * k)) ^ c = 0 := by
    apply geom_sum_eq_zero_of_pow
    · intro h
      apply hk
      have h2 : stdAddChar (-(((N / p : ℕ) : ZMod N) * k)) = stdAddChar (0 : ZMod N) := by
        rw [h, AddChar.map_zero_eq_one]
      exact neg_eq_zero.mp (ZMod.injective_stdAddChar h2)
    · rw [← AddChar.map_nsmul_eq_pow, hpw, AddChar.map_zero_eq_one]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hgeo, mul_zero, sub_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero), one_mul]

/-- **1f.** p ∣ N、p ∣ k.val なら (N/p)·k = 0。 -/
theorem div_mul_eq_zero_of_dvd_val {N p : ℕ} [NeZero N] (hpN : p ∣ N) {k : ZMod N} (hk : p ∣ k.val) :
    ((N / p : ℕ) : ZMod N) * k = 0 := by
  obtain ⟨a, ha⟩ := hk
  have e : ((N / p : ℕ) : ZMod N) * k = ((N / p * k.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e, ZMod.natCast_eq_zero_iff, ha, ← mul_assoc, Nat.div_mul_cancel hpN]
  exact Dvd.intro a rfl

/-- **1g.** 1 < d、d ∣ N なら (N/d : ZMod N) ≠ 0。 -/
theorem natCast_div_ne_zero {N d : ℕ} [NeZero N] (hd : 1 < d) (hdN : d ∣ N) : ((N / d : ℕ) : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have hN := Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : 0 < N / d := Nat.div_pos (Nat.le_of_dvd hN hdN) (by omega)
  have h2 : N / d < N := Nat.div_lt_self hN hd
  exact absurd (Nat.le_of_dvd h1 h) (not_le.mpr h2)

/-- **1h.** p ∣ N、p ∣ s なら E_s q = 0（𝓕q は p の倍数の上で 0、D_s の点は p の倍数）。 -/
theorem convL_geps_levelWit {N s p : ℕ} [NeZero N] (hpN : p ∣ N) (hps : p ∣ s) :
    PAG.Part15.convL (geps N s) (levelWit N p) = 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [map_zero, PAG.Part15.convL_apply, dft_conv_geps]
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hd : dind N s k = 0
  · rw [hd, zero_mul]
  · have hg : Nat.gcd N k.val = s := by
      by_contra hne
      exact hd (ite_eq_right hne)
    have hpk : p ∣ k.val := by
      have h1 := Nat.gcd_dvd_right N k.val
      rw [hg] at h1
      exact dvd_trans hps h1
    rw [dft_levelWit_of_mul_eq_zero (div_mul_eq_zero_of_dvd_val hpN hpk), mul_zero]

/-! ### 2. 主補題：p^{m+1} ∣ N、p ∣ s、p^m ∤ s、N ∤ 2p^m なら E_1 ∉ B_s -/

/-- **2a.** 主補題。f = q + h（h は Part 247 の unitWit）は U_s^⊥ に入り単数の殻に載る。E_1 ∈ B_s なら E_1 f = c·f。
𝓕f(1) = e(−1) で c = 1、𝓕f(p^m) = p^m(e(−p^m) − e(p^m)) ≠ 0 だが p^m ∉ D_1 なので 𝓕(E_1 f)(p^m) = 0 となり矛盾。 -/
theorem convL_geps_one_not_mem_addEAlg_of_level {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ m) :
    PAG.Part15.convL (geps N 1) ∉ addEAlg N s := by
  intro hX
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hpms
      rw [h0, pow_zero]
      exact one_dvd s
    · exact h0
  have hpmN : p ^ m ∣ N := dvd_trans (pow_dvd_pow p (Nat.le_succ m)) hpm
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by omega)) hpmN
  have hpp : p * p ∣ N := dvd_trans (by rw [← pow_two]; exact pow_dvd_pow p (by omega)) hpm
  have hP : shellAvg N (levelWit N p + unitWit N p m) = 0 := by
    rw [map_add, shellAvg_levelWit hp hpp, shellAvg_unitWit, add_zero]
  have hsupp : dind N 1 * (levelWit N p + unitWit N p m) = levelWit N p + unitWit N p m := by
    rw [mul_add, dind_one_mul_levelWit hp hpp, dind_one_mul_unitWit hp hpm]
  have hE0 : PAG.Part15.convL (geps N s) (levelWit N p + unitWit N p m) = 0 := by
    rw [map_add, convL_geps_levelWit hpN hps, convL_geps_unitWit hp hpmN hpms, add_zero]
  have hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * (levelWit N p + unitWit N p m)) = 0 := by
    intro u
    have e : dind N u * (levelWit N p + unitWit N p m) =
        if u = 1 then levelWit N p + unitWit N p m else 0 := by
      conv_lhs => rw [← hsupp]
      rw [← mul_assoc, dind_mul]
      split_ifs with h
      · rw [h, hsupp]
      · rw [zero_mul]
    rw [e]
    split_ifs
    · exact hE0
    · exact map_zero _
  obtain ⟨c, hc⟩ := exists_apply_eq_smul_of_mem_addEAlg hX hP hE hsupp
  rw [PAG.Part15.convL_apply] at hc
  have hF : dind N 1 * 𝓕 (levelWit N p + unitWit N p m) = c • 𝓕 (levelWit N p + unitWit N p m) := by
    rw [← dft_conv_geps, hc, map_smul]
  have hne1 : stdAddChar (-(1 : ZMod N)) ≠ 0 := by
    have h : stdAddChar (-(1 : ZMod N)) * stdAddChar (1 : ZMod N) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h
  -- k = 1
  have hF1 := congrFun hF (1 : ZMod N)
  have hq1 : 𝓕 (levelWit N p) 1 = stdAddChar (-(1 : ZMod N)) := by
    apply dft_levelWit_of_mul_ne_zero hp hpN
    rw [mul_one]
    exact natCast_div_ne_zero hp.one_lt hpN
  have hh1 : 𝓕 (unitWit N p m) 1 = 0 := by
    apply dft_unitWit_of_mul_ne_zero hpmN
    rw [mul_one]
    exact natCast_div_ne_zero (Nat.one_lt_pow (by omega) hp.one_lt) hpmN
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, map_add, Pi.add_apply, hq1, hh1, add_zero,
    dind_one_of_isUnit isUnit_one, one_mul] at hF1
  have hc1 : c = 1 := mul_right_cancel₀ hne1 (by rw [one_mul]; exact hF1.symm)
  -- k = p^m
  have hk1 : ((N / p ^ m : ℕ) : ZMod N) * ((p ^ m : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hpmN, ZMod.natCast_self]
  have hk2 : ((N / p : ℕ) : ZMod N) * ((p ^ m : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    have h : N / p * p ∣ N / p * p ^ m := mul_dvd_mul_left _ (dvd_pow_self p (by omega))
    rwa [Nat.div_mul_cancel hpN] at h
  have hF2 := congrFun hF ((p ^ m : ℕ) : ZMod N)
  have hd2 : dind N 1 ((p ^ m : ℕ) : ZMod N) = 0 := by
    have hg : Nat.gcd N ((p ^ m : ℕ) : ZMod N).val ≠ 1 := by
      rw [gcd_natCast_self N _ hpmN]
      exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
    exact ite_eq_right hg
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, map_add, Pi.add_apply, dft_levelWit_of_mul_eq_zero hk2,
    dft_unitWit_of_mul_eq_zero hk1, zero_add, hd2, zero_mul, hc1, one_mul] at hF2
  have hp0 : (p : ℂ) ^ m ≠ 0 := pow_ne_zero m (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hval : ∀ k : ZMod N, k + k ≠ 0 → stdAddChar (-k) - stdAddChar k ≠ 0 := by
    intro k hk h
    apply hk
    have h2 := ZMod.injective_stdAddChar (sub_eq_zero.mp h)
    linear_combination -h2
  have hcast : ((p ^ m : ℕ) : ZMod N) + ((p ^ m : ℕ) : ZMod N) = ((2 * p ^ m : ℕ) : ZMod N) := by
    push_cast
    ring
  refine mul_ne_zero hp0 (hval _ ?_) hF2.symm
  rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
  exact hN

/-- **2b.** 同じ仮定で B_s ≠ A_N。 -/
theorem addEAlg_ne_shellAlg_of_level {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ m) :
    addEAlg N s ≠ shellAlg N := by
  intro h
  apply convL_geps_one_not_mem_addEAlg_of_level hp hpm hps hpms hN
  rw [h]
  exact PAG.Part232.convL_geps_mem N 1

/-! ### 3. 除いた 2 種類の組 -/

/-- **3a.** N = p³（p は奇素数）、s = p なら E_1 ∉ B_s。 -/
theorem convL_geps_one_not_mem_addEAlg_cube {N p : ℕ} [NeZero N] (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N = p ^ 3) : PAG.Part15.convL (geps N 1) ∉ addEAlg N p := by
  apply convL_geps_one_not_mem_addEAlg_of_level (m := 2) hp (by subst hN; exact pow_dvd_pow p (by norm_num))
    (dvd_refl p) ?_ ?_
  · intro h
    have h2 : p ^ 2 ∣ p ^ 1 := by rw [pow_one]; exact h
    have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
    omega
  · rw [hN]
    intro h
    have h1 : p ^ 2 * p ∣ p ^ 2 * 2 := by
      rw [← pow_succ, mul_comm (p ^ 2) 2]
      exact h
    have h2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- **3b.** N = 16、s = 2 なら E_1 ∉ B_s。 -/
theorem convL_geps_one_not_mem_addEAlg_sixteen : PAG.Part15.convL (geps 16 1) ∉ addEAlg 16 2 :=
  convL_geps_one_not_mem_addEAlg_of_level (m := 2) Nat.prime_two (by decide) (dvd_refl 2) (by decide) (by decide)

/-- **3c.** N = p³（p は奇素数）なら |S′| = 3。 -/
theorem card_devSet_cube {N p : ℕ} [NeZero N] (hp : p.Prime) (hp2 : p ≠ 2) (hN : N = p ^ 3) :
    (devSet N).card = 3 := by
  have h := card_devSet N
  have h2 : ¬ 2 ∣ N := by
    rw [hN]
    intro h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hd : N.divisors.card = 4 := by rw [hN, card_divisors_primePow hp 3]
  rw [ite_eq_right h2, hd] at h
  omega

/-- **3d.** |S′(16)| = 3。 -/
theorem card_devSet_sixteen : (devSet 16).card = 3 := by
  have h := card_devSet 16
  have hd : (16 : ℕ).divisors.card = 5 := by decide
  rw [ite_eq_left (by decide : 2 ∣ 16), hd] at h
  omega

/-- **3e.** p³ は平方因子をもつ。 -/
theorem not_squarefree_cube {N p : ℕ} (hp : p.Prime) (hN : N = p ^ 3) : ¬ Squarefree N := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨p, hp, by rw [hN]; exact ⟨p, by ring⟩⟩

/-- **3f.** 16 は平方因子をもつ。 -/
theorem not_squarefree_sixteen : ¬ Squarefree 16 := by
  rw [Nat.squarefree_iff_prime_squarefree]
  push Not
  exact ⟨2, Nat.prime_two, by decide⟩

/-- **3g.** N = p³（p は奇素数）なら B_p ≠ A_N。 -/
theorem addEAlg_ne_shellAlg_cube {N p : ℕ} [NeZero N] (hp : p.Prime) (hp2 : p ≠ 2) (hN : N = p ^ 3) :
    addEAlg N p ≠ shellAlg N := by
  intro h
  apply convL_geps_one_not_mem_addEAlg_cube hp hp2 hN
  rw [h]
  exact PAG.Part232.convL_geps_mem N 1

/-- **3h.** B_2 ≠ A_16。 -/
theorem addEAlg_ne_shellAlg_sixteen : addEAlg 16 2 ≠ shellAlg 16 := by
  intro h
  apply convL_geps_one_not_mem_addEAlg_sixteen
  rw [h]
  exact PAG.Part232.convL_geps_mem 16 1

/-! ### 4. 分類の完成 -/

/-- **4a.** 除いた組では B_s ≠ A_N。 -/
theorem addEAlg_ne_shellAlg_of_exceptional {N s : ℕ} [NeZero N]
    (hex : (∃ p, p.Prime ∧ p ≠ 2 ∧ N = p ^ 3 ∧ s = p) ∨ (N = 16 ∧ s = 2)) : addEAlg N s ≠ shellAlg N := by
  rcases hex with ⟨p, hp, hp2, hN, rfl⟩ | ⟨rfl, rfl⟩
  · exact addEAlg_ne_shellAlg_cube hp hp2 hN
  · exact addEAlg_ne_shellAlg_sixteen

/-- **4b.** 除いた組では右辺も成り立たない（|S′| = 3 で、平方因子をもつ）。 -/
theorem not_rhs_of_exceptional {N s : ℕ}
    (hex : (∃ p, p.Prime ∧ p ≠ 2 ∧ N = p ^ 3 ∧ s = p) ∨ (N = 16 ∧ s = 2)) [NeZero N] :
    ¬ ((devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2))) := by
  rcases hex with ⟨p, hp, hp2, hN, rfl⟩ | ⟨rfl, rfl⟩
  · rintro (h | ⟨h, _⟩)
    · rw [card_devSet_cube hp hp2 hN] at h
      omega
    · exact not_squarefree_cube hp hN h
  · rintro (h | ⟨h, _⟩)
    · rw [card_devSet_sixteen] at h
      omega
    · exact not_squarefree_sixteen h

/-- **4c.** 主定理（除外なし）：s ∈ S′ なら B_s = A_N ⇔ |S′| ≤ 2 ∨ (N が平方因子なし ∧ (s = 1 ∨ s = 2))。 -/
theorem addEAlg_eq_shellAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∈ devSet N) :
    addEAlg N s = shellAlg N ↔ (devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2)) := by
  by_cases hex : (∃ p, p.Prime ∧ p ≠ 2 ∧ N = p ^ 3 ∧ s = p) ∨ (N = 16 ∧ s = 2)
  · exact iff_of_false (addEAlg_ne_shellAlg_of_exceptional hex) (not_rhs_of_exceptional hex)
  · exact addEAlg_eq_shellAlg_iff hs hex

/-- **4d.** 素冪 N = p^k、s ∈ S′ なら B_s = A_N ⇔ k ≤ 2 ∨ N = 8。 -/
theorem addEAlg_eq_shellAlg_iff_primePow {N s p k : ℕ} [NeZero N] (hp : p.Prime) (hN : N = p ^ k)
    (hs : s ∈ devSet N) : addEAlg N s = shellAlg N ↔ k ≤ 2 ∨ N = 8 := by
  rw [addEAlg_eq_shellAlg_iff_all hs]
  have hcard := card_devSet N
  have hd : N.divisors.card = k + 1 := by rw [hN, card_divisors_primePow hp k]
  rw [hd] at hcard
  have hpos : 1 ≤ (devSet N).card := Finset.card_pos.mpr ⟨s, hs⟩
  have hsq : Squarefree N → k ≤ 1 := by
    intro hsq
    by_contra hk
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    apply hsq p hp
    rw [hN, ← pow_two]
    exact pow_dvd_pow p (by omega)
  split_ifs at hcard with h2
  · have hp2 : p = 2 := by
      rw [hN] at h2
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    constructor
    · rintro (hc | ⟨hsq', _⟩)
      · by_cases hk : k ≤ 2
        · exact Or.inl hk
        · right
          calc N = 2 ^ k := by rw [hN, hp2]
            _ = 2 ^ 3 := by rw [show k = 3 by omega]
            _ = 8 := by norm_num
      · exact Or.inl (by have := hsq hsq'; omega)
    · rintro (hk | h8)
      · left
        omega
      · left
        rw [hN, hp2] at h8
        have hk3 : k = 3 := Nat.pow_right_injective (le_refl 2) (h8.trans (by norm_num : (8 : ℕ) = 2 ^ 3))
        omega
  · constructor
    · rintro (hc | ⟨hsq', _⟩)
      · left
        omega
      · left
        have := hsq hsq'
        omega
    · rintro (hk | h8)
      · left
        omega
      · exfalso
        apply h2
        rw [h8]
        decide

/-- **4e.** 素冪 N = p^k、s = p^j ∈ S′ なら E_1 ∈ B_s ⇔ j = 0 ∨ k ≤ 2 ∨ N = 8。 -/
theorem convL_geps_one_mem_addEAlg_iff_primePow {N s p k j : ℕ} [NeZero N] (hp : p.Prime) (hN : N = p ^ k)
    (hsj : s = p ^ j) (hs : s ∈ devSet N) :
    PAG.Part15.convL (geps N 1) ∈ addEAlg N s ↔ j = 0 ∨ k ≤ 2 ∨ N = 8 := by
  constructor
  · intro hmem
    by_contra hcon
    push Not at hcon
    obtain ⟨hj0, hk2, hN8⟩ := hcon
    have hsN : s ∣ N := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hs).1
    have hφ : Nat.totient (N / s) ≠ 1 := (Finset.mem_filter.mp hs).2
    have hjk : j < k := by
      have hjk' : j ≤ k := by
        rw [hsj, hN] at hsN
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hsN
      rcases lt_or_eq_of_le hjk' with h' | h'
      · exact h'
      · exfalso
        apply hφ
        rw [hsj, h', ← hN, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N)), Nat.totient_one]
    by_cases hj2 : 2 ≤ j
    · exact convL_geps_one_not_mem_addEAlg_primePow hp hN hsj hj2 hjk hmem
    · have hj1 : j = 1 := by omega
      rw [hj1, pow_one] at hsj
      have hp3 : p ^ (2 + 1) ∣ N := by
        rw [hN]
        exact pow_dvd_pow p (by omega)
      have hps2 : ¬ p ^ 2 ∣ p := by
        intro h
        have h2 : p ^ 2 ∣ p ^ 1 := by rw [pow_one]; exact h
        have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
        omega
      have hNd : ¬ N ∣ 2 * p ^ 2 := by
        intro hdiv
        by_cases hp2 : p = 2
        · rw [hN, hp2] at hdiv
          have h4 : 2 ^ k ∣ 2 ^ 3 := by
            have e : 2 * 2 ^ 2 = 2 ^ 3 := by norm_num
            rw [← e]
            exact hdiv
          have hk3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h4
          apply hN8
          calc N = 2 ^ k := by rw [hN, hp2]
            _ = 2 ^ 3 := by rw [show k = 3 by omega]
            _ = 8 := by norm_num
        · have h1 : p ^ 2 * p ∣ p ^ 2 * 2 := by
            rw [← pow_succ, mul_comm (p ^ 2) 2]
            exact dvd_trans hp3 hdiv
          have h2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h1
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      exact convL_geps_one_not_mem_addEAlg_of_level hp hp3 (dvd_of_eq hsj.symm) (by rw [hsj]; exact hps2) hNd hmem
  · rintro (hj0 | hk2 | hN8)
    · rw [hsj, hj0, pow_zero]
      exact convL_geps_mem_addEAlg N 1
    · rw [(addEAlg_eq_shellAlg_iff_primePow hp hN hs).mpr (Or.inl hk2)]
      exact PAG.Part232.convL_geps_mem N 1
    · rw [(addEAlg_eq_shellAlg_iff_primePow hp hN hs).mpr (Or.inr hN8)]
      exact PAG.Part232.convL_geps_mem N 1

/-! ### 5. フーリエ双対 -/

/-- **5a.** 同じ仮定で D_1 ∉ ⟨E_u, D_N, D_s⟩。 -/
theorem mulLeft_dind_one_not_mem_dualAddEAlg_of_level {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ m) :
    LinearMap.mulLeft ℂ (dind N 1) ∉ dualAddEAlg N s := by
  rw [← map_fourierConj_addEAlg, ← fourierConj_convL_geps N 1]
  intro h
  obtain ⟨Y, hY, hYX⟩ := Subalgebra.mem_map.mp h
  have hYX' : fourierConj N Y = fourierConj N (PAG.Part15.convL (geps N 1)) := hYX
  rw [(fourierConj N).injective hYX'] at hY
  exact convL_geps_one_not_mem_addEAlg_of_level hp hpm hps hpms hN hY

/-- **5b.** ⟨E_u, D_N, D_s⟩ = A_N の分類（除外なし）。 -/
theorem dualAddEAlg_eq_shellAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∈ devSet N) :
    dualAddEAlg N s = shellAlg N ↔ (devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2)) := by
  rw [dualAddEAlg_eq_shellAlg_iff, addEAlg_eq_shellAlg_iff_all hs]

/-! ### 6. 追補（2026-11-07 夜、著者の選択）：同じ証拠で E_{p^m} ∉ B_s（除いた組では E_{p²}） -/

/-- **6a.** 証拠 f = q + h（主補題の仮定のもと）：B_s の元 X は f にスカラーで働く（Part 246 の判定法）。 -/
theorem exists_smul_witness_of_mem_addEAlg {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) {X : Module.End ℂ (ZMod N → ℂ)}
    (hX : X ∈ addEAlg N s) :
    ∃ c : ℂ, X (levelWit N p + unitWit N p m) = c • (levelWit N p + unitWit N p m) := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hpms
      rw [h0, pow_zero]
      exact one_dvd s
    · exact h0
  have hpmN : p ^ m ∣ N := dvd_trans (pow_dvd_pow p (Nat.le_succ m)) hpm
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by omega)) hpmN
  have hpp : p * p ∣ N := dvd_trans (by rw [← pow_two]; exact pow_dvd_pow p (by omega)) hpm
  have hP : shellAvg N (levelWit N p + unitWit N p m) = 0 := by
    rw [map_add, shellAvg_levelWit hp hpp, shellAvg_unitWit, add_zero]
  have hsupp : dind N 1 * (levelWit N p + unitWit N p m) = levelWit N p + unitWit N p m := by
    rw [mul_add, dind_one_mul_levelWit hp hpp, dind_one_mul_unitWit hp hpm]
  have hE0 : PAG.Part15.convL (geps N s) (levelWit N p + unitWit N p m) = 0 := by
    rw [map_add, convL_geps_levelWit hpN hps, convL_geps_unitWit hp hpmN hpms, add_zero]
  have hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * (levelWit N p + unitWit N p m)) = 0 := by
    intro u
    have e : dind N u * (levelWit N p + unitWit N p m) =
        if u = 1 then levelWit N p + unitWit N p m else 0 := by
      conv_lhs => rw [← hsupp]
      rw [← mul_assoc, dind_mul]
      split_ifs with h
      · rw [h, hsupp]
      · rw [zero_mul]
    rw [e]
    split_ifs
    · exact hE0
    · exact map_zero _
  exact exists_apply_eq_smul_of_mem_addEAlg hX hP hE hsupp

/-- **6b.** 𝓕f(1) = e(−1)（m ≥ 1）。 -/
theorem dft_witness_one {N p m : ℕ} [NeZero N] (hp : p.Prime) (hm : 1 ≤ m) (hpmN : p ^ m ∣ N) :
    𝓕 (levelWit N p + unitWit N p m) 1 = stdAddChar (-(1 : ZMod N)) := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by omega)) hpmN
  rw [map_add, Pi.add_apply,
    dft_levelWit_of_mul_ne_zero hp hpN (by rw [mul_one]; exact natCast_div_ne_zero hp.one_lt hpN),
    dft_unitWit_of_mul_ne_zero hpmN
      (by rw [mul_one]; exact natCast_div_ne_zero (Nat.one_lt_pow (by omega) hp.one_lt) hpmN), add_zero]

/-- **6c.** 𝓕f(p^m) = p^m·(e(−p^m) − e(p^m))（m ≥ 1）。 -/
theorem dft_witness_primePow {N p m : ℕ} [NeZero N] (hm : 1 ≤ m) (hpmN : p ^ m ∣ N) :
    𝓕 (levelWit N p + unitWit N p m) ((p ^ m : ℕ) : ZMod N) =
      (p : ℂ) ^ m * (stdAddChar (-((p ^ m : ℕ) : ZMod N)) - stdAddChar ((p ^ m : ℕ) : ZMod N)) := by
  have hpN : p ∣ N := dvd_trans (dvd_pow_self p (by omega)) hpmN
  have hk1 : ((N / p ^ m : ℕ) : ZMod N) * ((p ^ m : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hpmN, ZMod.natCast_self]
  have hk2 : ((N / p : ℕ) : ZMod N) * ((p ^ m : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    have h : N / p * p ∣ N / p * p ^ m := mul_dvd_mul_left _ (dvd_pow_self p (by omega))
    rwa [Nat.div_mul_cancel hpN] at h
  rw [map_add, Pi.add_apply, dft_levelWit_of_mul_eq_zero hk2, dft_unitWit_of_mul_eq_zero hk1, zero_add]

/-- **6d.** N ∤ 2p^m なら 𝓕f(p^m) ≠ 0。 -/
theorem dft_witness_primePow_ne_zero {N p m : ℕ} [NeZero N] (hp : p.Prime) (hm : 1 ≤ m) (hpmN : p ^ m ∣ N)
    (hN : ¬ N ∣ 2 * p ^ m) : 𝓕 (levelWit N p + unitWit N p m) ((p ^ m : ℕ) : ZMod N) ≠ 0 := by
  rw [dft_witness_primePow hm hpmN]
  have hp0 : (p : ℂ) ^ m ≠ 0 := pow_ne_zero m (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hval : ∀ k : ZMod N, k + k ≠ 0 → stdAddChar (-k) - stdAddChar k ≠ 0 := by
    intro k hk h
    apply hk
    have h2 := ZMod.injective_stdAddChar (sub_eq_zero.mp h)
    linear_combination -h2
  have hcast : ((p ^ m : ℕ) : ZMod N) + ((p ^ m : ℕ) : ZMod N) = ((2 * p ^ m : ℕ) : ZMod N) := by
    push_cast
    ring
  refine mul_ne_zero hp0 (hval _ ?_)
  rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
  exact hN

/-- **6e.** 主補題の E_{p^m} 版：p 素数、p^{m+1} ∣ N、p ∣ s、p^m ∤ s、N ∤ 2p^m なら E_{p^m} ∉ B_s。
E_{p^m} ∈ B_s なら E_{p^m}f = c·f。k = 1 は D_{p^m} にないので c = 0、k = p^m は D_{p^m} にあるので 𝓕f(p^m) = 0 となり、6d と矛盾。 -/
theorem convL_geps_primePow_not_mem_addEAlg_of_level {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ m) :
    PAG.Part15.convL (geps N (p ^ m)) ∉ addEAlg N s := by
  intro hX
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      apply hpms
      rw [h0, pow_zero]
      exact one_dvd s
    · exact h0
  have hpmN : p ^ m ∣ N := dvd_trans (pow_dvd_pow p (Nat.le_succ m)) hpm
  obtain ⟨c, hc⟩ := exists_smul_witness_of_mem_addEAlg hp hpm hps hpms hX
  rw [PAG.Part15.convL_apply] at hc
  have hF : dind N (p ^ m) * 𝓕 (levelWit N p + unitWit N p m) = c • 𝓕 (levelWit N p + unitWit N p m) := by
    rw [← dft_conv_geps, hc, map_smul]
  have hne1 : stdAddChar (-(1 : ZMod N)) ≠ 0 := by
    have h : stdAddChar (-(1 : ZMod N)) * stdAddChar (1 : ZMod N) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h
  have hg1 : Nat.gcd N (1 : ZMod N).val = 1 := by
    have h := dind_one_of_isUnit (N := N) isUnit_one
    by_contra hne
    rw [show dind N 1 (1 : ZMod N) = 0 from ite_eq_right hne] at h
    exact zero_ne_one h
  have hd1 : dind N (p ^ m) (1 : ZMod N) = 0 := by
    have hg : Nat.gcd N (1 : ZMod N).val ≠ p ^ m := by
      rw [hg1]
      exact (Nat.one_lt_pow (by omega) hp.one_lt).ne
    exact ite_eq_right hg
  have hF1 := congrFun hF (1 : ZMod N)
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, dft_witness_one hp hm hpmN, hd1, zero_mul] at hF1
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hF1.symm with h | h
    · exact h
    · exact absurd h hne1
  have hF2 := congrFun hF ((p ^ m : ℕ) : ZMod N)
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, dind_self N (p ^ m) hpmN, one_mul, hc0, zero_mul] at hF2
  exact dft_witness_primePow_ne_zero hp hm hpmN hN hF2

/-- **6f.** 同じ仮定で、フーリエ双対：D_{p^m} ∉ ⟨E_u, D_N, D_s⟩。 -/
theorem mulLeft_dind_primePow_not_mem_dualAddEAlg_of_level {N s p m : ℕ} [NeZero N] (hp : p.Prime)
    (hpm : p ^ (m + 1) ∣ N) (hps : p ∣ s) (hpms : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ m) :
    LinearMap.mulLeft ℂ (dind N (p ^ m)) ∉ dualAddEAlg N s := by
  rw [← map_fourierConj_addEAlg, ← fourierConj_convL_geps N (p ^ m)]
  intro h
  obtain ⟨Y, hY, hYX⟩ := Subalgebra.mem_map.mp h
  have hYX' : fourierConj N Y = fourierConj N (PAG.Part15.convL (geps N (p ^ m))) := hYX
  rw [(fourierConj N).injective hYX'] at hY
  exact convL_geps_primePow_not_mem_addEAlg_of_level hp hpm hps hpms hN hY

/-- **6g.** N = p³（p は奇素数）、s = p なら E_{p²} ∉ B_s。 -/
theorem convL_geps_sq_not_mem_addEAlg_cube {N p : ℕ} [NeZero N] (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : N = p ^ 3) : PAG.Part15.convL (geps N (p ^ 2)) ∉ addEAlg N p := by
  apply convL_geps_primePow_not_mem_addEAlg_of_level (m := 2) hp
    (by subst hN; exact pow_dvd_pow p (by norm_num)) (dvd_refl p) ?_ ?_
  · intro h
    have h2 : p ^ 2 ∣ p ^ 1 := by rw [pow_one]; exact h
    have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
    omega
  · rw [hN]
    intro h
    have h1 : p ^ 2 * p ∣ p ^ 2 * 2 := by
      rw [← pow_succ, mul_comm (p ^ 2) 2]
      exact h
    have h2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 2) h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

/-- **6h.** N = 16、s = 2 なら E_4 ∉ B_s。 -/
theorem convL_geps_four_not_mem_addEAlg_sixteen : PAG.Part15.convL (geps 16 4) ∉ addEAlg 16 2 := by
  have h := convL_geps_primePow_not_mem_addEAlg_of_level (N := 16) (s := 2) (p := 2) (m := 2) Nat.prime_two
    (by norm_num) (dvd_refl 2) (by norm_num) (by norm_num)
  rwa [show (2 : ℕ) ^ 2 = 4 by norm_num] at h

end PAG.Part252

#print axioms PAG.Part252.levelWit
#print axioms PAG.Part252.isUnit_one_add_mul_div
#print axioms PAG.Part252.shellAvg_levelWit
#print axioms PAG.Part252.dind_one_mul_levelWit
#print axioms PAG.Part252.dft_levelWit_of_mul_eq_zero
#print axioms PAG.Part252.dft_levelWit_of_mul_ne_zero
#print axioms PAG.Part252.div_mul_eq_zero_of_dvd_val
#print axioms PAG.Part252.natCast_div_ne_zero
#print axioms PAG.Part252.convL_geps_levelWit
#print axioms PAG.Part252.convL_geps_one_not_mem_addEAlg_of_level
#print axioms PAG.Part252.addEAlg_ne_shellAlg_of_level
#print axioms PAG.Part252.convL_geps_one_not_mem_addEAlg_cube
#print axioms PAG.Part252.convL_geps_one_not_mem_addEAlg_sixteen
#print axioms PAG.Part252.card_devSet_cube
#print axioms PAG.Part252.card_devSet_sixteen
#print axioms PAG.Part252.not_squarefree_cube
#print axioms PAG.Part252.not_squarefree_sixteen
#print axioms PAG.Part252.addEAlg_ne_shellAlg_cube
#print axioms PAG.Part252.addEAlg_ne_shellAlg_sixteen
#print axioms PAG.Part252.addEAlg_ne_shellAlg_of_exceptional
#print axioms PAG.Part252.not_rhs_of_exceptional
#print axioms PAG.Part252.addEAlg_eq_shellAlg_iff_all
#print axioms PAG.Part252.addEAlg_eq_shellAlg_iff_primePow
#print axioms PAG.Part252.convL_geps_one_mem_addEAlg_iff_primePow
#print axioms PAG.Part252.mulLeft_dind_one_not_mem_dualAddEAlg_of_level
#print axioms PAG.Part252.dualAddEAlg_eq_shellAlg_iff_all
#print axioms PAG.Part252.exists_smul_witness_of_mem_addEAlg
#print axioms PAG.Part252.dft_witness_one
#print axioms PAG.Part252.dft_witness_primePow
#print axioms PAG.Part252.dft_witness_primePow_ne_zero
#print axioms PAG.Part252.convL_geps_primePow_not_mem_addEAlg_of_level
#print axioms PAG.Part252.mulLeft_dind_primePow_not_mem_dualAddEAlg_of_level
#print axioms PAG.Part252.convL_geps_sq_not_mem_addEAlg_cube
#print axioms PAG.Part252.convL_geps_four_not_mem_addEAlg_sixteen
