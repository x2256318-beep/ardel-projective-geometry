/-
  PAG 2.0 Part 245（2026-11-05）— ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N ∈ {1, 8} ∪ {p, p²}（p は素数）
  B1 = ⟨D_u, E_N⟩（Part 240 の oneEAlg N N）、B2 = ⟨E_u, D_N⟩（Part 242 の dualOneEAlg）、和 B1 + B2 は部分空間（sumSub）。
  Part 244 で dim(B1 ∩ B2) = d(N)² + 1、dim(B1 + B2) + 1 = d(N)² + 2|S′|（N ≥ 3）。
  1. B2 ≤ A_N（𝓕A_N𝓕⁻¹ = A_N）なので B1 + B2 ≤ A_N で、等号 ⇔ 次元が等しい（sumSub_eq_iff_finrank）。
     N ≥ 3 で dim(B1 + B2) + 3 + 2·[2 ∣ N] = d(N)² + 2·d(N)（finrank_sumSub_add）
  2. 素冪：dim A_{p^k} − dim(B1 + B2) = (k − 1)(k − 2)/2（p 奇数、k ≥ 1）、(k − 2)(k − 3)/2（p = 2、k ≥ 2）
     （finrank_shellAlg_primePow_odd_sum、finrank_shellAlg_two_pow_sum）。0 になるのは p、p²、8（と 4 = 2²）
  3. 素因数 2 つ以上：N = p^k·M（p = minFac N、M > 1 は奇数）。dim A_N = dim A_{p^k}·dim A_M、
     dim A_M ≥ dim ⟨D_u, E_M⟩ = d(M)² + d(M) − 1 と、x = k + 1、y = d(M) ≥ 2 の不等式
     2xy + x² + 1 < x²y + y² + y + 2（p 奇数）、2xy + x² ≤ x²y + 4（p = 2）から dim(B1 + B2) < dim A_N（finrank_sumSub_lt_of_eq_mul）
  4. 主定理：B1 + B2 = A_N ⇔ N = 1 ∨ N = 8 ∨ N = p ∨ N = p²（sumSub_eq_shellAlg_iff）。式の形（N ≥ 3）：
     Π_{p^k ∥ N}((k+1)² + k(k+1)/2 − [p = 2]k) = d² + 2d − 3 − 2[2 ∣ N] ⇔ N = 8 ∨ N = p ∨ N = p²（prod_eq_sum_iff）。
     和は A_N なのに B1 ≠ A_N となるのは、N = 8 と奇素数の平方だけ（sumSub_eq_and_ne_iff）
-/
import PAG248

namespace PAG.Part249

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246 PAG.Part247 PAG.Part248
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 和 ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ は A_N に含まれる -/

/-- ⟨D_u, E_N⟩ と ⟨E_u, D_N⟩ の和（部分空間）。 -/
noncomputable def sumSub (N : ℕ) [NeZero N] : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Subalgebra.toSubmodule (oneEAlg N N) ⊔ Subalgebra.toSubmodule (dualOneEAlg N)

/-- **1a.** ⟨E_u, D_N⟩ ≤ A_N（𝓕 A_N 𝓕⁻¹ = A_N、Part 242）。 -/
theorem dualOneEAlg_le (N : ℕ) [NeZero N] : dualOneEAlg N ≤ shellAlg N := by
  rw [← map_fourierConj_oneEAlg, ← map_fourierConj_shellAlg]
  exact Subalgebra.map_mono (oneEAlg_le N N)

/-- **1b.** ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ ≤ A_N。 -/
theorem sumSub_le (N : ℕ) [NeZero N] : sumSub N ≤ Subalgebra.toSubmodule (shellAlg N) :=
  sup_le (Subalgebra.toSubmodule.monotone (oneEAlg_le N N)) (Subalgebra.toSubmodule.monotone (dualOneEAlg_le N))

/-- **1c.** dim(⟨D_u, E_N⟩ + ⟨E_u, D_N⟩) ≤ dim A_N。 -/
theorem finrank_sumSub_le (N : ℕ) [NeZero N] :
    Module.finrank ℂ (sumSub N) ≤ Module.finrank ℂ (shellAlg N) :=
  Submodule.finrank_mono (sumSub_le N)

/-- **1d.** 和 = A_N ⇔ 次元が等しい。 -/
theorem sumSub_eq_iff_finrank (N : ℕ) [NeZero N] :
    sumSub N = Subalgebra.toSubmodule (shellAlg N) ↔
      Module.finrank ℂ (sumSub N) = Module.finrank ℂ (shellAlg N) := by
  constructor
  · intro h
    exact congrArg (fun S : Submodule ℂ (Module.End ℂ (ZMod N → ℂ)) => Module.finrank ℂ S) h
  · intro h
    exact Submodule.eq_of_le_of_finrank_eq (sumSub_le N) h

/-- **1e.** N ≥ 3 なら dim(和) + 3 + 2·[2 ∣ N] = d(N)² + 2·d(N)（Part 244 の次元と Part 241 の |S′|）。 -/
theorem finrank_sumSub_add {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    Module.finrank ℂ (sumSub N) + 3 + 2 * (if 2 ∣ N then 1 else 0) =
      N.divisors.card ^ 2 + 2 * N.divisors.card := by
  have h1 : Module.finrank ℂ (sumSub N) + 1 = N.divisors.card ^ 2 + 2 * (devSet N).card :=
    finrank_sup_add_one hN
  have h2 := card_devSet N
  generalize Module.finrank ℂ (sumSub N) = r at h1 ⊢
  generalize N.divisors.card ^ 2 = D2 at h1 ⊢
  generalize (if 2 ∣ N then 1 else 0) = e at h2 ⊢
  omega

/-- **1f.** A_N = ⟨D_u, E_N⟩ なら dim(和) = dim A_N。 -/
theorem finrank_sumSub_eq_of_shellAlg_eq {N : ℕ} [NeZero N] (h : shellAlg N = oneEAlg N N) :
    Module.finrank ℂ (sumSub N) = Module.finrank ℂ (shellAlg N) := by
  apply le_antisymm (finrank_sumSub_le N)
  have h1 : Subalgebra.toSubmodule (oneEAlg N N) ≤ sumSub N := le_sup_left
  have h2 := Submodule.finrank_mono h1
  rw [h]
  exact h2

/-! ### 2. 素冪 -/

/-- **2a.** k(k+1)/2 + 1 = 2k + (k − 1)(k − 2)/2（k ≥ 1）。 -/
theorem half_mul_succ_add_one {k : ℕ} (hk : 1 ≤ k) : k * (k + 1) / 2 + 1 = 2 * k + (k - 1) * (k - 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e1 : (m + 1) * (m + 1 + 1) = 2 * (2 * m + 1) + m * (m - 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rw [e1, Nat.mul_add_div two_pos, show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
  generalize m * (m - 1) / 2 = T
  omega

/-- **2b.** k(k+1)/2 + 3 = 3k + (k − 2)(k − 3)/2（k ≥ 2）。 -/
theorem half_mul_succ_add_three {k : ℕ} (hk : 2 ≤ k) : k * (k + 1) / 2 + 3 = 3 * k + (k - 2) * (k - 3) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have e1 : (m + 2) * (m + 2 + 1) = 2 * (3 * m + 3) + m * (m - 1) := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rfl
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  rw [e1, Nat.mul_add_div two_pos, show m + 2 - 2 = m by omega, show m + 2 - 3 = m - 1 by omega]
  generalize m * (m - 1) / 2 = T
  omega

/-- **2c.** 3 ≤ p^k なら dim(和_{p^k}) + 3 + 2·[p = 2] = (k + 1)² + 2(k + 1)。 -/
theorem finrank_sumSub_primePow_add {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (h3 : 3 ≤ p ^ k) [NeZero (p ^ k)] :
    Module.finrank ℂ (sumSub (p ^ k)) + 3 + 2 * (if p = 2 then 1 else 0) = (k + 1) ^ 2 + 2 * (k + 1) := by
  have h := finrank_sumSub_add h3
  rw [card_divisors_primePow hp, if_congr (two_dvd_primePow_iff hp hk) rfl rfl] at h
  exact h

/-- **2d.** 奇素数 p では dim A_{p^k} = dim(和) + (k − 1)(k − 2)/2（k ≥ 1）。 -/
theorem finrank_shellAlg_primePow_odd_sum {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≠ 0) [NeZero (p ^ k)] :
    Module.finrank ℂ (shellAlg (p ^ k)) = Module.finrank ℂ (sumSub (p ^ k)) + (k - 1) * (k - 2) / 2 := by
  have h3 : 3 ≤ p ^ k := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    exact le_trans hp3 (le_self_pow hp.one_lt.le hk)
  have h1 := finrank_shellAlg_primePow hp hk
  have h2 := finrank_sumSub_primePow_add hp hk h3
  have h4 := half_mul_succ_add_one (k := k) (by omega)
  rw [ite_eq_right hp2] at h1 h2
  rw [h1]
  generalize (k + 1) ^ 2 = Q at h2 ⊢
  generalize k * (k + 1) / 2 = T at h4 ⊢
  generalize (k - 1) * (k - 2) / 2 = U at h4 ⊢
  generalize Module.finrank ℂ (sumSub (p ^ k)) = r at h2 ⊢
  omega

/-- **2e.** p = 2 では dim A_{2^k} = dim(和) + (k − 2)(k − 3)/2（k ≥ 2）。 -/
theorem finrank_shellAlg_two_pow_sum {k : ℕ} (hk : 2 ≤ k) [NeZero (2 ^ k)] :
    Module.finrank ℂ (shellAlg (2 ^ k)) = Module.finrank ℂ (sumSub (2 ^ k)) + (k - 2) * (k - 3) / 2 := by
  have h3 : 3 ≤ 2 ^ k := le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hk)
  have h1 := finrank_shellAlg_primePow Nat.prime_two (by omega : k ≠ 0)
  have h2 := finrank_sumSub_primePow_add Nat.prime_two (by omega : k ≠ 0) h3
  have h4 := half_mul_succ_add_three hk
  rw [ite_eq_left rfl] at h1 h2
  rw [h1]
  generalize (k + 1) ^ 2 = Q at h2 ⊢
  generalize k * (k + 1) / 2 = T at h4 ⊢
  generalize (k - 2) * (k - 3) / 2 = U at h4 ⊢
  generalize Module.finrank ℂ (sumSub (2 ^ k)) = r at h2 ⊢
  omega

/-- **2f.** 奇素数の冪 n = p^k（k ≥ 3）では dim(和) < dim A_n。 -/
theorem finrank_sumSub_lt_of_eq_primePow_odd {n p k : ℕ} [NeZero n] (hn : n = p ^ k) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 3 ≤ k) : Module.finrank ℂ (sumSub n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  rw [finrank_shellAlg_primePow_odd_sum hp hp2 (by omega)]
  have h : 1 ≤ (k - 1) * (k - 2) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos, one_mul]
    exact le_trans (by norm_num) (Nat.mul_le_mul (by omega : 2 ≤ k - 1) (by omega : 1 ≤ k - 2))
  generalize (k - 1) * (k - 2) / 2 = T at h ⊢
  omega

/-- **2g.** n = 2^k（k ≥ 4）では dim(和) < dim A_n。 -/
theorem finrank_sumSub_lt_of_eq_two_pow {n k : ℕ} [NeZero n] (hn : n = 2 ^ k) (hk : 4 ≤ k) :
    Module.finrank ℂ (sumSub n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  rw [finrank_shellAlg_two_pow_sum (by omega)]
  have h : 1 ≤ (k - 2) * (k - 3) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos, one_mul]
    exact le_trans (by norm_num) (Nat.mul_le_mul (by omega : 2 ≤ k - 2) (by omega : 1 ≤ k - 3))
  generalize (k - 2) * (k - 3) / 2 = T at h ⊢
  omega

/-- **2h.** n = p²（p 素数）では dim(和) = dim A_n。 -/
theorem finrank_sumSub_eq_of_eq_sq {n p : ℕ} [NeZero n] (hn : n = p ^ 2) (hp : p.Prime) :
    Module.finrank ℂ (sumSub n) = Module.finrank ℂ (shellAlg n) := by
  subst hn
  by_cases hp2 : p = 2
  · subst hp2
    have h := finrank_shellAlg_two_pow_sum (k := 2) (le_refl 2)
    simp only [Nat.sub_self, zero_mul, Nat.zero_div, add_zero] at h
    exact h.symm
  · have h := finrank_shellAlg_primePow_odd_sum hp hp2 (two_ne_zero)
    simp only [Nat.sub_self, mul_zero, Nat.zero_div, add_zero] at h
    exact h.symm

/-- **2i.** n = 2³ = 8 では dim(和) = dim A_n。 -/
theorem finrank_sumSub_eq_two_pow_three [NeZero (2 ^ 3)] :
    Module.finrank ℂ (sumSub (2 ^ 3)) = Module.finrank ℂ (shellAlg (2 ^ 3)) := by
  have h := finrank_shellAlg_two_pow_sum (k := 3) (by norm_num)
  simp only [Nat.sub_self, mul_zero, Nat.zero_div, add_zero] at h
  exact h.symm

/-! ### 3. 素因数が 2 つ以上 -/

/-- **3a.** p 奇数用の不等式：x, y ≥ 2 なら 2xy + x² + 1 < x²y + y² + y + 2。 -/
theorem ineq_odd {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : 2 * (x * y) + x ^ 2 + 1 < x ^ 2 * y + y ^ 2 + y + 2 := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 2 := ⟨x - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = b + 2 := ⟨y - 2, by omega⟩
  ring_nf
  nlinarith [Nat.zero_le (a ^ 2 * b), Nat.zero_le (a * b), Nat.zero_le (a ^ 2), Nat.zero_le (b ^ 2)]

/-- **3b.** p = 2 用の不等式：x, y ≥ 2 なら 2xy + x² ≤ x²y + 4。 -/
theorem ineq_two {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : 2 * (x * y) + x ^ 2 ≤ x ^ 2 * y + 4 := by
  obtain ⟨a, rfl⟩ : ∃ a, x = a + 2 := ⟨x - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = b + 2 := ⟨y - 2, by omega⟩
  ring_nf
  nlinarith [Nat.zero_le (a ^ 2 * b), Nat.zero_le (a * b), Nat.zero_le (a ^ 2)]

/-- **3c.** n = p^k·M（p 素数、k ≥ 1、M > 1 は奇数で p^k と互いに素）なら dim(和) < dim A_n
（dim A_n = dim A_{p^k}·dim A_M、dim A_M ≥ dim ⟨D_u, E_M⟩ = d(M)² + d(M) − 1）。 -/
theorem finrank_sumSub_lt_of_eq_mul {n p k M : ℕ} [NeZero n] (hn : n = p ^ k * M) (hp : p.Prime) (hk : k ≠ 0)
    (hM1 : 1 < M) (hcop : Nat.Coprime (p ^ k) M) (hM2 : ¬ 2 ∣ M) :
    Module.finrank ℂ (sumSub n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  have : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  have : NeZero M := ⟨by omega⟩
  have hF := PAG.Part230.finrank_shellAlg_mul hcop
  have hFp := finrank_shellAlg_primePow hp hk
  have hGM := finrank_oneEAlg_le M
  have gM := finrank_oneEAlg_self_add M
  rw [ite_eq_right hM2] at gM
  have hpk2 : 2 ≤ p ^ k := le_trans hp.two_le (le_self_pow hp.one_lt.le hk)
  have hM3 : 3 ≤ M := by
    have h2 : M ≠ 2 := by
      rintro rfl
      exact hM2 (dvd_refl 2)
    omega
  have h3 : 3 ≤ p ^ k * M := le_trans (by norm_num : 3 ≤ 2 * 3) (Nat.mul_le_mul hpk2 hM3)
  have hS := finrank_sumSub_add h3
  have h2iff : 2 ∣ p ^ k * M ↔ p = 2 := by
    constructor
    · intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
      · exact (two_dvd_primePow_iff hp hk).mp h1
      · exact absurd h1 hM2
    · intro h
      exact dvd_mul_of_dvd_left ((two_dvd_primePow_iff hp hk).mpr h) M
  rw [if_congr h2iff rfl rfl, Nat.Coprime.card_divisors_mul hcop, card_divisors_primePow hp] at hS
  have hy : 2 ≤ M.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega), M,
    Nat.mem_divisors_self M (by omega), by omega⟩
  rw [hF, hFp]
  by_cases hp2 : p = 2
  · rw [ite_eq_left hp2] at hS ⊢
    have hT : k ≤ k * (k + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le two_pos]
      exact Nat.mul_le_mul_left k (by omega : 2 ≤ k + 1)
    have hf : (k + 1) ^ 2 ≤ (k + 1) ^ 2 + k * (k + 1) / 2 - k := by
      generalize k * (k + 1) / 2 = T at hT ⊢
      generalize (k + 1) ^ 2 = Q
      omega
    generalize (k + 1) ^ 2 + k * (k + 1) / 2 - k = f at hf ⊢
    generalize Module.finrank ℂ (sumSub (p ^ k * M)) = r at hS ⊢
    generalize Module.finrank ℂ (shellAlg M) = FM at hGM ⊢
    generalize Module.finrank ℂ (oneEAlg M M) = GM at hGM gM
    generalize M.divisors.card = y at hS gM hy
    generalize hx : k + 1 = x at hf hS
    have hx2 : 2 ≤ x := by omega
    have h1 : x ^ 2 * FM ≤ f * FM := Nat.mul_le_mul_right FM hf
    have h2 : x ^ 2 * (y ^ 2 + y) ≤ x ^ 2 * (FM + 1) := Nat.mul_le_mul_left _ (by omega)
    have key := ineq_two hx2 hy
    nlinarith [h1, h2, key, hS]
  · rw [ite_eq_right hp2] at hS ⊢
    have hT : 1 ≤ k * (k + 1) / 2 := by
      rw [Nat.le_div_iff_mul_le two_pos, one_mul]
      exact le_trans (by norm_num) (Nat.mul_le_mul (by omega : 1 ≤ k) (by omega : 2 ≤ k + 1))
    have hf : (k + 1) ^ 2 + 1 ≤ (k + 1) ^ 2 + k * (k + 1) / 2 - 0 := by
      generalize k * (k + 1) / 2 = T at hT ⊢
      generalize (k + 1) ^ 2 = Q
      omega
    generalize (k + 1) ^ 2 + k * (k + 1) / 2 - 0 = f at hf ⊢
    generalize Module.finrank ℂ (sumSub (p ^ k * M)) = r at hS ⊢
    generalize Module.finrank ℂ (shellAlg M) = FM at hGM ⊢
    generalize Module.finrank ℂ (oneEAlg M M) = GM at hGM gM
    generalize M.divisors.card = y at hS gM hy
    generalize hx : k + 1 = x at hf hS
    have hx2 : 2 ≤ x := by omega
    have h1 : (x ^ 2 + 1) * FM ≤ f * FM := Nat.mul_le_mul_right FM hf
    have h2 : (x ^ 2 + 1) * (y ^ 2 + y) ≤ (x ^ 2 + 1) * (FM + 1) := Nat.mul_le_mul_left _ (by omega)
    have key := ineq_odd hx2 hy
    nlinarith [h1, h2, key, hS]

/-! ### 4. ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N ∈ {1, 8} ∪ {p, p²} -/

/-- **4a.** N ∉ {1, 8} ∪ {p, p²} なら dim(和) < dim A_N。 -/
theorem finrank_sumSub_lt_shellAlg (N : ℕ) [NeZero N]
    (hN : ¬ (N = 1 ∨ N = 8 ∨ ∃ q : ℕ, q.Prime ∧ (N = q ∨ N = q ^ 2))) :
    Module.finrank ℂ (sumSub N) < Module.finrank ℂ (shellAlg N) := by
  have h1 : N ≠ 1 := fun e => hN (Or.inl e)
  have h8 : N ≠ 8 := fun e => hN (Or.inr (Or.inl e))
  have hpp : ∀ q : ℕ, q.Prime → N ≠ q ∧ N ≠ q ^ 2 := fun q hq =>
    ⟨fun e => hN (Or.inr (Or.inr ⟨q, hq, Or.inl e⟩)), fun e => hN (Or.inr (Or.inr ⟨q, hq, Or.inr e⟩))⟩
  have hN0 : N ≠ 0 := NeZero.ne N
  have hp : N.minFac.Prime := Nat.minFac_prime h1
  have hk1 : 0 < N.factorization N.minFac := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
  have hNM := (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm
  have hcop : Nat.Coprime (N.minFac ^ N.factorization N.minFac) (N / N.minFac ^ N.factorization N.minFac) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
  have hM0 := Nat.ordCompl_pos N.minFac hN0
  have hpM : ¬ N.minFac ∣ N / N.minFac ^ N.factorization N.minFac := Nat.not_dvd_ordCompl hp hN0
  have hmin : ∀ r, r.Prime → r ∣ N / N.minFac ^ N.factorization N.minFac → N.minFac < r := by
    intro r hr hrM
    have hrN : r ∣ N := dvd_trans hrM (Nat.ordCompl_dvd N N.minFac)
    have hle := Nat.minFac_le_of_dvd hr.two_le hrN
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hrM) hpM
  have hM2 : ¬ 2 ∣ N / N.minFac ^ N.factorization N.minFac := by
    intro h2
    have h5 := hmin 2 Nat.prime_two h2
    have h6 := hp.two_le
    omega
  generalize N.minFac = p at hp hk1 hNM hcop hM0 hM2
  generalize N.factorization p = k at hk1 hNM hcop hM0 hM2
  generalize N / p ^ k = M at hNM hcop hM0 hM2
  by_cases hM1 : M = 1
  · rw [hM1, mul_one] at hNM
    by_cases hp2 : p = 2
    · rw [hp2] at hNM
      have hk4 : 4 ≤ k := by
        by_contra hlt
        rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
        · exact (hpp 2 Nat.prime_two).1 (by rw [hNM, pow_one])
        · exact (hpp 2 Nat.prime_two).2 hNM
        · exact h8 (hNM.trans (by norm_num))
      exact finrank_sumSub_lt_of_eq_two_pow hNM hk4
    · have hk3 : 3 ≤ k := by
        by_contra hlt
        rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
        · exact (hpp p hp).1 (by rw [hNM, pow_one])
        · exact (hpp p hp).2 hNM
      exact finrank_sumSub_lt_of_eq_primePow_odd hNM hp hp2 hk3
  · exact finrank_sumSub_lt_of_eq_mul hNM hp (by omega) (by omega) hcop hM2

/-- **4b. ⟨D_u, E_N⟩ + ⟨E_u, D_N⟩ = A_N ⇔ N = 1 ∨ N = 8 ∨ N = p ∨ N = p²（p は素数）。** -/
theorem sumSub_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    sumSub N = Subalgebra.toSubmodule (shellAlg N) ↔
      N = 1 ∨ N = 8 ∨ ∃ p : ℕ, p.Prime ∧ (N = p ∨ N = p ^ 2) := by
  rw [sumSub_eq_iff_finrank]
  constructor
  · intro h
    by_contra hN
    have hlt := finrank_sumSub_lt_shellAlg N hN
    omega
  · rintro (h | h | ⟨p, hp, h | h⟩)
    · exact finrank_sumSub_eq_of_shellAlg_eq ((shellAlg_eq_oneEAlg_iff N).mpr (Or.inl h))
    · obtain rfl : N = 2 ^ 3 := by
        rw [h]
        norm_num
      exact finrank_sumSub_eq_two_pow_three
    · exact finrank_sumSub_eq_of_shellAlg_eq ((shellAlg_eq_oneEAlg_iff N).mpr (Or.inr (Or.inr (h ▸ hp))))
    · exact finrank_sumSub_eq_of_eq_sq h hp

/-- **4c.** dim(和) = dim A_N ⇔ 同じ条件。 -/
theorem finrank_sumSub_eq_iff (N : ℕ) [NeZero N] :
    Module.finrank ℂ (sumSub N) = Module.finrank ℂ (shellAlg N) ↔
      N = 1 ∨ N = 8 ∨ ∃ p : ℕ, p.Prime ∧ (N = p ∨ N = p ^ 2) := by
  rw [← sumSub_eq_iff_finrank, sumSub_eq_shellAlg_iff]

/-- **4d.** 式の形（N ≥ 3）：Π_{p^k ∥ N}((k+1)² + k(k+1)/2 − [p = 2]k) = d(N)² + 2d(N) − 3 − 2[2 ∣ N]
⇔ N = 8 ∨ N = p ∨ N = p²（Part 226 の dim A_N の式と、Part 244 の和の次元の比較）。 -/
theorem prod_eq_sum_iff {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (∏ q ∈ N.primeFactors, ((N.factorization q + 1) ^ 2 + N.factorization q * (N.factorization q + 1) / 2 -
        (if q = 2 then N.factorization q else 0))) =
      N.divisors.card ^ 2 + 2 * N.divisors.card - 3 - 2 * (if 2 ∣ N then 1 else 0) ↔
      N = 8 ∨ ∃ p : ℕ, p.Prime ∧ (N = p ∨ N = p ^ 2) := by
  have hr : Module.finrank ℂ (sumSub N) =
      N.divisors.card ^ 2 + 2 * N.divisors.card - 3 - 2 * (if 2 ∣ N then 1 else 0) := by
    have h := finrank_sumSub_add hN
    generalize Module.finrank ℂ (sumSub N) = r at h ⊢
    generalize N.divisors.card ^ 2 = D2 at h ⊢
    generalize (if 2 ∣ N then 1 else 0) = e at h ⊢
    omega
  rw [← PAG.Part230.finrank_shellAlg_eq_prod, ← hr, eq_comm, finrank_sumSub_eq_iff]
  constructor
  · rintro (h1 | h)
    · omega
    · exact h
  · intro h
    exact Or.inr h

/-- **4e.** 和は A_N なのに ⟨D_u, E_N⟩ ≠ A_N となるのは、N = 8 か N = p²（p は奇素数）のときだけ。 -/
theorem sumSub_eq_and_ne_iff (N : ℕ) [NeZero N] :
    (sumSub N = Subalgebra.toSubmodule (shellAlg N) ∧ shellAlg N ≠ oneEAlg N N) ↔
      N = 8 ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ N = p ^ 2 := by
  rw [sumSub_eq_shellAlg_iff, Ne, shellAlg_eq_oneEAlg_iff]
  constructor
  · rintro ⟨h1 | h8 | ⟨p, hp, hNp | hNp⟩, hn⟩
    · exact absurd (Or.inl h1) hn
    · exact Or.inl h8
    · exact absurd (Or.inr (Or.inr (hNp ▸ hp))) hn
    · refine Or.inr ⟨p, hp, ?_, hNp⟩
      rintro rfl
      exact hn (Or.inr (Or.inl (by rw [hNp]; norm_num)))
  · rintro (h8 | ⟨p, hp, hp2, hNp⟩)
    · refine ⟨Or.inr (Or.inl h8), ?_⟩
      rintro (h | h | h)
      · omega
      · omega
      · rw [h8] at h
        rcases h.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> omega
    · refine ⟨Or.inr (Or.inr ⟨p, hp, Or.inr hNp⟩), ?_⟩
      have hp2' := hp.two_le
      rintro (h | h | h)
      · rw [hNp] at h
        nlinarith
      · rw [hNp] at h
        have h3 : p ≤ 2 := by nlinarith
        exact hp2 (le_antisymm h3 hp2')
      · rw [hNp] at h
        rcases h.eq_one_or_self_of_dvd p (dvd_pow_self p two_ne_zero) with h1 | h1
        · omega
        · nlinarith

end PAG.Part249

#print axioms PAG.Part249.sumSub
#print axioms PAG.Part249.dualOneEAlg_le
#print axioms PAG.Part249.sumSub_le
#print axioms PAG.Part249.finrank_sumSub_le
#print axioms PAG.Part249.sumSub_eq_iff_finrank
#print axioms PAG.Part249.finrank_sumSub_add
#print axioms PAG.Part249.finrank_sumSub_eq_of_shellAlg_eq
#print axioms PAG.Part249.half_mul_succ_add_one
#print axioms PAG.Part249.half_mul_succ_add_three
#print axioms PAG.Part249.finrank_sumSub_primePow_add
#print axioms PAG.Part249.finrank_shellAlg_primePow_odd_sum
#print axioms PAG.Part249.finrank_shellAlg_two_pow_sum
#print axioms PAG.Part249.finrank_sumSub_lt_of_eq_primePow_odd
#print axioms PAG.Part249.finrank_sumSub_lt_of_eq_two_pow
#print axioms PAG.Part249.finrank_sumSub_eq_of_eq_sq
#print axioms PAG.Part249.finrank_sumSub_eq_two_pow_three
#print axioms PAG.Part249.ineq_odd
#print axioms PAG.Part249.ineq_two
#print axioms PAG.Part249.finrank_sumSub_lt_of_eq_mul
#print axioms PAG.Part249.finrank_sumSub_lt_shellAlg
#print axioms PAG.Part249.sumSub_eq_shellAlg_iff
#print axioms PAG.Part249.finrank_sumSub_eq_iff
#print axioms PAG.Part249.prod_eq_sum_iff
#print axioms PAG.Part249.sumSub_eq_and_ne_iff
