/-
  PAG 2.0 Part 242（2026-11-05）— A_N = ⟨D_u, E_N⟩ ⇔ N ∈ {1, 4} ∪ 素数（殻の射影と定数への射影だけで A_N 全体が出る条件）
  A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）、⟨D_u, E_N⟩（Part 240 の oneEAlg N N。Part 241 で ≅ M_{d(N)}(ℂ) × ℂ^{S′}）。
  1. φ(N/s) = 1（s = N, N/2）なら殻 D_s は 1 点で、1_{D_s}·g はどの g でも動径関数。𝓕(E_s f) = 1_{D_s}·𝓕f なので
     E_s の像は動径関数で、E_s = Φ([E_s]) ∈ ⟨D_u, E_N⟩（convL_geps_mem_oneEAlg）
  2. 1 でない約数 s の E_s がすべて ⟨D_u, E_N⟩ に入れば A_N = ⟨D_u, E_N⟩（E_1 = 1 − Σ_{s ≠ 1} E_s）。
     「1 でない約数 s ではどれも φ(N/s) = 1」⇔ N = 1 ∨ N = 4 ∨ N は素数（forall_totient_eq_one_iff）
  3. 次元：Part 226 の dim A_{p^k} = (k+1)² + k(k+1)/2 − [p = 2]k と Part 241 の dim ⟨D_u, E_{p^k}⟩ の差は
     k(k−1)/2（p 奇数）、(k−1)(k−2)/2（p = 2）。N = ab（a は奇数、a, b > 1、互いに素）では、dim A の乗法性と
     dim A_a ≥ d(a)² + d(a) − 1、dim A_b ≥ d(b)² から dim ⟨D_u, E_N⟩ < dim A_N（finrank_oneEAlg_lt_shellAlg）
  4. A_N = ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数（shellAlg_eq_oneEAlg_iff）。式の形：
     Π_{p^k ∥ N} ((k+1)² + k(k+1)/2 − [p = 2]k) = d(N)² + d(N) − 1 − [2 ∣ N] ⇔ 同じ条件（prod_eq_iff）。
     そのとき A_N ≅ M_{d(N)}(ℂ) × ℂ^{S′}（shellAlgEquivOfMem）。条件の外では E_s ∉ ⟨D_u, E_N⟩ となる s ≠ 1 がある
  5. フーリエ双対：conv(𝓕f, 𝓕g) = N·𝓕(fg)。𝓕 による共役（fourierConj）で E_s と D_s が入れ替わり、𝓕 A_N 𝓕⁻¹ = A_N、
     𝓕⟨D_u, E_N⟩𝓕⁻¹ = ⟨E_u, D_N⟩（dualOneEAlg）。A_N = ⟨E_u, D_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数（shellAlg_eq_dualOneEAlg_iff）
-/
import PAG245

namespace PAG.Part246

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. φ(N/s) = 1 の E_s は ⟨D_u, E_N⟩ に入る -/

/-- **1a.** φ(N/s) = 1（s ∣ N）なら殻 D_s は 1 点：gcd(N, x) = gcd(N, y) = s ⇒ x = y。 -/
theorem eq_of_gcd_eq {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) = 1) {x y : ZMod N}
    (hx : Nat.gcd N x.val = s) (hy : Nat.gcd N y.val = s) : x = y := by
  have hcard := card_dsh N s hs
  rw [hφ] at hcard
  exact Finset.card_le_one.mp hcard.le x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩) y
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)

/-- **1b.** φ(N/s) = 1 なら 1_{D_s}·g はどの g でも動径関数。 -/
theorem radial_dind_mul {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) = 1) (g : ZMod N → ℂ) :
    Radial (dind N s * g) := by
  intro a x
  simp only [Pi.mul_apply]
  by_cases hx : Nat.gcd N x.val = s
  · have hax : Nat.gcd N ((a : ZMod N) * x).val = s := by
      rw [gcd_val_unit_mul]
      exact hx
    rw [eq_of_gcd_eq hs hφ hax hx]
  · have hax : ¬ Nat.gcd N ((a : ZMod N) * x).val = s := by
      rw [gcd_val_unit_mul]
      exact hx
    have h1 : dind N s ((a : ZMod N) * x) = 0 := by
      show (if Nat.gcd N ((a : ZMod N) * x).val = s then (1 : ℂ) else 0) = 0
      exact ite_eq_right hax
    have h2 : dind N s x = 0 := by
      show (if Nat.gcd N x.val = s then (1 : ℂ) else 0) = 0
      exact ite_eq_right hx
    rw [h1, h2, zero_mul, zero_mul]

/-- **1c.** φ(N/s) = 1 なら E_s f は動径関数（𝓕(E_s f) = 1_{D_s}·𝓕f）。 -/
theorem radial_conv_geps {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) = 1) (f : ZMod N → ℂ) :
    Radial (PAG.Part15.conv (geps N s) f) := by
  rw [radial_iff_dft, dft_conv_geps]
  exact radial_dind_mul hs hφ _

/-- **1d.** φ(N/s) = 1 なら E_s = Φ([E_s])（E_s は角の代数に入る。s = N は Part 241 の 2e）。 -/
theorem convL_geps_eq_radialMatOp {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) = 1) :
    PAG.Part15.convL (geps N s) = radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N s), PAG.Part232.convL_geps_mem N s⟩)) := by
  rw [← shellAvg_mul_eq]
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply]
  symm
  exact shellAvg_apply_of_radial (radial_conv_geps hs hφ f)

/-- **1e.** φ(N/s) = 1 なら E_s ∈ ⟨D_u, E_N⟩。 -/
theorem convL_geps_mem_oneEAlg {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) = 1) :
    PAG.Part15.convL (geps N s) ∈ oneEAlg N N := by
  rw [convL_geps_eq_radialMatOp hs hφ]
  exact radialMatOp_mem_oneEAlg N _

/-- **1f.** N が偶数なら E_{N/2} ∈ ⟨D_u, E_N⟩。 -/
theorem convL_geps_half_mem_oneEAlg {N : ℕ} [NeZero N] (h2 : 2 ∣ N) :
    PAG.Part15.convL (geps N (N / 2)) ∈ oneEAlg N N :=
  convL_geps_mem_oneEAlg (Nat.div_dvd_of_dvd h2) (by rw [Nat.div_div_self h2 (NeZero.ne N), Nat.totient_two])

/-! ### 2. A_N = ⟨D_u, E_N⟩ となる十分条件と、その条件の言い換え -/

/-- **2a.** 1 でない約数 s の E_s がすべて ⟨D_u, E_N⟩ に入れば A_N ≤ ⟨D_u, E_N⟩
（E_1 = 1 − Σ_{s ≠ 1} E_s、s ∤ N なら E_s = 0）。 -/
theorem shellAlg_le_oneEAlg_of_forall_mem (N : ℕ) [NeZero N]
    (h : ∀ s ∈ N.divisors, s ≠ 1 → PAG.Part15.convL (geps N s) ∈ oneEAlg N N) : shellAlg N ≤ oneEAlg N N := by
  have hE : ∀ s : ℕ, PAG.Part15.convL (geps N s) ∈ oneEAlg N N := by
    intro s
    by_cases hs : s ∣ N
    · by_cases h1 : s = 1
      · subst h1
        have hsum := PAG.Part232.sum_convL_geps N
        rw [← Finset.add_sum_erase _ _ (Nat.one_mem_divisors.mpr (NeZero.ne N))] at hsum
        have e : PAG.Part15.convL (geps N 1) =
            1 - ∑ t ∈ N.divisors.erase 1, PAG.Part15.convL (geps N t) := by
          rw [← hsum]
          abel
        rw [e]
        refine Subalgebra.sub_mem _ (Subalgebra.one_mem _) (Subalgebra.sum_mem _ (fun t ht => ?_))
        have ht' := Finset.mem_erase.mp ht
        exact h t ht'.2 ht'.1
      · exact h s (Nat.mem_divisors.mpr ⟨hs, NeZero.ne N⟩) h1
    · rw [PAG.Part232.geps_eq_zero_of_not_dvd hs, map_zero]
      exact Subalgebra.zero_mem _
  rw [PAG.Part232.shellAlg_eq_adjoin]
  apply Algebra.adjoin_le
  rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact hE s
  · exact Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)

/-- **2b.** 1 でない約数 s ではどれも φ(N/s) = 1 なら A_N = ⟨D_u, E_N⟩。 -/
theorem shellAlg_eq_oneEAlg_of_forall (N : ℕ) [NeZero N]
    (h : ∀ s ∈ N.divisors, s ≠ 1 → Nat.totient (N / s) = 1) : shellAlg N = oneEAlg N N :=
  le_antisymm (shellAlg_le_oneEAlg_of_forall_mem N (fun s hs h1 =>
    convL_geps_mem_oneEAlg (Nat.dvd_of_mem_divisors hs) (h s hs h1))) (oneEAlg_le N N)

/-- **2c.** 「1 でない約数 s ではどれも φ(N/s) = 1」⇔ N = 1 ∨ N = 4 ∨ N は素数。 -/
theorem forall_totient_eq_one_iff (N : ℕ) [NeZero N] :
    (∀ s ∈ N.divisors, s ≠ 1 → Nat.totient (N / s) = 1) ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  constructor
  · intro h
    by_cases hN1 : N = 1
    · exact Or.inl hN1
    have hp := Nat.minFac_prime hN1
    have hpN : N.minFac ∣ N := Nat.minFac_dvd N
    have h1 := h N.minFac (Nat.mem_divisors.mpr ⟨hpN, NeZero.ne N⟩) hp.one_lt.ne'
    rw [Nat.totient_eq_one_iff] at h1
    rcases h1 with h1 | h1
    · right
      right
      rw [← Nat.eq_of_dvd_of_div_eq_one hpN h1]
      exact hp
    · have hN : N = 2 * N.minFac := by
        have := Nat.div_mul_cancel hpN
        rw [h1] at this
        omega
      have h2 : 2 ∣ N := ⟨N.minFac, hN⟩
      have h3 := h 2 (Nat.mem_divisors.mpr ⟨h2, NeZero.ne N⟩) (by norm_num)
      rw [hN, Nat.mul_div_cancel_left _ two_pos, Nat.totient_eq_one_iff] at h3
      rcases h3 with h3 | h3
      · exact absurd h3 hp.one_lt.ne'
      · right
        left
        rw [hN, h3]
  · rintro (rfl | rfl | hp)
    · intro s hs h1
      rw [Nat.divisors_one, Finset.mem_singleton] at hs
      exact absurd hs h1
    · intro s hs h1
      have h4 : (4 : ℕ).divisors = {1, 2, 4} := by decide
      rw [h4] at hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact absurd rfl h1
      · decide
      · decide
    · intro s hs h1
      rw [Nat.Prime.divisors hp, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact absurd rfl h1
      · rw [Nat.div_self hp.pos, Nat.totient_one]

/-! ### 3. 次元の比較 -/

/-- **3a.** ⟨D_u, E_N⟩ ⊆ A_N なので dim ⟨D_u, E_N⟩ ≤ dim A_N。 -/
theorem finrank_oneEAlg_le (N : ℕ) [NeZero N] :
    Module.finrank ℂ (oneEAlg N N) ≤ Module.finrank ℂ (shellAlg N) :=
  Submodule.finrank_mono (Subalgebra.toSubmodule.monotone (oneEAlg_le N N))

/-- **3b.** d(p^k) = k + 1。 -/
theorem card_divisors_primePow {p : ℕ} (hp : p.Prime) (k : ℕ) : (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

/-- **3c.** dim A_{p^k} = (k+1)² + k(k+1)/2 − [p = 2]·k（k ≥ 1、Part 226 の式）。 -/
theorem finrank_shellAlg_primePow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) [NeZero (p ^ k)] :
    Module.finrank ℂ (shellAlg (p ^ k)) = (k + 1) ^ 2 + k * (k + 1) / 2 - (if p = 2 then k else 0) := by
  rw [PAG.Part230.finrank_shellAlg_eq_prod, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton,
    hp.factorization_pow, Finsupp.single_eq_same]

/-- **3d.** k ≥ 1 なら 2 ∣ p^k ⇔ p = 2。 -/
theorem two_dvd_primePow_iff {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : 2 ∣ p ^ k ↔ p = 2 := by
  constructor
  · intro h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h)).symm
  · rintro rfl
    exact dvd_pow_self 2 hk

/-- **3e.** dim ⟨D_u, E_{p^k}⟩ + 1 + [p = 2] = (k+1)² + (k+1)（k ≥ 1）。 -/
theorem finrank_oneEAlg_primePow_add {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) [NeZero (p ^ k)] :
    Module.finrank ℂ (oneEAlg (p ^ k) (p ^ k)) + 1 + (if p = 2 then 1 else 0) = (k + 1) ^ 2 + (k + 1) := by
  have h := finrank_oneEAlg_self_add (p ^ k)
  rw [card_divisors_primePow hp, if_congr (two_dvd_primePow_iff hp hk) rfl rfl] at h
  exact h

/-- **3f.** k(k+1)/2 = k + k(k−1)/2。 -/
theorem half_mul_succ (k : ℕ) : k * (k + 1) / 2 = k + k * (k - 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : (m + 1) * (m + 1 + 1) = 2 * (m + 1) + (m + 1) * (m + 1 - 1) := by
    rw [Nat.add_sub_cancel]
    ring
  rw [e, Nat.mul_add_div two_pos]

/-- **3g.** 奇素数 p では dim A_{p^k} = dim ⟨D_u, E_{p^k}⟩ + k(k−1)/2（k ≥ 1）。 -/
theorem finrank_shellAlg_primePow_odd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : k ≠ 0) [NeZero (p ^ k)] :
    Module.finrank ℂ (shellAlg (p ^ k)) = Module.finrank ℂ (oneEAlg (p ^ k) (p ^ k)) + k * (k - 1) / 2 := by
  have h1 := finrank_shellAlg_primePow hp hk
  have h2 := finrank_oneEAlg_primePow_add hp hk
  rw [ite_eq_right hp2] at h1 h2
  rw [h1, half_mul_succ]
  generalize (k + 1) ^ 2 = Q at h2 ⊢
  generalize k * (k - 1) / 2 = T
  omega

/-- **3h.** p = 2 では dim A_{2^k} = dim ⟨D_u, E_{2^k}⟩ + (k−1)(k−2)/2（k ≥ 1）。 -/
theorem finrank_shellAlg_two_pow {k : ℕ} (hk : k ≠ 0) [NeZero (2 ^ k)] :
    Module.finrank ℂ (shellAlg (2 ^ k)) = Module.finrank ℂ (oneEAlg (2 ^ k) (2 ^ k)) + (k - 1) * (k - 2) / 2 := by
  have h1 := finrank_shellAlg_primePow Nat.prime_two hk
  have h2 := finrank_oneEAlg_primePow_add Nat.prime_two hk
  rw [ite_eq_left rfl] at h1 h2
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have e : (m + 1) * (m + 1 + 1) / 2 = (2 * m + 1) + m * (m - 1) / 2 := by
    have e1 : (m + 1) * (m + 1 + 1) = 2 * (2 * m + 1) + m * (m - 1) := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rfl
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      ring
    rw [e1, Nat.mul_add_div two_pos]
  rw [h1, e, show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
  generalize (m + 1 + 1) ^ 2 = Q at h2 ⊢
  generalize m * (m - 1) / 2 = T
  omega

/-- **3i.** 奇素数の冪 n = p^k（k ≥ 2）では dim ⟨D_u, E_n⟩ < dim A_n。 -/
theorem finrank_lt_of_eq_primePow_odd {n p k : ℕ} [NeZero n] (hn : n = p ^ k) (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 2 ≤ k) : Module.finrank ℂ (oneEAlg n n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  rw [finrank_shellAlg_primePow_odd hp hp2 (by omega)]
  have h : 1 ≤ k * (k - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos, one_mul]
    exact le_trans (by norm_num) (Nat.mul_le_mul hk (by omega : 1 ≤ k - 1))
  generalize k * (k - 1) / 2 = T at h ⊢
  omega

/-- **3j.** n = 2^k（k ≥ 3）では dim ⟨D_u, E_n⟩ < dim A_n。 -/
theorem finrank_lt_of_eq_two_pow {n k : ℕ} [NeZero n] (hn : n = 2 ^ k) (hk : 3 ≤ k) :
    Module.finrank ℂ (oneEAlg n n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  rw [finrank_shellAlg_two_pow (by omega)]
  have h : 1 ≤ (k - 1) * (k - 2) / 2 := by
    rw [Nat.le_div_iff_mul_le two_pos, one_mul]
    exact le_trans (by norm_num) (Nat.mul_le_mul (by omega : 2 ≤ k - 1) (by omega : 1 ≤ k - 2))
  generalize (k - 1) * (k - 2) / 2 = T at h ⊢
  omega

/-- **3k.** n = ab（a は奇数、a, b > 1、gcd(a, b) = 1）なら dim ⟨D_u, E_n⟩ < dim A_n
（dim A は乗法的、dim A_a ≥ d(a)² + d(a) − 1、dim A_b ≥ d(b)²）。 -/
theorem finrank_lt_of_eq_mul {n a b : ℕ} [NeZero n] (hn : n = a * b) (hab : Nat.Coprime a b) (ha : Odd a)
    (ha1 : 1 < a) (hb1 : 1 < b) : Module.finrank ℂ (oneEAlg n n) < Module.finrank ℂ (shellAlg n) := by
  subst hn
  have : NeZero a := ⟨by omega⟩
  have : NeZero b := ⟨by omega⟩
  have hF := PAG.Part230.finrank_shellAlg_mul hab
  have hA := finrank_oneEAlg_le a
  have hB := finrank_oneEAlg_le b
  have gA := finrank_oneEAlg_self_add a
  have gB := finrank_oneEAlg_self_add b
  have gAB := finrank_oneEAlg_self_add (a * b)
  have h2a : ¬ 2 ∣ a := fun h => (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr h)
  have h2ab : 2 ∣ a * b ↔ 2 ∣ b :=
    ⟨fun h => ((Nat.Prime.dvd_mul Nat.prime_two).mp h).resolve_left h2a, fun h => dvd_mul_of_dvd_right h a⟩
  rw [ite_eq_right h2a] at gA
  rw [if_congr h2ab rfl rfl, Nat.Coprime.card_divisors_mul hab] at gAB
  have he : (if 2 ∣ b then 1 else 0) ≤ 1 := by
    split_ifs <;> omega
  have hda : 2 ≤ a.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega), a,
    Nat.mem_divisors_self a (by omega), by omega⟩
  have hdb : 2 ≤ b.divisors.card := Finset.one_lt_card.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega), b,
    Nat.mem_divisors_self b (by omega), by omega⟩
  rw [hF]
  generalize Module.finrank ℂ (shellAlg a) = Fa at hA ⊢
  generalize Module.finrank ℂ (shellAlg b) = Fb at hB ⊢
  generalize Module.finrank ℂ (oneEAlg a a) = Ga at hA gA
  generalize Module.finrank ℂ (oneEAlg b b) = Gb at hB gB
  generalize Module.finrank ℂ (oneEAlg (a * b) (a * b)) = Gab at gAB ⊢
  generalize a.divisors.card = x at gA gAB hda
  generalize b.divisors.card = y at gB gAB hdb
  generalize (if 2 ∣ b then 1 else 0) = e at gB gAB he
  have hGb : y ^ 2 ≤ Gb := by nlinarith
  have h1 : Ga * Gb ≤ Fa * Fb := Nat.mul_le_mul hA hB
  have h2 : Ga * y ^ 2 ≤ Ga * Gb := Nat.mul_le_mul_left _ hGb
  have hx1 : x * 2 ≤ x * y := Nat.mul_le_mul_left x hdb
  have hx2 : 2 * y ≤ x * y := Nat.mul_le_mul_right y hda
  have hxy : x + y ≤ x * y := by linarith
  have key : (x * y) ^ 2 + x * y + y ^ 2 ≤ (x ^ 2 + x) * y ^ 2 := by
    nlinarith [Nat.mul_le_mul_left y hxy]
  have gA' : Ga * y ^ 2 + y ^ 2 = (x ^ 2 + x) * y ^ 2 := by
    rw [← gA]
    ring
  have h3 : Gab < Ga * y ^ 2 := by linarith
  linarith

/-- **3l.** N ≠ 1, 4 で N が素数でなければ dim ⟨D_u, E_N⟩ < dim A_N。 -/
theorem finrank_oneEAlg_lt_shellAlg (N : ℕ) [NeZero N] (h1 : N ≠ 1) (h4 : N ≠ 4) (hpr : ¬ N.Prime) :
    Module.finrank ℂ (oneEAlg N N) < Module.finrank ℂ (shellAlg N) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hp : N.minFac.Prime := Nat.minFac_prime h1
  have hk1 : 0 < N.factorization N.minFac := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
  have hNM := (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm
  have hcop : Nat.Coprime (N.minFac ^ N.factorization N.minFac) (N / N.minFac ^ N.factorization N.minFac) :=
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
  have hM0 := Nat.ordCompl_pos N.minFac hN0
  generalize N.minFac = p at hp hk1 hNM hcop hM0
  generalize N.factorization p = k at hk1 hNM hcop hM0
  generalize N / p ^ k = M at hNM hcop hM0
  by_cases hM1 : M = 1
  · rw [hM1, mul_one] at hNM
    by_cases hp2 : p = 2
    · rw [hp2] at hNM
      have hk3 : 3 ≤ k := by
        by_contra hlt
        rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
        · exact hpr (by rw [hNM, pow_one]; exact Nat.prime_two)
        · exact h4 (hNM.trans (by norm_num))
      exact finrank_lt_of_eq_two_pow hNM hk3
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have hk : k = 1 := by omega
        exact hpr (by rw [hNM, hk, pow_one]; exact hp)
      exact finrank_lt_of_eq_primePow_odd hNM hp hp2 hk2
  · have hM2 : 1 < M := by omega
    by_cases hp2 : p = 2
    · rw [hp2] at hNM hcop
      have hModd : Odd M := by
        have h2M : ¬ 2 ∣ M := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
          (Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 (by omega)) hcop)
        exact Nat.not_even_iff_odd.mp (fun he => h2M (even_iff_two_dvd.mp he))
      exact finrank_lt_of_eq_mul (hNM.trans (mul_comm _ _)) hcop.symm hModd hM2
        (Nat.one_lt_pow (by omega) one_lt_two)
    · exact finrank_lt_of_eq_mul hNM hcop ((hp.odd_of_ne_two hp2).pow) (Nat.one_lt_pow (by omega) hp.one_lt) hM2

/-! ### 4. A_N = ⟨D_u, E_N⟩ ⇔ N ∈ {1, 4} ∪ 素数 -/

/-- **4a. A_N = ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数。** -/
theorem shellAlg_eq_oneEAlg_iff (N : ℕ) [NeZero N] :
    shellAlg N = oneEAlg N N ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  constructor
  · intro h
    by_contra hN
    have hlt := finrank_oneEAlg_lt_shellAlg N (fun e => hN (Or.inl e)) (fun e => hN (Or.inr (Or.inl e)))
      (fun e => hN (Or.inr (Or.inr e)))
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro hN
    exact shellAlg_eq_oneEAlg_of_forall N ((forall_totient_eq_one_iff N).mpr hN)

/-- **4b.** A_N = ⟨D_u, E_N⟩ ⇔ 1 でない約数 s ではどれも φ(N/s) = 1。 -/
theorem shellAlg_eq_oneEAlg_iff_forall (N : ℕ) [NeZero N] :
    shellAlg N = oneEAlg N N ↔ ∀ s ∈ N.divisors, s ≠ 1 → Nat.totient (N / s) = 1 := by
  rw [shellAlg_eq_oneEAlg_iff, forall_totient_eq_one_iff]

/-- **4c.** 次元の形：dim A_N = dim ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数。 -/
theorem finrank_shellAlg_eq_iff (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = Module.finrank ℂ (oneEAlg N N) ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  constructor
  · intro h
    by_contra hN
    have hlt := finrank_oneEAlg_lt_shellAlg N (fun e => hN (Or.inl e)) (fun e => hN (Or.inr (Or.inl e)))
      (fun e => hN (Or.inr (Or.inr e)))
    omega
  · intro hN
    rw [(shellAlg_eq_oneEAlg_iff N).mpr hN]

/-- **4d.** 式の形：Π_{p^k ∥ N} ((k+1)² + k(k+1)/2 − [p = 2]k) = d(N)² + d(N) − 1 − [2 ∣ N]
⇔ N = 1 ∨ N = 4 ∨ N は素数（Part 226 の式と Part 241 の式の比較）。 -/
theorem prod_eq_iff (N : ℕ) [NeZero N] :
    (∏ q ∈ N.primeFactors, ((N.factorization q + 1) ^ 2 + N.factorization q * (N.factorization q + 1) / 2 -
        (if q = 2 then N.factorization q else 0))) =
      N.divisors.card ^ 2 + N.divisors.card - 1 - (if 2 ∣ N then 1 else 0) ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  rw [← PAG.Part230.finrank_shellAlg_eq_prod, ← finrank_oneEAlg_self_sub, finrank_shellAlg_eq_iff]

/-- N ∈ {1, 4} ∪ 素数 のときの A_N のウェダーバーン分解 M_{d(N)}(ℂ) × ℂ^{S′} ≃ A_N。 -/
noncomputable def shellAlgEquivOfMem (N : ℕ) [NeZero N] (hN : N = 1 ∨ N = 4 ∨ N.Prime) :
    (Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) ≃ₐ[ℂ] shellAlg N :=
  (wholeAlgEquiv N).trans (Subalgebra.equivOfEq _ _ ((shellAlg_eq_oneEAlg_iff N).mpr hN).symm)

/-- **4e.** shellAlgEquivOfMem の値は Ψ(M, b)。 -/
theorem shellAlgEquivOfMem_apply (N : ℕ) [NeZero N] (hN : N = 1 ∨ N = 4 ∨ N.Prime)
    (p : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    (shellAlgEquivOfMem N hN p : Module.End ℂ (ZMod N → ℂ)) = wholeMap N p := rfl

/-- **4f.** N ∉ {1, 4} ∪ 素数 なら、1 でない約数 s で φ(N/s) ≠ 1 かつ E_s ∉ ⟨D_u, E_N⟩ となるものがある。 -/
theorem exists_convL_geps_not_mem (N : ℕ) [NeZero N] (hN : ¬ (N = 1 ∨ N = 4 ∨ N.Prime)) :
    ∃ s ∈ N.divisors, s ≠ 1 ∧ Nat.totient (N / s) ≠ 1 ∧ PAG.Part15.convL (geps N s) ∉ oneEAlg N N := by
  by_contra h
  apply hN
  rw [← shellAlg_eq_oneEAlg_iff]
  refine le_antisymm (shellAlg_le_oneEAlg_of_forall_mem N (fun s hs h1 => ?_)) (oneEAlg_le N N)
  by_cases hφ : Nat.totient (N / s) = 1
  · exact convL_geps_mem_oneEAlg (Nat.dvd_of_mem_divisors hs) hφ
  · by_contra hmem
    exact h ⟨s, hs, h1, hφ, hmem⟩

/-! ### 5. フーリエ変換による双対：⟨E_u, D_N⟩ -/

/-- **5a.** conv(𝓕f, 𝓕g) = N·𝓕(f·g)（積の 𝓕 は 𝓕 どうしの畳み込み）。 -/
theorem conv_dft_dft (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) :
    PAG.Part15.conv (𝓕 f) (𝓕 g) = (N : ℂ) • 𝓕 (f * g) := by
  apply ZMod.dft.injective
  simp only [PAG.Part16.dft_conv, ZMod.dft_dft, map_smul]
  funext j
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- フーリエ変換による共役 T ↦ 𝓕 T 𝓕⁻¹（End(ℂ^{ℤ/N}) の代数の自己同型）。 -/
noncomputable def fourierConj (N : ℕ) [NeZero N] :
    Module.End ℂ (ZMod N → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  LinearEquiv.conjAlgEquiv ℂ (ZMod.dft : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ))

/-- **5b.** 𝓕 E_s 𝓕⁻¹ = D_s。 -/
theorem fourierConj_convL_geps (N s : ℕ) [NeZero N] :
    fourierConj N (PAG.Part15.convL (geps N s)) = LinearMap.mulLeft ℂ (dind N s) := by
  apply LinearMap.ext
  intro h
  rw [fourierConj, LinearEquiv.conjAlgEquiv_apply]
  show 𝓕 (PAG.Part15.conv (geps N s) (ZMod.dft.symm h)) = dind N s * h
  rw [dft_conv_geps, LinearEquiv.apply_symm_apply]

/-- **5c.** 𝓕 D_s 𝓕⁻¹ = E_s。 -/
theorem fourierConj_mulLeft_dind (N s : ℕ) [NeZero N] :
    fourierConj N (LinearMap.mulLeft ℂ (dind N s)) = PAG.Part15.convL (geps N s) := by
  apply LinearMap.ext
  intro h
  rw [fourierConj, LinearEquiv.conjAlgEquiv_apply]
  show 𝓕 (dind N s * ZMod.dft.symm h) = PAG.Part15.conv (geps N s) h
  have e := conv_dft_dft N (dind N s) (ZMod.dft.symm h)
  rw [dft_dind, LinearEquiv.apply_symm_apply] at e
  have hlin : PAG.Part15.conv ((N : ℂ) • geps N s) h = (N : ℂ) • PAG.Part15.conv (geps N s) h := by
    show PAG.Part15.convL ((N : ℂ) • geps N s) h = (N : ℂ) • PAG.Part15.convL (geps N s) h
    rw [map_smul, LinearMap.smul_apply]
  rw [hlin] at e
  exact (smul_right_injective _ (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℂ) ≠ 0) e).symm

/-- E_u（u ∈ ℕ）と D_N が生成する部分代数 ⟨E_u, D_N⟩（⟨D_u, E_N⟩ のフーリエ双対）。 -/
noncomputable def dualOneEAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : ℕ => PAG.Part15.convL (geps N u)) ∪ {LinearMap.mulLeft ℂ (dind N N)})

/-- **5d.** 𝓕 A_N 𝓕⁻¹ = A_N（D_s と E_s が入れ替わる）。 -/
theorem map_fourierConj_shellAlg (N : ℕ) [NeZero N] :
    (shellAlg N).map (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) = shellAlg N := by
  rw [PAG.Part232.shellAlg_eq_adjoin, AlgHom.map_adjoin, Set.image_union, ← Set.range_comp, ← Set.range_comp]
  have h1 : (⇑(fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ∘
      fun s : ℕ => PAG.Part15.convL (geps N s)) = fun s => LinearMap.mulLeft ℂ (dind N s) := by
    funext s
    exact fourierConj_convL_geps N s
  have h2 : (⇑(fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ∘
      fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)) = fun s => PAG.Part15.convL (geps N s) := by
    funext s
    exact fourierConj_mulLeft_dind N s
  rw [h1, h2, Set.union_comm]

/-- **5e.** 𝓕 ⟨D_u, E_N⟩ 𝓕⁻¹ = ⟨E_u, D_N⟩。 -/
theorem map_fourierConj_oneEAlg (N : ℕ) [NeZero N] :
    (oneEAlg N N).map (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) =
      dualOneEAlg N := by
  rw [oneEAlg, dualOneEAlg, AlgHom.map_adjoin, Set.image_union, Set.image_singleton, ← Set.range_comp]
  have h1 : (⇑(fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ∘
      fun u : ℕ => LinearMap.mulLeft ℂ (dind N u)) = fun u => PAG.Part15.convL (geps N u) := by
    funext u
    exact fourierConj_mulLeft_dind N u
  have h2 : (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ))
      (PAG.Part15.convL (geps N N)) = LinearMap.mulLeft ℂ (dind N N) := fourierConj_convL_geps N N
  rw [h1, h2]

/-- **5f.** dim ⟨E_u, D_N⟩ = dim ⟨D_u, E_N⟩ = d(N)² + d(N) − 1 − [2 ∣ N]。 -/
theorem finrank_dualOneEAlg (N : ℕ) [NeZero N] :
    Module.finrank ℂ (dualOneEAlg N) = Module.finrank ℂ (oneEAlg N N) := by
  rw [← map_fourierConj_oneEAlg]
  exact ((fourierConj N).subalgebraMap (oneEAlg N N)).toLinearEquiv.finrank_eq.symm

/-- **5g.** A_N = ⟨E_u, D_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数（4a のフーリエ双対）。 -/
theorem shellAlg_eq_dualOneEAlg_iff (N : ℕ) [NeZero N] :
    shellAlg N = dualOneEAlg N ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  rw [← shellAlg_eq_oneEAlg_iff, ← map_fourierConj_oneEAlg]
  constructor
  · intro h
    apply Subalgebra.map_injective
      (f := (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ))) (fourierConj N).injective
    rw [map_fourierConj_shellAlg]
    exact h
  · intro h
    rw [← h, map_fourierConj_shellAlg]

end PAG.Part246

#print axioms PAG.Part246.eq_of_gcd_eq
#print axioms PAG.Part246.radial_dind_mul
#print axioms PAG.Part246.radial_conv_geps
#print axioms PAG.Part246.convL_geps_eq_radialMatOp
#print axioms PAG.Part246.convL_geps_mem_oneEAlg
#print axioms PAG.Part246.convL_geps_half_mem_oneEAlg
#print axioms PAG.Part246.shellAlg_le_oneEAlg_of_forall_mem
#print axioms PAG.Part246.shellAlg_eq_oneEAlg_of_forall
#print axioms PAG.Part246.forall_totient_eq_one_iff
#print axioms PAG.Part246.finrank_oneEAlg_le
#print axioms PAG.Part246.card_divisors_primePow
#print axioms PAG.Part246.finrank_shellAlg_primePow
#print axioms PAG.Part246.two_dvd_primePow_iff
#print axioms PAG.Part246.finrank_oneEAlg_primePow_add
#print axioms PAG.Part246.half_mul_succ
#print axioms PAG.Part246.finrank_shellAlg_primePow_odd
#print axioms PAG.Part246.finrank_shellAlg_two_pow
#print axioms PAG.Part246.finrank_lt_of_eq_primePow_odd
#print axioms PAG.Part246.finrank_lt_of_eq_two_pow
#print axioms PAG.Part246.finrank_lt_of_eq_mul
#print axioms PAG.Part246.finrank_oneEAlg_lt_shellAlg
#print axioms PAG.Part246.shellAlg_eq_oneEAlg_iff
#print axioms PAG.Part246.shellAlg_eq_oneEAlg_iff_forall
#print axioms PAG.Part246.finrank_shellAlg_eq_iff
#print axioms PAG.Part246.prod_eq_iff
#print axioms PAG.Part246.shellAlgEquivOfMem
#print axioms PAG.Part246.shellAlgEquivOfMem_apply
#print axioms PAG.Part246.exists_convL_geps_not_mem
#print axioms PAG.Part246.conv_dft_dft
#print axioms PAG.Part246.fourierConj
#print axioms PAG.Part246.fourierConj_convL_geps
#print axioms PAG.Part246.fourierConj_mulLeft_dind
#print axioms PAG.Part246.dualOneEAlg
#print axioms PAG.Part246.map_fourierConj_shellAlg
#print axioms PAG.Part246.map_fourierConj_oneEAlg
#print axioms PAG.Part246.finrank_dualOneEAlg
#print axioms PAG.Part246.shellAlg_eq_dualOneEAlg_iff
