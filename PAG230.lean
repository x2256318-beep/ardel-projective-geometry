/-
  PAG 2.0 Part 226（2026-10-29）— A・A′・中心の次元の素数べきごとの積の式（Part 214 の式の証明）
  A = ⟨E_s, D_s⟩（Part 214 の shellAlg）、A′（Part 220 の fullComm）、A′ の中心（Part 222 の fullCommCenter）、
  m(c) = 法 c の原始指標の数（def primCount）、S = {(c, d)}（Part 222 の centerIdx）、
  n_(c,d) = #{v ∣ N/c : v は d の層}（Part 217 の layerDivs）、N = Π p^k、k_p = v_p(N)
  0. m は乗法的（Part 204 の Σ_{c ∣ n} m(c) = φ(n) とメビウスの反転公式、def totientAF）。
     m(1) = 1、m(p) = p − 2、m(p^k) = p^(k−2)(p − 1)²（k ≥ 2）、m(c) > 0 ⇔ v_2(c) ≠ 1 ⇔ c ≢ 2 (mod 4)
  1. n_(c,d) は d によらず Π_{q ∣ N/c, q ∤ c} (v_q(N/c) + 1)。Σ_d n_(c,d) = d(N/c)、Σ_{(c,d) ∈ S} n_(c,d)·m(c) = N
  2. 約数の和と素因数ごとの積：Σ_{c ∣ N} Π_{q ∣ N} w_q(v_q(c)) = Π_{q ∣ N} Σ_{γ ≤ k_q} w_q(γ)。
     [m(c) > 0]、#D(c)、n_(c,d) を素因数ごとの積に書く
  3. dim A = Π_p ((k+1)² + Σ_{γ=1..k} [m(p^γ) > 0](k + 1 − γ)) = Π_p ((k+1)² + k(k+1)/2 − [p = 2]k)
     = Part 214 の式 Π_p ((k+1)² + #{(σ, τ) : σ + τ ≤ k − 1, m(p^(k−σ−τ)) > 0})。
     dim A′ = Π_p (1 + Σ_{γ=1..k} m(p^γ)²(k + 1 − γ))。dim Z(A′) = dim Z(A) = Π_p (1 + k(k+1)/2 − [p = 2]k)
  4. 乗法性：gcd(a, b) = 1 なら dim A、dim A′、dim Z(A′) は N = ab で積に分かれる
-/
import PAG229

namespace PAG.Part230

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 原始指標の数 m(c) の乗法性 -/

/-- m(c) = 法 c の原始指標の数。 -/
noncomputable def primCount (c : ℕ) : ℕ := Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive}

/-- オイラーの φ を ℤ 値の数論的関数とみなしたもの。 -/
noncomputable def totientAF : ArithmeticFunction ℤ := ⟨fun n => (Nat.totient n : ℤ), by simp⟩

/-- **0a.** totientAF の値。 -/
theorem totientAF_apply (n : ℕ) : totientAF n = (Nat.totient n : ℤ) := rfl

/-- **0b.** φ は乗法的。 -/
theorem totientAF_isMultiplicative : totientAF.IsMultiplicative :=
  ⟨by rw [totientAF_apply, Nat.totient_one, Nat.cast_one], fun {m n} hmn => by
    rw [totientAF_apply, totientAF_apply, totientAF_apply, Nat.totient_mul hmn, Nat.cast_mul]⟩

/-- **0c.** m = μ ∗ φ（Part 204 の Σ_{c ∣ n} m(c) = φ(n) とメビウスの反転公式）。 -/
theorem primCount_eq_moebius_mul (n : ℕ) (hn : 0 < n) :
    (primCount n : ℤ) = (ArithmeticFunction.moebius * totientAF) n := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
    (f := fun n => (primCount n : ℤ)) (g := fun n => (Nat.totient n : ℤ))).mp (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      have h := sum_card_primitive n
      simp only [primCount]
      exact_mod_cast h) n hn
  rw [← key, ArithmeticFunction.mul_apply]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [totientAF_apply, Int.cast_id]

/-- **0d.** m(1) = 1。 -/
theorem primCount_one : primCount 1 = 1 := by
  have h := sum_card_primitive 1
  rw [Nat.divisors_one, Finset.sum_singleton, Nat.totient_one] at h
  exact h

/-- **0e. m は乗法的**：gcd(a, b) = 1 なら m(ab) = m(a)·m(b)。 -/
theorem primCount_mul {a b : ℕ} (hab : Nat.Coprime a b) : primCount (a * b) = primCount a * primCount b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.coprime_zero_left] at hab
    subst hab
    rw [primCount_one, mul_one, mul_one]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.coprime_zero_right] at hab
    subst hab
    rw [one_mul, primCount_one, one_mul]
  have hm := ArithmeticFunction.isMultiplicative_moebius.mul totientAF_isMultiplicative
  have h := hm.map_mul_of_coprime hab
  rw [← primCount_eq_moebius_mul _ (Nat.mul_pos ha hb), ← primCount_eq_moebius_mul _ ha,
    ← primCount_eq_moebius_mul _ hb] at h
  exact_mod_cast h

/-- **0f.** m(c) = Π_{q ∣ c} m(q^{v_q(c)})（c ≠ 0）。 -/
theorem primCount_eq_prod {c : ℕ} (hc : c ≠ 0) :
    primCount c = ∏ q ∈ c.primeFactors, primCount (q ^ c.factorization q) := by
  rw [Nat.multiplicative_factorization primCount (fun x y h => primCount_mul h) primCount_one hc,
    Finsupp.prod, Nat.support_factorization]

/-- **0g.** c ∣ N（N ≠ 0）なら m(c) = Π_{q ∣ N} m(q^{v_q(c)})。 -/
theorem primCount_eq_prod_of_dvd {c N : ℕ} (hN : N ≠ 0) (hcN : c ∣ N) :
    primCount c = ∏ q ∈ N.primeFactors, primCount (q ^ c.factorization q) := by
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
  rw [primCount_eq_prod hc]
  refine Finset.prod_subset (Nat.primeFactors_mono hcN hN) (fun q hq hqc => ?_)
  have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
  have hndvd : ¬ q ∣ c := fun h => hqc (Nat.mem_primeFactors.mpr ⟨hq', h, hc⟩)
  rw [Nat.factorization_eq_zero_of_not_dvd hndvd, pow_zero, primCount_one]

/-- **0h.** m(p^(k+1)) + φ(p^k) = φ(p^(k+1))。 -/
theorem primCount_prime_pow_succ_add {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primCount (p ^ (k + 1)) + Nat.totient (p ^ k) = Nat.totient (p ^ (k + 1)) := by
  have h1' : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h0' : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h1 := sum_card_primitive (p ^ (k + 1))
  have h0 := sum_card_primitive (p ^ k)
  rw [Nat.sum_divisors_prime_pow hp] at h1 h0
  rw [Finset.sum_range_succ] at h1
  unfold primCount
  omega

/-- **0i.** m(p) = p − 2。 -/
theorem primCount_prime {p : ℕ} (hp : p.Prime) : primCount p = p - 2 := by
  have h := primCount_prime_pow_succ_add hp 0
  rw [zero_add, pow_one, pow_zero, Nat.totient_one, Nat.totient_prime hp] at h
  omega

/-- **0j.** m(p^k) = p^(k−2)(p − 1)²（k ≥ 2）。 -/
theorem primCount_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    primCount (p ^ k) = p ^ (k - 2) * (p - 1) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h := primCount_prime_pow_succ_add hp (j + 1)
  rw [Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hp (by omega)] at h
  have e1 : j + 1 + 1 - 1 = j + 1 := by omega
  have e2 : j + 1 - 1 = j := by omega
  have e3 : j + 2 - 2 = j := by omega
  rw [e1, e2] at h
  rw [e3]
  have hp1 : 1 ≤ p := hp.one_lt.le
  have key : p ^ (j + 1) * (p - 1) = p ^ j * (p - 1) + p ^ j * (p - 1) ^ 2 := by
    zify [hp1]
    ring
  have h' : primCount (p ^ (j + 1 + 1)) + p ^ j * (p - 1) = p ^ j * (p - 1) + p ^ j * (p - 1) ^ 2 := by
    rw [← key]
    exact h
  have e4 : j + 2 = j + 1 + 1 := rfl
  rw [e4]
  omega

/-- **0k.** k ≥ 1 なら m(p^k) > 0 ⇔ (p, k) ≠ (2, 1)。 -/
theorem primCount_prime_pow_pos_iff {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 < primCount (p ^ k) ↔ ¬ (p = 2 ∧ k = 1) := by
  have hp2 := hp.two_le
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    rw [pow_one, primCount_prime hp]
    constructor
    · rintro h ⟨rfl, -⟩
      omega
    · intro h
      have : p ≠ 2 := fun h2 => h ⟨h2, rfl⟩
      omega
  · rw [primCount_prime_pow hp hk2]
    have hp1 : 0 < p - 1 := by omega
    constructor
    · rintro - ⟨-, h1⟩
      omega
    · intro _
      exact Nat.mul_pos (pow_pos hp.pos _) (pow_pos hp1 _)

/-- **0l.** m(c) > 0 ⇔ v_2(c) ≠ 1（c ≠ 0）。 -/
theorem primCount_pos_iff {c : ℕ} (hc : c ≠ 0) : 0 < primCount c ↔ c.factorization 2 ≠ 1 := by
  rw [primCount_eq_prod hc, Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  constructor
  · intro h h2
    have hmem : 2 ∈ c.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, h2]
      exact one_ne_zero
    have := h 2 hmem
    rw [h2, pow_one, primCount_prime Nat.prime_two] at this
    exact this rfl
  · intro h q hq
    have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
    have hpos := hq'.factorization_pos_of_dvd hc (Nat.mem_primeFactors.mp hq).2.1
    have := (primCount_prime_pow_pos_iff hq' hpos).mpr (fun ⟨h2, h1⟩ => h (h2 ▸ h1))
    omega

/-- **0m.** v_2(c) = 1 ⇔ c ≡ 2 (mod 4)（c ≠ 0）。よって m(c) > 0 ⇔ c ≢ 2 (mod 4)。 -/
theorem factorization_two_eq_one_iff {c : ℕ} (hc : c ≠ 0) : c.factorization 2 = 1 ↔ c % 4 = 2 := by
  have h2 : 2 ∣ c ↔ 1 ≤ c.factorization 2 := by
    have := Nat.prime_two.pow_dvd_iff_le_factorization (k := 1) hc
    rwa [pow_one] at this
  have h4 : 4 ∣ c ↔ 2 ≤ c.factorization 2 := by
    have := Nat.prime_two.pow_dvd_iff_le_factorization (k := 2) hc
    norm_num at this
    exact this
  constructor
  · intro hv
    have := h2.mpr (by omega)
    have := mt h4.mp (by omega)
    omega
  · intro hc4
    have := h2.mp (by omega)
    have := mt h4.mpr (by omega)
    omega

/-! ### 1. 層の大きさ n_(c,d) -/

/-- **1a.** d ∈ D(c) なら n_(c,d) = #{v ∣ L : v は d の層} = Π_{q ∣ L, q ∤ c} (v_q(L) + 1)（d によらない。L ≠ 0）。 -/
theorem card_layerDivs {c L d : ℕ} (hL : L ≠ 0) (hd : d ∈ layerIdx c L) :
    (layerDivs c d L).card = ∏ q ∈ L.primeFactors.filter (fun q => ¬ q ∣ c), (L.factorization q + 1) := by
  classical
  obtain ⟨Lc, hLc, L', hLeq, hL'⟩ := exists_layer c L hL
  have hLc0 : Lc ≠ 0 := fun h => hL (by rw [hLeq, h, zero_mul])
  have hL'0 : L' ≠ 0 := fun h => hL (by rw [hLeq, h, mul_zero])
  obtain ⟨hdL, hdc⟩ := (mem_layerIdx c L d).mp hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hdL).ne'
  have hdLc : d ∣ Lc :=
    (coprime_of_radDvd hdc hL').dvd_of_dvd_mul_right (by rw [← hLeq]; exact Nat.dvd_of_mem_divisors hdL)
  have hset : layerDivs c d L = L'.divisors.image (fun e => d * e) := by
    ext v
    rw [mem_layerDivs, Finset.mem_image]
    constructor
    · rintro ⟨hvL, e, rfl, he⟩
      refine ⟨e, Nat.mem_divisors.mpr ⟨?_, hL'0⟩, rfl⟩
      have heLc : Nat.Coprime e Lc := (coprime_of_radDvd hLc he).symm
      exact heLc.dvd_of_dvd_mul_left
        (by rw [← hLeq]; exact dvd_trans (Dvd.intro_left d rfl) (Nat.dvd_of_mem_divisors hvL))
    · rintro ⟨e, he, rfl⟩
      have heL' := Nat.dvd_of_mem_divisors he
      refine ⟨Nat.mem_divisors.mpr ⟨?_, hL⟩, e, rfl, Nat.Coprime.coprime_dvd_left heL' hL'⟩
      rw [hLeq]
      exact Nat.mul_dvd_mul hdLc heL'
  rw [hset, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h),
    Nat.card_divisors hL'0]
  have hpf : L'.primeFactors = L.primeFactors.filter (fun q => ¬ q ∣ c) := by
    ext q
    rw [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hq, hqL', -⟩
      refine ⟨⟨hq, dvd_trans hqL' ⟨Lc, by rw [hLeq, mul_comm]⟩, hL⟩, fun hqc => ?_⟩
      have h1 := Nat.dvd_gcd hqL' hqc
      rw [Nat.Coprime.gcd_eq_one hL'] at h1
      exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
    · rintro ⟨⟨hq, hqL, -⟩, hqc⟩
      refine ⟨hq, ?_, hL'0⟩
      rw [hLeq] at hqL
      rcases (Nat.Prime.dvd_mul hq).mp hqL with h | h
      · exact absurd (hLc q hq h) hqc
      · exact h
  rw [hpf]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  obtain ⟨hqL, hqc⟩ := Finset.mem_filter.mp hq
  have hq' : q.Prime := (Nat.mem_primeFactors.mp hqL).1
  have hqLc : ¬ q ∣ Lc := fun h => hqc (hLc q hq' h)
  rw [hLeq, Nat.factorization_mul hLc0 hL'0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqLc, zero_add]

/-- **1b.** Σ_{d ∈ D(c)} n_(c,d) = d(L)（L ≠ 0。L の約数はちょうど 1 つの層に入る）。 -/
theorem sum_card_layerDivs {c L : ℕ} (hL : L ≠ 0) :
    ∑ d ∈ layerIdx c L, (layerDivs c d L).card = L.divisors.card := by
  classical
  have hdisj : ((layerIdx c L : Set ℕ)).PairwiseDisjoint (fun d => layerDivs c d L) := by
    intro d₁ hd₁ d₂ hd₂ hne
    show Disjoint (layerDivs c d₁ L) (layerDivs c d₂ L)
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact hne (layer_unique ((mem_layerIdx c L d₁).mp (Finset.mem_coe.mp hd₁)).2
      ((mem_layerIdx c L d₂).mp (Finset.mem_coe.mp hd₂)).2
      ((mem_layerDivs c d₁ L v).mp hv1).2 ((mem_layerDivs c d₂ L v).mp hv2).2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext v
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨d, -, hv⟩
    exact ((mem_layerDivs c d L v).mp hv).1
  · intro hv
    obtain ⟨d, hd, hvd⟩ := exists_layer c v (Nat.pos_of_mem_divisors hv).ne'
    refine ⟨d, (mem_layerIdx c L d).mpr ⟨Nat.mem_divisors.mpr ⟨?_, hL⟩, hd⟩,
      (mem_layerDivs c d L v).mpr ⟨hv, hvd⟩⟩
    obtain ⟨e, he, -⟩ := hvd
    exact dvd_trans ⟨e, he⟩ (Nat.dvd_of_mem_divisors hv)

/-- **1c.** Σ_{p ∈ S} n_p·m(c_p) = N（ℂ^{ℤ/N} = ⊕_p W_p ⊗ ℂ^{m(c)} の次元の式。Part 209 の Σ_c m(c)·d(N/c) = N から）。 -/
theorem sum_centerIdx_card_mul_primCount (N : ℕ) [NeZero N] :
    ∑ p : centerIdx N, (layerDivs p.1.1 p.1.2 (N / p.1.1)).card * primCount p.1.1 = N := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  rw [Finset.sum_coe_sort (centerIdx N) (fun p => (layerDivs p.1 p.2 (N / p.1)).card * primCount p.1)]
  unfold centerIdx
  rw [Finset.sum_sigma, Finset.sum_filter]
  conv_rhs => rw [← sum_card_primitive_mul_card_divisors N]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hcN := Nat.dvd_of_mem_divisors hc
  have hL : N / c ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel hcN
    rw [h0, zero_mul] at this
    exact hN this.symm
  dsimp only
  split_ifs with hpos
  · rw [← Finset.sum_mul, sum_card_layerDivs hL, mul_comm]
    rfl
  · have h0 : Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} = 0 := by omega
    rw [h0, zero_mul]

/-! ### 2. 約数の和と素因数ごとの積 -/

/-- **2a.** 異なる素数のべきの積 Π_{q ∈ s} q^{x(q)} の v_r は x(r)。 -/
theorem factorization_prod_pow_subtype {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) (x : s → ℕ) (r : s) :
    (∏ q : s, (q : ℕ) ^ x q).factorization r = x r := by
  classical
  rw [Nat.factorization_prod (S := (Finset.univ : Finset s)) (g := fun q : s => (q : ℕ) ^ x q)
    (fun q _ => pow_ne_zero _ (hs q.1 q.2).ne_zero), Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single r]
  · rw [(hs r.1 r.2).factorization_self, mul_one]
  · intro q _ hqr
    rw [Nat.factorization_eq_zero_of_not_dvd, mul_zero]
    intro hdvd
    exact hqr (Subtype.ext ((Nat.prime_dvd_prime_iff_eq (hs r.1 r.2) (hs q.1 q.2)).mp hdvd).symm)
  · intro h
    exact absurd (Finset.mem_univ r) h

/-- **2b.** c ∣ N（N ≠ 0）なら Π_{q ∣ N} q^{v_q(c)} = c。 -/
theorem prod_primeFactors_pow_factorization {c N : ℕ} (hN : N ≠ 0) (hcN : c ∣ N) :
    ∏ q : N.primeFactors, (q : ℕ) ^ c.factorization q = c := by
  have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
  rw [Finset.prod_coe_sort N.primeFactors (fun q => q ^ c.factorization q)]
  rw [← Finsupp.prod_of_support_subset c.factorization
    (by rw [Nat.support_factorization]; exact Nat.primeFactors_mono hcN hN) (fun q k => q ^ k)
    (fun q _ => pow_zero q)]
  exact Nat.prod_factorization_pow_eq_self hc0

/-- **2c. 約数の和と素因数ごとの積**：Σ_{c ∣ N} Π_{q ∣ N} w_q(v_q(c)) = Π_{q ∣ N} Σ_{γ ≤ v_q(N)} w_q(γ)（N ≠ 0。
c ↔ (v_q(c))_q の全単射と分配法則）。 -/
theorem sum_divisors_prod_factorization {R : Type*} [CommSemiring R] {N : ℕ} (hN : N ≠ 0) (w : ℕ → ℕ → R) :
    ∑ c ∈ N.divisors, ∏ q ∈ N.primeFactors, w q (c.factorization q) =
      ∏ q ∈ N.primeFactors, ∑ γ ∈ Finset.range (N.factorization q + 1), w q γ := by
  classical
  have hs : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => (Nat.mem_primeFactors.mp hq).1
  rw [← Finset.prod_coe_sort N.primeFactors (fun q => ∑ γ ∈ Finset.range (N.factorization q + 1), w q γ),
    Finset.prod_univ_sum]
  symm
  refine Finset.sum_nbij' (fun x => ∏ q : N.primeFactors, (q : ℕ) ^ x q) (fun c q => c.factorization q)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Nat.mem_divisors]
    refine ⟨?_, hN⟩
    conv_rhs => rw [← prod_primeFactors_pow_factorization hN (dvd_refl N)]
    refine Finset.prod_dvd_prod_of_dvd _ _ (fun q _ => pow_dvd_pow _ ?_)
    have := Finset.mem_range.mp (Fintype.mem_piFinset.mp hx q)
    omega
  · intro c hc
    have hcN := Nat.dvd_of_mem_divisors hc
    have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
    refine Fintype.mem_piFinset.mpr (fun q => Finset.mem_range.mpr ?_)
    have := (Nat.factorization_le_iff_dvd hc0 hN).mpr hcN q
    omega
  · intro x _
    funext r
    exact factorization_prod_pow_subtype hs x r
  · intro c hc
    exact prod_primeFactors_pow_factorization hN (Nat.dvd_of_mem_divisors hc)
  · intro x _
    rw [← Finset.prod_coe_sort N.primeFactors
      (fun q => w q ((∏ q : N.primeFactors, (q : ℕ) ^ x q).factorization q))]
    refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [factorization_prod_pow_subtype hs x r]

/-- **2d.** c ∣ N なら [m(c) > 0] = Π_{q ∣ N} [m(q^{v_q(c)}) > 0]。 -/
theorem ind_primCount_pos_eq_prod {c N : ℕ} (hN : N ≠ 0) (hcN : c ∣ N) :
    (if 0 < primCount c then 1 else 0 : ℕ) =
      ∏ q ∈ N.primeFactors, (if 0 < primCount (q ^ c.factorization q) then 1 else 0 : ℕ) := by
  rw [Finset.prod_boole]
  refine if_congr ?_ rfl rfl
  rw [primCount_eq_prod_of_dvd hN hcN, Nat.pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  simp only [Nat.pos_iff_ne_zero]

/-- **2e.** c ∣ N なら #D(c) = Π_{q ∣ N} (v_q(c) = 0 なら 1、でなければ v_q(N) + 1 − v_q(c))。 -/
theorem card_layerIdx_eq_prod {c N : ℕ} (hN : N ≠ 0) (hcN : c ∣ N) :
    (layerIdx c (N / c)).card = ∏ q ∈ N.primeFactors,
      (if c.factorization q = 0 then 1 else N.factorization q + 1 - c.factorization q) := by
  have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
  have hL : N / c ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hcN) (Nat.pos_of_ne_zero hc0)).ne'
  have hfac : ∀ q, (N / c).factorization q = N.factorization q - c.factorization q := fun q => by
    rw [Nat.factorization_div hcN, Finsupp.tsub_apply]
  have hle : ∀ q, c.factorization q ≤ N.factorization q :=
    fun q => (Nat.factorization_le_iff_dvd hc0 hN).mpr hcN q
  have hsub : (Nat.gcd c (N / c)).primeFactors ⊆ N.primeFactors :=
    Nat.primeFactors_mono (dvd_trans (Nat.gcd_dvd_left c (N / c)) hcN) hN
  rw [card_layerIdx c (N / c) hL]
  calc ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1)
      = ∏ q ∈ (Nat.gcd c (N / c)).primeFactors,
          (if c.factorization q = 0 then 1 else N.factorization q + 1 - c.factorization q) := by
        refine Finset.prod_congr rfl (fun q hq => ?_)
        have hq' : q.Prime := (Nat.mem_primeFactors.mp hq).1
        have hqc : q ∣ c := dvd_trans (Nat.mem_primeFactors.mp hq).2.1 (Nat.gcd_dvd_left _ _)
        have hpos := hq'.factorization_pos_of_dvd hc0 hqc
        rw [ite_eq_right hpos.ne', hfac]
        have := hle q
        omega
    _ = _ := by
        refine Finset.prod_subset hsub (fun q hqN hqg => ?_)
        split_ifs with h0
        · rfl
        · have hq : q.Prime := (Nat.mem_primeFactors.mp hqN).1
          have hqc : q ∣ c := by
            by_contra hn
            exact h0 (Nat.factorization_eq_zero_of_not_dvd hn)
          have hg0 : Nat.gcd c (N / c) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hc0)).ne'
          have hqL : ¬ q ∣ N / c := fun h => hqg (Nat.mem_primeFactors.mpr ⟨hq, Nat.dvd_gcd hqc h, hg0⟩)
          have h1 := Nat.factorization_eq_zero_of_not_dvd hqL
          rw [hfac] at h1
          have := hle q
          omega

/-- **2f.** c ∣ N なら n_(c,d) = Π_{q ∣ N} (v_q(c) = 0 なら v_q(N) + 1、でなければ 1)。 -/
theorem layerSize_eq_prod {c N : ℕ} (hN : N ≠ 0) (hcN : c ∣ N) :
    ∏ q ∈ (N / c).primeFactors.filter (fun q => ¬ q ∣ c), ((N / c).factorization q + 1) =
      ∏ q ∈ N.primeFactors, (if c.factorization q = 0 then N.factorization q + 1 else 1) := by
  have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
  have hL : N / c ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hcN) (Nat.pos_of_ne_zero hc0)).ne'
  have hfac : ∀ q, (N / c).factorization q = N.factorization q - c.factorization q := fun q => by
    rw [Nat.factorization_div hcN, Finsupp.tsub_apply]
  have hsub : (N / c).primeFactors.filter (fun q => ¬ q ∣ c) ⊆ N.primeFactors := fun q hq =>
    Nat.primeFactors_mono (Nat.div_dvd_of_dvd hcN) hN (Finset.mem_filter.mp hq).1
  calc ∏ q ∈ (N / c).primeFactors.filter (fun q => ¬ q ∣ c), ((N / c).factorization q + 1)
      = ∏ q ∈ (N / c).primeFactors.filter (fun q => ¬ q ∣ c),
          (if c.factorization q = 0 then N.factorization q + 1 else 1) := by
        refine Finset.prod_congr rfl (fun q hq => ?_)
        obtain ⟨-, hqc⟩ := Finset.mem_filter.mp hq
        have h0 := Nat.factorization_eq_zero_of_not_dvd hqc
        rw [ite_eq_left h0, hfac, h0, Nat.sub_zero]
    _ = _ := by
        refine Finset.prod_subset hsub (fun q hqN hqf => ?_)
        split_ifs with h0
        · exfalso
          have hq : q.Prime := (Nat.mem_primeFactors.mp hqN).1
          have hqc : ¬ q ∣ c := fun h => (hq.factorization_pos_of_dvd hc0 h).ne' h0
          have hkpos := hq.factorization_pos_of_dvd hN (Nat.mem_primeFactors.mp hqN).2.1
          have hqL : q ∣ N / c := by
            by_contra hn
            have h1 := Nat.factorization_eq_zero_of_not_dvd hn
            rw [hfac, h0] at h1
            omega
          exact hqf (Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq, hqL, hL⟩, hqc⟩)
        · rfl

/-- **2g.** Σ_{γ ≤ k} f(γ) = f(0) + Σ_{γ=1..k} f(γ)。 -/
theorem sum_range_eq_add_sum_Icc {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ γ ∈ Finset.range (k + 1), f γ = f 0 + ∑ γ ∈ Finset.Icc 1 k, f γ := by
  have hIco : Finset.Ico 1 (k + 1) = Finset.Icc 1 k := by
    ext γ
    rw [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add, hIco]

/-! ### 3. 次元の積の式 -/

/-- **3a. dim A = Π_{p ∣ N} ((k+1)² + Σ_{γ=1..k} [m(p^γ) > 0](k + 1 − γ))**（k = v_p(N)）。 -/
theorem finrank_shellAlg_eq_prod_sum (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = ∏ q ∈ N.primeFactors,
      ((N.factorization q + 1) ^ 2 + ∑ γ ∈ Finset.Icc 1 (N.factorization q),
        (if 0 < primCount (q ^ γ) then N.factorization q + 1 - γ else 0)) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  rw [finrank_shellAlg, Finset.sum_coe_sort (centerIdx N) (fun p => (layerDivs p.1 p.2 (N / p.1)).card ^ 2)]
  unfold centerIdx
  rw [Finset.sum_sigma, Finset.sum_filter]
  have step : ∀ c ∈ N.divisors,
      (if 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} then
        ∑ d ∈ layerIdx c (N / c), (layerDivs (⟨c, d⟩ : Σ _ : ℕ, ℕ).1 (⟨c, d⟩ : Σ _ : ℕ, ℕ).2
          (N / (⟨c, d⟩ : Σ _ : ℕ, ℕ).1)).card ^ 2 else 0) =
      ∏ q ∈ N.primeFactors, ((if 0 < primCount (q ^ c.factorization q) then 1 else 0) *
        (if c.factorization q = 0 then (N.factorization q + 1) ^ 2
          else N.factorization q + 1 - c.factorization q)) := by
    intro c hc
    have hcN := Nat.dvd_of_mem_divisors hc
    have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
    have hL : N / c ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hcN) (Nat.pos_of_ne_zero hc0)).ne'
    dsimp only
    have hconst : ∀ d ∈ layerIdx c (N / c), (layerDivs c d (N / c)).card ^ 2 =
        (∏ q ∈ (N / c).primeFactors.filter (fun q => ¬ q ∣ c), ((N / c).factorization q + 1)) ^ 2 :=
      fun d hd => by rw [card_layerDivs hL hd]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, card_layerIdx_eq_prod hN hcN,
      layerSize_eq_prod hN hcN, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    conv_rhs => rw [Finset.prod_mul_distrib, ← ind_primCount_pos_eq_prod hN hcN]
    show (if 0 < primCount c then _ else 0) = _
    rw [ite_mul, one_mul, zero_mul]
    refine if_congr Iff.rfl (Finset.prod_congr rfl (fun q _ => ?_)) rfl
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step]
  refine (sum_divisors_prod_factorization hN (fun q γ => (if 0 < primCount (q ^ γ) then 1 else 0) *
    (if γ = 0 then (N.factorization q + 1) ^ 2 else N.factorization q + 1 - γ))).trans ?_
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [sum_range_eq_add_sum_Icc]
  rw [pow_zero, primCount_one, ite_eq_left one_pos, ite_eq_left rfl, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  have hγ0 : γ ≠ 0 := by have := (Finset.mem_Icc.mp hγ).1; omega
  rw [ite_eq_right hγ0]
  split_ifs <;> simp

/-- **3b.** 2·Σ_{γ=1..k} (k + 1 − γ) = k(k + 1)。 -/
theorem two_mul_sum_Icc_sub (k : ℕ) : 2 * ∑ γ ∈ Finset.Icc 1 k, (k + 1 - γ) = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h : ∑ γ ∈ Finset.Icc 1 k, (k + 1 + 1 - γ) = ∑ γ ∈ Finset.Icc 1 k, (k + 1 - γ) + k := by
      have e : ∀ γ ∈ Finset.Icc 1 k, k + 1 + 1 - γ = (k + 1 - γ) + 1 := fun γ hγ => by
        have := (Finset.mem_Icc.mp hγ).2
        omega
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Icc,
        Nat.add_sub_cancel]
    rw [h, show k + 1 + 1 - (k + 1) = 1 by omega]
    nlinarith [ih]

/-- **3c.** Σ_{γ=1..k} [m(p^γ) > 0](k + 1 − γ) = k(k + 1)/2 − [p = 2]k（p は素数）。 -/
theorem sum_Icc_primCount_pos {q k : ℕ} (hq : q.Prime) :
    ∑ γ ∈ Finset.Icc 1 k, (if 0 < primCount (q ^ γ) then k + 1 - γ else 0) =
      k * (k + 1) / 2 - (if q = 2 then k else 0) := by
  have hG := two_mul_sum_Icc_sub k
  by_cases h2 : q = 2
  · subst h2
    rw [ite_eq_left rfl]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hIco : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
        ext γ
        rw [Finset.mem_Ico, Finset.mem_Icc]
        omega
      rw [hIco, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      rw [hIco, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at hG
      have h1 : ¬ 0 < primCount (2 ^ 1) := by
        rw [pow_one, primCount_prime Nat.prime_two]
        omega
      rw [ite_eq_right h1]
      have hrest : ∀ γ ∈ Finset.Ico (1 + 1) (k + 1),
          (if 0 < primCount (2 ^ γ) then k + 1 - γ else 0) = k + 1 - γ := fun γ hγ => by
        have := (Finset.mem_Ico.mp hγ).1
        exact ite_eq_left ((primCount_prime_pow_pos_iff Nat.prime_two (by omega)).mpr
          (fun h => absurd h.2 (by omega)))
      rw [Finset.sum_congr rfl hrest]
      generalize k * (k + 1) = P at hG ⊢
      generalize ∑ γ ∈ Finset.Ico (1 + 1) (k + 1), (k + 1 - γ) = T at hG ⊢
      omega
  · rw [ite_eq_right h2, Nat.sub_zero]
    have hall : ∀ γ ∈ Finset.Icc 1 k, (if 0 < primCount (q ^ γ) then k + 1 - γ else 0) = k + 1 - γ :=
      fun γ hγ => ite_eq_left ((primCount_prime_pow_pos_iff hq (Finset.mem_Icc.mp hγ).1).mpr (fun h => h2 h.1))
    rw [Finset.sum_congr rfl hall]
    generalize k * (k + 1) = P at hG ⊢
    generalize ∑ γ ∈ Finset.Icc 1 k, (k + 1 - γ) = T at hG ⊢
    omega

/-- **3d. dim A = Π_{p^k ∥ N} ((k+1)² + k(k+1)/2 − [p = 2]k)**（奇素数では (k+1)² + k(k+1)/2、
p = 2 では (k+1)² + k(k−1)/2）。 -/
theorem finrank_shellAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = ∏ q ∈ N.primeFactors,
      ((N.factorization q + 1) ^ 2 + N.factorization q * (N.factorization q + 1) / 2 -
        (if q = 2 then N.factorization q else 0)) := by
  rw [finrank_shellAlg_eq_prod_sum]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hq' := (Nat.mem_primeFactors.mp hq).1
  rw [sum_Icc_primCount_pos hq']
  have hk : 1 ≤ N.factorization q :=
    hq'.factorization_pos_of_dvd (NeZero.ne N) (Nat.mem_primeFactors.mp hq).2.1
  have hP : 2 * N.factorization q ≤ N.factorization q * (N.factorization q + 1) := by nlinarith
  generalize (N.factorization q + 1) ^ 2 = Q
  generalize N.factorization q * (N.factorization q + 1) = P at hP ⊢
  split_ifs <;> omega

/-- **3e.** #{(σ, τ) : σ, τ < k, σ + τ ≤ k − 1, m(p^(k−σ−τ)) > 0} = Σ_{γ=1..k} [m(p^γ) > 0](k + 1 − γ)
（γ = k − σ − τ。和が k − γ の組は k − γ + 1 個）。 -/
theorem card_part214 (p k : ℕ) :
    ((Finset.range k ×ˢ Finset.range k).filter (fun st : ℕ × ℕ =>
      st.1 + st.2 ≤ k - 1 ∧ 0 < primCount (p ^ (k - st.1 - st.2)))).card =
      ∑ γ ∈ Finset.Icc 1 k, (if 0 < primCount (p ^ γ) then k + 1 - γ else 0) := by
  classical
  set s := (Finset.range k ×ˢ Finset.range k).filter (fun st : ℕ × ℕ =>
      st.1 + st.2 ≤ k - 1 ∧ 0 < primCount (p ^ (k - st.1 - st.2))) with hs
  have hmaps : Set.MapsTo (fun st : ℕ × ℕ => st.1 + st.2) ↑s ↑(Finset.range k) := by
    intro st hst
    have h := Finset.mem_coe.mp hst
    rw [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at h
    rw [Finset.mem_coe, Finset.mem_range]
    dsimp only
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ j ∈ Finset.range k, (s.filter (fun st : ℕ × ℕ => st.1 + st.2 = j)).card =
      if 0 < primCount (p ^ (k - j)) then j + 1 else 0 := by
    intro j hj
    have hjk := Finset.mem_range.mp hj
    split_ifs with hP
    · rw [← Finset.Nat.card_antidiagonal j]
      congr 1
      ext ⟨a, b⟩
      rw [hs, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range,
        Finset.mem_antidiagonal]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        refine ⟨⟨⟨by omega, by omega⟩, by omega, ?_⟩, h⟩
        have e : k - a - b = k - j := by omega
        rw [e]
        exact hP
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro ⟨a, b⟩ hab hj'
      rw [hs, Finset.mem_filter] at hab
      apply hP
      have e : k - a - b = k - j := by
        have := hab.2.1
        simp only at hj' this ⊢
        omega
      rw [← e]
      exact hab.2.2
  rw [Finset.sum_congr rfl hfib]
  refine Finset.sum_nbij' (fun j => k - j) (fun γ => k - γ) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have := Finset.mem_range.mp hj
    rw [Finset.mem_Icc]
    omega
  · intro γ hγ
    have := Finset.mem_Icc.mp hγ
    rw [Finset.mem_range]
    omega
  · intro j hj
    have := Finset.mem_range.mp hj
    omega
  · intro γ hγ
    have := Finset.mem_Icc.mp hγ
    omega
  · intro j hj
    have := Finset.mem_range.mp hj
    have e : k + 1 - (k - j) = j + 1 := by omega
    rw [e]

/-- **3f. Part 214 の式**：dim A = Π_{p^k ∥ N} ((k+1)² + #{(σ, τ) : σ + τ ≤ k − 1, m(p^(k−σ−τ)) > 0})
（Part 214・224 では数値だけだった式）。 -/
theorem finrank_shellAlg_eq_part214 (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = ∏ q ∈ N.primeFactors, ((N.factorization q + 1) ^ 2 +
      ((Finset.range (N.factorization q) ×ˢ Finset.range (N.factorization q)).filter (fun st : ℕ × ℕ =>
        st.1 + st.2 ≤ N.factorization q - 1 ∧
          0 < primCount (q ^ (N.factorization q - st.1 - st.2)))).card) := by
  rw [finrank_shellAlg_eq_prod_sum]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [card_part214]

/-- **3g. dim A′ = Π_{p^k ∥ N} (1 + Σ_{γ=1..k} m(p^γ)²(k + 1 − γ))**（Part 220 の Σ_c m(c)²π(c) を積に）。 -/
theorem finrank_fullComm_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullComm N) = ∏ q ∈ N.primeFactors,
      (1 + ∑ γ ∈ Finset.Icc 1 (N.factorization q), primCount (q ^ γ) ^ 2 * (N.factorization q + 1 - γ)) := by
  have hN : N ≠ 0 := NeZero.ne N
  rw [finrank_fullComm]
  have step : ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ^ 2 *
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) =
      ∏ q ∈ N.primeFactors, (primCount (q ^ c.factorization q) ^ 2 *
        (if c.factorization q = 0 then 1 else N.factorization q + 1 - c.factorization q)) := by
    intro c hc
    have hcN := Nat.dvd_of_mem_divisors hc
    have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
    have hL : N / c ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hcN) (Nat.pos_of_ne_zero hc0)).ne'
    rw [← card_layerIdx c (N / c) hL, card_layerIdx_eq_prod hN hcN, Finset.prod_mul_distrib, Finset.prod_pow,
      ← primCount_eq_prod_of_dvd hN hcN]
    rfl
  rw [Finset.sum_congr rfl step]
  refine (sum_divisors_prod_factorization hN (fun q γ => primCount (q ^ γ) ^ 2 *
    (if γ = 0 then 1 else N.factorization q + 1 - γ))).trans ?_
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [sum_range_eq_add_sum_Icc, pow_zero, primCount_one, ite_eq_left rfl, one_pow, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  have hγ0 : γ ≠ 0 := by have := (Finset.mem_Icc.mp hγ).1; omega
  rw [ite_eq_right hγ0]

/-- **3h.** dim Z(A′) = #S = Π_{p^k ∥ N} (1 + Σ_{γ=1..k} [m(p^γ) > 0](k + 1 − γ))。 -/
theorem finrank_fullCommCenter_eq_prod_sum (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommCenter N) = ∏ q ∈ N.primeFactors,
      (1 + ∑ γ ∈ Finset.Icc 1 (N.factorization q),
        (if 0 < primCount (q ^ γ) then N.factorization q + 1 - γ else 0)) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  rw [finrank_fullCommCenter, Finset.sum_filter]
  have step : ∀ c ∈ N.divisors, (if 0 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} then
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1) else 0) =
      ∏ q ∈ N.primeFactors, ((if 0 < primCount (q ^ c.factorization q) then 1 else 0) *
        (if c.factorization q = 0 then 1 else N.factorization q + 1 - c.factorization q)) := by
    intro c hc
    have hcN := Nat.dvd_of_mem_divisors hc
    have hc0 : c ≠ 0 := ne_zero_of_dvd_ne_zero hN hcN
    have hL : N / c ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hcN) (Nat.pos_of_ne_zero hc0)).ne'
    rw [← card_layerIdx c (N / c) hL, card_layerIdx_eq_prod hN hcN, Finset.prod_mul_distrib,
      ← ind_primCount_pos_eq_prod hN hcN]
    show (if 0 < primCount c then _ else 0) = _
    rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl step]
  refine (sum_divisors_prod_factorization hN (fun q γ => (if 0 < primCount (q ^ γ) then 1 else 0) *
    (if γ = 0 then 1 else N.factorization q + 1 - γ))).trans ?_
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [sum_range_eq_add_sum_Icc, pow_zero, primCount_one, ite_eq_left one_pos, ite_eq_left rfl, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  have hγ0 : γ ≠ 0 := by have := (Finset.mem_Icc.mp hγ).1; omega
  rw [ite_eq_right hγ0]
  split_ifs <;> simp

/-- **3i. dim Z(A′) = #S = Π_{p^k ∥ N} (1 + k(k+1)/2 − [p = 2]k)**。 -/
theorem finrank_fullCommCenter_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommCenter N) = ∏ q ∈ N.primeFactors,
      (1 + N.factorization q * (N.factorization q + 1) / 2 - (if q = 2 then N.factorization q else 0)) := by
  rw [finrank_fullCommCenter_eq_prod_sum]
  refine Finset.prod_congr rfl (fun q hq => ?_)
  have hq' := (Nat.mem_primeFactors.mp hq).1
  rw [sum_Icc_primCount_pos hq']
  have hk : 1 ≤ N.factorization q :=
    hq'.factorization_pos_of_dvd (NeZero.ne N) (Nat.mem_primeFactors.mp hq).2.1
  have hP : 2 * N.factorization q ≤ N.factorization q * (N.factorization q + 1) := by nlinarith
  generalize N.factorization q * (N.factorization q + 1) = P at hP ⊢
  split_ifs <;> omega

set_option synthInstance.maxHeartbeats 400000 in
/-- **3j.** dim Z(A)（Mathlib の Subalgebra.center、Part 225 で Z(A) = Z(A′)）= Π_{p^k ∥ N} (1 + k(k+1)/2 − [p = 2]k)。 -/
theorem finrank_center_shellAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Subalgebra.center ℂ (shellAlg N)) = ∏ q ∈ N.primeFactors,
      (1 + N.factorization q * (N.factorization q + 1) / 2 - (if q = 2 then N.factorization q else 0)) :=
  (finrank_center_shellAlg N).trans ((finrank_fullCommCenter N).symm.trans (finrank_fullCommCenter_eq_prod N))

/-! ### 4. N についての乗法性 -/

/-- **4a.** gcd(a, b) = 1（a, b ≠ 0）なら Π_{q ∣ ab} f(q, v_q(ab)) = Π_{q ∣ a} f(q, v_q(a))·Π_{q ∣ b} f(q, v_q(b))。 -/
theorem prod_primeFactors_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b)
    (f : ℕ → ℕ → ℕ) :
    ∏ q ∈ (a * b).primeFactors, f q ((a * b).factorization q) =
      (∏ q ∈ a.primeFactors, f q (a.factorization q)) * ∏ q ∈ b.primeFactors, f q (b.factorization q) := by
  classical
  rw [Nat.Coprime.primeFactors_mul hab, Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
  congr 1
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqb : ¬ q ∣ b := fun h => by
      have h1 := Nat.dvd_gcd (Nat.mem_primeFactors.mp hq).2.1 h
      rw [Nat.Coprime.gcd_eq_one hab] at h1
      exact (Nat.mem_primeFactors.mp hq).1.one_lt.ne' (Nat.dvd_one.mp h1)
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqb, add_zero]
  · refine Finset.prod_congr rfl (fun q hq => ?_)
    have hqa : ¬ q ∣ a := fun h => by
      have h1 := Nat.dvd_gcd h (Nat.mem_primeFactors.mp hq).2.1
      rw [Nat.Coprime.gcd_eq_one hab] at h1
      exact (Nat.mem_primeFactors.mp hq).1.one_lt.ne' (Nat.dvd_one.mp h1)
    rw [Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hqa, zero_add]

/-- **4b. dim A は N について乗法的**：gcd(a, b) = 1 なら dim A_{ab} = dim A_a·dim A_b。 -/
theorem finrank_shellAlg_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (shellAlg (a * b)) = Module.finrank ℂ (shellAlg a) * Module.finrank ℂ (shellAlg b) := by
  rw [finrank_shellAlg_eq_prod, finrank_shellAlg_eq_prod, finrank_shellAlg_eq_prod]
  exact prod_primeFactors_mul_of_coprime (NeZero.ne a) (NeZero.ne b) hab
    (fun q k => (k + 1) ^ 2 + k * (k + 1) / 2 - (if q = 2 then k else 0))

/-- **4c.** dim A′ も N について乗法的。 -/
theorem finrank_fullComm_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (fullComm (a * b)) = Module.finrank ℂ (fullComm a) * Module.finrank ℂ (fullComm b) := by
  rw [finrank_fullComm_eq_prod, finrank_fullComm_eq_prod, finrank_fullComm_eq_prod]
  exact prod_primeFactors_mul_of_coprime (NeZero.ne a) (NeZero.ne b) hab
    (fun q k => 1 + ∑ γ ∈ Finset.Icc 1 k, primCount (q ^ γ) ^ 2 * (k + 1 - γ))

/-- **4d.** dim Z(A′) = #S も N について乗法的。 -/
theorem finrank_fullCommCenter_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (fullCommCenter (a * b)) =
      Module.finrank ℂ (fullCommCenter a) * Module.finrank ℂ (fullCommCenter b) := by
  rw [finrank_fullCommCenter_eq_prod, finrank_fullCommCenter_eq_prod, finrank_fullCommCenter_eq_prod]
  exact prod_primeFactors_mul_of_coprime (NeZero.ne a) (NeZero.ne b) hab
    (fun q k => 1 + k * (k + 1) / 2 - (if q = 2 then k else 0))

end PAG.Part230

#print axioms PAG.Part230.primCount
#print axioms PAG.Part230.totientAF
#print axioms PAG.Part230.totientAF_apply
#print axioms PAG.Part230.totientAF_isMultiplicative
#print axioms PAG.Part230.primCount_eq_moebius_mul
#print axioms PAG.Part230.primCount_one
#print axioms PAG.Part230.primCount_mul
#print axioms PAG.Part230.primCount_eq_prod
#print axioms PAG.Part230.primCount_eq_prod_of_dvd
#print axioms PAG.Part230.primCount_prime_pow_succ_add
#print axioms PAG.Part230.primCount_prime
#print axioms PAG.Part230.primCount_prime_pow
#print axioms PAG.Part230.primCount_prime_pow_pos_iff
#print axioms PAG.Part230.primCount_pos_iff
#print axioms PAG.Part230.factorization_two_eq_one_iff
#print axioms PAG.Part230.card_layerDivs
#print axioms PAG.Part230.sum_card_layerDivs
#print axioms PAG.Part230.sum_centerIdx_card_mul_primCount
#print axioms PAG.Part230.factorization_prod_pow_subtype
#print axioms PAG.Part230.prod_primeFactors_pow_factorization
#print axioms PAG.Part230.sum_divisors_prod_factorization
#print axioms PAG.Part230.ind_primCount_pos_eq_prod
#print axioms PAG.Part230.card_layerIdx_eq_prod
#print axioms PAG.Part230.layerSize_eq_prod
#print axioms PAG.Part230.sum_range_eq_add_sum_Icc
#print axioms PAG.Part230.finrank_shellAlg_eq_prod_sum
#print axioms PAG.Part230.two_mul_sum_Icc_sub
#print axioms PAG.Part230.sum_Icc_primCount_pos
#print axioms PAG.Part230.finrank_shellAlg_eq_prod
#print axioms PAG.Part230.card_part214
#print axioms PAG.Part230.finrank_shellAlg_eq_part214
#print axioms PAG.Part230.finrank_fullComm_eq_prod
#print axioms PAG.Part230.finrank_fullCommCenter_eq_prod_sum
#print axioms PAG.Part230.finrank_fullCommCenter_eq_prod
#print axioms PAG.Part230.finrank_center_shellAlg_eq_prod
#print axioms PAG.Part230.prod_primeFactors_mul_of_coprime
#print axioms PAG.Part230.finrank_shellAlg_mul
#print axioms PAG.Part230.finrank_fullComm_mul
#print axioms PAG.Part230.finrank_fullCommCenter_mul
