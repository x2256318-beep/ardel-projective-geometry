/-
  PAG 2.0 Part 131（2026-10-21）— p = 2 の原始指標の位数と、単独のケットの ζ の位数
  1. 一般化: b^m = 1 + p^c s（p ∤ s）、χ 原始 mod p^{c+1} ⇒ χ(b)^m ≠ 1
  2. 5^{2^k} = 1 + 2^{k+2} s、s 奇数
  3. u 奇数 ⇒ 2^{k+3} ∣ u^{2^{k+1}} − 1、したがって法 2^{c+1}（c ≥ 2）の単元は u^{2^{c−1}} = 1
  4. 法 2^{c+1}（c ≥ 2）の指標は ord χ ∣ 2^{c−1}、原始なら ord χ = 2^{c−1}
  5. 単独のケット（導手 p^{c+1}）の ζ = z^{ord χ}: ord ζ = ord z / gcd(ord z, ord χ)
     p = 2、c ≥ 3 なら ord ζ = 4；p 奇素数なら p ∣ ord ζ、p² ∤ ord ζ
-/
import PAG134

namespace PAG.Part135

open ZMod Finset PAG.Part133

section Gen

variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hc : 1 ≤ c)

include hc in
/-- **1. 一般化**。 -/
theorem chi_pow_ne_one (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive)
    (b : ZMod (p ^ (c + 1))) (m s : ℕ) (hs : ¬ p ∣ s)
    (hg : b ^ m = 1 + (p : ZMod (p ^ (c + 1))) ^ c * s) : χ b ^ m ≠ 1 := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P : ZMod (p ^ (c + 1)) := (p : ZMod (p ^ (c + 1))) ^ c
  obtain ⟨v, hv1, hv⟩ := exists_ker_ne (p := p) c χ hχ
  -- v = 1 + P t
  have hcast : ((v : ZMod (p ^ (c + 1))).cast : ZMod (p ^ c)) = 1 := by
    have := congrArg Units.val hv1
    rw [ZMod.unitsMap_val] at this
    simpa using this
  set wv : ZMod (p ^ (c + 1)) := (v : ZMod (p ^ (c + 1))) - 1
  have hw0 : ((wv.val : ℕ) : ZMod (p ^ c)) = 0 := by
    have h1 : ((wv : ZMod (p ^ (c + 1))).cast : ZMod (p ^ c)) = 0 := by
      simp only [wv]
      rw [ZMod.cast_sub (m := p ^ c) (show p ^ c ∣ p ^ (c + 1) from pow_dvd_pow p (by omega)), hcast, ZMod.cast_one (m := p ^ c) (show p ^ c ∣ p ^ (c + 1) from pow_dvd_pow p (by omega)), sub_self]
    rwa [ZMod.cast_eq_val] at h1
  obtain ⟨t, ht⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hw0
  have hvt : (v : ZMod (p ^ (c + 1))) = 1 + P * t := by
    have : wv = ((wv.val : ℕ) : ZMod (p ^ (c + 1))) := (ZMod.natCast_zmod_val wv).symm
    rw [ht] at this
    simp only [wv, P] at this ⊢
    push_cast at this
    linear_combination this
  -- k s ≡ t (mod p)
  have hs0 : (s : ZMod p) ≠ 0 := fun h => hs ((ZMod.natCast_eq_zero_iff _ _).mp h)
  set k := ((t : ZMod p) * (s : ZMod p)⁻¹).val
  have hks : ((k * s : ℕ) : ZMod p) = (t : ZMod p) := by
    push_cast; simp only [k, ZMod.natCast_val, ZMod.cast_id', id]; field_simp
  have hmod : k * s ≡ t [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hks
  have hmod' : p ^ c * (k * s) ≡ p ^ c * t [MOD p ^ c * p] := Nat.ModEq.mul_left' _ hmod
  rw [← pow_succ] at hmod'
  have hPkt : P * ((k * s : ℕ) : ZMod (p ^ (c + 1))) = P * t := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod'
    simp only [P]; push_cast at this ⊢; exact this
  -- v = g^k
  have hvg : (v : ZMod (p ^ (c + 1))) = (b ^ m) ^ k := by
    rw [hg, one_add_Pc_pow (p := p) c hc, hvt]
    simp only [P] at hPkt ⊢
    push_cast at hPkt
    linear_combination (-1 : ZMod (p ^ (c + 1))) * hPkt
  intro h1
  apply hv
  rw [hvg, ← pow_mul, map_pow, pow_mul, h1, one_pow]

end Gen

/-- **2. 5^{2^k} = 1 + 2^{k+2} s、s 奇数**。 -/
theorem five_pow : ∀ k : ℕ, ∃ s : ℕ, Odd s ∧ 5 ^ (2 ^ k) = 1 + 2 ^ (k + 2) * s := by
  intro k
  induction k with
  | zero => exact ⟨1, odd_one, by norm_num⟩
  | succ k ih =>
    obtain ⟨s, hs, e⟩ := ih
    refine ⟨s + 2 ^ (k + 1) * s ^ 2, ?_, ?_⟩
    · exact hs.add_even (Even.mul_right (Nat.even_pow.mpr ⟨even_two, by omega⟩) _)
    · rw [pow_succ 2 k, pow_mul, e]; ring

/-- **3a. u 奇数 ⇒ 2^{k+3} ∣ u^{2^{k+1}} − 1**（ℤ）。 -/
theorem odd_pow_sub_one (u : ℤ) (hu : Odd u) : ∀ k : ℕ, (2 : ℤ) ^ (k + 3) ∣ u ^ (2 ^ (k + 1)) - 1 := by
  intro k
  induction k with
  | zero =>
    obtain ⟨m, rfl⟩ := hu
    obtain ⟨r, hr⟩ := Int.even_mul_succ_self m
    exact ⟨r, by norm_num; nlinarith [hr]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a * (2 ^ (k + 2) * a + 1), ?_⟩
    have e : u ^ (2 ^ (k + 1 + 1)) = (u ^ (2 ^ (k + 1))) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [e, show u ^ (2 ^ (k + 1)) = 2 ^ (k + 3) * a + 1 by linarith]
    ring

/-- **3b. 法 2^{c+1}（c ≥ 2）の単元は u^{2^{c−1}} = 1**。 -/
theorem unit_pow_two (c : ℕ) (hc : 2 ≤ c) (a : (ZMod (2 ^ (c + 1)))ˣ) :
    (a : ZMod (2 ^ (c + 1))) ^ (2 ^ (c - 1)) = 1 := by
  have : NeZero (2 ^ (c + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcop := ZMod.val_coe_unit_coprime a
  have hodd : Odd ((a : ZMod (2 ^ (c + 1))).val : ℤ) := by
    have : ¬ 2 ∣ (a : ZMod (2 ^ (c + 1))).val := by
      intro h2
      have := Nat.Coprime.coprime_dvd_left h2 hcop
      rw [Nat.coprime_pow_right_iff (by omega)] at this
      norm_num at this
    exact_mod_cast Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp this)
  have h := odd_pow_sub_one _ hodd (c - 2)
  rw [show c - 2 + 3 = c + 1 by omega, show c - 2 + 1 = c - 1 by omega] at h
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ (c + 1))).mpr (by exact_mod_cast h)
  push_cast at h'
  rw [ZMod.natCast_zmod_val] at h'
  linear_combination h'

/-- **4a. ord χ ∣ 2^{c−1}**。 -/
theorem orderOf_chi_two_dvd (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1))) :
    orderOf χ ∣ 2 ^ (c - 1) := by
  apply orderOf_dvd_of_pow_eq_one
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply' _ (pow_ne_zero _ two_ne_zero), ← map_pow, unit_pow_two c hc a, map_one,
    MulChar.one_apply a.isUnit]

/-- **4b. 原始なら ord χ = 2^{c−1}**。 -/
theorem orderOf_chi_two (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (2 ^ (c + 1))) (hχ : χ.IsPrimitive) :
    orderOf χ = 2 ^ (c - 1) := by
  obtain ⟨s, hs, e⟩ := five_pow (c - 2)
  rw [show c - 2 + 2 = c by omega] at e
  have hg : (5 : ZMod (2 ^ (c + 1))) ^ (2 ^ (c - 2)) = 1 + ((2 : ℕ) : ZMod (2 ^ (c + 1))) ^ c * s := by
    have := congrArg (fun n : ℕ => (n : ZMod (2 ^ (c + 1)))) e
    push_cast at this ⊢; exact this
  have hne := chi_pow_ne_one (p := 2) c (by omega) χ hχ 5 (2 ^ (c - 2)) s (by
    intro h; exact (Nat.not_even_iff_odd.mpr hs) (even_iff_two_dvd.mpr h)) hg
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_chi_two_dvd c hc χ)
  rw [hjo]
  congr 1
  by_contra hjc
  apply hne
  have hj2 : j ≤ c - 2 := by omega
  have h1 : χ ^ (2 ^ (c - 2)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hjo]; exact pow_dvd_pow 2 hj2)
  have h5 : IsUnit (5 : ZMod (2 ^ (c + 1))) := by
    have : IsUnit ((5 : ZMod (2 ^ (c + 1))) ^ (2 ^ (c - 2))) := by
      rw [hg]
      refine isUnit_iff_exists_inv.mpr ⟨1 - ((2 : ℕ) : ZMod (2 ^ (c + 1))) ^ c * s, ?_⟩
      have h := Pc_sq (p := 2) c (by omega)
      linear_combination (-((s : ZMod (2 ^ (c + 1))) * s)) * h
    exact (isUnit_pow_iff (pow_ne_zero _ two_ne_zero)).mp this
  rw [← MulChar.pow_apply' _ (pow_ne_zero _ two_ne_zero), h1, MulChar.one_apply h5]

/-! ## 5. 単独のケットの ζ -/

section Single

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117

variable {p : ℕ} [hp : Fact p.Prime]

/-- **5a. ord ζ = ord z / gcd(ord z, ord χ)**。 -/
theorem orderOf_zeta_single (K w c : ℕ) (h : w + (c + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (c + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (c + 1) - w)) :
    orderOf ((cnorm p K (K - (c + 1) - w) * 𝓕 (ket K w (c + 1) h χ) t₀) ^ orderOf χ)
      = orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ))
        / Nat.gcd (orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (c + 1)) : ℝ) : ℂ))) (orderOf χ) := by
  rw [zeta_eq_gauss K w c h χ hχ t₀ ht₀]
  exact orderOf_pow' _ (orderOf_pos χ).ne'

/-- **5b. p 奇素数: p ∣ ord ζ、p² ∤ ord ζ**（c ≥ 1）。 -/
theorem zeta_single_odd (hp2 : p ≠ 2) (K w c : ℕ) (hc : 1 ≤ c) (h : w + (c + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K))
    (ht₀ : t₀ ∈ Tset (p := p) K (K - (c + 1) - w)) :
    p ∣ orderOf ((cnorm p K (K - (c + 1) - w) * 𝓕 (ket K w (c + 1) h χ) t₀) ^ orderOf χ) ∧
    ¬ p ^ 2 ∣ orderOf ((cnorm p K (K - (c + 1) - w) * 𝓕 (ket K w (c + 1) h χ) t₀) ^ orderOf χ) := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [orderOf_zeta_single K w c h χ hχ t₀ ht₀]
  have hb := PAG.Part128.orderOf_gauss_bounds hp2 (c + 1) (by omega) χ hχ
  have hφ := PAG.Part134.orderOf_dvd_totient χ
  rw [Nat.totient_prime_pow hp.out (by omega), show c + 1 - 1 = c by omega] at hφ
  refine ⟨PAG.Part132.p_dvd_div_gcd p hp.out (c + 1) _ _ hb.1
    (fun h' => PAG.Part134.not_pow_succ_dvd hp.out c (h'.trans hφ)), ?_⟩
  exact not_sq_dvd_div_gcd p c _ _ ((pow_dvd_pow p (by omega)).trans hb.1)
    (pc_dvd_orderOf (p := p) c hc (hp.out.odd_of_ne_two hp2) χ hχ)
    (PAG.Part134.not_pow_dvd_gauss hp2 c hc χ hχ)

/-- **5c. p = 2、c ≥ 3: ord ζ = 4**。 -/
theorem zeta_single_two (K w c : ℕ) (hc : 3 ≤ c) (h : w + (c + 1) ≤ K)
    (χ : DirichletCharacter ℂ (2 ^ (c + 1))) (hχ : χ.IsPrimitive) (t₀ : ZMod (2 ^ K))
    (ht₀ : t₀ ∈ Tset (p := 2) K (K - (c + 1) - w)) :
    orderOf ((cnorm 2 K (K - (c + 1) - w) * 𝓕 (ket K w (c + 1) h χ) t₀)
      ^ orderOf χ) = 4 := by
  rw [orderOf_zeta_single K w c h χ hχ t₀ ht₀]
  have hz : orderOf (gaussSum χ stdAddChar / ((Real.sqrt (((2 : ℕ) : ℝ) ^ (c + 1)) : ℝ) : ℂ)) = 2 ^ (c + 1) := by
    rcases Nat.even_or_odd (c + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
    · have := PAG.Part130.orderOf_gauss_two_even (c + 1) m (by omega) (by omega) χ hχ
      push_cast; exact this
    · have := PAG.Part130.orderOf_gauss_two_odd (c + 1) m hm (by omega) χ hχ
      push_cast; exact this
  rw [hz, orderOf_chi_two c (by omega) χ hχ, Nat.gcd_eq_right (pow_dvd_pow 2 (by omega)),
    Nat.pow_div (by omega) (by norm_num), show c + 1 - (c - 1) = 2 by omega]

end Single

end PAG.Part135

#print axioms PAG.Part135.chi_pow_ne_one
#print axioms PAG.Part135.five_pow
#print axioms PAG.Part135.odd_pow_sub_one
#print axioms PAG.Part135.unit_pow_two
#print axioms PAG.Part135.orderOf_chi_two_dvd
#print axioms PAG.Part135.orderOf_chi_two
#print axioms PAG.Part135.orderOf_zeta_single
#print axioms PAG.Part135.zeta_single_odd
#print axioms PAG.Part135.zeta_single_two
