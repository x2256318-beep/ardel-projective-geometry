/-
  PAG 2.0 Part 160（2026-10-22）— 導手 p^{2m+1} の原始指標の ζ の位数の分布（個数の完全な表）
  1. odd_iff_pow: ord χ 奇数 ⇔ χ^{p^n o} = 1
  2. fiber_size: fp のファイバーの大きさ = p^{n−1} o
  3. card_prim_odd: #{原始・ord χ 奇} = (p−1) p^{n−1} o
  4. count_three: p ≡ 3 で #{ord ζ = 4p} = #{ord ζ = 2p} = (p−1) p^{n−1} (p−1)/2
  5. count_one: p ≡ 1 で #{ord ζ = 2p} = (p−1)/2 · p^{n−1} o、#{ord ζ = p} = 残り
-/
import PAG163

namespace PAG.Part164

open ZMod Finset PAG.Part119 PAG.Part143 PAG.Part144 PAG.Part160 PAG.Part162 PAG.Part163

variable {p : ℕ} [hp : Fact p.Prime]

/-- 単独のケットの ζ。 -/
noncomputable def zeta (n : ℕ) (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ

/-- **1. ord χ 奇数 ⇔ χ^{p^n o} = 1**。 -/
theorem odd_iff_pow (hp2 : p ≠ 2) (n v o : ℕ) (ho : Odd o) (hvo : p - 1 = 2 ^ v * o)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ¬ 2 ∣ orderOf χ ↔ χ ^ (p ^ n * o) = 1 := by
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hNodd : Odd (p ^ n * o) := (hp.out.odd_of_ne_two hp2).pow.mul ho
  constructor
  · intro h
    have hd := PAG.Part134.orderOf_dvd_totient χ
    rw [Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel, hvo,
      show p ^ n * (2 ^ v * o) = 2 ^ v * (p ^ n * o) by ring] at hd
    have hcop : Nat.Coprime (orderOf χ) (2 ^ v) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h)))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)
  · intro h h2
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr (h2.trans (orderOf_dvd_of_pow_eq_one h)))

open Classical in
/-- **2. ファイバーの大きさ = p^{n−1} o**。 -/
theorem fiber_size (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) {k : ℕ} (hkc : k < n + 1) (h2k : n + 1 ≤ 2 * k)
    (v o : ℕ) (hvo : p - 1 = 2 ^ v * o) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ = 0} = p ^ (n - 1) * o := by
  have hω := fun t => exists_omega hp2 n hkc h2k v o hvo t
  have hall := count_set hkc h2k (p ^ n * o) hω univ
  rw [Finset.card_univ, ZMod.card] at hall
  have htot : #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ (univ : Finset (ZMod p))}
      = p ^ n * o := by
    simp only [Finset.mem_univ, and_true]
    apply card_pow_eq_one hp2
    rw [Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel, hvo]
    exact ⟨2 ^ v, by ring⟩
  have h := htot.symm.trans hall
  have hpn : p ^ n * o = p * (p ^ (n - 1) * o) := by
    rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega]; ring
  exact (Nat.eq_of_mul_eq_mul_left hp.out.pos (hpn.symm.trans h)).symm

open Classical in
/-- **3. #{原始・ord χ 奇} = (p−1) p^{n−1} o**。 -/
theorem card_prim_odd (hp2 : p ≠ 2) (n : ℕ) (hn : 1 ≤ n) {k : ℕ} (hkc : k < n + 1) (h2k : n + 1 ≤ 2 * k)
    (v o : ℕ) (ho : Odd o) (hvo : p - 1 = 2 ^ v * o) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive} = (p - 1) * (p ^ (n - 1) * o) := by
  have hω := fun t => exists_omega hp2 n hkc h2k v o hvo t
  have e : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive)
      = univ.filter (fun χ => χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ univ.erase (0 : ZMod p)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    rw [odd_iff_pow hp2 n v o ho hvo, fp_ne_zero_iff hkc h2k]
  rw [e, count_set hkc h2k _ hω, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card,
    fiber_size hp2 n hn hkc h2k v o hvo]

open Classical in
/-- **4. p ≡ 3：ord ζ = 4p と 2p はそれぞれ原始指標のちょうど半分**。 -/
theorem count_three (h4 : p % 4 = 3) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ orderOf (zeta n χ) = 4 * p}
        = (p - 1) * (p ^ (n - 1) * ((p - 1) / 2)) ∧
      #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ orderOf (zeta n χ) = 2 * p}
        = (p - 1) * (p ^ (n - 1) * ((p - 1) / 2)) := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  have hkc : m + 1 < n + 1 := by omega
  have h2k : n + 1 ≤ 2 * (m + 1) := by omega
  have ho : Odd ((p - 1) / 2) := by
    rw [Nat.odd_iff]; have := hp.out.two_le; omega
  have hvo : p - 1 = 2 ^ 1 * ((p - 1) / 2) := by have := hp.out.two_le; omega
  have hodd := card_prim_odd hp2 n hn hkc h2k 1 _ ho hvo
  have hp0 : 0 < p := hp.out.pos
  have h24 : 2 * p ≠ 4 * p := by omega
  have e4 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive ∧ orderOf (zeta n χ) = 4 * p)
      = univ.filter (fun χ => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hpr, h⟩
      refine ⟨fun hev => h24 ?_, hpr⟩
      rw [← h]; exact ((PAG.Part159.zeta_order_parity h4 n m hnm hm χ hpr).1 hev).symm
    · rintro ⟨hod, hpr⟩
      exact ⟨hpr, (PAG.Part159.zeta_order_parity h4 n m hnm hm χ hpr).2 hod⟩
  have e2 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive ∧ orderOf (zeta n χ) = 2 * p)
      = (univ.filter (fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive)).filter
          (fun χ => ¬ ¬ 2 ∣ orderOf χ) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor
    · rintro ⟨hpr, h⟩
      refine ⟨hpr, by_contra fun hod => h24 ?_⟩
      rw [← h]; exact (PAG.Part159.zeta_order_parity h4 n m hnm hm χ hpr).2 hod
    · rintro ⟨hpr, hev⟩
      exact ⟨hpr, (PAG.Part159.zeta_order_parity h4 n m hnm hm χ hpr).1 hev⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive)) (fun χ => ¬ 2 ∣ orderOf χ)
  rw [Finset.filter_filter, PAG.Part145.card_primitive hkc h2k] at hsplit
  have hodd' : #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ ¬ 2 ∣ orderOf χ}
      = (p - 1) * (p ^ (n - 1) * ((p - 1) / 2)) := by
    rw [← hodd]; congr 1; ext χ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  rw [hodd', show n + 1 - 2 = n - 1 by omega] at hsplit
  refine ⟨by rw [e4, hodd], ?_⟩
  rw [e2]
  have hY : p - 1 = 2 * ((p - 1) / 2) := by omega
  set Y := (p - 1) / 2
  set X := p ^ (n - 1)
  rw [hY] at hsplit ⊢
  have : (2 * Y) * (X * Y) + (2 * Y) * (X * Y) = X * (2 * Y) ^ 2 := by ring
  omega

open Classical in
/-- **5. p ≡ 1：#{原始・ord ζ = 2p} = (p−1)/2 · p^{n−1} o、#{原始・ord ζ = p} = 残り**。 -/
theorem count_one (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m) (v o : ℕ)
    (ho : Odd o) (hvo : p - 1 = 2 ^ v * o) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ orderOf (zeta n χ) = 2 * p}
        = (p - 1) / 2 * (p ^ (n - 1) * o) ∧
      #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ orderOf (zeta n χ) = p}
        + (p - 1) / 2 * (p ^ (n - 1) * o) = p ^ (n - 1) * (p - 1) ^ 2 := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have hn : 1 ≤ n := by omega
  have hkc : m + 1 < n + 1 := by omega
  have h2k : n + 1 ≤ 2 * (m + 1) := by omega
  have hp0 : 0 < p := hp.out.pos
  -- 原始指標の ord ζ は p か 2p
  have hpq : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), χ.IsPrimitive →
      (orderOf (zeta n χ) = p ∨ orderOf (zeta n χ) = 2 * p) := by
    intro χ hpr
    obtain ⟨-, hpd, h2⟩ := PAG.Part157.zeta_order_odd hp2 n m hnm hm χ hpr
    have hd : orderOf (zeta n χ) ∣ 2 * p := orderOf_dvd_of_pow_eq_one (h2 h4)
    obtain ⟨j, hj⟩ := hpd
    change orderOf (zeta n χ) = p * j at hj
    rw [hj] at hd ⊢
    have hj2 : j ∣ 2 := by
      obtain ⟨r, hr⟩ := hd
      exact ⟨r, by have := Nat.eq_of_mul_eq_mul_left hp0 (show p * 2 = p * (j * r) by rw [mul_comm 2 p] at hr; linarith); linarith⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hj2 with rfl | rfl
    · left; ring
    · right; ring
  have hne : p ≠ 2 * p := by omega
  have e2 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive ∧ orderOf (zeta n χ) = 2 * p)
      = univ.filter (fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
          orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) ≠ p) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hpr, h⟩
      refine ⟨fun hev => hne ?_, hpr, fun h' => hne (h'.symm.trans h)⟩
      rw [← h]; exact (PAG.Part159.zeta_order_one_even h4 n m hnm hm χ hpr hev).symm
    · rintro ⟨-, hpr, h⟩
      exact ⟨hpr, (hpq χ hpr).resolve_left h⟩
  have hc2 : #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ.IsPrimitive ∧ orderOf (zeta n χ) = 2 * p}
      = (p - 1) / 2 * (p ^ (n - 1) * o) := by
    rw [e2, ← half_half h4 n m hnm hm, count_closed h4 n m hnm hm v o ho hvo]
  refine ⟨hc2, ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => χ.IsPrimitive)) (fun χ => orderOf (zeta n χ) = p)
  rw [Finset.filter_filter, Finset.filter_filter, PAG.Part145.card_primitive hkc h2k, show n + 1 - 2 = n - 1 by omega] at hsplit
  rw [← hsplit, ← hc2]
  congr 1
  congr 1; ext χ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hpr, h⟩; exact ⟨hpr, fun h' => hne (h'.symm.trans h)⟩
  · rintro ⟨hpr, h⟩; exact ⟨hpr, (hpq χ hpr).resolve_left h⟩

end PAG.Part164

#print axioms PAG.Part164.odd_iff_pow
#print axioms PAG.Part164.fiber_size
#print axioms PAG.Part164.card_prim_odd
#print axioms PAG.Part164.count_three
#print axioms PAG.Part164.count_one
