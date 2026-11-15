/-
  PAG 2.0 Part 159（2026-10-22）— Part 158 の個数の閉じた形
  1. 指標群（法 p^{n+1}、p 奇素数）は巡回群
  2. N ∣ φ(p^{n+1}) なら #{χ^N = 1} = N
  3. #{ord χ 奇・原始・ord ζ = p} = (p−1)/2 · p^{n−1} · o（p − 1 = 2^v o、o 奇数）
-/
import PAG162

namespace PAG.Part163

open ZMod Finset PAG.Part119 PAG.Part143 PAG.Part144 PAG.Part160 PAG.Part162

variable {p : ℕ} [hp : Fact p.Prime]

/-- **1. 指標群は巡回群**。 -/
theorem isCyclic_chars (hp2 : p ≠ 2) (c : ℕ) : IsCyclic (DirichletCharacter ℂ (p ^ c)) := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 c
  exact isCyclic_of_surjective (MulChar.equiv_rootsOfUnity (ZMod (p ^ c)) ℂ).symm
    (MulChar.equiv_rootsOfUnity (ZMod (p ^ c)) ℂ).symm.surjective

open Classical in
/-- **2. #{χ^N = 1} = N（N ∣ φ(p^c)）**。 -/
theorem card_pow_eq_one (hp2 : p ≠ 2) (c : ℕ) (N : ℕ) (hN : N ∣ Nat.totient (p ^ c)) :
    #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1} = N := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have := isCyclic_chars hp2 c (p := p)
  have hcard : Fintype.card (DirichletCharacter ℂ (p ^ c)) = Nat.totient (p ^ c) := by
    rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (p ^ c)
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Nat.totient_pos.mpr (pow_pos hp.out.pos c)).ne' (Nat.eq_zero_of_zero_dvd hN)
  have h := sum_card_orderOf_eq_card_pow_eq_one (G := DirichletCharacter ℂ (p ^ c)) hN0
  rw [Finset.sum_congr rfl (fun d hd => IsCyclic.card_orderOf_eq_totient
    (hcard ▸ (Nat.dvd_of_mem_divisors hd).trans hN)), Nat.sum_totient] at h
  convert h.symm

open Classical in
/-- **3. 個数の閉じた形**。 -/
theorem count_closed (h4 : p % 4 = 1) (n m : ℕ) (hnm : n + 1 = 2 * m + 1) (hm : 1 ≤ m) (v o : ℕ)
    (ho : Odd o) (hvo : p - 1 = 2 ^ v * o) :
    #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p}
      = (p - 1) / 2 * (p ^ (n - 1) * o) := by
  have hp2 : p ≠ 2 := by intro h; subst h; norm_num at h4
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hkc : m + 1 < n + 1 := by omega
  have h2k : n + 1 ≤ 2 * (m + 1) := by omega
  have hω := fun t => exists_omega hp2 n hkc h2k v o hvo t
  have hε : epsG p ^ 2 = 1 := by rw [epsG_sq hp2, PAG.Part129.Lc_neg_one_of_one h4]
  have hodd : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), ¬ 2 ∣ orderOf χ ↔ χ ^ (p ^ n * o) = 1 := by
    intro χ
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
  have hζ : ∀ χ : DirichletCharacter ℂ (p ^ (n + 1)), ¬ 2 ∣ orderOf χ → χ.IsPrimitive →
      (orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p ↔
        Lc p (-(fp hkc h2k χ) * 2⁻¹) = epsG p) := by
    intro χ ho' hpr
    have hδ := Classical.choose_spec (freq_exists hkc h2k χ)
    rw [zeta_order_one_odd_iff h4 n m hnm hm χ hpr _ hδ ho']
    have hcast : (((-Classical.choose (freq_exists hkc h2k χ) : ZMod (p ^ (n + 1)))).cast : ZMod p)
        = -(fp hkc h2k χ) := by
      rw [ZMod.cast_neg (dvd_pow_self p (by omega))]
      congr 1
      unfold fp freq
      have hc := congrArg (fun f => f (Classical.choose (freq_exists hkc h2k χ)))
        (ZMod.castHom_comp (n := p) (dvd_pow_self p (by omega : n + 1 - (m + 1) ≠ 0))
          (pow_dvd_pow p (by omega : n + 1 - (m + 1) ≤ n + 1)))
      simpa [ZMod.castHom_apply] using hc.symm
    rw [hcast]
  set SP := univ.filter (fun t : ZMod p => t ≠ 0 ∧ Lc p (-t * 2⁻¹) = epsG p)
  set SN := univ.filter (fun t : ZMod p => t ≠ 0 ∧ Lc p (-t * 2⁻¹) ≠ epsG p)
  have e1 : (univ.filter fun χ : DirichletCharacter ℂ (p ^ (n + 1)) => ¬ 2 ∣ orderOf χ ∧ χ.IsPrimitive ∧
        orderOf ((gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ (n + 1)) : ℝ) : ℂ)) ^ orderOf χ) = p)
      = univ.filter (fun χ => χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ SP) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SP]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hodd χ).mp h1, (fp_ne_zero_iff hkc h2k χ).mp h2, (hζ χ h1 h2).mp h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' := (hodd χ).mpr h1
      have h2' := (fp_ne_zero_iff hkc h2k χ).mpr h2
      exact ⟨h1', h2', (hζ χ h1' h2').mpr h3⟩
  -- ファイバーの大きさ K = p^{n−1} o
  set K := #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ = 0}
  have hall := count_set hkc h2k (p ^ n * o) hω univ
  rw [Finset.card_univ, ZMod.card] at hall
  have htot : #{χ : DirichletCharacter ℂ (p ^ (n + 1)) | χ ^ (p ^ n * o) = 1 ∧ fp hkc h2k χ ∈ (univ : Finset (ZMod p))}
      = p ^ n * o := by
    simp only [Finset.mem_univ, and_true]
    apply card_pow_eq_one hp2
    rw [Nat.totient_prime_pow hp.out (by omega), Nat.add_sub_cancel, hvo]
    exact ⟨2 ^ v, by ring⟩
  have hK : K = p ^ (n - 1) * o := by
    have h := htot.symm.trans hall
    have hpn : p ^ n * o = p * (p ^ (n - 1) * o) := by
      rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega]; ring
    have h' : p * (p ^ (n - 1) * o) = p * K := hpn.symm.trans h
    exact (Nat.eq_of_mul_eq_mul_left hp.out.pos h').symm
  -- |SP| = (p − 1)/2
  have hSP : SP.card = (p - 1) / 2 := by
    have heq := card_res hp2 _ hε
    have hunion : SP.card + SN.card = p - 1 := by
      rw [← Finset.card_union_of_disjoint]
      · have : SP ∪ SN = univ.filter (fun t : ZMod p => t ≠ 0) := by
          ext t; simp only [SP, SN, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
        rw [this, Finset.filter_ne' univ (0 : ZMod p), Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
          ZMod.card]
      · rw [Finset.disjoint_filter]; intro t _ h1 h2; exact h2.2 h1.2
    have : SP.card = SN.card := heq
    omega
  rw [e1, count_set hkc h2k _ hω, hSP]
  exact congrArg ((p - 1) / 2 * ·) hK

end PAG.Part163

#print axioms PAG.Part163.isCyclic_chars
#print axioms PAG.Part163.card_pow_eq_one
#print axioms PAG.Part163.count_closed
