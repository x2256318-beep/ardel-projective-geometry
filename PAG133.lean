/-
  PAG 2.0 Part 129（2026-10-21）— 原始指標の位数の p 部分（野性部分）と、ζ の p 部分
  p 奇素数、N = p^{c+1}（c ≥ 1）、χ 原始について
  1. (1 + p^c s)^k = 1 + k p^c s（ZMod N）
  2. (1 + p)^{p^{c-1}(p-1)} = 1 + p^c s、p ∤ s（LTE: padicValNat.pow_sub_pow）
  3. 原始 ⇒ v ≡ 1 (mod p^c) で χ(v) ≠ 1 となる単元 v がある
  4. χ((1+p)^{p^{c-1}(p-1)}) ≠ 1、したがって p^c ∣ ord χ
  5. p^c ∣ a、p^c ∣ L、p^{c+2} ∤ a ⇒ p² ∤ a / gcd(a, L)
  6. 積のケットの ζ の p_i 部分はちょうど p_i（十分条件の下で）
-/
import PAG132
import Mathlib.NumberTheory.Multiplicity

namespace PAG.Part133

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

section Wild

variable (c : ℕ) (hc : 1 ≤ c)

omit hp in
include hc in
theorem Pc_sq : ((p : ZMod (p ^ (c + 1))) ^ c) * ((p : ZMod (p ^ (c + 1))) ^ c) = 0 := by
  rw [← pow_add]
  exact pow_eq_zero_of_le (show c + 1 ≤ c + c by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])

omit hp in
include hc in
/-- **1. (1 + p^c s)^k = 1 + k p^c s**。 -/
theorem one_add_Pc_pow (s : ZMod (p ^ (c + 1))) (k : ℕ) :
    (1 + (p : ZMod (p ^ (c + 1))) ^ c * s) ^ k = 1 + (k : ZMod (p ^ (c + 1))) * (p : ZMod (p ^ (c + 1))) ^ c * s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ (1 + (p : ZMod (p ^ (c + 1))) ^ c * s) k, ih]
    have h := Pc_sq (p := p) c hc
    push_cast
    linear_combination ((k : ZMod (p ^ (c + 1))) * s * s) * h

include hc in
/-- **2. (1 + p)^{p^{c-1}(p-1)} = 1 + p^c s、p ∤ s**。 -/
theorem one_add_p_pow (hodd : Odd p) :
    ∃ s : ℕ, ¬ p ∣ s ∧ (1 + (p : ZMod (p ^ (c + 1)))) ^ (p ^ (c - 1) * (p - 1))
      = 1 + (p : ZMod (p ^ (c + 1))) ^ c * s := by
  set m := p ^ (c - 1) * (p - 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hm0 : m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by omega)
  set X := (1 + p) ^ m - 1
  have hv : padicValNat p X = c := by
    have h := padicValNat.pow_sub_pow (p := p) hodd (x := 1 + p) (y := 1) (by omega)
      (by simp) (by
        intro h; have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp (by rwa [add_comm] at h)
        exact hp.out.one_lt.ne' (Nat.dvd_one.mp this)) hm0
    rw [one_pow, show 1 + p - 1 = p by omega, padicValNat_self] at h
    have hm : padicValNat p m = c - 1 := by
      simp only [m]
      rw [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) (by omega), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd (by omega) h; omega)]
      simp
    simp only [X]; rw [h, hm]; omega
  have hX0 : X ≠ 0 := by intro h0; rw [h0] at hv; simp at hv; omega
  obtain ⟨s, hs⟩ : p ^ c ∣ X := hv ▸ pow_padicValNat_dvd
  refine ⟨s, fun hps => ?_, ?_⟩
  · have := pow_succ_padicValNat_not_dvd (p := p) hX0
    rw [hv] at this
    exact this (by rw [hs, pow_succ]; exact Nat.mul_dvd_mul_left _ hps)
  · have hle : 1 ≤ (1 + p) ^ m := Nat.one_le_pow _ _ (by omega)
    have e : (1 + p) ^ m = 1 + p ^ c * s := by rw [← hs]; simp only [X]; omega
    have := congrArg (fun n : ℕ => (n : ZMod (p ^ (c + 1)))) e
    push_cast at this
    exact this

/-- **3. 原始 ⇒ v ≡ 1 (mod p^c) で χ(v) ≠ 1**。 -/
theorem exists_ker_ne (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    ∃ v : (ZMod (p ^ (c + 1)))ˣ, ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ c)) v = 1 ∧ χ v ≠ 1 := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  by_contra hn
  push Not at hn
  have hker : (ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ c))).ker ≤ χ.toUnitHom.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one]
    exact hn v hv
  have hft := (DirichletCharacter.factorsThrough_iff_ker_unitsMap (pow_dvd_pow p (Nat.le_succ c))).mpr hker
  have hdvd := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hft
  rw [hχ] at hdvd
  have := (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hdvd
  omega

include hc in
/-- **4. 原始指標 mod p^{c+1} の位数は p^c で割れる**。 -/
theorem pc_dvd_orderOf (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    p ^ c ∣ orderOf χ := by
  have : NeZero (p ^ (c + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P : ZMod (p ^ (c + 1)) := (p : ZMod (p ^ (c + 1))) ^ c
  set m := p ^ (c - 1) * (p - 1)
  have hp1 : 1 < p := hp.out.one_lt
  -- χ((1+p)^m) ≠ 1
  obtain ⟨s, hs, hg⟩ := one_add_p_pow (p := p) c hc hodd
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
  have hvg : (v : ZMod (p ^ (c + 1))) = ((1 + (p : ZMod (p ^ (c + 1)))) ^ m) ^ k := by
    rw [hg, one_add_Pc_pow (p := p) c hc, hvt]
    simp only [P] at hPkt ⊢
    push_cast at hPkt
    linear_combination (-1 : ZMod (p ^ (c + 1))) * hPkt
  have hm0 : m ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by omega)
  have hgunit : IsUnit (1 + (p : ZMod (p ^ (c + 1)))) := by
    have : IsUnit ((1 + (p : ZMod (p ^ (c + 1)))) ^ m) := by
      rw [hg]
      refine isUnit_iff_exists_inv.mpr ⟨1 - P * s, ?_⟩
      have h := Pc_sq (p := p) c hc
      simp only [P]
      linear_combination (-((s : ZMod (p ^ (c + 1))) * s)) * h
    exact (isUnit_pow_iff hm0).mp this
  -- ord χ ∤ m
  have hnd : ¬ orderOf χ ∣ m := by
    intro hdm
    have hχm : χ ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hdm
    have h1 : χ (1 + (p : ZMod (p ^ (c + 1)))) ^ m = 1 := by
      rw [← MulChar.pow_apply' _ hm0, hχm, MulChar.one_apply hgunit]
    apply hv
    rw [hvg, ← pow_mul, map_pow, pow_mul, h1, one_pow]
  -- ord χ ∣ p^c (p-1)
  have hφ : orderOf χ ∣ p ^ c * (p - 1) := by
    apply orderOf_dvd_of_pow_eq_one
    apply MulChar.ext
    intro a
    have h := PAG.Part127.chi_pow_totient χ (a : ZMod (p ^ (c + 1))) a.isUnit
    rw [Nat.totient_prime_pow hp.out (by omega), show c + 1 - 1 = c by omega] at h
    rw [MulChar.pow_apply' _ (Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (by omega)), h,
      MulChar.one_apply a.isUnit]
  -- 数論の結論
  obtain ⟨j, o', ho', hoj⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos χ).ne' p hp.out.ne_one
  rw [hoj] at hφ hnd ⊢
  have hcop' : Nat.Coprime o' (p ^ c) :=
    (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr ho')).symm
  have ho'1 : o' ∣ p - 1 := hcop'.dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hφ)
  by_contra hj
  have hjc : j < c := by
    by_contra h; exact hj (dvd_mul_of_dvd_left (pow_dvd_pow p (by omega)) _)
  exact hnd (Nat.mul_dvd_mul (pow_dvd_pow p (by omega)) ho'1)

end Wild

/-- **5. 抽象補題**: p^c ∣ a、p^c ∣ L、p^{c+2} ∤ a ⇒ p² ∤ a / gcd(a, L)。 -/
theorem not_sq_dvd_div_gcd (p c a L : ℕ) (ha : p ^ c ∣ a) (hL : p ^ c ∣ L) (ha2 : ¬ p ^ (c + 2) ∣ a) :
    ¬ p ^ 2 ∣ a / Nat.gcd a L := by
  intro h
  have hg : p ^ c ∣ Nat.gcd a L := Nat.dvd_gcd ha hL
  apply ha2
  rw [pow_add, ← Nat.mul_div_cancel' (Nat.gcd_dvd_left a L)]
  exact Nat.mul_dvd_mul hg h

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **6. ζ の p_i 部分はちょうど p_i**（十分条件の下で）。 -/
theorem zeta_prod_ppart (hp2 : ∀ i, p i ≠ 2) (hc : ∀ i, 1 ≤ c i) (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) (i : Fin n)
    (hcond : ¬ p i ^ (c i + 1) ∣ ∏ j ∈ univ.erase i,
      orderOf (gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ (c j + 1)) : ℝ) : ℂ)))
    (hL : ¬ p i ^ (c i + 1) ∣ lcmF n (fun i => orderOf (χ i)))
    (hw2 : ¬ p i ^ (c i + 2) ∣ orderOf (∏ j, gaussSum (χ j) stdAddChar / ((Real.sqrt ((p j : ℝ) ^ (c j + 1)) : ℝ) : ℂ))) :
    p i ∣ orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) ∧
    ¬ p i ^ 2 ∣ orderOf ((∏ i, cnorm (p i) (K i) (K i - (c i + 1) - w i)
        * 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))) := by
  refine ⟨p_dvd_orderOf_zeta_prod p K w c hp2 hc h χ hχ t ht i hcond hL, ?_⟩
  rw [orderOf_zeta_prod p K w c h χ hχ t ht]
  apply not_sq_dvd_div_gcd (p i) (c i)
  · exact (pow_dvd_pow (p i) (Nat.le_succ _)).trans
      (PAG.Part131.gauss_prod_pdvd_sharp p (fun j => c j + 1) hp2 (fun j => by have := hc j; omega) χ hχ i hcond)
  · exact (pc_dvd_orderOf (p := p i) (c i) (hc i) ((hp i).out.odd_of_ne_two (hp2 i)) (χ i) (hχ i)).trans
      (dvd_lcmF n (fun i => orderOf (χ i)) i)
  · exact hw2

end Ket

end PAG.Part133

#print axioms PAG.Part133.Pc_sq
#print axioms PAG.Part133.one_add_Pc_pow
#print axioms PAG.Part133.one_add_p_pow
#print axioms PAG.Part133.exists_ker_ne
#print axioms PAG.Part133.pc_dvd_orderOf
#print axioms PAG.Part133.not_sq_dvd_div_gcd
#print axioms PAG.Part133.zeta_prod_ppart
