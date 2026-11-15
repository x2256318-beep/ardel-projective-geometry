/-
  PAG 2.0 Part 191（2026-10-23）— 一般の法の原始指標で z(χ) が 1 の冪根になる条件
  z(χ) = τ(χ)/√N（τ は stdAddChar のガウス和）。RootCrit χ：N をちょうど 1 回割る素数 q ごとに、
  χ² が N/q を経由する（x ≡ 1 (mod N/q) の単数 x で χ(x)² = 1 と同じ）。
  1. z_level_one：法 1 では z = 1
  2. rootCrit_mul_iff：法 p^e·M（e ≥ 1、互いに素）で、RootCrit (χ₁′χ₂′) ⇔ (e = 1 ⇒ χ₁² = 1) かつ RootCrit χ₂
  3. local_cond_iff：χ₁ 原始的（法 p^e、e ≥ 1）なら (e ≥ 2 または ord χ₁ = 2) ⇔ (e = 1 ⇒ χ₁² = 1)
  4. general_root_iff：法 N の原始指標 χ で、z(χ) が 1 の冪根 ⇔ RootCrit χ
     （N についての強い帰納法。最小素因数 p の冪をはがし、Part 190 の peel_root_iff を使う）
  5. 系：general_root_iff_units（単数での言い換え）、squarefull_root（N を割る素数がすべて 2 回以上割るなら
     つねに 1 の冪根）、squarefree_root_iff（N が平方因子をもたないなら、1 の冪根 ⇔ χ² = 1）
-/
import PAG194

namespace PAG.Part195

open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194

/-- 判定の右辺：N をちょうど 1 回割る素数 q ごとに、χ² が N/q を経由する。 -/
def RootCrit {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ^ 2 ∣ N → (χ ^ 2).FactorsThrough (N / q)

/-! ### 1. 法 1 -/

/-- **1.** 法 1 では z = 1。 -/
theorem z_level_one (χ : DirichletCharacter ℂ 1) :
    gaussSum χ stdAddChar / ((Real.sqrt ((1 : ℕ) : ℝ) : ℝ) : ℂ) = 1 := by
  have h0 : χ 0 = 1 := by
    rw [show (0 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  rw [gaussSum, Fintype.sum_subsingleton _ 0, h0, AddChar.map_zero_eq_one, mul_one, Nat.cast_one,
    Real.sqrt_one, ofReal_one, div_one]

/-! ### 2. 判定の右辺を成分に分ける -/

/-- 2 乗は成分ごとにとれる。 -/
theorem sq_mul_changeLevel {N₁ N₂ : ℕ} (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) ^ 2 =
      (χ₁ ^ 2).changeLevel (dvd_mul_right N₁ N₂) * (χ₂ ^ 2).changeLevel (dvd_mul_left N₂ N₁) := by
  rw [mul_pow, map_pow, map_pow]

/-- **2.** 法 p^e·M（e ≥ 1、p^e と M は互いに素）で、
  RootCrit (χ₁′χ₂′) ⇔ (e = 1 ⇒ χ₁² = 1) かつ RootCrit χ₂。 -/
theorem rootCrit_mul_iff {p e M : ℕ} [hp : Fact p.Prime] [NeZero M] (he : 1 ≤ e)
    (hcop : (p ^ e).Coprime M) (χ₁ : DirichletCharacter ℂ (p ^ e)) (χ₂ : DirichletCharacter ℂ M) :
    RootCrit (χ₁.changeLevel (dvd_mul_right (p ^ e) M) * χ₂.changeLevel (dvd_mul_left M (p ^ e))) ↔
      (e = 1 → χ₁ ^ 2 = 1) ∧ RootCrit χ₂ := by
  have hpM : ¬ p ∣ M := by
    intro h
    have hc : p.Coprime M := Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) hcop
    exact hp.out.one_lt.ne' (hc.eq_one_of_dvd h)
  unfold RootCrit
  rw [sq_mul_changeLevel]
  constructor
  · intro h
    refine ⟨fun he1 => ?_, fun q hq hqM hq2 => ?_⟩
    · subst he1
      have hnd : ¬ p ^ 2 ∣ p ^ 1 * M := by
        intro h2
        rw [pow_one, sq] at h2
        exact hpM (Nat.dvd_of_mul_dvd_mul_left hp.out.pos h2)
      have h1 := h p hp.out (dvd_mul_of_dvd_left (dvd_pow_self p one_ne_zero) M) hnd
      rw [show p ^ 1 * M / p = 1 * M by rw [pow_one, Nat.mul_div_cancel_left M hp.out.pos, one_mul]]
        at h1
      exact (DirichletCharacter.factorsThrough_one_iff _).mp
        ((factorsThrough_mul_iff hcop (one_dvd _) dvd_rfl _ _).mp h1).1
    · have hqp : q ≠ p := fun h' => hpM (h' ▸ hqM)
      have hqN : q ∣ p ^ e * M := dvd_mul_of_dvd_right hqM _
      have hq2N : ¬ q ^ 2 ∣ p ^ e * M := by
        intro h'
        apply hq2
        have hc : (q ^ 2).Coprime (p ^ e) :=
          Nat.Coprime.pow 2 e ((Nat.coprime_primes hq hp.out).mpr hqp)
        exact hc.dvd_of_dvd_mul_left h'
      have h1 := h q hq hqN hq2N
      rw [Nat.mul_div_assoc _ hqM] at h1
      exact ((factorsThrough_mul_iff hcop dvd_rfl (Nat.div_dvd_of_dvd hqM) _ _).mp h1).2
  · rintro ⟨h1, h2⟩ q hq hqN hq2
    by_cases hqp : q = p
    · subst hqp
      have he1 : e = 1 := by
        by_contra hne
        apply hq2
        exact dvd_mul_of_dvd_left (pow_dvd_pow q (by omega)) M
      subst he1
      have hsq := h1 rfl
      rw [show q ^ 1 * M / q = 1 * M by rw [pow_one, Nat.mul_div_cancel_left M hq.pos, one_mul]]
      refine (factorsThrough_mul_iff hcop (one_dvd _) dvd_rfl _ _).mpr ⟨?_, ?_⟩
      · rw [hsq]; exact (DirichletCharacter.factorsThrough_one_iff _).mpr rfl
      · exact DirichletCharacter.FactorsThrough.same_level _
    · have hqM : q ∣ M := by
        have hc : q.Coprime (p ^ e) := Nat.Coprime.pow_right e ((Nat.coprime_primes hq hp.out).mpr hqp)
        exact hc.dvd_of_dvd_mul_left hqN
      have hq2M : ¬ q ^ 2 ∣ M := fun h' => hq2 (dvd_mul_of_dvd_right h' _)
      rw [Nat.mul_div_assoc _ hqM]
      exact (factorsThrough_mul_iff hcop dvd_rfl (Nat.div_dvd_of_dvd hqM) _ _).mpr
        ⟨DirichletCharacter.FactorsThrough.same_level _, h2 q hq hqM hq2M⟩

/-! ### 3. 素数冪の成分の条件 -/

/-- 原始的な指標は、法が 2 以上なら自明でない。 -/
theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  intro h1
  have hcond := (DirichletCharacter.isPrimitive_def _).mp hχ
  rw [h1, DirichletCharacter.conductor_one] at hcond
  omega

/-- **3.** χ₁ が原始的（法 p^e、e ≥ 1）なら、(e ≥ 2 または ord χ₁ = 2) ⇔ (e = 1 ⇒ χ₁² = 1)。 -/
theorem local_cond_iff {p e : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (χ₁ : DirichletCharacter ℂ (p ^ e))
    (hχ₁ : χ₁.IsPrimitive) : (2 ≤ e ∨ orderOf χ₁ = 2) ↔ (e = 1 → χ₁ ^ 2 = 1) := by
  constructor
  · rintro (h | h) he1
    · omega
    · rw [← h]; exact pow_orderOf_eq_one χ₁
  · intro h
    by_cases he2 : 2 ≤ e
    · exact Or.inl he2
    · right
      have he1 : e = 1 := by omega
      have h2 : 2 ≤ p ^ e := by rw [he1, pow_one]; exact hp.out.two_le
      exact orderOf_eq_prime (h he1) (ne_one_of_isPrimitive h2 χ₁ hχ₁)

/-! ### 4. 一般の法の判定 -/

/-- 帰納法のための形：NeZero N を明示的な引数にした版。 -/
theorem general_root_iff_aux (N : ℕ) : ∀ (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ((∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      RootCrit χ) := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro hNZ χ hχ
  by_cases hN1 : N = 1
  · subst hN1
    constructor
    · intro _ q hq hq1 _
      have := Nat.le_of_dvd one_pos hq1
      have := hq.two_le
      omega
    · intro _
      exact ⟨1, one_pos, by rw [pow_one]; exact z_level_one χ⟩
  · have hN0 : N ≠ 0 := NeZero.ne N
    obtain ⟨p, e, M, hp, he, hcop, rfl⟩ : ∃ p e M : ℕ, p.Prime ∧ 1 ≤ e ∧ (p ^ e).Coprime M ∧
        N = p ^ e * M := by
      have hp := Nat.minFac_prime hN1
      refine ⟨N.minFac, N.factorization N.minFac, N / N.minFac ^ N.factorization N.minFac, hp,
        hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N), ?_, ?_⟩
      · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
      · exact (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm
    have : Fact p.Prime := ⟨hp⟩
    have hMZ : NeZero M := ⟨fun h0 => NeZero.ne (p ^ e * M) (by rw [h0, mul_zero])⟩
    have hMlt : M < p ^ e * M := by
      have h2 : 2 ≤ p ^ e := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
      have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
      nlinarith
    have hdec := decomp hcop χ
    obtain ⟨h₁, h₂⟩ := (isPrimitive_iff hcop χ).mp hχ
    have hz : gaussSum χ stdAddChar = gaussSum ((comp₁ hcop χ).changeLevel (dvd_mul_right (p ^ e) M) *
        (comp₂ hcop χ).changeLevel (dvd_mul_left M (p ^ e))) stdAddChar :=
      congrArg (fun φ => gaussSum φ stdAddChar) hdec
    have hR : RootCrit χ ↔ RootCrit ((comp₁ hcop χ).changeLevel (dvd_mul_right (p ^ e) M) *
        (comp₂ hcop χ).changeLevel (dvd_mul_left M (p ^ e))) := by
      rw [← hdec]
    rw [hz, peel_root_iff e he hcop _ h₁ _ h₂, IH M hMlt hMZ _ h₂, hR, rootCrit_mul_iff he hcop,
      local_cond_iff he _ h₁]

/-- **4. 一般の法の判定**：法 N の原始指標 χ で、z(χ) = τ(χ)/√N が 1 の冪根 ⇔
  N をちょうど 1 回割る素数 q ごとに χ² が N/q を経由する。 -/
theorem general_root_iff (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      RootCrit χ :=
  general_root_iff_aux N inferInstance χ hχ

/-! ### 5. 系 -/

/-- 単数での言い換え：χ² が d を経由 ⇔ x ≡ 1 (mod d) の単数 x で χ(x)² = 1。 -/
theorem factorsThrough_sq_iff_units {N d : ℕ} [NeZero N] (hd : d ∣ N) (χ : DirichletCharacter ℂ N) :
    (χ ^ 2).FactorsThrough d ↔ ∀ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 → χ u ^ 2 = 1 := by
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
  constructor
  · intro h u hu
    have h1 := h hu
    rw [MonoidHom.mem_ker] at h1
    have h2 := congrArg (fun v : ℂˣ => (v : ℂ)) h1
    simp only [MulChar.coe_toUnitHom, Units.val_one] at h2
    rwa [MulChar.pow_apply_coe] at h2
  · intro h u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, MulChar.pow_apply_coe, Units.val_one]
    exact h u hu

/-- **5a.** 単数での形：z(χ) が 1 の冪根 ⇔ N をちょうど 1 回割る素数 q ごとに、
  x ≡ 1 (mod N/q) の単数 x で χ(x)² = 1。 -/
theorem general_root_iff_units (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      ∀ q : ℕ, q.Prime → ∀ hq : q ∣ N, ¬ q ^ 2 ∣ N →
        ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hq) u = 1 → χ u ^ 2 = 1 := by
  rw [general_root_iff N χ hχ]
  unfold RootCrit
  refine forall_congr' (fun q => forall_congr' (fun _ => forall_congr' (fun hq =>
    forall_congr' (fun _ => ?_))))
  exact factorsThrough_sq_iff_units _ χ

/-- **5b.** N を割る素数がすべて N を 2 回以上割るなら、法 N の原始指標の z はつねに 1 の冪根。 -/
theorem squarefull_root (N : ℕ) [NeZero N] (hN : ∀ q : ℕ, q.Prime → q ∣ N → q ^ 2 ∣ N)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1 :=
  (general_root_iff N χ hχ).mpr (fun q hq hqN hq2 => absurd (hN q hq hqN) hq2)

/-- **5c.** N が平方因子をもたないなら、法 N の原始指標 χ で、z(χ) が 1 の冪根 ⇔ χ² = 1。 -/
theorem squarefree_root_iff (N : ℕ) [NeZero N] (hN : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ^ 2 ∣ N)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      χ ^ 2 = 1 := by
  rw [general_root_iff N χ hχ]
  constructor
  · intro h
    have hc : (χ ^ 2).conductor ∣ N := DirichletCharacter.conductor_dvd_level _
    have hc1 : (χ ^ 2).conductor = 1 := by
      by_contra hne
      obtain ⟨q, hq, hqc⟩ := Nat.exists_prime_and_dvd hne
      have hqN : q ∣ N := dvd_trans hqc hc
      have hcq : (χ ^ 2).conductor ∣ N / q :=
        DirichletCharacter.conductor_dvd_of_mem_conductorSet _ (h q hq hqN (hN q hq hqN))
      apply hN q hq hqN
      rw [sq]
      exact Nat.mul_dvd_of_dvd_div hqN (dvd_trans hqc hcq)
    have hf := DirichletCharacter.factorsThrough_conductor (χ ^ 2)
    rw [hc1] at hf
    exact (DirichletCharacter.factorsThrough_one_iff _).mp hf
  · intro h q _ hqN _
    rw [h]
    exact ⟨Nat.div_dvd_of_dvd hqN, 1, (DirichletCharacter.changeLevel_one _).symm⟩

end PAG.Part195

#print axioms PAG.Part195.z_level_one
#print axioms PAG.Part195.sq_mul_changeLevel
#print axioms PAG.Part195.rootCrit_mul_iff
#print axioms PAG.Part195.ne_one_of_isPrimitive
#print axioms PAG.Part195.local_cond_iff
#print axioms PAG.Part195.general_root_iff_aux
#print axioms PAG.Part195.general_root_iff
#print axioms PAG.Part195.factorsThrough_sq_iff_units
#print axioms PAG.Part195.general_root_iff_units
#print axioms PAG.Part195.squarefull_root
#print axioms PAG.Part195.squarefree_root_iff
