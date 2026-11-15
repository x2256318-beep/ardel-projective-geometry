/-
  Projective Adelic Geometry 2.0, Part 5 — formalization（PAG9.lean）
    1. 双対殻写像 D_c(v) = K − c − v の合成と許容殻への収まり（定理 A の殻算術）
    2. 共役ガウス和: conj τ(χ) = χ(−1) τ(χ⁻¹)、τ(χ)τ(χ⁻¹) = χ(−1)|τ(χ)|²（定理 B の核）
    3. p 奇素数・法 p^(n+1)（n ≥ 1）で χ が原始的なら χ² も原始的（2 乗では導手が下がらない）
       核 ker(Z/p^(n+1) → Z/p^n) の元 u は u^p = 1 を満たし、χ(u) ≠ 1 なら χ(u)² ≠ 1。
-/
import PAG8

open Complex Finset

namespace PAG.Part9

/-! ## 1. 殻算術 -/

/-- 双対殻写像 D_c(v) = K − c − v。 -/
def D (K c v : ℤ) : ℤ := K - c - v

/-- 導手 c で順変換し、導手 c' で逆変換すると v ↦ v + (c − c')。 -/
theorem D_comp (K c c' v : ℤ) : D K c' (D K c v) = v + (c - c') := by unfold D; ring

/-- 0 ≤ v ≤ K − c、c' ≤ c なら、行き先 v + (c − c') は導手 c' の許容殻 [c − c', K − c'] に収まる。 -/
theorem D_comp_mem {K c c' v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ K - c) (_hc : c' ≤ c) :
    c - c' ≤ D K c' (D K c v) ∧ D K c' (D K c v) ≤ K - c' := by
  rw [D_comp]; constructor <;> omega

/-- 中間の双対殻 w₀ = D_c(v) は導手 c' の許容範囲 [0, K − c'] に入る（逆変換が殻を広げない条件）。 -/
theorem D_mem {K c c' v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ K - c) (_hc : c' ≤ c) :
    0 ≤ D K c v ∧ D K c v ≤ K - c' := by
  unfold D; constructor <;> omega

/-! ## 2. 共役ガウス和 -/

section Conj

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- χ(−1)² = 1。 -/
theorem chi_neg_one_sq (χ : MulChar (ZMod N) ℂ) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

omit [NeZero N] in
/-- χ⁻¹(−1) = χ(−1)。 -/
theorem inv_apply_neg_one (χ : MulChar (ZMod N) ℂ) : χ⁻¹ (-1) = χ (-1) := by
  have h1 : χ⁻¹ (-1) * χ (-1) = 1 := by
    have h : (χ⁻¹ * χ) (-1) = 1 := by
      rw [MulChar.inv_mul]; exact MulChar.one_apply isUnit_one.neg
    rwa [MulChar.coeToFun_mul, Pi.mul_apply] at h
  have h2 := chi_neg_one_sq χ
  calc χ⁻¹ (-1) = χ⁻¹ (-1) * (χ (-1) * χ (-1)) := by rw [h2, mul_one]
    _ = (χ⁻¹ (-1) * χ (-1)) * χ (-1) := by ring
    _ = χ (-1) := by rw [h1, one_mul]

/-- **共役ガウス和**: conj τ(χ) = χ(−1) τ(χ⁻¹)（ψ = e(·/N)）。 -/
theorem conj_gaussSum (χ : MulChar (ZMod N) ℂ) :
    starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  unfold gaussSum
  rw [map_sum, mul_sum]
  -- conj(χ x ψ x) = χ⁻¹ x ψ(−x)、x ↦ −x で並べ替え
  have : ∀ x : ZMod N, starRingEnd ℂ (χ x * ZMod.stdAddChar x) = χ⁻¹ x * ZMod.stdAddChar (-x) := by
    intro x
    rw [map_mul, AddChar.map_neg_eq_conj]
    congr 1
    exact MulChar.star_apply' χ x
  simp_rw [this]
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ fun x => ?_
  simp only [Equiv.neg_apply]
  rw [show χ⁻¹ (-x) = χ⁻¹ (-1) * χ⁻¹ x by rw [← map_mul, neg_one_mul], inv_apply_neg_one]
  linear_combination (-(χ⁻¹ x * ZMod.stdAddChar (-x))) * chi_neg_one_sq χ

/-- **定理 B の核**: τ(χ)τ(χ⁻¹) = χ(−1)·|τ(χ)|²。|τ|² = p^c なら χ(−1)p^c。 -/
theorem gauss_mul_gauss_inv (χ : MulChar (ZMod N) ℂ) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar
      = χ (-1) * (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) := by
  have h := conj_gaussSum χ
  have h2 := chi_neg_one_sq χ
  have hinv : gaussSum χ⁻¹ ZMod.stdAddChar = χ (-1) * starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) := by
    rw [h, ← mul_assoc, h2, one_mul]
  rw [hinv, ← mul_assoc, mul_comm (gaussSum χ ZMod.stdAddChar) (χ (-1)), mul_assoc,
    Complex.mul_conj]

theorem gauss_mul_gauss_inv_of_norm (χ : MulChar (ZMod N) ℂ) (M : ℝ)
    (hM : Complex.normSq (gaussSum χ ZMod.stdAddChar) = M) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = χ (-1) * M := by
  rw [gauss_mul_gauss_inv, hM]

end Conj

/-! ## 3. 2 乗では導手が下がらない（p 奇素数、c ≥ 2） -/

section Square

variable {p n : ℕ} [hp : Fact p.Prime]

instance neZero_pow' : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-- d² = 0 かつ (m : R) d = 0 型の補題: (1 + d)^m = 1 + m d（d² = 0 のとき）。 -/
theorem one_add_pow_of_sq_zero {R : Type*} [CommRing R] (d : R) (hd : d * d = 0) (m : ℕ) :
    (1 + d) ^ m = 1 + (m : R) * d := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination (m : R) * hd

/-- 核の元は p 乗すると 1（n ≥ 1）。 -/
theorem ker_pow_p (hn : 1 ≤ n) (u : (ZMod (p ^ (n + 1)))ˣ)
    (hu : ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1) :
    (u : ZMod (p ^ (n + 1))) ^ p = 1 := by
  have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
  set d : ZMod (p ^ (n + 1)) := (u : ZMod (p ^ (n + 1))) - 1 with hdef
  have hc : ZMod.castHom hd (ZMod (p ^ n)) d = 0 := by
    rw [hdef, map_sub, map_one, ZMod.castHom_apply, ← ZMod.unitsMap_val hd, hu, Units.val_one,
      sub_self]
  have h1' : ((d.val : ℕ) : ZMod (p ^ n)) = 0 := by
    rw [← hc, ZMod.castHom_apply (h := hd), ZMod.cast_eq_val]
  have h1 : p ^ n ∣ d.val := (ZMod.natCast_eq_zero_iff _ _).mp h1'
  -- d² = 0（p^{2n} ⊇ p^{n+1}）と p·d = 0
  have hsq : d * d = 0 := by
    rw [← ZMod.natCast_zmod_val d, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    have : p ^ n * p ^ n ∣ d.val * d.val := Nat.mul_dvd_mul h1 h1
    rw [← pow_add] at this
    exact Nat.dvd_trans (pow_dvd_pow p (show n + 1 ≤ n + n by omega)) this
  have hpd : (p : ZMod (p ^ (n + 1))) * d = 0 := by
    rw [← ZMod.natCast_zmod_val d, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_trans (dvd_of_eq (by rw [pow_succ, mul_comm] : p ^ (n + 1) = p * p ^ n))
      (Nat.mul_dvd_mul (dvd_refl p) h1)
  have : (u : ZMod (p ^ (n + 1))) = 1 + d := by rw [hdef]; ring
  rw [this, one_add_pow_of_sq_zero d hsq p, hpd, add_zero]

omit hp in
/-- z^2 = 1 かつ z^p = 1（p 奇数）なら z = 1。 -/
theorem eq_one_of_sq_of_pow_odd {z : ℂ} (hodd : Odd p) (h2 : z ^ 2 = 1) (hp' : z ^ p = 1) : z = 1 := by
  obtain ⟨m, hm⟩ := hodd
  rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at hp'
  exact hp'

/-- **2 乗の原始性**: p 奇素数、n ≥ 1（c = n + 1 ≥ 2）で χ が原始的なら χ² も原始的。 -/
theorem sq_isPrimitive (hodd : Odd p) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : (χ * χ).IsPrimitive := by
  obtain ⟨u, hker, hne⟩ := PAG.Part8.exists_ker_ne_one_of_primitive χ hχ
  -- χ(u)² ≠ 1
  have hup : (u : ZMod (p ^ (n + 1))) ^ p = 1 := ker_pow_p hn u hker
  have hχp : χ u ^ p = 1 := by rw [← map_pow, hup, map_one]
  have hsq : (χ * χ) u ≠ 1 := by
    intro h
    apply hne
    rw [MulChar.coeToFun_mul, Pi.mul_apply, ← sq] at h
    exact eq_one_of_sq_of_pow_odd hodd h hχp
  -- 導手 = p^(n+1) を示す
  rw [DirichletCharacter.isPrimitive_def]
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level (χ * χ))
  by_contra hne'
  have hkn : k ≤ n := by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · omega
    · exact absurd (by rw [hkeq, show k = n + 1 by omega]) hne'
  -- χ² は p^k を経由するので、核 ker(→ p^n) の上で自明
  have hft := DirichletCharacter.factorsThrough_conductor (χ * χ)
  rw [hkeq] at hft
  have hdk : p ^ k ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ * χ) hdk] at hft
  have hmem : u ∈ (ZMod.unitsMap hdk).ker := by
    rw [MonoidHom.mem_ker, ← ZMod.unitsMap_comp (pow_dvd_pow p hkn) (pow_dvd_pow p (Nat.le_succ n)),
      MonoidHom.comp_apply, hker, map_one]
  have := hft hmem
  rw [MonoidHom.mem_ker] at this
  apply hsq
  have h' := congrArg (fun w : ℂˣ => (w : ℂ)) this
  simpa [MulChar.coe_toUnitHom] using h'

end Square

end PAG.Part9

#print axioms PAG.Part9.D_comp
#print axioms PAG.Part9.D_comp_mem
#print axioms PAG.Part9.D_mem
#print axioms PAG.Part9.chi_neg_one_sq
#print axioms PAG.Part9.inv_apply_neg_one
#print axioms PAG.Part9.conj_gaussSum
#print axioms PAG.Part9.gauss_mul_gauss_inv
#print axioms PAG.Part9.gauss_mul_gauss_inv_of_norm
#print axioms PAG.Part9.one_add_pow_of_sq_zero
#print axioms PAG.Part9.ker_pow_p
#print axioms PAG.Part9.eq_one_of_sq_of_pow_odd
#print axioms PAG.Part9.sq_isPrimitive
