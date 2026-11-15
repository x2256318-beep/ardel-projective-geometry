/-
  PAG 2.0 Part 139（2026-10-22）— 周波数写像: 指標群から ℤ/p^{c−k} への準同型
  P = p^k（k < c ≤ 2k）
  1. p^k x = 0 ↔ x ≡ 0 (mod p^{c−k})
  2. 周波数は mod p^{c−k} で一意
  3. freq : DirichletCharacter ℂ (p^c) → ZMod (p^{c−k})、freq(χψ) = freq χ + freq ψ、freq 1 = 0
  4. freq χ = 0 ↔ χ は 1 + P ℤ の上で自明
  5. χ 原始 ↔ freq χ が ZMod (p^{c−k}) の単元
  6. 準同型 freqHom : DirichletCharacter ℂ (p^c) →* Multiplicative (ZMod (p^{c−k}))
-/
import PAG142

namespace PAG.Part143

open ZMod Finset

variable {p : ℕ} [hp : Fact p.Prime]

section Freq

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

include hkc in
/-- **1. p^k x = 0 ↔ x ≡ 0 (mod p^{c−k})**。 -/
theorem P_mul_eq_zero_iff (x : ZMod (p ^ c)) :
    (p : ZMod (p ^ c)) ^ k * x = 0 ↔ ((x.cast : ZMod (p ^ (c - k))) = 0) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hsplit : p ^ k * p ^ (c - k) = p ^ c := by rw [← pow_add]; congr 1; omega
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.cast_pow, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  generalize x.val = v
  have key : p ^ c ∣ p ^ k * v ↔ p ^ k * p ^ (c - k) ∣ p ^ k * v := by rw [hsplit]
  rw [key]
  exact Nat.mul_dvd_mul_iff_left (pow_pos hp.out.pos k)

include hkc in
/-- **2. 周波数の一意性**。 -/
theorem freq_unique (χ : DirichletCharacter ℂ (p ^ c)) (δ δ' : ZMod (p ^ c))
    (h : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y))
    (h' : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ' * y)) :
    ((δ.cast : ZMod (p ^ (c - k)))) = (δ'.cast : ZMod (p ^ (c - k))) := by
  have hpd : p ^ (c - k) ∣ p ^ c := pow_dvd_pow p (by omega)
  have e := (h 1).symm.trans (h' 1)
  rw [mul_one, mul_one] at e
  have e2 := ZMod.injective_stdAddChar e
  have e3 : (p : ZMod (p ^ c)) ^ k * (δ - δ') = 0 := by rw [mul_sub, e2, sub_self]
  rw [P_mul_eq_zero_iff hkc, ZMod.cast_sub hpd] at e3
  exact sub_eq_zero.mp e3

include hkc h2k in
theorem freq_exists (χ : DirichletCharacter ℂ (p ^ c)) :
    ∃ δ : ZMod (p ^ c), ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y) :=
  PAG.Part141.exists_delta_gen hkc h2k χ

/-- **3. 周波数写像**。 -/
noncomputable def freq (χ : DirichletCharacter ℂ (p ^ c)) : ZMod (p ^ (c - k)) :=
  ((Classical.choose (freq_exists hkc h2k χ)).cast : ZMod (p ^ (c - k)))

theorem freq_spec (χ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (h : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y)) :
    freq hkc h2k χ = (δ.cast : ZMod (p ^ (c - k))) :=
  freq_unique hkc χ _ δ (Classical.choose_spec (freq_exists hkc h2k χ)) h

theorem freq_mul (χ ψ : DirichletCharacter ℂ (p ^ c)) :
    freq hkc h2k (χ * ψ) = freq hkc h2k χ + freq hkc h2k ψ := by
  have hpd : p ^ (c - k) ∣ p ^ c := pow_dvd_pow p (by omega)
  have h₁ := Classical.choose_spec (freq_exists hkc h2k χ)
  have h₂ := Classical.choose_spec (freq_exists hkc h2k ψ)
  rw [freq_spec hkc h2k (χ * ψ) _ (PAG.Part142.freq_mul χ ψ _ _ h₁ h₂), ZMod.cast_add hpd]
  rfl

theorem freq_one : freq hkc h2k (1 : DirichletCharacter ℂ (p ^ c)) = 0 := by
  have hP : (p : ZMod (p ^ c)) ^ k * (p : ZMod (p ^ c)) ^ k = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (show c ≤ k + k by omega) (by rw [← Nat.cast_pow, ZMod.natCast_self])
  rw [freq_spec hkc h2k 1 0 (fun y => by
    rw [mul_zero, zero_mul, AddChar.map_zero_eq_one]
    exact MulChar.one_apply (PAG.Part120.one_add_unit _ hP y))]
  exact ZMod.cast_zero

/-- **4. freq χ = 0 ↔ χ は 1 + Pℤ 上で自明**。 -/
theorem freq_eq_zero_iff (χ : DirichletCharacter ℂ (p ^ c)) :
    freq hkc h2k χ = 0 ↔ ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = 1 := by
  have h := Classical.choose_spec (freq_exists hkc h2k χ)
  set δ := Classical.choose (freq_exists hkc h2k χ)
  change (δ.cast : ZMod (p ^ (c - k))) = 0 ↔ _
  rw [← P_mul_eq_zero_iff hkc]
  constructor
  · intro h0 y; rw [h, mul_comm _ δ, mul_assoc, ← mul_assoc, mul_comm δ, h0, zero_mul, AddChar.map_zero_eq_one]
  · intro h1
    have e := (h 1).symm.trans (h1 1)
    rw [mul_one] at e
    exact ZMod.injective_stdAddChar (e.trans (AddChar.map_zero_eq_one _).symm)

/-- **5. χ 原始 ↔ freq χ 単元**。 -/
theorem primitive_iff_freq_unit (χ : DirichletCharacter ℂ (p ^ c)) :
    χ.IsPrimitive ↔ IsUnit (freq hkc h2k χ) := by
  have hpd : p ^ (c - k) ∣ p ^ c := pow_dvd_pow p (by omega)
  have hp1 : p ∣ p ^ (c - k) := dvd_pow_self p (by omega)
  have h := Classical.choose_spec (freq_exists hkc h2k χ)
  rw [PAG.Part142.primitive_iff_freq hkc h2k χ _ h, PAG.Part140.isUnit_iff_cast_ne_zero c (by omega),
    PAG.Part140.isUnit_iff_cast_ne_zero (c - k) (by omega)]
  unfold freq
  have hc := congrArg (fun f => f (Classical.choose (freq_exists hkc h2k χ)))
    (ZMod.castHom_comp (n := p) hp1 hpd)
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at hc
  rw [hc]

/-- **6. 準同型**。 -/
noncomputable def freqHom : DirichletCharacter ℂ (p ^ c) →* Multiplicative (ZMod (p ^ (c - k))) where
  toFun χ := Multiplicative.ofAdd (freq hkc h2k χ)
  map_one' := by rw [freq_one]; rfl
  map_mul' χ ψ := by rw [freq_mul]; rfl

end Freq

end PAG.Part143

#print axioms PAG.Part143.P_mul_eq_zero_iff
#print axioms PAG.Part143.freq_unique
#print axioms PAG.Part143.freq_spec
#print axioms PAG.Part143.freq_mul
#print axioms PAG.Part143.freq_one
#print axioms PAG.Part143.freq_eq_zero_iff
#print axioms PAG.Part143.primitive_iff_freq_unit
#print axioms PAG.Part143.freqHom
