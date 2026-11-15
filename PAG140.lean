/-
  PAG 2.0 Part 136（2026-10-22）— 野性的なひねり: 停留点の移動
  N = p^c、c = 2m、P = p^m について、ψ(1 + P y) = e(P δ y)（∀ y）なら
  1. S(χψ) = S(χ) − δ（u ∈ S(χψ) ↔ u + δ ∈ S(χ)）、|S(χψ)| = |S(χ)|
  2. τ(χψ) · χ(u₀)e(u₀) = τ(χ) · (χψ)(u₀ − δ) e(u₀ − δ)（u₀ ∈ S(χ)、u₀、u₀ − δ 単元）
  0. どの ψ にもそのような δ がある（exists_delta）
  3. δ = 0（ψ が 1 + P ℤ 上で自明）なら Part 134 のひねり公式に戻る
  4. u₀ − δ が単元でなければ τ(χψ) = 0
-/
import PAG139

namespace PAG.Part140

open ZMod Finset PAG.Part118

variable {p : ℕ} [hp : Fact p.Prime]

section Even

variable {c m : ℕ} (hc : c = 2 * m)

/-- **1a. S の移動**。 -/
theorem mem_S_twist (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y)) (u : ZMod (p ^ c)) :
    (∀ y, phi (m := m) (χ * ψ) y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u * y) = 1) ↔
      (∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * (u + δ) * y) = 1) := by
  have key : ∀ y, phi (m := m) (χ * ψ) y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u * y)
      = phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * (u + δ) * y) := by
    intro y
    simp only [phi, MulChar.mul_apply, hψ]
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2; ring
  simp only [key]

/-- e(1) は 1 の原始 p^c 乗根。 -/
theorem stdAddChar_one_primitive (c : ℕ) : IsPrimitiveRoot (stdAddChar (1 : ZMod (p ^ c))) (p ^ c) := by
  have h := Complex.isPrimitiveRoot_exp (p ^ c) (pow_ne_zero _ hp.out.ne_zero)
  have e := ZMod.stdAddChar_coe (N := p ^ c) 1
  push_cast at e
  rw [e]
  convert h using 2
  push_cast; ring

include hc in
/-- **0. δ の存在**: どの ψ にも ψ(1 + P y) = e(P δ y) となる δ がある。 -/
theorem exists_delta (ψ : DirichletCharacter ℂ (p ^ c)) :
    ∃ δ : ZMod (p ^ c), ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set P := (p : ZMod (p ^ c)) ^ m
  have hP : P * P = 0 := P_sq (p := p) c m hc
  set f : ZMod (p ^ c) → ℂ := fun y => ψ (1 + P * y)
  have hadd : ∀ y z, f (y + z) = f y * f z := by
    intro y z; simp only [f]; rw [← map_mul]; congr 1; linear_combination (-(y * z)) * hP
  have hnat : ∀ n : ℕ, f n = f 1 ^ n := by
    intro n; induction n with
    | zero => simp [f]
    | succ n ih => rw [Nat.cast_succ, hadd, ih, pow_succ]
  have hf1 : f 1 ^ (p ^ c) = 1 := by
    rw [← hnat, ZMod.natCast_self]; simp [f]
  have hprim := stdAddChar_one_primitive (p := p) c
  obtain ⟨j, -, hj⟩ := hprim.eq_pow_of_pow_eq_one hf1
  have hsplit : p ^ m * p ^ m = p ^ c := by rw [← pow_add]; congr 1; omega
  have hf2 : f 1 ^ (p ^ m) = 1 := by
    rw [← hnat]; simp only [f]
    rw [show P * ((p ^ m : ℕ) : ZMod (p ^ c)) = 0 by
      simp only [P]; push_cast; rw [← pow_add, show m + m = c by omega, ← Nat.cast_pow, ZMod.natCast_self],
      add_zero, map_one]
  rw [← hj, ← pow_mul] at hf2
  have h3 := (hprim.pow_eq_one_iff_dvd _).mp hf2
  rw [← hsplit, mul_comm j] at h3
  obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos m) h3
  refine ⟨d, fun y => ?_⟩
  change f y = _
  rw [← ZMod.natCast_zmod_val y, hnat, ← hj, ← pow_mul, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hd]
  congr 1
  simp only [P]; push_cast; ring

include hc in
/-- **2. 停留点の移動を伴うひねり公式**。 -/
theorem gauss_twist_wild (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y))
    (u₀ : ZMod (p ^ c)) (hu₀ : IsUnit u₀) (hu₀' : IsUnit (u₀ - δ))
    (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1) :
    gaussSum (χ * ψ) stdAddChar * (χ u₀ * stdAddChar u₀)
      = gaussSum χ stdAddChar * ((χ * ψ) (u₀ - δ) * stdAddChar (u₀ - δ)) := by
  classical
  set P := (p : ZMod (p ^ c)) ^ m
  set S := univ.filter (fun u : ZMod (p ^ c) => ∀ y, phi (m := m) χ y * stdAddChar (P * u * y) = 1)
  set S' := univ.filter (fun u : ZMod (p ^ c) => ∀ y, phi (m := m) (χ * ψ) y * stdAddChar (P * u * y) = 1)
  have hS₀' : ∀ y, phi (m := m) (χ * ψ) y * stdAddChar (P * (u₀ - δ) * y) = 1 :=
    (mem_S_twist χ ψ δ hψ (u₀ - δ)).mpr (by rw [sub_add_cancel]; exact hS₀)
  have hcard : S'.card = S.card := by
    apply Finset.card_bij (fun u _ => u + δ)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨mem_univ _, (mem_S_twist χ ψ δ hψ u).mp (Finset.mem_filter.mp hu).2⟩
    · intro a _ b _ h; exact add_right_cancel h
    · intro b hb
      refine ⟨b - δ, Finset.mem_filter.mpr ⟨mem_univ _, (mem_S_twist χ ψ δ hψ (b - δ)).mpr ?_⟩, sub_add_cancel b δ⟩
      rw [sub_add_cancel]; exact (Finset.mem_filter.mp hb).2
  have h1 : gaussSum (χ * ψ) stdAddChar = (S'.card : ℂ) * ((χ * ψ) (u₀ - δ) * stdAddChar (u₀ - δ)) := by
    rw [gauss_eq_sum_S (p := p) hc (χ * ψ),
      Finset.sum_congr rfl (fun u hu => const_on_S (p := p) hc (χ * ψ) (u₀ - δ) u hu₀' hS₀' (Finset.mem_filter.mp hu).2),
      Finset.sum_const, nsmul_eq_mul]
  have h2 : gaussSum χ stdAddChar = (S.card : ℂ) * (χ u₀ * stdAddChar u₀) := by
    rw [gauss_eq_sum_S (p := p) hc χ,
      Finset.sum_congr rfl (fun u hu => const_on_S (p := p) hc χ u₀ u hu₀ hS₀ (Finset.mem_filter.mp hu).2),
      Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2, hcard]; ring

/-- 単元 ↔ 法 p で 0 でない（ZMod p^c、c ≥ 1）。 -/
theorem isUnit_iff_cast_ne_zero (c : ℕ) (hc : 1 ≤ c) (x : ZMod (p ^ c)) :
    IsUnit x ↔ ((x.cast : ZMod p) ≠ 0) := by
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega),
    ZMod.cast_natCast (dvd_pow_self p (by omega)), Ne, ZMod.natCast_eq_zero_iff,
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]

include hc in
/-- **4. u₀ − δ が単元でなければ τ(χψ) = 0**。 -/
theorem gauss_twist_wild_zero (hm : 1 ≤ m) (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ : ZMod (p ^ c))
    (hψ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y))
    (u₀ : ZMod (p ^ c)) (hu₀' : ¬ IsUnit (u₀ - δ))
    (hS₀ : ∀ y, phi (m := m) χ y * stdAddChar ((p : ZMod (p ^ c)) ^ m * u₀ * y) = 1) :
    gaussSum (χ * ψ) stdAddChar = 0 := by
  classical
  have hpc : p ∣ p ^ c := dvd_pow_self p (by omega)
  rw [gauss_eq_sum_S (p := p) hc (χ * ψ)]
  apply Finset.sum_eq_zero
  intro u hu
  have hS := (mem_S_twist χ ψ δ hψ u).mp (Finset.mem_filter.mp hu).2
  have hPu : (p : ZMod (p ^ c)) ^ m * (u + δ) = (p : ZMod (p ^ c)) ^ m * u₀ := by
    have h1 := hS 1; have h2 := hS₀ 1
    rw [mul_one] at h1 h2
    have hφ : phi (m := m) χ 1 ≠ 0 := by intro h0; rw [h0, zero_mul] at h1; exact zero_ne_one h1
    exact ZMod.injective_stdAddChar (mul_left_cancel₀ hφ (h1.trans h2.symm))
  have hcast := PAG.Part139.cast_eq_of_P (p := p) (k := m) (by omega) (u + δ) u₀ hPu
  have hnu : ¬ IsUnit u := by
    rw [isUnit_iff_cast_ne_zero c (by omega)]
    rw [isUnit_iff_cast_ne_zero c (by omega), ZMod.cast_sub hpc, not_not] at hu₀'
    rw [ZMod.cast_add hpc] at hcast
    intro h; apply h
    linear_combination hcast + hu₀'
  rw [MulChar.map_nonunit _ hnu, zero_mul]

end Even

end PAG.Part140

#print axioms PAG.Part140.mem_S_twist
#print axioms PAG.Part140.gauss_twist_wild
#print axioms PAG.Part140.stdAddChar_one_primitive
#print axioms PAG.Part140.exists_delta
#print axioms PAG.Part140.isUnit_iff_cast_ne_zero
#print axioms PAG.Part140.gauss_twist_wild_zero
