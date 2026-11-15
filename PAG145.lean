/-
  PAG 2.0 Part 141（2026-10-22）— 原始指標の数え上げ
  P = p^k（k < c ≤ 2k）、freq は全射準同型（Part 139・140）
  1. freq のファイバーはすべて同じ大きさ F、p^{c−k}·F = φ(p^c)
  2. 原始指標の数 · p^{c−k} = φ(p^{c−k}) · φ(p^c)
  3. 原始指標の数 = p^{c−2} (p − 1)²（= φ(p^c) − φ(p^{c−1})）
-/
import PAG144

namespace PAG.Part145

open ZMod Finset PAG.Part143 PAG.Part144

variable {p : ℕ} [hp : Fact p.Prime]

section Count

variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)

theorem fiber_eq (t : ZMod (p ^ (c - k))) :
    #{χ : DirichletCharacter ℂ (p ^ c) | freq hkc h2k χ = t}
      = #{χ : DirichletCharacter ℂ (p ^ c) | freq hkc h2k χ = 0} := by
  classical
  have h := MonoidHom.card_fiber_eq_of_mem_range (freqHom hkc h2k (p := p))
    (x := Multiplicative.ofAdd t) (y := Multiplicative.ofAdd 0)
    (by obtain ⟨χ, hχ⟩ := freq_surjective hkc h2k (p := p) t; exact ⟨χ, by simp [freqHom, hχ]⟩)
    (by obtain ⟨χ, hχ⟩ := freq_surjective hkc h2k (p := p) 0; exact ⟨χ, by simp [freqHom, hχ]⟩)
  simpa [freqHom] using h

/-- **1. p^{c−k} · F = φ(p^c)**。 -/
theorem fiber_card :
    p ^ (c - k) * #{χ : DirichletCharacter ℂ (p ^ c) | freq hkc h2k χ = 0} = Nat.totient (p ^ c) := by
  classical
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (c - k)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have htot := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (p ^ c)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ] at htot
  have hsum := Finset.card_eq_sum_card_fiberwise (f := freq hkc h2k)
    (s := (univ : Finset (DirichletCharacter ℂ (p ^ c)))) (t := univ) (fun _ _ => mem_univ _)
  rw [Finset.sum_congr rfl (fun t _ => fiber_eq hkc h2k t), Finset.sum_const, Finset.card_univ (α := ZMod _),
    ZMod.card, smul_eq_mul] at hsum
  rw [← htot, hsum]

theorem card_units_filter (n : ℕ) [NeZero n] : #{x : ZMod n | IsUnit x} = Nat.totient n := by
  classical
  rw [← ZMod.card_units_eq_totient, ← Finset.card_univ]
  symm
  apply Finset.card_bij (s := (univ : Finset (ZMod n)ˣ)) (fun (u : (ZMod n)ˣ) _ => (u : ZMod n))
  · intro u _; simp
  · intro a _ b _ h; exact Units.ext h
  · intro x hx
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨u, mem_univ _, rfl⟩

open Classical in
include hkc h2k in
/-- **2. 原始指標の数 · p^{c−k} = φ(p^{c−k}) · φ(p^c)**。 -/
theorem card_primitive_mul :
    #{χ : DirichletCharacter ℂ (p ^ c) | χ.IsPrimitive} * p ^ (c - k)
      = Nat.totient (p ^ (c - k)) * Nat.totient (p ^ c) := by
  classical
  have : NeZero (p ^ (c - k)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have e1 : #{χ : DirichletCharacter ℂ (p ^ c) | χ.IsPrimitive}
      = #{χ : DirichletCharacter ℂ (p ^ c) | IsUnit (freq hkc h2k χ)} := by
    congr 1; ext χ; simp [primitive_iff_freq_unit hkc h2k χ]
  rw [e1, Finset.card_eq_sum_card_fiberwise (f := freq hkc h2k)
    (t := univ.filter (fun x : ZMod (p ^ (c - k)) => IsUnit x)) (fun χ hχ => Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp hχ).2⟩)]
  rw [Finset.sum_congr rfl (fun t ht => by
    have hu : IsUnit t := (Finset.mem_filter.mp ht).2
    rw [show #({χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (p ^ c) => IsUnit (freq hkc h2k χ)) |
        freq hkc h2k χ = t}) = #{χ : DirichletCharacter ℂ (p ^ c) | freq hkc h2k χ = t} by
      congr 1; ext χ; simp only [Finset.mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h ▸ hu, h⟩, fiber_eq hkc h2k t]),
    Finset.sum_const, smul_eq_mul, card_units_filter, mul_assoc, mul_comm _ (p ^ (c - k)),
    fiber_card hkc h2k]

open Classical in
include hkc h2k in
/-- **3. 原始指標の数 = p^{c−2} (p − 1)²**。 -/
theorem card_primitive : #{χ : DirichletCharacter ℂ (p ^ c) | χ.IsPrimitive} = p ^ (c - 2) * (p - 1) ^ 2 := by
  have h := card_primitive_mul hkc h2k (p := p)
  rw [Nat.totient_prime_pow hp.out (by omega), Nat.totient_prime_pow hp.out (by omega)] at h
  have hsplit : p ^ (c - k) = p * p ^ (c - k - 1) := by rw [← pow_succ']; congr 1; omega
  have hsplit2 : p ^ (c - 1) = p * p ^ (c - 2) := by rw [← pow_succ']; congr 1; omega
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hp.out.pos (c - k))
  rw [h, hsplit, hsplit2]
  ring

end Count

end PAG.Part145

#print axioms PAG.Part145.fiber_eq
#print axioms PAG.Part145.fiber_card
#print axioms PAG.Part145.card_units_filter
#print axioms PAG.Part145.card_primitive_mul
#print axioms PAG.Part145.card_primitive
