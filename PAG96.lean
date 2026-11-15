/-
  PAG 2.0 Part 92（2026-10-19）— 原始指標の個数の公式（幾何的導出の完成）
  N(c) := #{法 p^c の原始指標} とおくと、任意の素数で
  1. Σ_{c=1}^{m} N(c) + 1 = p^(m−1)(p−1)（m ≥ 1）
  2. N(1) = p − 2、N(m+2) = p^m (p−1)²
  （存在の仮定は、奇素数は法 p の ω、p = 2 は χ₄ で外した。p = 2・m = 1 は N(1) = 0 を直接示す）
-/
import PAG95

namespace PAG.Part96

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part61 PAG.Part67 PAG.Part90 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime]

/-- 法 p^c の原始指標の個数。 -/
noncomputable def Np (c : ℕ) : ℕ := Nat.card {χ : DirichletCharacter ℂ (p ^ c) // χ.IsPrimitive}

omit hp in
/-- **#J_a = Σ_{n < K−a} N(n+1)**。 -/
theorem card_J (K a : ℕ) (ha : a ≤ K) :
    Fintype.card (J (p := p) K a) = ∑ n ∈ range (K - a), Np (p := p) (n + 1) := by
  rw [← Nat.card_eq_fintype_card]
  have e : J (p := p) K a ≃ (i : Fin (K - a)) × {χ : DirichletCharacter ℂ (p ^ ((i : ℕ) + 1)) // χ.IsPrimitive} :=
    { toFun := fun x => ⟨⟨x.1.1, by have := x.2.2; omega⟩, ⟨x.1.2, x.2.1⟩⟩
      invFun := fun y => ⟨⟨⟨y.1, by have := y.1.2; omega⟩, y.2.1⟩, y.2.2, by have := y.1.2; simp only; omega⟩
      left_inv := by rintro ⟨⟨⟨n, hn⟩, χ⟩, h1, h2⟩; rfl
      right_inv := by rintro ⟨⟨i, hi⟩, ⟨χ, hχ⟩⟩; rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  exact Fin.sum_univ_eq_sum_range (fun n => Np (p := p) (n + 1)) (K - a)

/-- 奇素数: 法 p の原始指標（ω^1）があるので、a < K なら双対殻 a の原始ケットがある。 -/
theorem exists_ket_odd (hp2 : p ≠ 2) (K a : ℕ) (ha : a < K) : ∃ k, KetDual (p := p) K a k := by
  have hφ : ¬ phi (p := p) 0 ∣ 1 := by
    intro h
    have h1 := Nat.eq_one_of_dvd_one h
    have hc : phi (p := p) 0 = p - 1 := by
      simp [phi, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
    have h3 : 3 ≤ p := by
      have := hp.out.two_le
      rcases Nat.lt_or_ge p 3 with h | h
      · exact absurd (by omega : p = 2) hp2
      · exact h
    omega
  have hP := (PAG.Part74.levelp_prim_iff hp2 0 1).mpr hφ
  exact ⟨_, K - a - 1, 0, by omega, _, hP, by omega, rfl⟩

/-- p = 2: χ₄ があるので、a + 2 ≤ K なら双対殻 a の原始ケットがある。 -/
theorem exists_ket_two (K a : ℕ) (ha : a + 2 ≤ K) : ∃ k, KetDual (p := 2) K a k := by
  have hp' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨_, K - a - 2, 1, by omega, PAG.Part72.chi4, PAG.Part72.chi4_prim, by omega, rfl⟩

/-- p = 2 では N(1) = 0。 -/
theorem Np_one_two : Np (p := 2) 1 = 0 := by
  have : IsEmpty {χ : DirichletCharacter ℂ (2 ^ 1) // χ.IsPrimitive} :=
    ⟨fun ⟨χ, hχ⟩ => PAG.Part85.no_prim_mod2 χ hχ⟩
  unfold Np
  exact Nat.card_of_isEmpty

/-- **累積和の公式**: Σ_{c=1}^{m} N(c) + 1 = p^(m−1)(p−1)（m ≥ 1）。 -/
theorem sum_Np (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ range m, Np (p := p) (n + 1) + 1 = p ^ (m - 1) * (p - 1) := by
  by_cases hp2 : p = 2
  · subst hp2
    rcases Nat.lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      simp [Np_one_two]
    · obtain ⟨k, hk⟩ := exists_ket_two m 0 (by omega)
      have := card_J_add_one (p := 2) m 0 (Nat.zero_le _) k hk
      rw [card_J m 0 (Nat.zero_le _), Nat.sub_zero] at this
      rw [this]; unfold sz; rfl
  · obtain ⟨k, hk⟩ := exists_ket_odd hp2 m 0 (by omega)
    have := card_J_add_one (p := p) m 0 (Nat.zero_le _) k hk
    rw [card_J m 0 (Nat.zero_le _), Nat.sub_zero] at this
    rw [this]; unfold sz; rfl

/-- **N(1) = p − 2**。 -/
theorem Np_one : Np (p := p) 1 = p - 2 := by
  have h := sum_Np (p := p) 1 le_rfl
  simp only [range_one, sum_singleton, zero_add, Nat.sub_self, pow_zero, one_mul] at h
  omega

/-- **N(m+2) = p^m (p−1)²**。 -/
theorem Np_succ_succ (m : ℕ) : Np (p := p) (m + 2) = p ^ m * (p - 1) ^ 2 := by
  have h1 := sum_Np (p := p) (m + 1) (by omega)
  have h2 := sum_Np (p := p) (m + 2) (by omega)
  rw [Finset.sum_range_succ, show m + 1 + 1 = m + 2 from rfl] at h2
  rw [show m + 1 - 1 = m by omega] at h1
  rw [show m + 2 - 1 = m + 1 by omega] at h2
  have hA : p ^ (m + 1) * (p - 1) = p ^ m * (p - 1) ^ 2 + p ^ m * (p - 1) := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.out.one_lt; omega⟩
    rw [hq, Nat.add_sub_cancel]; ring
  omega

end PAG.Part96

#print axioms PAG.Part96.card_J
#print axioms PAG.Part96.exists_ket_odd
#print axioms PAG.Part96.exists_ket_two
#print axioms PAG.Part96.Np_one_two
#print axioms PAG.Part96.sum_Np
#print axioms PAG.Part96.Np_one
#print axioms PAG.Part96.Np_succ_succ
