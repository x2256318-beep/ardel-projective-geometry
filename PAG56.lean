/-
  PAG 2.0 Part 52（2026-10-19）— 族 S による展開と Parseval の等式
  1. 殻の指示関数のノルム: ⟨1_{S_w}, 1_{S_w}⟩ = |S_w| = p^(K−1−w)(p−1)
  2. 正規化: 原始ケットと 1_{S_w}/√|S_w|、δ₀ はノルム 1
  3. 展開: f = Σ_{b ∈ S} (⟨b,f⟩/⟨b,b⟩)·b
  4. Parseval: ⟨f,f⟩ = Σ_{b ∈ S} |⟨b,f⟩|²/⟨b,b⟩
-/
import PAG55

namespace PAG.Part56

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part52 PAG.Part54 PAG.Part55

variable {p : ℕ} [hp : Fact p.Prime]

/-- **殻の指示関数のノルム** ⟨1_{S_w}, 1_{S_w}⟩ = |S_w|。 -/
theorem ip_shellInd_self (K w : ℕ) (hw : w < K) :
    ip (shellInd (p := p) K w hw) (shellInd (p := p) K w hw) = (sz p K w : ℂ) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [shellInd, ip_push_same]
  have hterm : ∀ y : ZMod (p ^ (K - w)),
      starRingEnd ℂ ((1 : DirichletCharacter ℂ (p ^ (K - w))) y) * (1 : DirichletCharacter ℂ (p ^ (K - w))) y
        = (1 : DirichletCharacter ℂ (p ^ (K - w))) y := by
    intro y
    by_cases hy : IsUnit y
    · rw [MulChar.one_apply hy, map_one, mul_one]
    · rw [vanish_one K w hw y hy, mul_zero]
  simp_rw [hterm]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out (by omega)]
  unfold sz
  rw [show K - w - 1 = K - 1 - w by omega]

/-- 正規化した族の元のノルムは 1。 -/
theorem ip_normalized_shellInd (K w : ℕ) (hw : w < K) :
    ip ((((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) • shellInd (p := p) K w hw)
      ((((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) • shellInd (p := p) K w hw) = 1 := by
  rw [ip_smul_left, ip_smul_right, ip_shellInd_self, Complex.conj_ofReal]
  have h1 : 0 < sz p K w := by
    unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
  have hs : (0 : ℝ) < Real.sqrt (sz p K w) := Real.sqrt_pos.mpr (by exact_mod_cast h1)
  have e : ((sz p K w : ℕ) : ℂ) = ((Real.sqrt (sz p K w) * Real.sqrt (sz p K w) : ℝ) : ℂ) := by
    rw [Real.mul_self_sqrt (by positivity)]; push_cast; rfl
  rw [e]
  push_cast
  field_simp
  exact div_self (by exact_mod_cast hs.ne')

theorem ip_delta_self (K : ℕ) : ip (Pi.single (0 : ZMod (p ^ K)) (1 : ℂ)) (Pi.single 0 1) = 1 := by
  rw [ip_delta]; simp

/-- 族 S は有限。 -/
noncomputable instance (K : ℕ) : Fintype (family (p := p) K) :=
  have : Finite (family (p := p) K) :=
    Nat.finite_of_card_ne_zero (by rw [card_family]; exact pow_ne_zero _ hp.out.ne_zero)
  Fintype.ofFinite _

theorem familyBasis_apply (K : ℕ) (b : family (p := p) K) : familyBasis (p := p) K b = b := by
  simp [familyBasis]

/-- 基底の係数は ⟨b,f⟩/⟨b,b⟩。 -/
theorem repr_eq (K : ℕ) (f : ZMod (p ^ K) → ℂ) (b : family (p := p) K) :
    (familyBasis (p := p) K).repr f b = ip (b : ZMod (p ^ K) → ℂ) f / ip (b : ZMod (p ^ K) → ℂ) b := by
  have hb := ip_self_ne_zero _ (ne_zero_of_mem (p := p) K b.1 b.2)
  rw [eq_div_iff hb]
  conv_rhs => rw [← (familyBasis (p := p) K).sum_repr f]
  rw [ip_sum_right, Finset.sum_eq_single b]
  · rw [familyBasis_apply]
  · intro j _ hjb
    rw [familyBasis_apply, family_orthogonal (p := p) K b.1 j.1 b.2 j.2 (fun h => hjb (Subtype.ext h).symm),
      mul_zero]
  · intro h; exact absurd (mem_univ _) h

/-- **展開**: f = Σ_{b ∈ S} (⟨b,f⟩/⟨b,b⟩)·b。 -/
theorem expand (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    f = ∑ b : family (p := p) K,
      (ip (b : ZMod (p ^ K) → ℂ) f / ip (b : ZMod (p ^ K) → ℂ) b) • (b : ZMod (p ^ K) → ℂ) := by
  conv_lhs => rw [← (familyBasis (p := p) K).sum_repr f]
  exact Finset.sum_congr rfl (fun b _ => by rw [repr_eq, familyBasis_apply])

/-- **Parseval の等式**: ⟨f,f⟩ = Σ_{b ∈ S} |⟨b,f⟩|²/⟨b,b⟩。 -/
theorem parseval (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    ip f f = ∑ b : family (p := p) K,
      ((Complex.normSq (ip (b : ZMod (p ^ K) → ℂ) f) : ℝ) : ℂ) / ip (b : ZMod (p ^ K) → ℂ) b := by
  conv_lhs => arg 2; rw [expand (p := p) K f]
  rw [ip_sum_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [ip_conj (b : ZMod (p ^ K) → ℂ) f, ← Complex.mul_conj, div_mul_eq_mul_div, mul_comm]

end PAG.Part56

#print axioms PAG.Part56.ip_shellInd_self
#print axioms PAG.Part56.ip_normalized_shellInd
#print axioms PAG.Part56.ip_delta_self
#print axioms PAG.Part56.familyBasis_apply
#print axioms PAG.Part56.repr_eq
#print axioms PAG.Part56.expand
#print axioms PAG.Part56.parseval
