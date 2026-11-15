/-
  PAG 2.0 Part 46（2026-10-19）— p = 2 での分類の具体化: χ_{s,j} のケット積の行き先
  法 2^(d+3)、M = 2^(d+1)、j, j' 奇数（原始）、同じ殻 w のケット |w,χ_{s,j}⟩, |w,χ_{s',j'}⟩ について
  1. 一般の p: 積の導手が p^c（1 ≤ c）と分かっていれば、行き先は殻 u（u + c = w + (n+1)）のケット
  2. p = 2:
     (a) s+s' 偶数 ∧ M ∣ j+j' ⇒ 定理 B（球の差）、符号 (−1)^s
     (b) ν₂(j+j') = d+3−m（3 ≤ m ≤ d+3）⇒ 行き先は殻 w+(d+3−m)、導手 2^m のケット、|C|² = λ
     (c) M ∣ j+j' ∧ s+s' 奇数 ⇒ 行き先は殻 w+(d+1)、導手 4 のケット
-/
import PAG49

namespace PAG.Part50

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part37 PAG.Part40 PAG.Part44 PAG.Part45 PAG.Part47
  PAG.Part48

/-- **導手指定の定理 A**: 積の導手が p^c（1 ≤ c ≤ n+1）なら、行き先は殻 u（u + c = w + (n+1)）。 -/
theorem thmA_of_conductor {p : ℕ} [hp : Fact p.Prime] (K w n u c : ℕ) (hK : w + (n + 1) ≤ K)
    (hc1 : 1 ≤ c) (hcn : c ≤ n + 1) (hu : u + c = w + (n + 1)) (huK : u + c ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (hcond : (χ₁ * χ₂).conductor = p ^ c) :
    ∃ ψ : DirichletCharacter ℂ (p ^ c), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) ∧
      conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂) = C • ket K u c huK ψ := by
  obtain ⟨v, hv, rfl⟩ : ∃ v, v ≤ n ∧ c = n + 1 - v := ⟨n + 1 - c, by omega, by omega⟩
  obtain rfl : u = w + v := by omega
  obtain ⟨ψ, hψ, hdvd, hcl⟩ := exists_prim_of_conductor (χ₁ * χ₂) hcond
  have hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x) := by
    intro x
    rw [← hcl]
    exact changeLevel_apply_cast (by omega) (Nat.sub_le (n + 1) v) ψ x
  have hA := thmA_ket K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod
  refine ⟨ψ, hψ, _, ?_, hA⟩
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact normSq_coef_of _ _ _ _ hA (norm_ket' K (w + v) (n + 1 - v) (by omega) _ ψ hψ)
    (thmA_norm K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod)

variable {d : ℕ}

/-- **p = 2 (a)**: s+s' 偶数 ∧ M ∣ j+j' なら球の差（定理 B）、符号 (−1)^s。 -/
theorem p2_caseB (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j)
    (hs : Even (s + s')) (hM : 2 ^ (d + 1) ∣ j + j') :
    conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
      = ((-1 : ℂ) ^ s) • ballB (p := 2) K w (d + 2) := by
  have h1 : chiSJ d s j * chiSJ d s' j' = 1 := by rw [chiSJ_mul, chiSJ_eq_one_iff]; exact ⟨hs, hM⟩
  have hB := thmB_of_mul_eq_one (p := 2) K w (d + 2) hK (chiSJ d s j) (chiSJ d s' j')
    ((chiSJ_prim_iff s j).mpr hj) h1
  rw [chiSJ_neg_one] at hB
  exact hB

/-- **p = 2 (b)**: ν₂(j+j') = d+3−m（3 ≤ m ≤ d+3）なら行き先は殻 w+(d+3−m)・導手 2^m のケット。 -/
theorem p2_caseA (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    {m : ℕ} (hm3 : 3 ≤ m) (hm : m ≤ d + 3)
    (hν : 2 ^ (d + 3 - m) ∣ (j + j') ∧ ¬ 2 ^ (d + 4 - m) ∣ (j + j')) :
    ∃ ψ : DirichletCharacter ℂ (2 ^ m), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
        = C • ket (p := 2) K (w + (d + 3 - m)) m (by omega) ψ := by
  have hcond := (chiSJ_mul_conductor_iff (d := d) s j s' j' hm3 hm).mpr hν
  have e := thmA_of_conductor (p := 2) K w (d + 2) (w + (d + 3 - m)) m hK (by omega) (by omega) (by omega)
    (by omega) (chiSJ d s j) (chiSJ d s' j') ((chiSJ_prim_iff s j).mpr hj) ((chiSJ_prim_iff s' j').mpr hj')
    hcond
  push_cast at e
  exact e

/-- j, j' 奇数なら j+j' は偶数なので、(b) の m は d+2 以下（殻は少なくとも 1 動く）。 -/
theorem p2_caseA_shift (j j' : ℕ) (hj : Odd j) (hj' : Odd j') {m : ℕ} (hm : m ≤ d + 3)
    (hν : ¬ 2 ^ (d + 4 - m) ∣ (j + j')) : m ≤ d + 2 := by
  by_contra h
  have : d + 4 - m = 1 := by omega
  rw [this, pow_one] at hν
  exact hν (even_iff_two_dvd.mp (hj.add_odd hj'))

/-- **p = 2 (c)**: M ∣ j+j' ∧ s+s' 奇数なら行き先は殻 w+(d+1)・導手 4 のケット。 -/
theorem p2_caseA4 (K w : ℕ) (hK : w + (d + 3) ≤ K) (s j s' j' : ℕ) (hj : Odd j) (hj' : Odd j')
    (hs : Odd (s + s')) (hM : 2 ^ (d + 1) ∣ j + j') :
    ∃ ψ : DirichletCharacter ℂ (2 ^ 2), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K w (d + 3) hK (chiSJ d s' j'))
        = C • ket (p := 2) K (w + (d + 1)) 2 (by omega) ψ := by
  have hcond : (chiSJ d s j * chiSJ d s' j').conductor = 2 ^ 2 := by
    rw [chiSJ_mul, chiSJ_conductor_four_iff]; exact ⟨hM, hs⟩
  have e := thmA_of_conductor (p := 2) K w (d + 2) (w + (d + 1)) 2 hK (by omega) (by omega) (by omega)
    (by omega) (chiSJ d s j) (chiSJ d s' j') ((chiSJ_prim_iff s j).mpr hj) ((chiSJ_prim_iff s' j').mpr hj')
    hcond
  push_cast at e
  exact e

end PAG.Part50

#print axioms PAG.Part50.thmA_of_conductor
#print axioms PAG.Part50.p2_caseB
#print axioms PAG.Part50.p2_caseA
#print axioms PAG.Part50.p2_caseA_shift
#print axioms PAG.Part50.p2_caseA4
