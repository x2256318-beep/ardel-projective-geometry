/-
  PAG 2.0 Part 79（2026-10-19）— p = 2・レベル 2 の因子（χ₄）を含む混合
  1. changeLevel(χ₄) = χ_{1,0}（法 2^(d+3)）
  2. 混合の行き先: |w, χ_{s,j}⟩ ⋆ |w+(d+1), χ₄⟩ = C·|w, χ_{s+1,j}⟩、|C|² = λ（双対殻は共通）
  3. 像からの読み取り: 像が C·|u,m,ψ⟩（C ≠ 0、ψ 原始）なら u = w、m = d+3（左右どちらの順でも）
-/
import PAG82

namespace PAG.Part83

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part45 PAG.Part47 PAG.Part51 PAG.Part72

/-- **changeLevel(χ₄) = χ_{1,0}**。 -/
theorem changeLevel_chi4 (d : ℕ) :
    DirichletCharacter.changeLevel (pow_dvd_pow 2 (by omega : 2 ≤ d + 3)) chi4 = chiSJ d 1 0 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply char_ext
  · rw [changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega), map_ofNat, chiSJ_five, pow_zero]
    have : (OfNat.ofNat 5 : ZMod (2 ^ 2)) = 1 := by decide
    rw [this, map_one]
  · rw [changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega), map_neg, map_one, chiSJ_neg_one,
      chi4_neg_one, pow_one]

theorem mixed_chi4_apply (d s j : ℕ) (x : ZMod (2 ^ (d + 3))) :
    chiSJ d (s + 1) j x = chiSJ d s j x * chi4 (ZMod.castHom (pow_dvd_pow 2 (by omega : 2 ≤ d + 3)) _ x) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← changeLevel_apply_cast (p := 2) (K := d + 3) (by omega) (by omega), changeLevel_chi4,
    ← MulChar.mul_apply, chiSJ_mul, add_zero]

/-- **χ₄ を含む混合の行き先**。 -/
theorem mixed_ket_chi4 (d : ℕ) (K w : ℕ) (hK : w + (d + 3) ≤ K) (h₂ : w + (d + 1) + 2 ≤ K)
    (s j : ℕ) (hj : Odd j) :
    ∃ C : ℂ, Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (d + 3) - w) : ℝ) ∧
      conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K (w + (d + 1)) 2 h₂ chi4)
        = C • ket (p := 2) K w (d + 3) hK (chiSJ d (s + 1) j) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact PAG.Part65.mixed_general_psi (p := 2) K w (d + 2) (d + 1) (w + (d + 1)) 2 (by omega) hK rfl (by omega) h₂
    (chiSJ d s j) ((chiSJ_prim_iff s j).mpr hj) chi4 chi4_prim (chiSJ d (s + 1) j) ((chiSJ_prim_iff (s + 1) j).mpr hj)
    (fun x => mixed_chi4_apply d s j x)

/-- **χ₄ を含む混合の像からの読み取り**。 -/
theorem mixed_chi4_determines (d : ℕ) (K w : ℕ) (hK : w + (d + 3) ≤ K) (h₂ : w + (d + 1) + 2 ≤ K)
    (s j : ℕ) (hj : Odd j) (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (2 ^ m))
    (hψ : ψ.IsPrimitive) (C : ℂ) (hC : C ≠ 0)
    (hF : conv (ket (p := 2) K w (d + 3) hK (chiSJ d s j)) (ket (p := 2) K (w + (d + 1)) 2 h₂ chi4)
      = C • ket (p := 2) K u m hu ψ) :
    u = w ∧ m = d + 3 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C', -, e⟩ := mixed_ket_chi4 d K w hK h₂ s j hj
  rw [hF] at e
  obtain ⟨hu', hm', -⟩ := ket_rep_unique (p := 2) K u m w (d + 3) hm (by omega) hu hK ψ hψ _
    ((chiSJ_prim_iff (s + 1) j).mpr hj) C C' hC e
  exact ⟨hu', hm'⟩

/-- 左右を入れ替えた形。 -/
theorem mixed_chi4_determines' (d : ℕ) (K w : ℕ) (hK : w + (d + 3) ≤ K) (h₂ : w + (d + 1) + 2 ≤ K)
    (s j : ℕ) (hj : Odd j) (u m : ℕ) (hm : 1 ≤ m) (hu : u + m ≤ K) (ψ : DirichletCharacter ℂ (2 ^ m))
    (hψ : ψ.IsPrimitive) (C : ℂ) (hC : C ≠ 0)
    (hF : conv (ket (p := 2) K (w + (d + 1)) 2 h₂ chi4) (ket (p := 2) K w (d + 3) hK (chiSJ d s j))
      = C • ket (p := 2) K u m hu ψ) :
    u = w ∧ m = d + 3 := by
  rw [conv_comm] at hF
  exact mixed_chi4_determines d K w hK h₂ s j hj u m hm hu ψ hψ C hC hF

end PAG.Part83

#print axioms PAG.Part83.changeLevel_chi4
#print axioms PAG.Part83.mixed_chi4_apply
#print axioms PAG.Part83.mixed_ket_chi4
#print axioms PAG.Part83.mixed_chi4_determines
#print axioms PAG.Part83.mixed_chi4_determines'
