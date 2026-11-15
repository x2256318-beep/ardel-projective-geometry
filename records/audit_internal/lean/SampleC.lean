import PAG260
import PAG3
import PAG6
/-! 内部照合の監査（2026-11-14）：照合者が C（前の宣言から数行）と判定したもののうち 4 件を、
前の鎖の宣言だけから示して、C の判定の当たり具合を確かめる（標本）。 -/
open Complex DirichletCharacter

namespace PAG.Audit257C

/-- C：Part 252 の `normSq_rootNum` は Part 12 の `normSq_gaussSum` から数行。 -/
theorem normSq_rootNum_of_PAG16 {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : Complex.normSq (PAG.Part256.rootNum χ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold PAG.Part256.rootNum
  rw [Complex.normSq_div, Complex.normSq_mul, PAG.Part16.normSq_gaussSum hχ,
    Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  split_ifs <;> simp [hN]

/-- C：Part 254 の `rootNum_one_of_eq_one` は Part 192 の `zN_level_one` と、
`rootNum = zN / gs`（このファイルの外の確認 `ManualChecks.lean` と同じ計算）から数行。 -/
theorem rootNum_one_of_eq_one_of_PAG196 {d : ℕ} [NeZero d] (hd : d = 1) :
    PAG.Part256.rootNum (1 : DirichletCharacter ℂ d) = 1 := by
  have hz := PAG.Part196.zN_level_one hd (1 : DirichletCharacter ℂ d)
  have hg : PAG.Part198.gs (1 : DirichletCharacter ℂ d) = 1 := by
    simp [PAG.Part198.gs, MulChar.one_apply isUnit_one.neg]
  have e : PAG.Part256.rootNum (1 : DirichletCharacter ℂ d)
      = PAG.Part196.zN (1 : DirichletCharacter ℂ d) / PAG.Part198.gs (1 : DirichletCharacter ℂ d) := by
    unfold PAG.Part256.rootNum PAG.Part196.zN PAG.Part198.gs
    rw [div_div, mul_comm]
    rfl
  rw [e, hz, hg, div_one]

/-- C：Part 251 の `units_eq_of_coprime_parts` は Part 192 の `crt_unique` を単数に移すだけ。 -/
theorem units_eq_of_coprime_parts_of_PAG196 {N A B : ℕ} [NeZero N] (hN : N = A * B)
    (hAB : A.Coprime B) (hA : A ∣ N) (hB : B ∣ N) (b c : (ZMod N)ˣ)
    (h1 : ZMod.unitsMap hA b = ZMod.unitsMap hA c) (h2 : ZMod.unitsMap hB b = ZMod.unitsMap hB c) :
    b = c := by
  have hA0 : NeZero A := ⟨fun h => NeZero.ne N (by simp [hN, h])⟩
  have hB0 : NeZero B := ⟨fun h => NeZero.ne N (by simp [hN, h])⟩
  apply Units.ext
  refine PAG.Part196.crt_unique hN.symm hAB hA hB ?_ ?_
  · have := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) h1
    simpa [ZMod.unitsMap_def] using this
  · have := congrArg (fun u : (ZMod B)ˣ => (u : ZMod B)) h2
    simpa [ZMod.unitsMap_def] using this

/-- C：Part 252 の `exists_primitive_odd_three` は Part 115・163・167 の補題から数行。 -/
theorem exists_primitive_odd_three_of_earlier :
    ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨PAG.Part119.Lc 3, PAG.Part171.primitive_of_ne_one _ (PAG.Part119.Lc_ne_one (by norm_num)), ?_⟩
  show (PAG.Part119.Lc 3) (-1) = -1
  rw [PAG.Part167.Lc_neg_one_pow (p := 3) 1 (by norm_num)]
  norm_num

end PAG.Audit257C
