import ManualChecks2
/-! 内部照合の監査（2026-11-14、直しの照合 F の指摘を受けた版）：照合者が C（前の宣言から数行）と判定したもののうち 6 件を、
前の鎖の宣言だけから示す（標本）。定理の型は対象の型そのもの（`type_of%`）。`casKer_eq_casK` は ManualChecks2 の、
定義から直接示した値の一致（Part 252 の補題は使わない）。 -/
open Complex DirichletCharacter

namespace PAG.Audit257C

/-- C：Part 252 の `normSq_rootNum` は Part 12 の `normSq_gaussSum` から数行。 -/
theorem normSq_rootNum_of_PAG16 : type_of% @PAG.Part256.normSq_rootNum := by
  intro N _ χ hχ
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold PAG.Part256.rootNum
  rw [Complex.normSq_div, Complex.normSq_mul, PAG.Part16.normSq_gaussSum hχ,
    Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  split_ifs <;> simp [hN]

/-- C：Part 254 の `rootNum_one_of_eq_one` は Part 192 の `zN_level_one` から数行。 -/
theorem rootNum_one_of_eq_one_of_PAG196 : type_of% @PAG.Part258.rootNum_one_of_eq_one := by
  intro d _ hd
  have hz := PAG.Part196.zN_level_one hd (1 : DirichletCharacter ℂ d)
  have hg : PAG.Part198.gs (1 : DirichletCharacter ℂ d) = 1 := by
    simp [PAG.Part198.gs, MulChar.one_apply isUnit_one.neg]
  rw [PAG.Audit257.rootNum_eq_zN_div_gs, hz, hg, div_one]

/-- C：Part 251 の `units_eq_of_coprime_parts` は Part 192 の `crt_unique` を単数に移すだけ。 -/
theorem units_eq_of_coprime_parts_of_PAG196 : type_of% @PAG.Part255.units_eq_of_coprime_parts := by
  intro N A B _ hN hAB hA hB b c h1 h2
  have hA0 : NeZero A := ⟨fun h => NeZero.ne N (by simp [hN, h])⟩
  have hB0 : NeZero B := ⟨fun h => NeZero.ne N (by simp [hN, h])⟩
  apply Units.ext
  refine PAG.Part196.crt_unique hN.symm hAB hA hB ?_ ?_
  · have := congrArg (fun u : (ZMod A)ˣ => (u : ZMod A)) h1
    simpa [ZMod.unitsMap_def] using this
  · have := congrArg (fun u : (ZMod B)ˣ => (u : ZMod B)) h2
    simpa [ZMod.unitsMap_def] using this

/-- C：Part 252 の `exists_primitive_odd_three` は Part 115・163・167 の補題から数行。 -/
theorem exists_primitive_odd_three_of_earlier : type_of% @PAG.Part256.exists_primitive_odd_three := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨PAG.Part119.Lc 3, PAG.Part171.primitive_of_ne_one _ (PAG.Part119.Lc_ne_one (by norm_num)), ?_⟩
  show (PAG.Part119.Lc 3) (-1) = -1
  rw [PAG.Part167.Lc_neg_one_pow (p := 3) 1 (by norm_num)]
  norm_num

/-- C：Part 252 の `hartley_one` は付録 A の Part 3 の `hartley_char`（命題 2.8）の x = 1 の場合と、
`casKer = casK`（値）と、偶奇の場合分けから数行（Part 252 のほかの補題は使わない）。 -/
theorem hartley_one_of_PAG3 : type_of% @PAG.Part256.hartley_one := by
  intro N _ χ
  have h := PAG.Part3.hartley_char χ 1
  simp only [one_mul] at h
  unfold PAG.Part256.hartley
  simp only [mul_one, PAG.Audit257.casKer_eq_casK]
  have e1 : ∑ x : ZMod N, χ x * PAG.Part3.casK x = ∑ y : ZMod N, PAG.Part3.casK y * χ y :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have e2 : ∑ y : ZMod N, ZMod.stdAddChar y * χ y = gaussSum χ ZMod.stdAddChar := by
    unfold gaussSum
    exact Finset.sum_congr rfl (fun y _ => mul_comm _ _)
  rw [e1, h, e2]
  congr 1
  unfold PAG.Part256.parFac
  rcases χ.even_or_odd with he | ho
  · rw [if_pos he, show χ (-1) = 1 from he]
    ring
  · have hne : ¬ χ.Even := fun he => by
      have h1 : χ (-1) = 1 := he
      have h2 : χ (-1) = -1 := ho
      rw [h1] at h2
      norm_num at h2
    rw [if_neg hne, show χ (-1) = -1 from ho]
    ring

/-- C：Part 252 の `casKer_eq` は、`casKer = casK`（値）と付録 A の Part 3 の `casK_even_part`・`casK_odd_part` から数行。 -/
theorem casKer_eq_of_PAG3 : type_of% @PAG.Part256.casKer_eq := by
  intro N _ t
  rw [PAG.Audit257.casKer_eq_casK]
  have h1 := PAG.Part3.casK_even_part t
  have h2 := PAG.Part3.casK_odd_part t
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2

end PAG.Audit257C

#print axioms PAG.Audit257C.normSq_rootNum_of_PAG16
#print axioms PAG.Audit257C.rootNum_one_of_eq_one_of_PAG196
#print axioms PAG.Audit257C.units_eq_of_coprime_parts_of_PAG196
#print axioms PAG.Audit257C.exists_primitive_odd_three_of_earlier
#print axioms PAG.Audit257C.hartley_one_of_PAG3
#print axioms PAG.Audit257C.casKer_eq_of_PAG3
