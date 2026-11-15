/-
  PAG_axioms_supplement.lean（2026-10-31 に作り直したもの）
  各ファイルで #print axioms の行がなかった補助補題 36 個（PAG.lean〜PAG181.lean のうち 19 本）の公理を確認する。
  元は 2026-10-24 の点検で作ったファイル。新しいコンテナに添付がなかったので、同じ規則（PAG3 と PAG181 を import し、#print axioms だけを並べる）で作り直した。
-/
import PAG3
import PAG181

#print axioms PAG.conj_s
#print axioms PAG.s_mul_s
#print axioms PAG.s_ne_zero
#print axioms PAG.Kloosterman.addChar_sum
#print axioms PAG.Kloosterman.gaussSum_pow
#print axioms PAG.Kloosterman.inv_neg_unit
#print axioms PAG.Part3.apply_mul_apply_inv
#print axioms PAG.Part3.sum_neg_twist
#print axioms PAG.Part27.isUnit_units_mul_iff
#print axioms PAG.Part27.a_unit_of
#print axioms PAG.Part27.swap_unimod
#print axioms PAG.Part95.dft_eps_conv
#print axioms PAG.Part95.ketJ_dual
#print axioms PAG.Part95.fam_ne_zero
#print axioms PAG.Part105.proj_apply
#print axioms PAG.Part108.tens_add_left
#print axioms PAG.Part114.tens_smul_left
#print axioms PAG.Part119.ringChar_ne_two
#print axioms PAG.Part119.Lc_isQuadratic
#print axioms PAG.Part119.Lc_apply
#print axioms PAG.Part119.two_ne_zero'
#print axioms PAG.Part143.freq_exists
#print axioms PAG.Part147.evalUnits_val
#print axioms PAG.Part152.e4_one
#print axioms PAG.Part152.e4_pow
#print axioms PAG.Part152.e8_pow
#print axioms PAG.Part165.zp_prim
#print axioms PAG.Part165.zp_ne_zero
#print axioms PAG.Part166.T_mul
#print axioms PAG.Part166.T_sub
#print axioms PAG.Part171.InZω_add
#print axioms PAG.Part172.InZi_add
#print axioms PAG.Part179.InQω_one
#print axioms PAG.Part179.InQi_one
#print axioms PAG.Part180.Rep2_one
#print axioms PAG.Part181.Rep4_one
