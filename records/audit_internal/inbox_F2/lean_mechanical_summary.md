# 直接の当てはめで通った組（1〜3 回目、自動生成物 congr_simp を除く）

名前空間 `PAG.PartNNN` の NNN はファイル番号（PAG 2.0 の Part 番号は NNN − 4）。各組は `lean/MechChecks.lean` に、対象の型そのもの（`type_of%`）を述べる名前つきの定理として書き直してあり、`MechChecks.out` で 44 定理すべての公理が propext・Classical.choice・Quot.sound だけであることを確かめた。

| 対象（Part 249〜256） | 前の宣言 | 結果 | 範囲 | MechChecks.lean の定理名（PAG.AuditMech.…） |
|---|---|---|---|---|
| `PAG.Part253.ipG_smul_left` | `PAG.Part217.inner_smul_left'` | 対象のほうが一般（前の宣言が対象から出る） | 前の鎖 | Part217_inner_smul_left___of__Part253_ipG_smul_left |
| `PAG.Part253.ipG_smul_left` | `PAG.Part229.herm_smul_left` | 対象のほうが一般（前の宣言が対象から出る） | 前の鎖 | Part229_herm_smul_left__of__Part253_ipG_smul_left |
| `PAG.Part253.ipG_smul_left` | `PAG.Part55.ip_smul_left` | 対象のほうが一般（前の宣言が対象から出る） | 前の鎖 | Part55_ip_smul_left__of__Part253_ipG_smul_left |
| `PAG.Part253.ipG_smul_right` | `PAG.Part229.herm_smul_right` | 対象のほうが一般（前の宣言が対象から出る） | 前の鎖 | Part229_herm_smul_right__of__Part253_ipG_smul_right |
| `PAG.Part253.ipG_smul_right` | `PAG.Part55.ip_smul_right` | 対象のほうが一般（前の宣言が対象から出る） | 前の鎖 | Part55_ip_smul_right__of__Part253_ipG_smul_right |
| `PAG.Part256.inv_apply_neg_one` | `PAG.Part25.chi_inv_neg_one` | 同じ文（両向き） | 前の鎖 | Part256_inv_apply_neg_one__of__Part25_chi_inv_neg_one、Part25_chi_inv_neg_one__of__Part256_inv_apply_neg_one |
| `PAG.Part256.inv_apply_neg_one` | `PAG.Part81.inv_neg_one` | 同じ文（両向き） | 前の鎖 | Part256_inv_apply_neg_one__of__Part81_inv_neg_one、Part81_inv_neg_one__of__Part256_inv_apply_neg_one |
| `PAG.Part256.inv_apply_neg_one` | `PAG.Part9.inv_apply_neg_one` | 同じ文（両向き） | 前の鎖 | Part256_inv_apply_neg_one__of__Part9_inv_apply_neg_one、Part9_inv_apply_neg_one__of__Part256_inv_apply_neg_one |
| `PAG.Part256.isPrimitive_of_prime_of_ne_one` | `PAG.Part171.primitive_of_ne_one` | 同じ文（両向き） | 前の鎖 | Part256_isPrimitive_of_prime_of_ne_one__of__Part171_primitive_of_ne_one、Part171_primitive_of_ne_one__of__Part256_isPrimitive_of_prime_of_ne_one |
| `PAG.Part256.neg_one_mul_self` | `PAG.Part29.chi_neg_one_sq'` | 同じ文（両向き） | 前の鎖 | Part256_neg_one_mul_self__of__Part29_chi_neg_one_sq_、Part29_chi_neg_one_sq___of__Part256_neg_one_mul_self |
| `PAG.Part256.neg_one_mul_self` | `PAG.Part9.chi_neg_one_sq` | 同じ文（両向き） | 前の鎖 | Part256_neg_one_mul_self__of__Part9_chi_neg_one_sq、Part9_chi_neg_one_sq__of__Part256_neg_one_mul_self |
| `PAG.Part257.eq_one_of_two` | `PAG.Part198.level_two_trivial` | 前の宣言から直ちに出る | 前の鎖 | Part257_eq_one_of_two__of__Part198_level_two_trivial |
| `PAG.Part257.normSq_rootNum_one_prime` | `PAG.Part256.removal_counterexample_normSq` | 対象のほうが一般（前の宣言が対象から出る） | 範囲の中 | Part256_removal_counterexample_normSq__of__Part257_normSq_rootNum_one_prime |
| `PAG.Part258.ip_smul_right` | `PAG.Part253.ipG_smul_right` | 前の宣言から直ちに出る | 範囲の中 | Part258_ip_smul_right__of__Part253_ipG_smul_right |
| `PAG.Part260.cast_crtMap_fst` | `PAG.Part193.param_cast₁` | 前の宣言から直ちに出る | 前の鎖 | Part260_cast_crtMap_fst__of__Part193_param_cast_ |
| `PAG.Part260.cast_crtMap_snd` | `PAG.Part193.param_cast₂` | 前の宣言から直ちに出る | 前の鎖 | Part260_cast_crtMap_snd__of__Part193_param_cast_ |
| `PAG.Part260.charU_prodChar` | `PAG.Part193.mul_changeLevel_apply` | 前の宣言から直ちに出る | 前の鎖 | Part260_charU_prodChar__of__Part193_mul_changeLevel_apply |
| `PAG.Part260.charU_prodChar` | `PAG.Part199.cmul_apply` | 前の宣言から直ちに出る | 前の鎖 | Part260_charU_prodChar__of__Part199_cmul_apply |
| `PAG.Part260.charU_prodChar` | `PAG.Part236.charMul_apply` | 前の宣言から直ちに出る | 前の鎖 | Part260_charU_prodChar__of__Part236_charMul_apply |
| `PAG.Part260.charU_prodChar` | `PAG.Part236.charMul_apply_unit` | 前の宣言から直ちに出る | 前の鎖 | Part260_charU_prodChar__of__Part236_charMul_apply_unit |
| `PAG.Part260.crtMap_bijective` | `PAG.Part193.param_bijective` | 同じ文（両向き） | 前の鎖 | Part260_crtMap_bijective__of__Part193_param_bijective、Part193_param_bijective__of__Part260_crtMap_bijective |
| `PAG.Part260.gaussSum_prodChar` | `PAG.Part193.gaussSum_mul_coprime` | 同じ文（両向き） | 前の鎖 | Part260_gaussSum_prodChar__of__Part193_gaussSum_mul_coprime、Part193_gaussSum_mul_coprime__of__Part260_gaussSum_prodChar |
| `PAG.Part260.isPrimitive_prodChar` | `PAG.Part194.isPrimitive_mul` | 同じ文（両向き） | 前の鎖 | Part260_isPrimitive_prodChar__of__Part194_isPrimitive_mul、Part194_isPrimitive_mul__of__Part260_isPrimitive_prodChar |
| `PAG.Part260.isPrimitive_prodChar` | `PAG.Part236.isPrimitive_charMul` | 同じ文（両向き） | 前の鎖 | Part260_isPrimitive_prodChar__of__Part236_isPrimitive_charMul、Part236_isPrimitive_charMul__of__Part260_isPrimitive_prodChar |
| `PAG.Part260.prodChar` | `PAG.Part199.cmul` | 定義が同じ（HEq rfl） | 前の鎖 | defeq_Part260_prodChar__Part199_cmul |
| `PAG.Part260.prodChar` | `PAG.Part236.charMul` | 定義が同じ（HEq rfl） | 前の鎖 | defeq_Part260_prodChar__Part236_charMul |
| `PAG.Part260.prodChar_apply` | `PAG.Part193.mul_changeLevel_apply` | 同じ文（両向き） | 前の鎖 | Part260_prodChar_apply__of__Part193_mul_changeLevel_apply、Part193_mul_changeLevel_apply__of__Part260_prodChar_apply |
| `PAG.Part260.prodChar_apply` | `PAG.Part199.cmul_apply` | 同じ文（両向き） | 前の鎖 | Part260_prodChar_apply__of__Part199_cmul_apply、Part199_cmul_apply__of__Part260_prodChar_apply |
| `PAG.Part260.prodChar_apply` | `PAG.Part236.charMul_apply` | 同じ文（両向き） | 前の鎖 | Part260_prodChar_apply__of__Part236_charMul_apply、Part236_charMul_apply__of__Part260_prodChar_apply |
| `PAG.Part260.stdAddChar_crtMap` | `PAG.Part193.stdAddChar_param` | 同じ文（両向き） | 前の鎖 | Part260_stdAddChar_crtMap__of__Part193_stdAddChar_param、Part193_stdAddChar_param__of__Part260_stdAddChar_crtMap |
