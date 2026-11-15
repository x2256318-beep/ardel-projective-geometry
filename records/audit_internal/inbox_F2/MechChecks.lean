import PAG260
import PAG3
import PAG6
/-! 内部照合の監査（2026-11-14）：直接の当てはめ（`#dupcheck`・`#defeqcheck`）で通った組を、名前つきの定理として書き直したもの。
各定理の型は対象の宣言の型そのもの（`type_of%`）。鎖の外のファイルで、鎖は変えない。 -/

namespace PAG.AuditMech

/-- PAG.Part217.inner_smul_left' の文を PAG.Part253.ipG_smul_left から示す（T⇒S、対象 PAG.Part253.ipG_smul_left）。 -/
theorem Part217_inner_smul_left___of__Part253_ipG_smul_left : type_of% @PAG.Part217.inner_smul_left' := by
  intros
  first
  | exact PAG.Part253.ipG_smul_left
  | (apply PAG.Part253.ipG_smul_left <;> assumption)
  | (apply PAG.Part253.ipG_smul_left <;> simp_all)

/-- PAG.Part55.ip_smul_left の文を PAG.Part253.ipG_smul_left から示す（T⇒S、対象 PAG.Part253.ipG_smul_left）。 -/
theorem Part55_ip_smul_left__of__Part253_ipG_smul_left : type_of% @PAG.Part55.ip_smul_left := by
  intros
  first
  | exact PAG.Part253.ipG_smul_left
  | (apply PAG.Part253.ipG_smul_left <;> assumption)
  | (apply PAG.Part253.ipG_smul_left <;> simp_all)

/-- PAG.Part229.herm_smul_left の文を PAG.Part253.ipG_smul_left から示す（T⇒S、対象 PAG.Part253.ipG_smul_left）。 -/
theorem Part229_herm_smul_left__of__Part253_ipG_smul_left : type_of% @PAG.Part229.herm_smul_left := by
  intros
  first
  | exact PAG.Part253.ipG_smul_left
  | (apply PAG.Part253.ipG_smul_left <;> assumption)
  | (apply PAG.Part253.ipG_smul_left <;> simp_all)

/-- PAG.Part55.ip_smul_right の文を PAG.Part253.ipG_smul_right から示す（T⇒S、対象 PAG.Part253.ipG_smul_right）。 -/
theorem Part55_ip_smul_right__of__Part253_ipG_smul_right : type_of% @PAG.Part55.ip_smul_right := by
  intros
  first
  | exact PAG.Part253.ipG_smul_right
  | (apply PAG.Part253.ipG_smul_right <;> assumption)
  | (apply PAG.Part253.ipG_smul_right <;> simp_all)

/-- PAG.Part229.herm_smul_right の文を PAG.Part253.ipG_smul_right から示す（T⇒S、対象 PAG.Part253.ipG_smul_right）。 -/
theorem Part229_herm_smul_right__of__Part253_ipG_smul_right : type_of% @PAG.Part229.herm_smul_right := by
  intros
  first
  | exact PAG.Part253.ipG_smul_right
  | (apply PAG.Part253.ipG_smul_right <;> assumption)
  | (apply PAG.Part253.ipG_smul_right <;> simp_all)

/-- PAG.Part256.inv_apply_neg_one の文を PAG.Part25.chi_inv_neg_one から示す（S⇒T、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part256_inv_apply_neg_one__of__Part25_chi_inv_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part25.chi_inv_neg_one
  | (apply PAG.Part25.chi_inv_neg_one <;> assumption)
  | (apply PAG.Part25.chi_inv_neg_one <;> simp_all)

/-- PAG.Part256.inv_apply_neg_one の文を PAG.Part81.inv_neg_one から示す（S⇒T、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part256_inv_apply_neg_one__of__Part81_inv_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part81.inv_neg_one
  | (apply PAG.Part81.inv_neg_one <;> assumption)
  | (apply PAG.Part81.inv_neg_one <;> simp_all)

/-- PAG.Part256.inv_apply_neg_one の文を PAG.Part9.inv_apply_neg_one から示す（S⇒T、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part256_inv_apply_neg_one__of__Part9_inv_apply_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part9.inv_apply_neg_one
  | (apply PAG.Part9.inv_apply_neg_one <;> assumption)
  | (apply PAG.Part9.inv_apply_neg_one <;> simp_all)

/-- PAG.Part81.inv_neg_one の文を PAG.Part256.inv_apply_neg_one から示す（T⇒S、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part81_inv_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part81.inv_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)
  | (apply PAG.Part256.inv_apply_neg_one <;> simp_all)

/-- PAG.Part25.chi_inv_neg_one の文を PAG.Part256.inv_apply_neg_one から示す（T⇒S、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part25_chi_inv_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part25.chi_inv_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)
  | (apply PAG.Part256.inv_apply_neg_one <;> simp_all)

/-- PAG.Part9.inv_apply_neg_one の文を PAG.Part256.inv_apply_neg_one から示す（T⇒S、対象 PAG.Part256.inv_apply_neg_one）。 -/
theorem Part9_inv_apply_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part9.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)
  | (apply PAG.Part256.inv_apply_neg_one <;> simp_all)

/-- PAG.Part256.isPrimitive_of_prime_of_ne_one の文を PAG.Part171.primitive_of_ne_one から示す（S⇒T、対象 PAG.Part256.isPrimitive_of_prime_of_ne_one）。 -/
theorem Part256_isPrimitive_of_prime_of_ne_one__of__Part171_primitive_of_ne_one : type_of% @PAG.Part256.isPrimitive_of_prime_of_ne_one := by
  intros
  first
  | exact PAG.Part171.primitive_of_ne_one
  | (apply PAG.Part171.primitive_of_ne_one <;> assumption)
  | (apply PAG.Part171.primitive_of_ne_one <;> simp_all)

/-- PAG.Part171.primitive_of_ne_one の文を PAG.Part256.isPrimitive_of_prime_of_ne_one から示す（T⇒S、対象 PAG.Part256.isPrimitive_of_prime_of_ne_one）。 -/
theorem Part171_primitive_of_ne_one__of__Part256_isPrimitive_of_prime_of_ne_one : type_of% @PAG.Part171.primitive_of_ne_one := by
  intros
  first
  | exact PAG.Part256.isPrimitive_of_prime_of_ne_one
  | (apply PAG.Part256.isPrimitive_of_prime_of_ne_one <;> assumption)
  | (apply PAG.Part256.isPrimitive_of_prime_of_ne_one <;> simp_all)

/-- PAG.Part256.neg_one_mul_self の文を PAG.Part29.chi_neg_one_sq' から示す（S⇒T、対象 PAG.Part256.neg_one_mul_self）。 -/
theorem Part256_neg_one_mul_self__of__Part29_chi_neg_one_sq_ : type_of% @PAG.Part256.neg_one_mul_self := by
  intros
  first
  | exact PAG.Part29.chi_neg_one_sq'
  | (apply PAG.Part29.chi_neg_one_sq' <;> assumption)
  | (apply PAG.Part29.chi_neg_one_sq' <;> simp_all)

/-- PAG.Part256.neg_one_mul_self の文を PAG.Part9.chi_neg_one_sq から示す（S⇒T、対象 PAG.Part256.neg_one_mul_self）。 -/
theorem Part256_neg_one_mul_self__of__Part9_chi_neg_one_sq : type_of% @PAG.Part256.neg_one_mul_self := by
  intros
  first
  | exact PAG.Part9.chi_neg_one_sq
  | (apply PAG.Part9.chi_neg_one_sq <;> assumption)
  | (apply PAG.Part9.chi_neg_one_sq <;> simp_all)

/-- PAG.Part29.chi_neg_one_sq' の文を PAG.Part256.neg_one_mul_self から示す（T⇒S、対象 PAG.Part256.neg_one_mul_self）。 -/
theorem Part29_chi_neg_one_sq___of__Part256_neg_one_mul_self : type_of% @PAG.Part29.chi_neg_one_sq' := by
  intros
  first
  | exact PAG.Part256.neg_one_mul_self
  | (apply PAG.Part256.neg_one_mul_self <;> assumption)
  | (apply PAG.Part256.neg_one_mul_self <;> simp_all)

/-- PAG.Part9.chi_neg_one_sq の文を PAG.Part256.neg_one_mul_self から示す（T⇒S、対象 PAG.Part256.neg_one_mul_self）。 -/
theorem Part9_chi_neg_one_sq__of__Part256_neg_one_mul_self : type_of% @PAG.Part9.chi_neg_one_sq := by
  intros
  first
  | exact PAG.Part256.neg_one_mul_self
  | (apply PAG.Part256.neg_one_mul_self <;> assumption)
  | (apply PAG.Part256.neg_one_mul_self <;> simp_all)

/-- PAG.Part257.eq_one_of_two の文を PAG.Part198.level_two_trivial から示す（S⇒T、対象 PAG.Part257.eq_one_of_two）。 -/
theorem Part257_eq_one_of_two__of__Part198_level_two_trivial : type_of% @PAG.Part257.eq_one_of_two := by
  intros
  first
  | exact PAG.Part198.level_two_trivial
  | (apply PAG.Part198.level_two_trivial <;> assumption)
  | (apply PAG.Part198.level_two_trivial <;> simp_all)

/-- PAG.Part256.removal_counterexample_normSq の文を PAG.Part257.normSq_rootNum_one_prime から示す（T⇒S、対象 PAG.Part257.normSq_rootNum_one_prime）。 -/
theorem Part256_removal_counterexample_normSq__of__Part257_normSq_rootNum_one_prime : type_of% @PAG.Part256.removal_counterexample_normSq := by
  intros
  first
  | exact PAG.Part257.normSq_rootNum_one_prime
  | (apply PAG.Part257.normSq_rootNum_one_prime <;> assumption)
  | (apply PAG.Part257.normSq_rootNum_one_prime <;> simp_all)

/-- PAG.Part258.ip_smul_right の文を PAG.Part253.ipG_smul_right から示す（S⇒T、対象 PAG.Part258.ip_smul_right）。 -/
theorem Part258_ip_smul_right__of__Part253_ipG_smul_right : type_of% @PAG.Part258.ip_smul_right := by
  intros
  first
  | exact PAG.Part253.ipG_smul_right
  | (apply PAG.Part253.ipG_smul_right <;> assumption)
  | (apply PAG.Part253.ipG_smul_right <;> simp_all)

/-- PAG.Part260.cast_crtMap_fst の文を PAG.Part193.param_cast₁ から示す（S⇒T、対象 PAG.Part260.cast_crtMap_fst）。 -/
theorem Part260_cast_crtMap_fst__of__Part193_param_cast_ : type_of% @PAG.Part260.cast_crtMap_fst := by
  intros
  first
  | exact PAG.Part193.param_cast₁
  | (apply PAG.Part193.param_cast₁ <;> assumption)
  | (apply PAG.Part193.param_cast₁ <;> simp_all)

/-- PAG.Part260.cast_crtMap_snd の文を PAG.Part193.param_cast₂ から示す（S⇒T、対象 PAG.Part260.cast_crtMap_snd）。 -/
theorem Part260_cast_crtMap_snd__of__Part193_param_cast_ : type_of% @PAG.Part260.cast_crtMap_snd := by
  intros
  first
  | exact PAG.Part193.param_cast₂
  | (apply PAG.Part193.param_cast₂ <;> assumption)
  | (apply PAG.Part193.param_cast₂ <;> simp_all)

/-- PAG.Part260.charU_prodChar の文を PAG.Part193.mul_changeLevel_apply から示す（S⇒T、対象 PAG.Part260.charU_prodChar）。 -/
theorem Part260_charU_prodChar__of__Part193_mul_changeLevel_apply : type_of% @PAG.Part260.charU_prodChar := by
  intros
  first
  | exact PAG.Part193.mul_changeLevel_apply
  | (apply PAG.Part193.mul_changeLevel_apply <;> assumption)
  | (apply PAG.Part193.mul_changeLevel_apply <;> simp_all)

/-- PAG.Part260.charU_prodChar の文を PAG.Part199.cmul_apply から示す（S⇒T、対象 PAG.Part260.charU_prodChar）。 -/
theorem Part260_charU_prodChar__of__Part199_cmul_apply : type_of% @PAG.Part260.charU_prodChar := by
  intros
  first
  | exact PAG.Part199.cmul_apply
  | (apply PAG.Part199.cmul_apply <;> assumption)
  | (apply PAG.Part199.cmul_apply <;> simp_all)

/-- PAG.Part260.charU_prodChar の文を PAG.Part236.charMul_apply から示す（S⇒T、対象 PAG.Part260.charU_prodChar）。 -/
theorem Part260_charU_prodChar__of__Part236_charMul_apply : type_of% @PAG.Part260.charU_prodChar := by
  intros
  first
  | exact PAG.Part236.charMul_apply
  | (apply PAG.Part236.charMul_apply <;> assumption)
  | (apply PAG.Part236.charMul_apply <;> simp_all)

/-- PAG.Part260.charU_prodChar の文を PAG.Part236.charMul_apply_unit から示す（S⇒T、対象 PAG.Part260.charU_prodChar）。 -/
theorem Part260_charU_prodChar__of__Part236_charMul_apply_unit : type_of% @PAG.Part260.charU_prodChar := by
  intros
  first
  | exact PAG.Part236.charMul_apply_unit
  | (apply PAG.Part236.charMul_apply_unit <;> assumption)
  | (apply PAG.Part236.charMul_apply_unit <;> simp_all)

/-- PAG.Part260.crtMap_bijective の文を PAG.Part193.param_bijective から示す（S⇒T、対象 PAG.Part260.crtMap_bijective）。 -/
theorem Part260_crtMap_bijective__of__Part193_param_bijective : type_of% @PAG.Part260.crtMap_bijective := by
  intros
  first
  | exact PAG.Part193.param_bijective
  | (apply PAG.Part193.param_bijective <;> assumption)
  | (apply PAG.Part193.param_bijective <;> simp_all)

/-- PAG.Part193.param_bijective の文を PAG.Part260.crtMap_bijective から示す（T⇒S、対象 PAG.Part260.crtMap_bijective）。 -/
theorem Part193_param_bijective__of__Part260_crtMap_bijective : type_of% @PAG.Part193.param_bijective := by
  intros
  first
  | exact PAG.Part260.crtMap_bijective
  | (apply PAG.Part260.crtMap_bijective <;> assumption)
  | (apply PAG.Part260.crtMap_bijective <;> simp_all)

/-- PAG.Part260.gaussSum_prodChar の文を PAG.Part193.gaussSum_mul_coprime から示す（S⇒T、対象 PAG.Part260.gaussSum_prodChar）。 -/
theorem Part260_gaussSum_prodChar__of__Part193_gaussSum_mul_coprime : type_of% @PAG.Part260.gaussSum_prodChar := by
  intros
  first
  | exact PAG.Part193.gaussSum_mul_coprime
  | (apply PAG.Part193.gaussSum_mul_coprime <;> assumption)
  | (apply PAG.Part193.gaussSum_mul_coprime <;> simp_all)

/-- PAG.Part193.gaussSum_mul_coprime の文を PAG.Part260.gaussSum_prodChar から示す（T⇒S、対象 PAG.Part260.gaussSum_prodChar）。 -/
theorem Part193_gaussSum_mul_coprime__of__Part260_gaussSum_prodChar : type_of% @PAG.Part193.gaussSum_mul_coprime := by
  intros
  first
  | exact PAG.Part260.gaussSum_prodChar
  | (apply PAG.Part260.gaussSum_prodChar <;> assumption)
  | (apply PAG.Part260.gaussSum_prodChar <;> simp_all)

/-- PAG.Part260.isPrimitive_prodChar の文を PAG.Part194.isPrimitive_mul から示す（S⇒T、対象 PAG.Part260.isPrimitive_prodChar）。 -/
theorem Part260_isPrimitive_prodChar__of__Part194_isPrimitive_mul : type_of% @PAG.Part260.isPrimitive_prodChar := by
  intros
  first
  | exact PAG.Part194.isPrimitive_mul
  | (apply PAG.Part194.isPrimitive_mul <;> assumption)
  | (apply PAG.Part194.isPrimitive_mul <;> simp_all)

/-- PAG.Part260.isPrimitive_prodChar の文を PAG.Part236.isPrimitive_charMul から示す（S⇒T、対象 PAG.Part260.isPrimitive_prodChar）。 -/
theorem Part260_isPrimitive_prodChar__of__Part236_isPrimitive_charMul : type_of% @PAG.Part260.isPrimitive_prodChar := by
  intros
  first
  | exact PAG.Part236.isPrimitive_charMul
  | (apply PAG.Part236.isPrimitive_charMul <;> assumption)
  | (apply PAG.Part236.isPrimitive_charMul <;> simp_all)

/-- PAG.Part194.isPrimitive_mul の文を PAG.Part260.isPrimitive_prodChar から示す（T⇒S、対象 PAG.Part260.isPrimitive_prodChar）。 -/
theorem Part194_isPrimitive_mul__of__Part260_isPrimitive_prodChar : type_of% @PAG.Part194.isPrimitive_mul := by
  intros
  first
  | exact PAG.Part260.isPrimitive_prodChar
  | (apply PAG.Part260.isPrimitive_prodChar <;> assumption)
  | (apply PAG.Part260.isPrimitive_prodChar <;> simp_all)

/-- PAG.Part236.isPrimitive_charMul の文を PAG.Part260.isPrimitive_prodChar から示す（T⇒S、対象 PAG.Part260.isPrimitive_prodChar）。 -/
theorem Part236_isPrimitive_charMul__of__Part260_isPrimitive_prodChar : type_of% @PAG.Part236.isPrimitive_charMul := by
  intros
  first
  | exact PAG.Part260.isPrimitive_prodChar
  | (apply PAG.Part260.isPrimitive_prodChar <;> assumption)
  | (apply PAG.Part260.isPrimitive_prodChar <;> simp_all)

/-- PAG.Part260.prodChar と PAG.Part199.cmul は同じ定義（HEq rfl）。 -/
theorem defeq_Part260_prodChar__Part199_cmul : HEq @PAG.Part260.prodChar @PAG.Part199.cmul := HEq.rfl

/-- PAG.Part260.prodChar と PAG.Part236.charMul は同じ定義（HEq rfl）。 -/
theorem defeq_Part260_prodChar__Part236_charMul : HEq @PAG.Part260.prodChar @PAG.Part236.charMul := HEq.rfl

/-- PAG.Part260.prodChar_apply の文を PAG.Part193.mul_changeLevel_apply から示す（S⇒T、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part260_prodChar_apply__of__Part193_mul_changeLevel_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part193.mul_changeLevel_apply
  | (apply PAG.Part193.mul_changeLevel_apply <;> assumption)
  | (apply PAG.Part193.mul_changeLevel_apply <;> simp_all)

/-- PAG.Part260.prodChar_apply の文を PAG.Part199.cmul_apply から示す（S⇒T、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part260_prodChar_apply__of__Part199_cmul_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part199.cmul_apply
  | (apply PAG.Part199.cmul_apply <;> assumption)
  | (apply PAG.Part199.cmul_apply <;> simp_all)

/-- PAG.Part260.prodChar_apply の文を PAG.Part236.charMul_apply から示す（S⇒T、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part260_prodChar_apply__of__Part236_charMul_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part236.charMul_apply
  | (apply PAG.Part236.charMul_apply <;> assumption)
  | (apply PAG.Part236.charMul_apply <;> simp_all)

/-- PAG.Part236.charMul_apply の文を PAG.Part260.prodChar_apply から示す（T⇒S、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part236_charMul_apply__of__Part260_prodChar_apply : type_of% @PAG.Part236.charMul_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)
  | (apply PAG.Part260.prodChar_apply <;> simp_all)

/-- PAG.Part193.mul_changeLevel_apply の文を PAG.Part260.prodChar_apply から示す（T⇒S、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part193_mul_changeLevel_apply__of__Part260_prodChar_apply : type_of% @PAG.Part193.mul_changeLevel_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)
  | (apply PAG.Part260.prodChar_apply <;> simp_all)

/-- PAG.Part199.cmul_apply の文を PAG.Part260.prodChar_apply から示す（T⇒S、対象 PAG.Part260.prodChar_apply）。 -/
theorem Part199_cmul_apply__of__Part260_prodChar_apply : type_of% @PAG.Part199.cmul_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)
  | (apply PAG.Part260.prodChar_apply <;> simp_all)

/-- PAG.Part260.stdAddChar_crtMap の文を PAG.Part193.stdAddChar_param から示す（S⇒T、対象 PAG.Part260.stdAddChar_crtMap）。 -/
theorem Part260_stdAddChar_crtMap__of__Part193_stdAddChar_param : type_of% @PAG.Part260.stdAddChar_crtMap := by
  intros
  first
  | exact PAG.Part193.stdAddChar_param
  | (apply PAG.Part193.stdAddChar_param <;> assumption)
  | (apply PAG.Part193.stdAddChar_param <;> simp_all)

/-- PAG.Part193.stdAddChar_param の文を PAG.Part260.stdAddChar_crtMap から示す（T⇒S、対象 PAG.Part260.stdAddChar_crtMap）。 -/
theorem Part193_stdAddChar_param__of__Part260_stdAddChar_crtMap : type_of% @PAG.Part193.stdAddChar_param := by
  intros
  first
  | exact PAG.Part260.stdAddChar_crtMap
  | (apply PAG.Part260.stdAddChar_crtMap <;> assumption)
  | (apply PAG.Part260.stdAddChar_crtMap <;> simp_all)

end PAG.AuditMech

#print axioms PAG.AuditMech.Part217_inner_smul_left___of__Part253_ipG_smul_left
#print axioms PAG.AuditMech.Part55_ip_smul_left__of__Part253_ipG_smul_left
#print axioms PAG.AuditMech.Part229_herm_smul_left__of__Part253_ipG_smul_left
#print axioms PAG.AuditMech.Part55_ip_smul_right__of__Part253_ipG_smul_right
#print axioms PAG.AuditMech.Part229_herm_smul_right__of__Part253_ipG_smul_right
#print axioms PAG.AuditMech.Part256_inv_apply_neg_one__of__Part25_chi_inv_neg_one
#print axioms PAG.AuditMech.Part256_inv_apply_neg_one__of__Part81_inv_neg_one
#print axioms PAG.AuditMech.Part256_inv_apply_neg_one__of__Part9_inv_apply_neg_one
#print axioms PAG.AuditMech.Part81_inv_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMech.Part25_chi_inv_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMech.Part9_inv_apply_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMech.Part256_isPrimitive_of_prime_of_ne_one__of__Part171_primitive_of_ne_one
#print axioms PAG.AuditMech.Part171_primitive_of_ne_one__of__Part256_isPrimitive_of_prime_of_ne_one
#print axioms PAG.AuditMech.Part256_neg_one_mul_self__of__Part29_chi_neg_one_sq_
#print axioms PAG.AuditMech.Part256_neg_one_mul_self__of__Part9_chi_neg_one_sq
#print axioms PAG.AuditMech.Part29_chi_neg_one_sq___of__Part256_neg_one_mul_self
#print axioms PAG.AuditMech.Part9_chi_neg_one_sq__of__Part256_neg_one_mul_self
#print axioms PAG.AuditMech.Part257_eq_one_of_two__of__Part198_level_two_trivial
#print axioms PAG.AuditMech.Part256_removal_counterexample_normSq__of__Part257_normSq_rootNum_one_prime
#print axioms PAG.AuditMech.Part258_ip_smul_right__of__Part253_ipG_smul_right
#print axioms PAG.AuditMech.Part260_cast_crtMap_fst__of__Part193_param_cast_
#print axioms PAG.AuditMech.Part260_cast_crtMap_snd__of__Part193_param_cast_
#print axioms PAG.AuditMech.Part260_charU_prodChar__of__Part193_mul_changeLevel_apply
#print axioms PAG.AuditMech.Part260_charU_prodChar__of__Part199_cmul_apply
#print axioms PAG.AuditMech.Part260_charU_prodChar__of__Part236_charMul_apply
#print axioms PAG.AuditMech.Part260_charU_prodChar__of__Part236_charMul_apply_unit
#print axioms PAG.AuditMech.Part260_crtMap_bijective__of__Part193_param_bijective
#print axioms PAG.AuditMech.Part193_param_bijective__of__Part260_crtMap_bijective
#print axioms PAG.AuditMech.Part260_gaussSum_prodChar__of__Part193_gaussSum_mul_coprime
#print axioms PAG.AuditMech.Part193_gaussSum_mul_coprime__of__Part260_gaussSum_prodChar
#print axioms PAG.AuditMech.Part260_isPrimitive_prodChar__of__Part194_isPrimitive_mul
#print axioms PAG.AuditMech.Part260_isPrimitive_prodChar__of__Part236_isPrimitive_charMul
#print axioms PAG.AuditMech.Part194_isPrimitive_mul__of__Part260_isPrimitive_prodChar
#print axioms PAG.AuditMech.Part236_isPrimitive_charMul__of__Part260_isPrimitive_prodChar
#print axioms PAG.AuditMech.defeq_Part260_prodChar__Part199_cmul
#print axioms PAG.AuditMech.defeq_Part260_prodChar__Part236_charMul
#print axioms PAG.AuditMech.Part260_prodChar_apply__of__Part193_mul_changeLevel_apply
#print axioms PAG.AuditMech.Part260_prodChar_apply__of__Part199_cmul_apply
#print axioms PAG.AuditMech.Part260_prodChar_apply__of__Part236_charMul_apply
#print axioms PAG.AuditMech.Part236_charMul_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMech.Part193_mul_changeLevel_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMech.Part199_cmul_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMech.Part260_stdAddChar_crtMap__of__Part193_stdAddChar_param
#print axioms PAG.AuditMech.Part193_stdAddChar_param__of__Part260_stdAddChar_crtMap
