import PAG260
import PAG3
import PAG6
/-! 新15：同じ文（両向き）の組を、`simp_all` の分岐なしで確かめる（exact か、apply と assumption だけ）。 -/
namespace PAG.AuditMechA

theorem Part256_inv_apply_neg_one__of__Part25_chi_inv_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part25.chi_inv_neg_one
  | (apply PAG.Part25.chi_inv_neg_one <;> assumption)

theorem Part25_chi_inv_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part25.chi_inv_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)

theorem Part256_inv_apply_neg_one__of__Part81_inv_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part81.inv_neg_one
  | (apply PAG.Part81.inv_neg_one <;> assumption)

theorem Part81_inv_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part81.inv_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)

theorem Part256_inv_apply_neg_one__of__Part9_inv_apply_neg_one : type_of% @PAG.Part256.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part9.inv_apply_neg_one
  | (apply PAG.Part9.inv_apply_neg_one <;> assumption)

theorem Part9_inv_apply_neg_one__of__Part256_inv_apply_neg_one : type_of% @PAG.Part9.inv_apply_neg_one := by
  intros
  first
  | exact PAG.Part256.inv_apply_neg_one
  | (apply PAG.Part256.inv_apply_neg_one <;> assumption)

theorem Part256_isPrimitive_of_prime_of_ne_one__of__Part171_primitive_of_ne_one : type_of% @PAG.Part256.isPrimitive_of_prime_of_ne_one := by
  intros
  first
  | exact PAG.Part171.primitive_of_ne_one
  | (apply PAG.Part171.primitive_of_ne_one <;> assumption)

theorem Part171_primitive_of_ne_one__of__Part256_isPrimitive_of_prime_of_ne_one : type_of% @PAG.Part171.primitive_of_ne_one := by
  intros
  first
  | exact PAG.Part256.isPrimitive_of_prime_of_ne_one
  | (apply PAG.Part256.isPrimitive_of_prime_of_ne_one <;> assumption)

theorem Part256_neg_one_mul_self__of__Part29_chi_neg_one_sq_ : type_of% @PAG.Part256.neg_one_mul_self := by
  intros
  first
  | exact PAG.Part29.chi_neg_one_sq'
  | (apply PAG.Part29.chi_neg_one_sq' <;> assumption)

theorem Part29_chi_neg_one_sq___of__Part256_neg_one_mul_self : type_of% @PAG.Part29.chi_neg_one_sq' := by
  intros
  first
  | exact PAG.Part256.neg_one_mul_self
  | (apply PAG.Part256.neg_one_mul_self <;> assumption)

theorem Part256_neg_one_mul_self__of__Part9_chi_neg_one_sq : type_of% @PAG.Part256.neg_one_mul_self := by
  intros
  first
  | exact PAG.Part9.chi_neg_one_sq
  | (apply PAG.Part9.chi_neg_one_sq <;> assumption)

theorem Part9_chi_neg_one_sq__of__Part256_neg_one_mul_self : type_of% @PAG.Part9.chi_neg_one_sq := by
  intros
  first
  | exact PAG.Part256.neg_one_mul_self
  | (apply PAG.Part256.neg_one_mul_self <;> assumption)

theorem Part260_crtMap_bijective__of__Part193_param_bijective : type_of% @PAG.Part260.crtMap_bijective := by
  intros
  first
  | exact PAG.Part193.param_bijective
  | (apply PAG.Part193.param_bijective <;> assumption)

theorem Part193_param_bijective__of__Part260_crtMap_bijective : type_of% @PAG.Part193.param_bijective := by
  intros
  first
  | exact PAG.Part260.crtMap_bijective
  | (apply PAG.Part260.crtMap_bijective <;> assumption)

theorem Part260_gaussSum_prodChar__of__Part193_gaussSum_mul_coprime : type_of% @PAG.Part260.gaussSum_prodChar := by
  intros
  first
  | exact PAG.Part193.gaussSum_mul_coprime
  | (apply PAG.Part193.gaussSum_mul_coprime <;> assumption)

theorem Part193_gaussSum_mul_coprime__of__Part260_gaussSum_prodChar : type_of% @PAG.Part193.gaussSum_mul_coprime := by
  intros
  first
  | exact PAG.Part260.gaussSum_prodChar
  | (apply PAG.Part260.gaussSum_prodChar <;> assumption)

theorem Part260_isPrimitive_prodChar__of__Part194_isPrimitive_mul : type_of% @PAG.Part260.isPrimitive_prodChar := by
  intros
  first
  | exact PAG.Part194.isPrimitive_mul
  | (apply PAG.Part194.isPrimitive_mul <;> assumption)

theorem Part194_isPrimitive_mul__of__Part260_isPrimitive_prodChar : type_of% @PAG.Part194.isPrimitive_mul := by
  intros
  first
  | exact PAG.Part260.isPrimitive_prodChar
  | (apply PAG.Part260.isPrimitive_prodChar <;> assumption)

theorem Part260_isPrimitive_prodChar__of__Part236_isPrimitive_charMul : type_of% @PAG.Part260.isPrimitive_prodChar := by
  intros
  first
  | exact PAG.Part236.isPrimitive_charMul
  | (apply PAG.Part236.isPrimitive_charMul <;> assumption)

theorem Part236_isPrimitive_charMul__of__Part260_isPrimitive_prodChar : type_of% @PAG.Part236.isPrimitive_charMul := by
  intros
  first
  | exact PAG.Part260.isPrimitive_prodChar
  | (apply PAG.Part260.isPrimitive_prodChar <;> assumption)

theorem Part260_prodChar_apply__of__Part193_mul_changeLevel_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part193.mul_changeLevel_apply
  | (apply PAG.Part193.mul_changeLevel_apply <;> assumption)

theorem Part193_mul_changeLevel_apply__of__Part260_prodChar_apply : type_of% @PAG.Part193.mul_changeLevel_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)

theorem Part260_prodChar_apply__of__Part199_cmul_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part199.cmul_apply
  | (apply PAG.Part199.cmul_apply <;> assumption)

theorem Part199_cmul_apply__of__Part260_prodChar_apply : type_of% @PAG.Part199.cmul_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)

theorem Part260_prodChar_apply__of__Part236_charMul_apply : type_of% @PAG.Part260.prodChar_apply := by
  intros
  first
  | exact PAG.Part236.charMul_apply
  | (apply PAG.Part236.charMul_apply <;> assumption)

theorem Part236_charMul_apply__of__Part260_prodChar_apply : type_of% @PAG.Part236.charMul_apply := by
  intros
  first
  | exact PAG.Part260.prodChar_apply
  | (apply PAG.Part260.prodChar_apply <;> assumption)

theorem Part260_stdAddChar_crtMap__of__Part193_stdAddChar_param : type_of% @PAG.Part260.stdAddChar_crtMap := by
  intros
  first
  | exact PAG.Part193.stdAddChar_param
  | (apply PAG.Part193.stdAddChar_param <;> assumption)

theorem Part193_stdAddChar_param__of__Part260_stdAddChar_crtMap : type_of% @PAG.Part193.stdAddChar_param := by
  intros
  first
  | exact PAG.Part260.stdAddChar_crtMap
  | (apply PAG.Part260.stdAddChar_crtMap <;> assumption)

end PAG.AuditMechA

#print axioms PAG.AuditMechA.Part256_inv_apply_neg_one__of__Part25_chi_inv_neg_one
#print axioms PAG.AuditMechA.Part25_chi_inv_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMechA.Part256_inv_apply_neg_one__of__Part81_inv_neg_one
#print axioms PAG.AuditMechA.Part81_inv_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMechA.Part256_inv_apply_neg_one__of__Part9_inv_apply_neg_one
#print axioms PAG.AuditMechA.Part9_inv_apply_neg_one__of__Part256_inv_apply_neg_one
#print axioms PAG.AuditMechA.Part256_isPrimitive_of_prime_of_ne_one__of__Part171_primitive_of_ne_one
#print axioms PAG.AuditMechA.Part171_primitive_of_ne_one__of__Part256_isPrimitive_of_prime_of_ne_one
#print axioms PAG.AuditMechA.Part256_neg_one_mul_self__of__Part29_chi_neg_one_sq_
#print axioms PAG.AuditMechA.Part29_chi_neg_one_sq___of__Part256_neg_one_mul_self
#print axioms PAG.AuditMechA.Part256_neg_one_mul_self__of__Part9_chi_neg_one_sq
#print axioms PAG.AuditMechA.Part9_chi_neg_one_sq__of__Part256_neg_one_mul_self
#print axioms PAG.AuditMechA.Part260_crtMap_bijective__of__Part193_param_bijective
#print axioms PAG.AuditMechA.Part193_param_bijective__of__Part260_crtMap_bijective
#print axioms PAG.AuditMechA.Part260_gaussSum_prodChar__of__Part193_gaussSum_mul_coprime
#print axioms PAG.AuditMechA.Part193_gaussSum_mul_coprime__of__Part260_gaussSum_prodChar
#print axioms PAG.AuditMechA.Part260_isPrimitive_prodChar__of__Part194_isPrimitive_mul
#print axioms PAG.AuditMechA.Part194_isPrimitive_mul__of__Part260_isPrimitive_prodChar
#print axioms PAG.AuditMechA.Part260_isPrimitive_prodChar__of__Part236_isPrimitive_charMul
#print axioms PAG.AuditMechA.Part236_isPrimitive_charMul__of__Part260_isPrimitive_prodChar
#print axioms PAG.AuditMechA.Part260_prodChar_apply__of__Part193_mul_changeLevel_apply
#print axioms PAG.AuditMechA.Part193_mul_changeLevel_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMechA.Part260_prodChar_apply__of__Part199_cmul_apply
#print axioms PAG.AuditMechA.Part199_cmul_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMechA.Part260_prodChar_apply__of__Part236_charMul_apply
#print axioms PAG.AuditMechA.Part236_charMul_apply__of__Part260_prodChar_apply
#print axioms PAG.AuditMechA.Part260_stdAddChar_crtMap__of__Part193_stdAddChar_param
#print axioms PAG.AuditMechA.Part193_stdAddChar_param__of__Part260_stdAddChar_crtMap
