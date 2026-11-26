
import PAG264

namespace PAG.Part265

open PAG.Part218 PAG.Part258 PAG.Part264

noncomputable def cornerSys (a b : Lvl) (h : a ≤ b) : shellAlg a.val →ₙₐ[ℂ] shellAlg b.val :=
  cornerHom (N := a.val) (M := b.val) h

theorem cornerSys_self (a : Lvl) (S : shellAlg a.val) : cornerSys a a le_rfl S = S := by
  apply Subtype.ext
  exact cornerOp_self (N := a.val) (S : Module.End ℂ (ZMod a.val → ℂ))

theorem cornerSys_comp {a b c : Lvl} (hab : a ≤ b) (hbc : b ≤ c) (S : shellAlg a.val) :
    cornerSys b c hbc (cornerSys a b hab S) = cornerSys a c (hab.trans hbc) S := by
  apply Subtype.ext
  exact cornerOp_comp (N := a.val) (M := b.val) (L := c.val) hab hbc (S : Module.End ℂ (ZMod a.val → ℂ))

instance : DirectedSystem (fun a : Lvl => shellAlg a.val)
    (fun a b h => (cornerSys a b h : shellAlg a.val → shellAlg b.val)) where
  map_self a S := cornerSys_self a S
  map_map _ _ _ hab hbc S := cornerSys_comp hab hbc S

abbrev CornerLim : Type := DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys

noncomputable def ofCorner (a : Lvl) : shellAlg a.val →ₙₐ[ℂ] CornerLim :=
  DirectLimit.NonUnitalAlgebra.of _ cornerSys a

theorem ofCorner_apply (a : Lvl) (S : shellAlg a.val) :
    ofCorner a S = (⟦⟨a, S⟩⟧ : CornerLim) := rfl

theorem ofCorner_cornerSys {a b : Lvl} (h : a ≤ b) (S : shellAlg a.val) :
    ofCorner b (cornerSys a b h S) = ofCorner a S := by
  rw [ofCorner_apply, ofCorner_apply]
  exact (DirectLimit.eq_of_le (F := fun a : Lvl => shellAlg a.val) (f := cornerSys) ⟨a, S⟩ b h).symm

theorem ofCorner_injective (a : Lvl) : Function.Injective (ofCorner a) :=
  DirectLimit.mk_injective cornerSys (fun b c h => cornerHom_injective (N := b.val) (M := c.val) h) a

theorem exists_local_unit (x : CornerLim) :
    ∃ a : Lvl, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  obtain ⟨a, S, rfl⟩ := DirectLimit.exists_eq_mk cornerSys x
  refine ⟨a, ?_, ?_⟩
  · rw [← ofCorner_apply, ← map_mul, one_mul]
  · rw [← ofCorner_apply, ← map_mul, mul_one]

theorem ofCorner_one_mul_self (a : Lvl) : ofCorner a 1 * ofCorner a 1 = ofCorner a 1 := by
  rw [← map_mul, one_mul]

theorem ofCorner_one_le {a b : Lvl} (h : a ≤ b) :
    ofCorner b 1 * ofCorner a 1 = ofCorner a 1 ∧ ofCorner a 1 * ofCorner b 1 = ofCorner a 1 := by
  rw [← ofCorner_cornerSys h 1]
  exact ⟨by rw [← map_mul, one_mul], by rw [← map_mul, mul_one]⟩

theorem exists_local_unit_finset (F : Finset CornerLim) :
    ∃ a : Lvl, ∀ x ∈ F, ofCorner a 1 * x = x ∧ x * ofCorner a 1 = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨⟨1, Nat.one_pos⟩, fun x hx => by simp at hx⟩
  | insert x F _ ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := exists_local_unit x
    obtain ⟨c, hac, hbc⟩ := (show IsDirectedOrder Lvl from inferInstance).directed a b
    have mono : ∀ {d : Lvl}, d ≤ c → ∀ y : CornerLim, (ofCorner d 1 * y = y ∧ y * ofCorner d 1 = y) →
        (ofCorner c 1 * y = y ∧ y * ofCorner c 1 = y) := by
      intro d hd y hy
      obtain ⟨l, r⟩ := ofCorner_one_le hd
      constructor
      · calc ofCorner c 1 * y = ofCorner c 1 * (ofCorner d 1 * y) := by rw [hy.1]
          _ = ofCorner d 1 * y := by rw [← mul_assoc, l]
          _ = y := hy.1
      · calc y * ofCorner c 1 = (y * ofCorner d 1) * ofCorner c 1 := by rw [hy.2]
          _ = y * ofCorner d 1 := by rw [mul_assoc, r]
          _ = y := hy.2
    refine ⟨c, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact mono hbc y hb
    · exact mono hac y (ha y hy)

theorem not_exists_left_one : ¬ ∃ u : CornerLim, ∀ x : CornerLim, u * x = x := by
  rintro ⟨u, hu⟩
  obtain ⟨c, U, rfl⟩ := DirectLimit.exists_eq_mk cornerSys u
  let d : Lvl := ⟨2 * c.val, Nat.mul_pos (by norm_num) c.pos⟩
  have h : c ≤ d := ⟨2, by simp [d, mul_comm]⟩
  have e := hu (ofCorner d 1)
  rw [← ofCorner_apply, ← ofCorner_cornerSys h U, ← map_mul, mul_one] at e
  have e2 : cornerSys c d h U = 1 := ofCorner_injective d e
  have e3 := congrArg Subtype.val e2
  change cornerOp (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ)) = 1 at e3
  have hq := cornerOp_one_mul (N := c.val) (M := d.val) h (U : Module.End ℂ (ZMod c.val → ℂ))
  rw [e3] at hq
  have hlt : c.val < d.val := by
    show c.val < 2 * c.val
    have := c.pos; omega
  exact cornerOp_one_ne_one (N := c.val) (M := d.val) h hlt (by simpa using hq)

end PAG.Part265

#print axioms PAG.Part265.cornerSys_self
#print axioms PAG.Part265.cornerSys_comp
#print axioms PAG.Part265.ofCorner_apply
#print axioms PAG.Part265.ofCorner_cornerSys
#print axioms PAG.Part265.ofCorner_injective
#print axioms PAG.Part265.exists_local_unit
#print axioms PAG.Part265.ofCorner_one_mul_self
#print axioms PAG.Part265.ofCorner_one_le
#print axioms PAG.Part265.exists_local_unit_finset
#print axioms PAG.Part265.not_exists_left_one
