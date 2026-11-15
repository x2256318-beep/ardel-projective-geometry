/-
  PAG 2.0 Part 18（2026-10-18）— 定理 B の閉じた形（球・殻の指示関数による展開）
  B_cv(|w,χ⟩, |w,χ̄⟩) = χ(−1) · ( 1_{p^(w+c)Z} − (p−1)⁻¹ · 1_{S_(w+c−1)} )
  （1_{S_u} = 1_{p^u Z} − 1_{p^(u+1) Z} は殻 u の指示関数）
  Part 5 の展開 χ(−1)√(p^K/|S_{w0}|) Σ_u F_{u,w0} e_u の係数は、殻 u ≥ w+c で √|S_u|、
  殻 w+c−1 で −√|S_u|/(p−1) に対応する。
-/
import PAG21

namespace PAG.Part22

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21

variable {p : ℕ} [hp : Fact p.Prime]

/-- 球 p^j Z/p^K の指示関数。 -/
noncomputable def ball (K j : ℕ) : ZMod (p ^ K) → ℂ := fun x => if p ^ j ∣ x.val then 1 else 0

/-- ι_w の値の val。 -/
theorem val_shellEmb (K w : ℕ) (hw : w ≤ K) (y : ZMod (p ^ (K - w))) :
    (shellEmb (p := p) K w hw y).val = (p ^ w * y.val) % p ^ K := by
  rw [shellEmb_apply, ZMod.val_natCast]

/-- p^(w+j) ∣ (ι_w y).val ⇔ p^j ∣ y.val（w + j ≤ K）。 -/
theorem dvd_val_shellEmb (K w j : ℕ) (hw : w ≤ K) (hj : w + j ≤ K) (y : ZMod (p ^ (K - w))) :
    p ^ (w + j) ∣ (shellEmb (p := p) K w hw y).val ↔ p ^ j ∣ y.val := by
  rw [val_shellEmb, Nat.dvd_mod_iff (pow_dvd_pow p hj), pow_add]
  exact Nat.mul_dvd_mul_iff_left (pow_pos hp.out.pos w)

/-- ι_w の像 ⇔ p^w ∣ x.val。 -/
theorem mem_range_iff (K w : ℕ) (hw : w ≤ K) (x : ZMod (p ^ K)) :
    (∃ y, shellEmb (p := p) K w hw y = x) ↔ p ^ w ∣ x.val := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hKw : p ^ K = p ^ w * p ^ (K - w) := by rw [← pow_add]; congr 1; omega
  constructor
  · rintro ⟨y, rfl⟩
    rw [val_shellEmb]
    exact (Nat.dvd_mod_iff (pow_dvd_pow p hw)).mpr (dvd_mul_right _ _)
  · rintro ⟨m, hm⟩
    refine ⟨((m : ℕ) : ZMod (p ^ (K - w))), ?_⟩
    rw [shellEmb_apply, ZMod.val_natCast, ← ZMod.natCast_zmod_val x, hm, ZMod.natCast_eq_natCast_iff', hKw]
    simp only [Nat.mul_mod_mul_left, Nat.mod_mod]

/-- **球の押し出し**: ι_{w,*}(a·1_{p^j | ·}) = a · 1_{p^(w+j) Z}（w + j ≤ K）。 -/
theorem push_ball (K w j : ℕ) (hw : w ≤ K) (hj : w + j ≤ K) (a : ℂ) :
    push (shellEmb (p := p) K w hw) (fun y : ZMod (p ^ (K - w)) => if p ^ j ∣ y.val then a else 0)
      = a • ball (p := p) K (w + j) := by
  funext x
  by_cases hx : ∃ y, shellEmb (p := p) K w hw y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [push_apply_emb _ (shellEmb_injective K w hw), Pi.smul_apply, ball]
    simp only [dvd_val_shellEmb K w j hw hj]
    split_ifs <;> simp
  · rw [push_apply_not _ _ _ hx, Pi.smul_apply, ball]
    have : ¬ p ^ (w + j) ∣ x.val := fun h => hx ((mem_range_iff K w hw x).mpr
      ((pow_dvd_pow p (Nat.le_add_right w j)).trans h))
    simp [this]

/-- ラマヌジャン和の引き戻しの値: c_{p^(n+1)}(π y) = p^(n+1)[p^(n+1) ∣ y] − p^n[p^n ∣ y]。 -/
theorem ram_pull (M n : ℕ) (hM : n + 1 ≤ M) (y : ZMod (p ^ M)) :
    ram (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ (n + 1))) y)
      = (if p ^ (n + 1) ∣ y.val then ((p ^ (n + 1) : ℕ) : ℂ) else 0)
        - (if p ^ (n + 1 - 1) ∣ y.val then ((p ^ (n + 1 - 1) : ℕ) : ℂ) else 0) := by
  have : NeZero (p ^ M) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ram_eq (p := p) (n := n) (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ (n + 1))) y)]
  have e1 : (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ (n + 1))) y = 0) ↔ p ^ (n + 1) ∣ y.val := by
    rw [castHom_eq_natCast, ZMod.natCast_eq_zero_iff]
  have e2 : (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) 1)) (ZMod (p ^ (n + 1 - 1)))
      (ZMod.castHom (pow_dvd_pow p hM) (ZMod (p ^ (n + 1))) y) = 0) ↔ p ^ (n + 1 - 1) ∣ y.val := by
    rw [castHom_eq_natCast, ZMod.natCast_eq_zero_iff, castHom_eq_natCast, ZMod.val_natCast,
      Nat.dvd_mod_iff (pow_dvd_pow p (Nat.sub_le (n + 1) 1))]
  simp only [e1, e2]

theorem push_sub {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G)
    (hι : Function.Injective ι) (f g : H → ℂ) : push ι (f - g) = push ι f - push ι g := by
  funext x
  by_cases hx : ∃ y, ι y = x
  · obtain ⟨y, rfl⟩ := hx
    simp only [Pi.sub_apply, push_apply_emb _ hι]
  · simp only [Pi.sub_apply, push_apply_not _ _ _ hx, sub_zero]

/-- **定理 B（球の差の形）**: B_cv(|w,χ⟩,|w,χ̄⟩) = C · (p^c 1_{p^(w+c)} − p^(c−1) 1_{p^(w+c−1)})、
C = p^(K−w−c) χ(−1)/|S_w|、c = n+1。 -/
theorem thmB_balls (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = (((p : ℂ) ^ (K - w - (n + 1)) / (sz p K w : ℂ)) * χ (-1)) •
          (((p ^ (n + 1) : ℕ) : ℂ) • ball (p := p) K (w + (n + 1))
            - ((p ^ (n + 1 - 1) : ℕ) : ℂ) • ball (p := p) K (w + (n + 1 - 1))) := by
  have h := PAG.Part20.thmB_normalized K w n hK χ hχ
  simp only at h
  unfold ket
  rw [h]
  congr 1
  have hfun : (ram ∘ (ZMod.castHom (pow_dvd_pow p (by omega : n + 1 ≤ K - w)) (ZMod (p ^ (n + 1)))).toAddMonoidHom)
      = (fun y : ZMod (p ^ (K - w)) => if p ^ (n + 1) ∣ y.val then ((p ^ (n + 1) : ℕ) : ℂ) else 0)
        - (fun y : ZMod (p ^ (K - w)) => if p ^ (n + 1 - 1) ∣ y.val then ((p ^ (n + 1 - 1) : ℕ) : ℂ) else 0) := by
    funext y
    simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, Pi.sub_apply]
    exact ram_pull (K - w) n (by omega) y
  rw [hfun, push_sub _ (shellEmb_injective K w (by omega)), push_ball K w (n + 1) (by omega) hK,
    push_ball K w (n + 1 - 1) (by omega) (by omega)]

/-- **定理 B（閉じた形）**: B_cv(|w,χ⟩,|w,χ̄⟩) = χ(−1) · (1_{p^(w+c)Z} − (p−1)⁻¹ 1_{S_(w+c−1)})、
1_{S_(w+c−1)} = 1_{p^(w+c−1)} − 1_{p^(w+c)}。 -/
theorem thmB_closed (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = χ (-1) • (ball (p := p) K (w + (n + 1))
          - ((p : ℂ) - 1)⁻¹ • (ball (p := p) K (w + n) - ball (p := p) K (w + (n + 1)))) := by
  rw [thmB_balls K w n hK χ hχ, Nat.add_sub_cancel]
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    intro h; apply this.ne'; exact_mod_cast (sub_eq_zero.mp h)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hsz : (sz p K w : ℂ) = (p : ℂ) ^ (K - w - (n + 1)) * (p : ℂ) ^ n * ((p : ℂ) - 1) := by
    unfold sz
    rw [show K - 1 - w = (K - w - (n + 1)) + n by omega, pow_add]
    push_cast [Nat.cast_sub hp.out.one_lt.le]
    ring
  funext x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hsz]
  push_cast
  field_simp
  ring

end PAG.Part22

#print axioms PAG.Part22.val_shellEmb
#print axioms PAG.Part22.dvd_val_shellEmb
#print axioms PAG.Part22.mem_range_iff
#print axioms PAG.Part22.push_ball
#print axioms PAG.Part22.ram_pull
#print axioms PAG.Part22.push_sub
#print axioms PAG.Part22.thmB_balls
#print axioms PAG.Part22.thmB_closed
