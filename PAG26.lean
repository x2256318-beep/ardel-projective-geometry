/-
  PAG 2.0 Part 22（2026-10-18）— 点モデルと 2 チャートモデルの同値性
  点集合 Pt N := Z/N ⊔ {y : Z/N // y 非単数}（南の点 [x:1] と北の内部点 [1:y]）。
  1. 点の関数 f ↦ (F_S, F_N)（F_N(y) = f[y⁻¹:1]（y 単数）、f[1:y]（y 非単数））は
     貼り合わせ条件を満たす組の部分空間への線形同型
  2. 点の反転 Wpt（[x:1] ↔ [1:x]）は対合で、同型のもとで W（南北の入れ替え）に対応する
  3. |Pt (p^K)| = p^K + p^(K−1)（K ≥ 1）
-/
import PAG25

namespace PAG.Part26

open ZMod Finset PAG.Part23

open Classical

variable {N : ℕ}

/-- P¹(Z/N) の点: 南の点 [x:1]（inl x）と北の内部点 [1:y]（inr y、y 非単数）。 -/
abbrev Pt (N : ℕ) := ZMod N ⊕ {y : ZMod N // ¬ IsUnit y}

/-- 点の関数 → 2 チャートの組。 -/
noncomputable def toP1 (f : Pt N → ℂ) : P1F N :=
  (fun x => f (Sum.inl x), fun y => if h : IsUnit y then f (Sum.inl y⁻¹) else f (Sum.inr ⟨y, h⟩))

/-- 2 チャートの組 → 点の関数。 -/
def ofP1 (F : P1F N) : Pt N → ℂ
  | Sum.inl x => F.1 x
  | Sum.inr y => F.2 y.1

theorem compat_toP1 (f : Pt N → ℂ) : Compat (toP1 f) := fun y hy => by
  simp [toP1, hy]

theorem ofP1_toP1 (f : Pt N → ℂ) : ofP1 (toP1 f) = f := by
  funext z
  rcases z with x | ⟨y, hy⟩
  · rfl
  · simp [ofP1, toP1, hy]

theorem toP1_ofP1 {F : P1F N} (hF : Compat F) : toP1 (ofP1 F) = F := by
  ext y
  · rfl
  · simp only [toP1, ofP1]
    split_ifs with hy
    · exact (hF y hy).symm
    · rfl

/-- 貼り合わせ条件を満たす組の部分空間。 -/
def compatSub (N : ℕ) : Submodule ℂ (P1F N) where
  carrier := {F | Compat F}
  add_mem' := fun {F G} hF hG y hy => by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, hF y hy, hG y hy]
  zero_mem' := fun y _ => rfl
  smul_mem' := fun a {F} hF y hy => by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, hF y hy]

/-- **点モデル ≃ 2 チャートモデル**（線形同型）。 -/
noncomputable def ptEquiv (N : ℕ) : (Pt N → ℂ) ≃ₗ[ℂ] compatSub N where
  toFun f := ⟨toP1 f, compat_toP1 f⟩
  invFun F := ofP1 F.1
  map_add' f g := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.add_apply, Submodule.coe_add, Prod.snd_add]
      split_ifs <;> rfl
  map_smul' a f := by
    apply Subtype.ext
    ext y
    · rfl
    · simp only [toP1, Pi.smul_apply, Submodule.coe_smul, Prod.smul_snd, RingHom.id_apply]
      split_ifs <;> rfl
  left_inv f := ofP1_toP1 f
  right_inv F := Subtype.ext (toP1_ofP1 F.2)

/-- 点の反転 [x:1] ↦ [1:x]。 -/
noncomputable def Wpt : Pt N → Pt N
  | Sum.inl x => if h : IsUnit x then Sum.inl x⁻¹ else Sum.inr ⟨x, h⟩
  | Sum.inr y => Sum.inl y.1

theorem Wpt_Wpt (z : Pt N) : Wpt (Wpt z) = z := by
  rcases z with x | ⟨y, hy⟩
  · by_cases h : IsUnit x
    · obtain ⟨hu, hii⟩ := inv_inv_of_unit h
      simp [Wpt, h, hu, hii]
    · simp [Wpt, h]
  · simp [Wpt, hy]

/-- Wpt は置換（対合）。 -/
noncomputable def WptEquiv (N : ℕ) : Equiv.Perm (Pt N) :=
  Function.Involutive.toPerm Wpt Wpt_Wpt

/-- **同型のもとで W は点の置換**: toP1 (f ∘ Wpt) = W (toP1 f)。 -/
theorem toP1_comp_Wpt (f : Pt N → ℂ) : toP1 (f ∘ Wpt) = W (toP1 f) := by
  ext y
  · simp only [toP1, W, Function.comp_apply, Wpt]
    split_ifs <;> rfl
  · simp only [toP1, W, Function.comp_apply]
    split_ifs with hy
    · obtain ⟨hu, hii⟩ := inv_inv_of_unit hy
      simp [Wpt, hu, hii]
    · simp [Wpt]

/-- ofP1 版: 貼り合わせ条件のもとで ofP1 (W F) = ofP1 F ∘ Wpt。 -/
theorem ofP1_W {F : P1F N} (hF : Compat F) : ofP1 (W F) = ofP1 F ∘ Wpt := by
  have h := toP1_comp_Wpt (ofP1 F)
  rw [toP1_ofP1 hF] at h
  rw [← h, ofP1_toP1]

/-- 単数の部分型と単数群の同値。 -/
noncomputable def isUnitEquiv (N : ℕ) : {x : ZMod N // IsUnit x} ≃ (ZMod N)ˣ where
  toFun x := x.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv x := by simp
  right_inv u := by ext; simp

variable {p : ℕ} [hp : Fact p.Prime]

/-- **点の数**: |Pt (p^K)| = p^K + p^(K−1)（K ≥ 1）。 -/
theorem card_Pt (K : ℕ) (hK : 1 ≤ K) : Fintype.card (Pt (p ^ K)) = p ^ K + p ^ (K - 1) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [Fintype.card_sum, ZMod.card, Fintype.card_subtype_compl, ZMod.card,
    Fintype.card_congr (isUnitEquiv (p ^ K)), ZMod.card_units_eq_totient,
    Nat.totient_prime_pow hp.out (by omega)]
  congr 1
  have h1 : p ^ K = p ^ (K - 1) * p := by rw [← pow_succ]; congr 1; omega
  have h2 : 1 ≤ p := hp.out.one_lt.le
  rw [h1, Nat.mul_sub, mul_one, Nat.sub_sub_self (Nat.le_mul_of_pos_right _ (by omega))]

end PAG.Part26

#print axioms PAG.Part26.compat_toP1
#print axioms PAG.Part26.ofP1_toP1
#print axioms PAG.Part26.toP1_ofP1
#print axioms PAG.Part26.ptEquiv
#print axioms PAG.Part26.Wpt_Wpt
#print axioms PAG.Part26.WptEquiv
#print axioms PAG.Part26.toP1_comp_Wpt
#print axioms PAG.Part26.ofP1_W
#print axioms PAG.Part26.isUnitEquiv
#print axioms PAG.Part26.card_Pt
