# 入力 1：PAG265.lean の形式文の全文（docstring・コメントを除いた）と、使う定義
## A. PAG265.lean
```lean
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
```
## B. 使う定義・前の鎖の補題の文（証明は省略）・Mathlib の定義
```lean
-- PAG258（Part 254）
structure Lvl where
  val : ℕ
  pos : 0 < val
deriving DecidableEq
instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans
instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩
instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩
instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

-- PAG218（Part 214）
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
-- （dind N s は gcd(N, x) = s の指示関数、geps N s はその逆フーリエ変換、convL は畳み込み作用素）

-- PAG264（Part 260）。pull は引き戻し f ↦ f ∘ π（π : ℤ/M → ℤ/N）、fsum は繊維の和
noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M   -- 値は cornerOp h S（cornerHom_coe、rfl）
theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S
theorem cornerOp_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h2 (cornerOp h1 S) = cornerOp (h1.trans h2) S
theorem cornerHom_injective (h : N ∣ M) : Function.Injective (cornerHom h)
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1
theorem cornerOp_one_mul (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp h 1 * cornerOp h S = cornerOp h S
theorem cornerOp_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerOp h 1 ≠ 1

-- Mathlib
-- class DirectedSystem (F : ι → Type*) (f : ∀ ⦃i j⦄, i ≤ j → F i → F j) : Prop where
--   map_self ⦃i⦄ (x : F i) : f le_rfl x = x
--   map_map ⦃k j i⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F i) : f hjk (f hij x) = f (le_trans hij hjk) x
-- DirectLimit F f（Mathlib/Order/DirectedInverseSystem.lean）：有向な前順序 ι の上の DirectedSystem の直極限。
--   台は Σ i, F i を「ある共通の上界で像が等しい」で割った商。⟦⟨i, x⟩⟧ はその類。
-- theorem DirectLimit.eq_of_le (x : Σ i, F i) (j) (h : x.1 ≤ j) : (⟦x⟧ : DirectLimit F f) = ⟦⟨j, f x.1 j h x.2⟩⟧
-- theorem DirectLimit.exists_eq_mk (z : DirectLimit F f) : ∃ i x, z = ⟦⟨i, x⟩⟧
-- theorem DirectLimit.mk_injective (h : ∀ i j hij, Function.Injective (f i j hij)) (i) :
--     Function.Injective fun x ↦ (⟦⟨i, x⟩⟧ : DirectLimit F f)
-- Mathlib/Algebra/Colimit/DirectLimit.lean：各 F i が非単位的な環で遷移写像が NonUnitalRingHomClass なら、
--   DirectLimit F f に NonUnitalRing のインスタンス（積は共通の上界に送ってから掛ける）、ℂ のスカラー倍（Module）がある。
-- DirectLimit.NonUnitalAlgebra.of F f i : F i →ₙₐ[R] DirectLimit F f、値は x ↦ ⟦⟨i, x⟩⟧。

```
