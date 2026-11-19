# 入力 1（先に読む）：PAG265.lean の形式文の全文（docstring・コメントを除いた）と、使う定義
## A. PAG265.lean
```lean
import PAG264

namespace PAG.Part265

open PAG.Part218 PAG.Part258 PAG.Part264

noncomputable def cornerSys (a b : Lvl) (h : a ≤ b) : shellAlg a.val →ₗ[ℂ] shellAlg b.val where
  toFun := cornerHom (N := a.val) (M := b.val) h
  map_add' := map_add _
  map_smul' := map_smul _

theorem cornerSys_apply (a b : Lvl) (h : a ≤ b) (S : shellAlg a.val) :
    cornerSys a b h S = cornerHom (N := a.val) (M := b.val) h S := rfl

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

abbrev CornerLim : Type :=
  Module.DirectLimit (fun a : Lvl => shellAlg a.val) cornerSys

theorem cornerLim_of_injective (a : Lvl) :
    Function.Injective (Module.DirectLimit.of ℂ Lvl (fun a : Lvl => shellAlg a.val) cornerSys a) := by
  intro x y hxy
  obtain ⟨b, hab, hb⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact cornerHom_injective (N := a.val) (M := b.val) hab hb

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

-- Mathlib
-- class DirectedSystem (F : ι → Type*) (f : ∀ ⦃i j⦄, i ≤ j → F i → F j) : Prop where
--   map_self ⦃i⦄ (x : F i) : f le_rfl x = x
--   map_map ⦃k j i⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : F i) : f hjk (f hij x) = f (le_trans hij hjk) x
-- Module.DirectLimit G f：線形写像 f の帰納系の ℂ 加群としての直極限。Module.DirectLimit.of R ι G f i : G i →ₗ G∞ は標準の写像。
-- Module.DirectLimit.exists_eq_of_of_eq：有向な添字で of i x = of i y なら、ある j ≥ i で f i j x = f i j y。
```
