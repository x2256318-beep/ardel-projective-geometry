# 入力：形式文と定義

Lean 4 / Mathlib。定理の証明は省略し、定義は全文を写した（コメントと docstring は除いた）。すべてエラー 0・警告 0 で通っており、`#print axioms` は標準の 3 つ（propext, Classical.choice, Quot.sound）だけ。

## 前提の定義 1：PAG27.lean（名前空間 PAG.Part27）
```lean
namespace PAG.Part27
open ZMod PAG.Part23 PAG.Part26
open Classical
variable {N : ℕ}
variable {p : ℕ} [hp : Fact p.Prime]
variable (K : ℕ) (hK : 1 ≤ K)

def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }

def ProjLine (N : ℕ) := Quotient (projSetoid N)

def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v

theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
    mk v = mk w := …（証明は省略）

theorem swap_unimod (v : Unimod N) : ∃ s t : ZMod N, s * v.1.2 + t * v.1.1 = 1 := …（証明は省略）

def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)

theorem Wproj_Wproj (q : ProjLine N) : Wproj (Wproj q) = q := …（証明は省略）
```

## 前提の定義 2：PAG28.lean（名前空間 PAG.Part28）
```lean
def Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : ProjLine N → ℂ := Φ ∘ Wproj

theorem Wpull_Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : Wpull (Wpull Φ) = Φ := …（証明は省略）
```

## 前提の定義 3：PAG258.lean（名前空間 PAG.Part258）
```lean
namespace PAG.Part258
open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter
variable {N : ℕ} [NeZero N]

instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring

noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

abbrev Lim : Type := Module.DirectLimit Gsp pullSys

noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

theorem ofL_injective (a : Lvl) : Function.Injective (ofL a) := …（証明は省略）

noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f) := …（証明は省略）
```
（`UA1` は法 N の単数の上の関数の空間の ℂ 線形写像で、ここでは使わない内部の定義 `charU`・`phaseA1`・`ip` などに依存する。この入力の定理には `UA1`・`Uinf` は現れない。）

## 前提の定義 4：PAG262.lean（名前空間 PAG.Part262）
```lean
theorem mem_ker_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (y : ZMod M) :
    ZMod.castHom hNM (ZMod N) y = 0 ↔ ∃ c : ZMod M, y = (N : ZMod M) * c := …（証明は省略）
```

## 検査対象：PAG267.lean（名前空間 PAG.Part267）
```lean
namespace PAG.Part267
open ZMod PAG.Part27 PAG.Part258
variable {N M L : ℕ}

def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
    obtain ⟨s, t, hst⟩ := v.2
    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩

def red (h : N ∣ M) : ProjLine M → ProjLine N :=
  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
    mk_eq_mk (unitsMap h u)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))

theorem red_mk (h : N ∣ M) (v : Unimod M) : red h (mk v) = mk (redU h v) := …（証明は省略）

theorem red_self (q : ProjLine N) : red (dvd_refl N) q = q := …（証明は省略）

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := …（証明は省略）

theorem red_Wproj (h : N ∣ M) (q : ProjLine M) : red h (Wproj q) = Wproj (red h q) := …（証明は省略）

def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

def infU (N : ℕ) : Unimod N := ⟨(1, 0), ⟨1, 0, by simp⟩⟩

def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

def infPt (N : ℕ) : ProjLine N := mk (infU N)

theorem Wproj_zeroPt : Wproj (zeroPt N) = infPt N := …（証明は省略）

theorem Wproj_infPt : Wproj (infPt N) = zeroPt N := …（証明は省略）

theorem red_zeroPt (h : N ∣ M) : red h (zeroPt M) = zeroPt N := …（証明は省略）

theorem red_infPt (h : N ∣ M) : red h (infPt M) = infPt N := …（証明は省略）

theorem zeroPt_ne_infPt (hN : N ≠ 1) : zeroPt N ≠ infPt N := …（証明は省略）

theorem exists_redU [NeZero M] (h : N ∣ M) (v : Unimod N) :
    ∃ w : Unimod M, mk (redU h w) = mk v := …（証明は省略）

theorem red_surjective [NeZero M] (h : N ∣ M) : Function.Surjective (red h) := …（証明は省略）

def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem eqPt_injective : Function.Injective (eqPt (N := N)) := …（証明は省略）

theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := …（証明は省略）

theorem isUnit_of_castHom [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (c : ZMod M) (hc : IsUnit (castHom h (ZMod N) c)) : IsUnit c := …（証明は省略）

theorem exists_eqPt_of_red [NeZero M] (h : N ∣ M) (hp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (q : ProjLine M) (x : (ZMod N)ˣ) (hx : eqPt x = red h q) : ∃ y, eqPt y = q := …（証明は省略）

abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : DirectedSystem Fsp (fun a b h => (pullP a b h : Fsp a → Fsp b)) where
  map_self a f := by
    funext q
    show f (red (dvd_refl a.val) q) = f q
    rw [red_self]
  map_map c b a hab hbc f := by
    funext q
    show f (red hab (red hbc q)) = f (red (dvd_trans hab hbc) q)
    rw [red_comp]

abbrev LimP : Type := Module.DirectLimit Fsp pullP

noncomputable abbrev ofP (a : Lvl) : Fsp a →ₗ[ℂ] LimP := Module.DirectLimit.of ℂ Lvl Fsp pullP a

theorem pullP_injective (a b : Lvl) (h : a ≤ b) : Function.Injective (pullP a b h) := …（証明は省略）

theorem ofP_injective (a : Lvl) : Function.Injective (ofP a) := …（証明は省略）

noncomputable def Wfun (a : Lvl) : Fsp a →ₗ[ℂ] Fsp a where
  toFun := PAG.Part28.Wpull
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Wfun_comp_pullP (a b : Lvl) (h : a ≤ b) :
    Wfun b ∘ₗ pullP a b h = pullP a b h ∘ₗ Wfun a := …（証明は省略）

noncomputable def WL : LimP →ₗ[ℂ] LimP :=
  Module.DirectLimit.map Wfun (fun a b h => Wfun_comp_pullP a b h)

theorem WL_ofP (a : Lvl) (f : Fsp a) : WL (ofP a f) = ofP a (Wfun a f) := …（証明は省略）

theorem WL_WL (x : LimP) : WL (WL x) = x := …（証明は省略）

noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resE_comp_pullP (a b : Lvl) (h : a ≤ b) :
    resE b ∘ₗ pullP a b h = pullSys a b h ∘ₗ resE a := …（証明は省略）

noncomputable def resL : LimP →ₗ[ℂ] Lim :=
  Module.DirectLimit.map resE (fun a b h => resE_comp_pullP a b h)

theorem resL_ofP (a : Lvl) (f : Fsp a) : resL (ofP a f) = ofL a (resE a f) := …（証明は省略）

open Classical in
noncomputable def extE (a : Lvl) : Gsp a →ₗ[ℂ] Fsp a where
  toFun g q := if h : ∃ x, eqPt x = q then g h.choose else 0
  map_add' g g' := by
    funext q
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    funext q
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem extE_eqPt (a : Lvl) (g : Gsp a) (x : (ZMod a.val)ˣ) : extE a g (eqPt x) = g x := …（証明は省略）

theorem extE_off (a : Lvl) (g : Gsp a) (q : ProjLine a.val) (hq : ∀ x, eqPt x ≠ q) :
    extE a g q = 0 := …（証明は省略）

theorem resE_extE (a : Lvl) (g : Gsp a) : resE a (extE a g) = g := …（証明は省略）

theorem resL_surjective : Function.Surjective resL := …（証明は省略）

theorem extE_compat_iff (a b : Lvl) (h : a ≤ b) :
    (∀ g : Gsp a, extE b (pullSys a b h g) = pullP a b h (extE a g)) ↔
      ∀ p : ℕ, p.Prime → p ∣ b.val → p ∣ a.val := …（証明は省略）

def lv1 : Lvl := ⟨1, Nat.one_pos⟩

def lv2 : Lvl := ⟨2, Nat.two_pos⟩

theorem lv1_le_lv2 : lv1 ≤ lv2 := …（証明は省略）

theorem extE_not_compat :
    ∃ g : Gsp lv1, extE lv2 (pullSys lv1 lv2 lv1_le_lv2 g) ≠ pullP lv1 lv2 lv1_le_lv2 (extE lv1 g) := …（証明は省略）

theorem not_exists_extL :
    ¬ ∃ E : Lim →ₗ[ℂ] LimP, ∀ (a : Lvl) (g : Gsp a), E (ofL a g) = ofP a (extE a g) := …（証明は省略）
```
