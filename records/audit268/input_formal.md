# 入力：形式文と定義

Lean 4 / Mathlib。定理の証明は省略し、定義は全文を写した（コメントと docstring は除いた。本体を省略した定義はそう書いた）。検査対象はエラー 0・警告 0 で通っており、`#print axioms` は標準の 3 つだけ。

## 前提 1：PAG27（名前空間 PAG.Part27）
```lean
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

def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)
```

## 前提 2：PAG267（名前空間 PAG.Part267）
```lean
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

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := …（証明は省略）

def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := …（証明は省略）

abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
```

## 前提 3：PAG258・PAG257（名前空間 PAG.Part258・PAG.Part257）
```lean
noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ) := …（証明は省略）

structure Lvl where
  
  val : ℕ
  pos : 0 < val
deriving DecidableEq

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u
```
（Lvl の順序は a ≤ b ↔ a.val ∣ b.val。各 a に NeZero a.val のインスタンスがある。）

## 前提 4：2 チャートのモデル（PAG19・PAG21・PAG23・PAG24・PAG28・PAG29。p は素数）
```lean
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)

noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ := …（本体は省略）

abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)

noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)

noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)

theorem ket0_apply (K c : ℕ) (h : 0 + c ≤ K) (f : ZMod (p ^ c) → ℂ) (x : ZMod (p ^ K)) :
    ket K 0 c h f x = (((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) *
      f (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) := …（証明は省略）

theorem chi_cast_inv {K c : ℕ} (hcK : c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) {x : ZMod (p ^ K)}
    (hx : IsUnit x) :
    χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x⁻¹)
      = χ⁻¹ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) := …（証明は省略）

noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))

theorem projFun_south (Φ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.1 x = Φ (mk ⟨(x, 1), 0, 1, by simp⟩) := …（証明は省略）

theorem projFun_north (Φ : ProjLine (p ^ K) → ℂ) (y : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.2 y = Φ (mk ⟨(1, y), 1, 0, by simp⟩) := …（証明は省略）

noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩

theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ := …（証明は省略）
```
（P1F N = (ZMod N → ℂ) × (ZMod N → ℂ)：南のチャートの関数と北のチャートの関数の組。projFunEquiv は ProjLine (p^K) の上の関数と、貼り合わせ条件を満たす組の ℂ 線形同型。）

## 検査対象：PAG268（名前空間 PAG.Part268）
```lean
namespace PAG.Part268
open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter
variable {N : ℕ}
-- 節 2（extChi・extChi_eqPt・extChi_torus）では [NeZero N] が仮定に入る（extChi_changeLevel では外した）。
-- 節 4（ketS_proj_zero_eq）では variable {p : ℕ} [hp : Fact p.Prime]。

theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := …（証明は省略）

noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
    rw [h1, h2, map_mul, map_mul]
    calc χ v.1.1 * χ⁻¹ v.1.2
        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
          rw [mul_inv_apply_unit, one_mul]
      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)

theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := …（証明は省略）

theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := …（証明は省略）

theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
    chiPt χ (Wproj q) = chiPt χ⁻¹ q := …（証明は省略）

def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
  ⟨((u : ZMod N) * v.1.1, v.1.2), by
    obtain ⟨s, t, h⟩ := v.2
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
    linear_combination h + s * v.1.1 * hu⟩

def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)

theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := …（証明は省略）

theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    chiPt χ (torus u q) = χ u * chiPt χ q := …（証明は省略）

theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := …（証明は省略）

noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)

theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := …（証明は省略）

theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := …（証明は省略）

theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    extChi χ (torus u q) = χ u * extChi χ q := …（証明は省略）

theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) := …（証明は省略）

theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    resE a (extChi χ) = PAG.Part257.charU χ := …（証明は省略）

theorem chiPt_not_compat :
    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := …（証明は省略）

theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ c)) :
    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := …（証明は省略）
```
