
######## PAG2.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Kloosterman
variable {N : ℕ} [NeZero N]
open scoped Classical in
end PAG.Kloosterman

### PAG2::cas（def、121 行）
noncomputable def cas (z : ℂ) : ℂ := ((z.re + z.im : ℝ) : ℂ)

### PAG2::S_odd（theorem、156 行）
theorem S_odd (k : ℕ) {a : ZMod N} (ha : IsUnit a) :
    ∑ χ : DirichletCharacter ℂ N, χ a⁻¹ * Wpow χ (2 * k + 1)
      = N.totient / (Real.sqrt N : ℂ) ^ (2 * k + 1)
          * cas (Kl ZMod.stdAddChar (2 * k + 1) ((-1) ^ k * a))

### PAG2::cas_Kl_even（theorem、198 行）
theorem cas_Kl_even (k : ℕ) (c : ZMod N) :
    cas (Kl ZMod.stdAddChar (2 * k) c) = Kl ZMod.stdAddChar (2 * k) c

######## PAG4.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Part4
variable {N : ℕ} [NeZero N]
end PAG.Part4

### PAG4::T（def、17 行）
def T (a : ZMod N) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun f x := f (x + a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

### PAG4::F_comm_T（theorem、35 行）
theorem F_comm_T (a : ZMod N) : F ∘ₗ T a = M (-a) ∘ₗ F

### PAG4::F_comm_M（theorem、45 行）
theorem F_comm_M (b : ZMod N) : F ∘ₗ M b = T b ∘ₗ F

### PAG4::heisenberg_unique（theorem、55 行）
theorem heisenberg_unique (U : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ))
    (h1 : ∀ a, U ∘ₗ T a = M (-a) ∘ₗ U) (h2 : ∀ b, U ∘ₗ M b = T b ∘ₗ U) :
    ∃ c : ℂ, U = c • F

######## PAG7.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Part7
section Abstract
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {H0 Hi : V →ₗ[R] V} {e0 : V} {κ : R}
end Abstract
section Jacobi
variable {N : ℕ} [NeZero N]
end Jacobi
section Intertwine
variable {N : ℕ} [NeZero N]
end Intertwine
end PAG.Part7

### PAG7::W_sq（theorem、134 行）
theorem W_sq (τ τ₂ Jv : ℂ) (q : ℝ) (hq : 0 < q) (a : ℕ) (h : τ ^ 2 = Jv * τ₂) :
    (τ / (I ^ a * (Real.sqrt q : ℂ))) ^ 2 = (-1) ^ a * (Jv / (Real.sqrt q : ℂ)) * (τ₂ / (Real.sqrt q : ℂ))

######## PAG8.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Part8
open PAG.Part7
section General
variable {N : ℕ} [NeZero N]
end General
section PrimePower
variable {p n : ℕ} [hp : Fact p.Prime]
end PrimePower
end PAG.Part8

### PAG8::exists_ker_ne_one_of_primitive（theorem、95 行）
theorem exists_ker_ne_one_of_primitive (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    ∃ u : (ZMod (p ^ (n + 1)))ˣ,
      ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1 ∧ χ u ≠ 1

######## PAG9.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Part9
section Conj
variable {N : ℕ} [NeZero N]
end Conj
section Square
variable {p n : ℕ} [hp : Fact p.Prime]
end Square
end PAG.Part9

### PAG9::D（def、17 行）
def D (K c v : ℤ) : ℤ := K - c - v

### PAG9::D_comp（theorem、20 行）
theorem D_comp (K c c' v : ℤ) : D K c' (D K c v) = v + (c - c')

### PAG9::ker_pow_p（theorem、108 行）
theorem ker_pow_p (hn : 1 ≤ n) (u : (ZMod (p ^ (n + 1)))ˣ)
    (hu : ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1) :
    (u : ZMod (p ^ (n + 1))) ^ p = 1

######## PAG10.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part10
section Idem
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
end Idem
section Pow
variable {p n : ℕ} [hp : Fact p.Prime]
end Pow
end PAG.Part10

### PAG10::ind（def、17 行）
def ind {X W : Type*} [DecidableEq W] (shell : X → W) (a : W → R) (w : W) : X → R :=
  fun x => if shell x = w then a w else 0

### PAG10::Bcv_idempotent（theorem、73 行）
theorem Bcv_idempotent {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]
    (F : B ≃ₗ[K] B) (α : K) (e : B) (c : K) (he : e * e = c • e) :
    Bcv F α ((α * c)⁻¹ • F.symm e) ((α * c)⁻¹ • F.symm e) = (α * c)⁻¹ • F.symm e

### PAG10::pow_isPrimitive_of_coprime（theorem、103 行）
theorem pow_isPrimitive_of_coprime (hn : 1 ≤ n) {m : ℕ} (hcop : Nat.Coprime m p)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) : (χ ^ m).IsPrimitive

######## PAG11.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part11
open PAG.Part10
section Unit
variable {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]
end Unit
section Exact
variable {p n : ℕ} [hp : Fact p.Prime]
end Exact
end PAG.Part11

### PAG11::Bcv_idempotent_orthogonal（theorem、25 行）
theorem Bcv_idempotent_orthogonal {W : Type*} [DecidableEq W] (F : B ≃ₗ[K] B) (α : K)
    (e : W → B) (c : W → K) (he : ∀ w₀ w₁, e w₀ * e w₁ = if w₀ = w₁ then c w₀ • e w₀ else 0)
    {w₀ w₁ : W} (h : w₀ ≠ w₁) :
    Bcv F α ((α * c w₀)⁻¹ • F.symm (e w₀)) ((α * c w₁)⁻¹ • F.symm (e w₁)) = 0

### PAG11::Bcv_unit（theorem、34 行）
theorem Bcv_unit (F : B ≃ₗ[K] B) {α : K} (hα : α ≠ 0) (f : B) :
    Bcv F α (α⁻¹ • F.symm 1) f = f

### PAG11::sum_idempotent_eq_unit（theorem、41 行）
theorem sum_idempotent_eq_unit {X W : Type*} [Fintype W] [DecidableEq W] (shell : X → W)
    (F : (X → K) ≃ₗ[K] (X → K)) (α : K) :
    ∑ w : W, (α * 1)⁻¹ • F.symm (ind shell (fun _ => (1 : K)) w) = α⁻¹ • F.symm 1

######## PAG14.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part14
open PAG.Part9 PAG.Part13 Finset
section Tame
variable {p n : ℕ} [hp : Fact p.Prime]
end Tame
section Synthesis
variable {p n : ℕ} [hp : Fact p.Prime]
end Synthesis
section Ball
variable {R : Type*} [CommRing R]
end Ball
section Phase
variable {M : ℕ} [NeZero M]
end Phase
end PAG.Part14

### PAG14::epsBall（def、117 行）
def epsBall (P : ℕ → R) (K w : ℕ) : R := if w < K then P w - P (w + 1) else P K

### PAG14::lift_invariance（theorem、192 行）
theorem lift_invariance (A : (ZMod M)ˣ) (r : ZMod M) :
    ZMod.stdAddChar (-(A : ZMod M) * (r * ((A⁻¹ : (ZMod M)ˣ) : ZMod M))) * ZMod.stdAddChar r = 1

######## PAG15.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part15
open Finset PAG.Part14
section Subgroup
variable {G : Type*} [AddCommGroup G] [Fintype G] {K : Type*} [Field K]
open Classical in
open Classical in
end Subgroup
section Shell
end Shell
section ThmA
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {p n : ℕ} [hp : Fact p.Prime]
end ThmA
end PAG.Part15

### PAG15::cardH_pos（theorem、51 行）
theorem cardH_pos (H : AddSubgroup G) : 0 < cardH H

### PAG15::ballAvg（def、76 行）
noncomputable def ballAvg (H : AddSubgroup G) : G → K := ((cardH H : K))⁻¹ • indH H

### PAG15::ball_avg_absorb（theorem、79 行）
theorem ball_avg_absorb [CharZero K] {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) :
    conv (ballAvg (K := K) H₁) (ballAvg H₂) = ballAvg H₂

### PAG15::ball_avg_absorb'（theorem、88 行）
theorem ball_avg_absorb' [CharZero K] {H₁ H₂ : AddSubgroup G} (h : H₁ ≤ H₂) :
    conv (ballAvg (K := K) H₂) (ballAvg H₁) = ballAvg H₂

### PAG15::radial_column_unitary（theorem、201 行）
theorem radial_column_unitary (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    (1 : ℝ) / p + ∑ k ∈ range L, ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ (k + 2) + ((p : ℝ) - 1) / (p : ℝ) ^ (L + 1) = 1

######## PAG17.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part17
open Finset
section Glue
variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
end Glue
section PushPull
variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
end PushPull
section Support
open ZMod
variable {M M' : ℕ} [NeZero M']
end Support
section GeneralShell
variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {p n : ℕ} [hp : Fact p.Prime]
end GeneralShell
end PAG.Part17

### PAG17::glue_identity（theorem、29 行）
theorem glue_identity (p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (s n u : M) :
    q⁻¹ • (s + u) - q⁻¹ • (n + u) = p⁻¹ • ((q / p)⁻¹ • s - (q / p)⁻¹ • n)

### PAG17::equator_from_south（theorem、36 行）
theorem equator_from_south (p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (s u : M) :
    q • (q⁻¹ • (s + u)) - (q / p) • ((q / p)⁻¹ • s) = u

### PAG17::AS（def、43 行）
def AS {X : Type*} (Nn : Set X) : Submodule K (X → K) where
  carrier := {f | ∀ x ∈ Nn, f x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

######## PAG25.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part25
open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part24
variable {p : ℕ} [hp : Fact p.Prime]
section Jacobi
variable {n : ℕ}
end Jacobi
section ThmB
end ThmB
section Residue
open Classical in
end Residue
end PAG.Part25

### PAG25::Eq1（def、128 行）
open Classical in
noncomputable def Eq1 (N : ℕ) : P1F N := (fun x => if IsUnit x then 1 else 0, fun y => if IsUnit y then 1 else 0)

######## PAG30.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part30
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part25 PAG.Part28 PAG.Part29
section Tilde
variable {p : ℕ} [hp : Fact p.Prime]
end Tilde
section Two
variable {c : ℕ}
end Two
end PAG.Part30

### PAG30::tilde（def、22 行）
noncomputable def tilde {N : ℕ} (f : ZMod N → ℂ) : ZMod N → ℂ := fun x => starRingEnd ℂ (f (-x))

### PAG30::fourLe（theorem、125 行）
theorem fourLe (hc : 1 ≤ c) : 1 < 2 ^ c

######## PAG31.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part31
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part25 PAG.Part28
section Fourier
variable {p : ℕ} [hp : Fact p.Prime]
end Fourier
section TildeW
variable {p : ℕ} [hp : Fact p.Prime]
end TildeW
section TwoDescent
variable {d : ℕ}
end TwoDescent
end PAG.Part31

### PAG31::lam_pos（theorem、38 行）
theorem lam_pos (K u : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K u : ℝ)

### PAG31::tildeP1（def、151 行）
noncomputable def tildeP1 {N : ℕ} (F : P1F N) : P1F N := (tilde F.1, tilde F.2)

######## PAG37.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part37
open ZMod Finset
section Units
variable {d : ℕ}
end Units
section Cond
variable {d : ℕ}
end Cond
end PAG.Part37

### PAG37::five（def、29 行）
def five (m : ℕ) : (ZMod (2 ^ m))ˣ := ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right m (by norm_num))

### PAG37::unitsMap_five（theorem、34 行）
theorem unitsMap_five {m c : ℕ} (h : m ≤ c) :
    ZMod.unitsMap (pow_dvd_pow 2 h) (five c) = five m

### PAG37::five_pow_val（theorem、43 行）
theorem five_pow_val (m k : ℕ) :
    ∃ u : ℕ, Odd u ∧ (((five m) ^ (2 ^ k) : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)) = ((1 + 2 ^ (k + 2) * u : ℕ) : ZMod _)

### PAG37::orderOf_five_ge3（theorem、50 行）
theorem orderOf_five_ge3 {m : ℕ} (hm : 3 ≤ m) : orderOf (five m) = 2 ^ (m - 2)

### PAG37::five_two（theorem、69 行）
theorem five_two : five 2 = 1

### PAG37::orderOf_five（theorem、73 行）
theorem orderOf_five {m : ℕ} (hm : 2 ≤ m) : orderOf (five m) = 2 ^ (m - 2)

### PAG37::unitsMap_neg_one（theorem、78 行）
theorem unitsMap_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.unitsMap h (-1) = -1

### PAG37::toFour_five（theorem、91 行）
theorem toFour_five : toFour d (five (d + 3)) = 1

### PAG37::neg_one_ne_one_four（theorem、94 行）
theorem neg_one_ne_one_four : (-1 : (ZMod (2 ^ 2))ˣ) ≠ 1

### PAG37::pm5（def、100 行）
def pm5 (d : ℕ) (x : Fin 2 × Fin (2 ^ (d + 1))) : (ZMod (2 ^ (d + 3)))ˣ :=
  (-1) ^ (x.1 : ℕ) * (five (d + 3)) ^ (x.2 : ℕ)

### PAG37::pm5_injective（theorem、103 行）
theorem pm5_injective : Function.Injective (pm5 d)

### PAG37::pm5_bijective（theorem、120 行）
theorem pm5_bijective : Function.Bijective (pm5 d)

### PAG37::units_pm5（theorem、127 行）
theorem units_pm5 (u : (ZMod (2 ^ (d + 3)))ˣ) : ∃ a b : ℕ, u = (-1) ^ a * (five (d + 3)) ^ b

### PAG37::ker_five（theorem、132 行）
theorem ker_five {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ d + 3) (u : (ZMod (2 ^ (d + 3)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow 2 hm)).ker) :
    ∃ t : ℕ, u = (five (d + 3)) ^ (2 ^ (m - 2) * t)

### PAG37::prim_iff_five（theorem、196 行）
theorem prim_iff_five (ψ : DirichletCharacter ℂ (2 ^ (d + 3))) : ψ.IsPrimitive ↔ ψ 5 ^ (2 ^ d) ≠ 1

######## PAG39.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part39
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part31 PAG.Part38
section Planch
variable {N : ℕ} [NeZero N]
end Planch
section Op
variable {p : ℕ} [hp : Fact p.Prime]
end Op
end PAG.Part39

### PAG39::plancherel（theorem、26 行）
theorem plancherel (f g : ZMod N → ℂ) :
    ∑ k, starRingEnd ℂ (𝓕 f k) * 𝓕 g k = (N : ℂ) * ∑ j, starRingEnd ℂ (f j) * g j

######## PAG44.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part44
open ZMod Finset PAG.Part37 Complex
variable {d : ℕ}
end PAG.Part44

### PAG44::orderOf_five'（theorem、22 行）
theorem orderOf_five' : orderOf (five (d + 3)) = 2 ^ (d + 1)

### PAG44::pm5_eq_iff（theorem、43 行）
theorem pm5_eq_iff (a b a' b' : ℕ) :
    (-1 : (ZMod (2 ^ (d + 3)))ˣ) ^ a * (five (d + 3)) ^ b = (-1) ^ a' * (five (d + 3)) ^ b' ↔
      a % 2 = a' % 2 ∧ b % 2 ^ (d + 1) = b' % 2 ^ (d + 1)

### PAG44::rep（def、73 行）
noncomputable def rep (d : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : Fin 2 × Fin (2 ^ (d + 1)) :=
  (Equiv.ofBijective (pm5 d) pm5_bijective).symm u

### PAG44::rep_spec（theorem、76 行）
theorem rep_spec (u : (ZMod (2 ^ (d + 3)))ˣ) :
    u = (-1) ^ ((rep d u).1 : ℕ) * (five (d + 3)) ^ ((rep d u).2 : ℕ)

### PAG44::val（def、83 行）
noncomputable def val (d s j : ℕ) (u : (ZMod (2 ^ (d + 3)))ˣ) : ℂ :=
  (-1) ^ (s * ((rep d u).1 : ℕ)) * zeta d ^ (j * ((rep d u).2 : ℕ))

### PAG44::unitHom（def、103 行）
noncomputable def unitHom (d s j : ℕ) : (ZMod (2 ^ (d + 3)))ˣ →* ℂˣ where
  toFun u := Units.mk0 (val d s j u) (val_ne_zero s j u)
  map_one' := by
    ext
    have := val_formula (d := d) s j 0 0
    simp only [pow_zero, mul_one, mul_zero] at this
    simp [this]
  map_mul' u u' := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [rep_spec u, rep_spec u']
    rw [show (-1 : (ZMod (2 ^ (d + 3)))ˣ) ^ ((rep d u).1 : ℕ) * five (d + 3) ^ ((rep d u).2 : ℕ) *
        ((-1) ^ ((rep d u').1 : ℕ) * five (d + 3) ^ ((rep d u').2 : ℕ))
        = (-1) ^ (((rep d u).1 : ℕ) + ((rep d u').1 : ℕ)) * five (d + 3) ^ (((rep d u).2 : ℕ) + ((rep d u').2 : ℕ)) by
      rw [pow_add (-1 : (ZMod (2 ^ (d + 3)))ˣ), pow_add (five (d + 3))]; exact mul_mul_mul_comm _ _ _ _]
    rw [val_formula, val_formula, val_formula, mul_add, mul_add, pow_add (-1 : ℂ), pow_add (zeta d)]
    ring

### PAG44::chiSJ（def、122 行）
noncomputable def chiSJ (d s j : ℕ) : DirichletCharacter ℂ (2 ^ (d + 3)) := MulChar.ofUnitHom (unitHom d s j)

######## PAG45.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part45
open ZMod Finset PAG.Part37 PAG.Part44 Complex
variable {d : ℕ}
end PAG.Part45

### PAG45::five_pow_M（theorem、18 行）
theorem five_pow_M : (5 : ZMod (2 ^ (d + 3))) ^ (2 ^ (d + 1)) = 1

### PAG45::char_ext（theorem、24 行）
theorem char_ext (χ χ' : DirichletCharacter ℂ (2 ^ (d + 3)))
    (h5 : χ 5 = χ' 5) (h1 : χ (-1) = χ' (-1)) : χ = χ'

######## PAG46.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part46
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part42
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part46

### PAG46::lam_pos（theorem、17 行）
theorem lam_pos (K u : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K u : ℝ)

######## PAG51.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part51
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part51

### PAG51::prim_not_changeLevel（theorem、103 行）
theorem prim_not_changeLevel {c c' : ℕ} (hlt : c' < c) (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive)
    (ψ' : DirichletCharacter ℂ (p ^ c')) (hdvd : p ^ c' ∣ p ^ c) :
    ψ ≠ DirichletCharacter.changeLevel hdvd ψ'

### PAG51::caseII_target_unique（theorem、153 行）
theorem caseII_target_unique (K : ℕ) (w c w' c' : ℕ) (hc : 1 ≤ c) (hc' : 1 ≤ c') (h : w + c ≤ K) (h' : w' + c' ≤ K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive) (ψ' : DirichletCharacter ℂ (p ^ c'))
    (hψ' : ψ'.IsPrimitive) (C C' : ℂ) (lam : ℝ) (hlam : 0 < lam) (hCl : Complex.normSq C = lam)
    (F : ZMod (p ^ K) → ℂ) (hF : F = C • ket K w c h ψ) (hF' : F = C' • ket K w' c' h' ψ') :
    w = w' ∧ c = c' ∧ C = C'

######## PAG52.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part52
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part31 PAG.Part48 PAG.Part49
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
end PAG.Part52

### PAG52::ip（def、18 行）
noncomputable def ip {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

######## PAG54.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part54
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part47
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part54

### PAG54::family（def、22 行）
def family (K : ℕ) : Set (ZMod (p ^ K) → ℂ) :=
  {f | (∃ w c, ∃ h : w + c ≤ K, 1 ≤ c ∧ ∃ ψ : DirichletCharacter ℂ (p ^ c), ψ.IsPrimitive ∧ f = ket K w c h ψ) ∨
    (∃ w, ∃ hw : w < K, f = shellInd K w hw) ∨ f = Pi.single 0 1}

######## PAG55.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part55
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part52 PAG.Part54
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part55

### PAG55::familyBasis（def、237 行）
noncomputable def familyBasis (K : ℕ) : Module.Basis (family (p := p) K) ℂ (ZMod (p ^ K) → ℂ) :=
  Module.Basis.mk (family_linearIndependent K) (by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, span_family_eq_top])

######## PAG58.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part58
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part58

### PAG58::Good（def、171 行）
def Good (K : ℕ) (F : ZMod (p ^ K) → ℂ) : Prop :=
  F = 0 ∨ (∃ b ∈ family (p := p) K, ∃ C : ℂ, C ≠ 0 ∧ F = C • b) ∨ F ∈ IndSpan (p := p) K

######## PAG61.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part61
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part32 Complex
variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ)
variable (hp2 : p ≠ 2)
end PAG.Part61

### PAG61::phi（abbrev、21 行）
abbrev phi : ℕ := Fintype.card (ZMod (p ^ (c + 1)))ˣ

######## PAG68.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part68
open ZMod Finset PAG.Part32 PAG.Part61 PAG.Part62 PAG.Part67
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part68

### PAG68::Faithful（def、19 行）
def Faithful {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∀ u : (ZMod N)ˣ, χ u = 1 → u = 1

######## PAG89.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part89
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part41
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part89

### PAG89::lam_nonneg（theorem、47 行）
omit hp in
theorem lam_nonneg (K a : ℕ) : 0 ≤ (p : ℝ) ^ K / (sz p K a : ℝ)

######## PAG93.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part93
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part56 PAG.Part57 PAG.Part58 PAG.Part59
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part93

### PAG93::Bset（def、19 行）
noncomputable def Bset (K a : ℕ) : Set (ZMod (p ^ K) → ℂ) := {g | KetDual (p := p) K a g} ∪ {eps (p := p) K a}

######## PAG95.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part95
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part59
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part95

### PAG95::Va（abbrev、52 行）
noncomputable abbrev Va (K a : ℕ) : Submodule ℂ (ZMod (p ^ K) → ℂ) := Submodule.span ℂ (Bset (p := p) K a)

######## PAG98.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part98
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part51 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part59 PAG.Part89 PAG.Part90
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part98

### PAG98::Equivariant（def、27 行）
def Equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), f (u * x) = α u * f x

######## PAG112.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part112
open ZMod Finset PAG.Part15 PAG.Part108 PAG.Part109 PAG.Part110 PAG.Part111
section Generic
variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
end Generic
section Primes
open PAG.Part21 PAG.Part59
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K : Fin n → ℕ)
end Primes
end PAG.Part112

### PAG112::inj_of_isoOn（theorem、42 行）
theorem inj_of_isoOn (e k : G → ℂ) (l : ℝ) (hl : 0 < l) (hk : IsoOn e k l) (f : G → ℂ)
    (hf : conv e f = f) (h0 : conv k f = 0) : f = 0

######## PAG116.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part116
open ZMod Finset Polynomial PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part116

### PAG116::lam_pos（theorem、60 行）
theorem lam_pos (K a : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K a : ℝ)

######## PAG118.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part118
open ZMod Finset
section CharSum
variable {G : Type*} [AddCommGroup G] [Fintype G]
end CharSum
variable {p : ℕ} [hp : Fact p.Prime]
section Gauss
variable (c m : ℕ) (hc : c = 2 * m)
variable {c m}
end Gauss
open PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 in
end PAG.Part118

### PAG118::sum_mult_eq_zero（theorem、21 行）
theorem sum_mult_eq_zero (g : G → ℂ) (hg : ∀ y z, g (y + z) = g y * g z) (h : ¬ ∀ y, g y = 1) :
    ∑ y, g y = 0

######## PAG120.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part120
open ZMod Finset PAG.Part118 PAG.Part119
variable {p : ℕ} [hp : Fact p.Prime]
section Avg
variable {c : ℕ}
end Avg
section Odd
variable {c m : ℕ} (hc : c = 2 * m + 1) (hm : 1 ≤ m)
end Odd
open PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 in
end PAG.Part120

### PAG120::quad_root_two（theorem、26 行）
theorem quad_root_two (F : ZMod 2 → ℂ) (a : ZMod 2) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt 2 : ℝ) : ℂ)) ^ (4 * 2) = 1

######## PAG133.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part133
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Wild
variable (c : ℕ) (hc : 1 ≤ c)
end Wild
section Ket
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)
end Ket
end PAG.Part133

### PAG133::exists_ker_ne（theorem、77 行）
theorem exists_ker_ne (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    ∃ v : (ZMod (p ^ (c + 1)))ˣ, ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ c)) v = 1 ∧ χ v ≠ 1

######## PAG135.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part135
open ZMod Finset PAG.Part133
section Gen
variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hc : 1 ≤ c)
end Gen
section Single
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117
variable {p : ℕ} [hp : Fact p.Prime]
end Single
end PAG.Part135

### PAG135::unit_pow_two（theorem、96 行）
theorem unit_pow_two (c : ℕ) (hc : 2 ≤ c) (a : (ZMod (2 ^ (c + 1)))ˣ) :
    (a : ZMod (2 ^ (c + 1))) ^ (2 ^ (c - 1)) = 1

######## PAG146.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part146
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part146

### PAG146::twist_digit_uniform（theorem、39 行）
theorem twist_digit_uniform (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive)
    (hpc : p ∣ p ^ c) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧ ∀ (N : ℕ) (x y : ℂ),
      x ∈ Set.range (fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N) →
      y ∈ Set.range (fun ψ₀ : DirichletCharacter ℂ p =>
        (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N) →
      #{ψ₀ : DirichletCharacter ℂ p |
          (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = x}
        = #{ψ₀ : DirichletCharacter ℂ p |
          (gaussSum (χ * DirichletCharacter.changeLevel hpc ψ₀) stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ N = y}

######## PAG152.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part152
open ZMod Finset Complex Real
end PAG.Part152

### PAG152::gauss_mod4（theorem、25 行）
theorem gauss_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar = 2 * I

### PAG152::e8_one（theorem、49 行）
theorem e8_one : stdAddChar (1 : ZMod 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I)

### PAG152::five_mod8（theorem、65 行）
theorem five_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) : χ 5 = -1

######## PAG153.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part153
open ZMod Finset
section Ket
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117 PAG.Part125 PAG.Part126 PAG.Part132 PAG.Part136
variable {n : ℕ} (q : Fin n → ℕ) [hq : ∀ i, Fact (q i).Prime] (K w c : Fin n → ℕ)
end Ket
end PAG.Part153

### PAG153::orderOf_of_sq_neg_one（theorem、15 行）
theorem orderOf_of_sq_neg_one (z : ℂ) (h : z ^ 2 = -1) : orderOf z = 4

######## PAG171.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part171
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part171

### PAG171::not_root_of_trace（theorem、17 行）
theorem not_root_of_trace (x : ℂ) (r : ℚ) (hr : x + x⁻¹ = (r : ℂ)) (hnot : ∀ n : ℤ, r ≠ n) :
    ∀ N : ℕ, 0 < N → x ^ N ≠ 1

######## PAG172.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part172
open Complex Finset Polynomial PAG.Part171
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
end PAG.Part172

### PAG172::quartic_eq_one（theorem、16 行）
theorem quartic_eq_one (u : ℂ) (hu : u ^ 4 = 1) : u = 1 ∨ u = -1 ∨ u = I ∨ u = -I

### PAG172::InZi（def、28 行）
def InZi (y : ℂ) : Prop := ∃ a b : ℤ, y = a + b * I

######## PAG174.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part174
open Complex Finset PAG.Part171
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part174

### PAG174::Tpoly（def、30 行）
def Tpoly (a b c d : ℤ) : ℤ :=
  2*a^2*c^2 - 2*a^2*c*d - a^2*d^2 - 2*a*b*c^2 - 4*a*b*c*d + 4*a*b*d^2 - b^2*c^2 + 4*b^2*c*d - b^2*d^2

######## PAG175.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part175
open Complex Finset PAG.Part171 PAG.Part172
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part175

### PAG175::T4（def、43 行）
def T4 (a b c d : ℤ) : ℤ := 2*a^2*c^2 - 2*a^2*d^2 - 8*a*b*c*d - 2*b^2*c^2 + 2*b^2*d^2

### PAG175::trace4_identity（theorem、46 行）
theorem trace4_identity (a b c d : ℤ) :
    ((a : ℂ) + b * I) ^ 2 * ((c : ℂ) + d * I) ^ 2 + ((a : ℂ) - b * I) ^ 2 * ((c : ℂ) - d * I) ^ 2
      = (T4 a b c d : ℂ)

######## PAG176.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part176
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part174 PAG.Part175
open ZMod (stdAddChar)
variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
end PAG.Part176

### PAG176::InQω（def、19 行）
def InQω (y : ℂ) : Prop := ∃ A B : ℚ, y = A + B * ω

### PAG176::InQi（def、22 行）
def InQi (y : ℂ) : Prop := ∃ A B : ℚ, y = A + B * I

### PAG176::InQi_mul（theorem、28 行）
theorem InQi_mul {y y' : ℂ} (h : InQi y) (h' : InQi y') : InQi (y * y')

### PAG176::InQi_pow（theorem、36 行）
theorem InQi_pow {y : ℂ} (h : InQi y) : ∀ n : ℕ, InQi (y ^ n)
  | 0 => ⟨1, 0, by simp⟩
  | n + 1 => by rw [pow_succ]; exact InQi_mul (InQi_pow h n) h

######## PAG177.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part177
open Complex Finset PAG.Part171 PAG.Part174
open ZMod (stdAddChar)
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]
end PAG.Part177

### PAG177::Tlin（def、15 行）
def Tlin (a b C D : ℤ) : ℤ := 2*C*a^2 - 2*C*a*b - C*b^2 - D*a^2 - 2*D*a*b + 2*D*b^2

######## PAG178.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part178
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part175
open ZMod (stdAddChar)
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]
end PAG.Part178

### PAG178::Tlin4（def、15 行）
def Tlin4 (a b C D : ℤ) : ℤ := 2 * ((a ^ 2 - b ^ 2) * C - 2 * a * b * D)

### PAG178::trace_lin4（theorem、17 行）
theorem trace_lin4 (a b C D : ℤ) :
    ((a : ℂ) + b * I) ^ 2 * ((C : ℂ) + D * I) + ((a : ℂ) - b * I) ^ 2 * ((C : ℂ) - D * I) = (Tlin4 a b C D : ℂ)

######## PAG179.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part179
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part174 PAG.Part175 PAG.Part176 PAG.Part177 PAG.Part178
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part179

### PAG179::InQi_one（theorem、16 行）
theorem InQi_one : InQi 1

### PAG179::InQi_prod（theorem、26 行）
theorem InQi_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, InQi (f i)) : InQi (∏ i ∈ s, f i)

### PAG179::InQi_conj（theorem、38 行）
theorem InQi_conj {y : ℂ} (h : InQi y) : InQi ((starRingEnd ℂ) y)

### PAG179::z4_facts（theorem、67 行）
theorem z4_facts (ψ : DirichletCharacter ℂ p) (h4 : orderOf ψ = 4) :
    InQi ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4) ∧
      (starRingEnd ℂ) ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4)
        = ((gaussSum ψ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ 4)⁻¹

######## PAG181.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part181
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part175 PAG.Part176 PAG.Part178 PAG.Part179 PAG.Part180
open ZMod (stdAddChar)
variable {P : ℕ} (μ : ZMod P)
variable {μ}
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part181

### PAG181::InQi_zpow（theorem、258 行）
theorem InQi_zpow {u : ℂ} (hu : InQi u) (hu' : (starRingEnd ℂ) u = u⁻¹) (k : ℤ) :
    InQi (u ^ k) ∧ (starRingEnd ℂ) (u ^ k) = (u ^ k)⁻¹

######## PAG183.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part183
open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part180 PAG.Part181 PAG.Part182
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part183

### PAG183::root_mul_iff（theorem、16 行）
theorem root_mul_iff (C Y : ℂ) (M : ℕ) (hM : 0 < M) (hC : C ^ M = 1) :
    (∃ N : ℕ, 0 < N ∧ (C * Y) ^ N = 1) ↔ (∃ N : ℕ, 0 < N ∧ Y ^ N = 1)

######## PAG185.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part185
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part185

### PAG185::powChar_pow（theorem、71 行）
theorem powChar_pow (k m : ℕ) : powChar (p := p) k ^ m = powChar (k * m)

### PAG185::sqrt_ne_zero（theorem、264 行）
theorem sqrt_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0

### PAG185::aux_ineq（theorem、346 行）
theorem aux_ineq (k n i : ℕ) (hk : 0 < k) (hi1 : 1 ≤ i) (hin : i + 2 ≤ n) :
    0 < k * (n - 1) ∧ 0 < k * (n - i) ∧ k * (n - 1) < k * n ∧ k * (n - i) < k * n ∧
      k * n ≤ k * (n - 1) + k * (n - i)

######## PAG187.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part187
open Complex Finset
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part187

### PAG187::root_pow_iff（theorem、22 行）
theorem root_pow_iff (x : ℂ) (k : ℕ) (hk : 0 < k) :
    (∃ N : ℕ, 0 < N ∧ (x ^ k) ^ N = 1) ↔ (∃ N : ℕ, 0 < N ∧ x ^ N = 1)

### PAG187::units_eight_sq（theorem、51 行）
omit hp in
theorem units_eight_sq (u : (ZMod (2 ^ 3))ˣ) : u ^ 2 = 1

######## PAG189.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part189
open Complex Finset Polynomial
open PAG.Part185 (powChar)
variable {p : ℕ} [hp : Fact p.Prime]
section Embedding
variable {χ : MulChar (ZMod p) ℂ} {c : ℕ} {A : Subalgebra ℤ ℂ} {χA : MulChar (ZMod p) A}
variable (hval : χA.ringHomComp A.val.toRingHom = χ)
end Embedding
end PAG.Part189

### PAG189::toZMod_eq_zero_iff（theorem、31 行）
theorem toZMod_eq_zero_iff (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1

######## PAG190.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part190
open Complex Finset Polynomial Matrix
open PAG.Part185 (powChar)
variable {p : ℕ} [hp : Fact p.Prime]
section AB
variable {A : Subalgebra ℤ ℂ}
variable {χ : MulChar (ZMod p) ℂ} {χA : MulChar (ZMod p) A}
end AB
section Suff
variable {A : Subalgebra ℤ ℂ} {χ : MulChar (ZMod p) ℂ} {χA : MulChar (ZMod p) A}
end Suff
end PAG.Part190

### PAG190::coord_bound（theorem、112 行）
theorem coord_bound {d : ℕ} (v : Fin d → ℂ) (hv : (vandermonde v).det ≠ 0) :
    ∃ B : ℝ, ∀ w : Fin d → ℂ, (∀ k, ‖(vandermonde v *ᵥ w) k‖ ≤ 1) → ∀ i, ‖w i‖ ≤ B

### PAG190::norm_z（theorem、347 行）
theorem norm_z (φ : MulChar (ZMod p) ℂ) (hφ : φ ≠ 1) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum φ ψ / ((Real.sqrt p : ℝ) : ℂ)‖ = 1

### PAG190::norm_prod_z（theorem、437 行）
theorem norm_prod_z (χ' : MulChar (ZMod p) ℂ) (n : ℕ) (hord : orderOf χ' = n) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (a : ℕ → ℤ) :
    ‖∏ j ∈ Ico 1 n, ((gaussSum (χ' ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j‖ = 1

######## PAG195.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part195
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194
end PAG.Part195

### PAG195::factorsThrough_sq_iff_units（theorem、178 行）
theorem factorsThrough_sq_iff_units {N d : ℕ} [NeZero N] (hd : d ∣ N) (χ : DirichletCharacter ℂ N) :
    (χ ^ 2).FactorsThrough d ↔ ∀ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 → χ u ^ 2 = 1

### PAG195::general_root_iff_units（theorem、196 行）
theorem general_root_iff_units (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      ∀ q : ℕ, q.Prime → ∀ hq : q ∣ N, ¬ q ^ 2 ∣ N →
        ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hq) u = 1 → χ u ^ 2 = 1

######## PAG196.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part196
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194
end PAG.Part196

### PAG196::pcomp_aux（theorem、202 行）
theorem pcomp_aux {q N : ℕ} (hq : q.Prime) (h : q ∣ N ∧ ¬ q ^ 2 ∣ N) :
    0 < N / q ∧ q.Coprime (N / q)

######## PAG198.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part198
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196
end PAG.Part198

### PAG198::gs_combine（theorem、38 行）
theorem gs_combine (s₁ s₂ : ℂ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) :
    (if s₁ * s₂ = 1 then (1 : ℂ) else I) =
      (if s₁ = 1 then (1 : ℂ) else s₂) * (if s₁ = 1 then (1 : ℂ) else I) * (if s₂ = 1 then (1 : ℂ) else I)

### PAG198::real_val_gen（theorem、52 行）
theorem real_val_gen {p : ℕ} [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, g ^ j = x)
    (φ : DirichletCharacter ℂ p) (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) : φ g = -1

### PAG198::gaussSum_real（theorem、515 行）
theorem gaussSum_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    (χ (-1) = 1 → gaussSum χ stdAddChar = ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ∧
    (χ (-1) = -1 → gaussSum χ stdAddChar = I * ((Real.sqrt (N : ℝ) : ℝ) : ℂ))

######## PAG199.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part199
open Complex Finset
open ZMod (stdAddChar)
section CRT
variable {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ : ℕ} [NeZero N₁] [NeZero N₂]
end CRT
section Mul
variable {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ : ℕ} [NeZero N₁] [NeZero N₂]
end Mul
end PAG.Part199

### PAG199::pos_of_mul（theorem、38 行）
theorem pos_of_mul {u M N : ℕ} [NeZero N] (h : u * M = N) : 0 < u

### PAG199::changeLevel_natCast（theorem、222 行）
theorem changeLevel_natCast {d c : ℕ} (hd : d ∣ c) (Ψ : DirichletCharacter ℂ d) (n : ℕ)
    (hn : n.Coprime c) : Ψ.changeLevel hd (n : ZMod c) = Ψ (n : ZMod d)

######## PAG203.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part203
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part203

### PAG203::inv_mul_inv_apply（theorem、128 行）
theorem inv_mul_inv_apply {c d : ℕ} (hdc : d ∣ c) (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) (hprod : A * B = Ψ.changeLevel hdc) (x : ZMod c) :
    A⁻¹ x * B⁻¹ x = (Ψ⁻¹).changeLevel hdc x

######## PAG207.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part207
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part207

### PAG207::Radial（def、21 行）
def Radial {N : ℕ} (f : ZMod N → ℂ) : Prop := ∀ (a : (ZMod N)ˣ) (x : ZMod N), f ((a : ZMod N) * x) = f x



### PAG207::gcd_val_unit_mul（theorem、26 行）
theorem gcd_val_unit_mul (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (x : ZMod N) :
    Nat.gcd N ((a : ZMod N) * x).val = Nat.gcd N x.val

### PAG207::exists_unit_mul_gcd（theorem、32 行）
theorem exists_unit_mul_gcd (N : ℕ) [NeZero N] (ξ : ZMod N) :
    ∃ a : (ZMod N)ˣ, (a : ZMod N) * ((Nat.gcd N ξ.val : ℕ) : ZMod N) = ξ

######## PAG208.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part208
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part208

### PAG208::inner_smul_smul（theorem、370 行）
theorem inner_smul_smul {N : ℕ} [NeZero N] (a b : ℂ) (u v : ZMod N → ℂ) :
    ∑ j, starRingEnd ℂ ((a • u) j) * (b • v) j = starRingEnd ℂ a * b * ∑ j, starRingEnd ℂ (u j) * v j

### PAG208::changeLevel_inv_injective（theorem、396 行）
theorem changeLevel_inv_injective (n c : ℕ) [NeZero n] (hcn : c ∣ n) (χ₁ χ₂ : DirichletCharacter ℂ c)
    (e : (χ₁⁻¹).changeLevel hcn = (χ₂⁻¹).changeLevel hcn) : χ₁ = χ₂

### PAG208::exists_primitive_changeLevel（theorem、401 行）
theorem exists_primitive_changeLevel (n : ℕ) (ψ : DirichletCharacter ℂ n) :
    ∃ (c : ℕ) (hcn : c ∣ n) (χ : DirichletCharacter ℂ c), χ.IsPrimitive ∧ (χ⁻¹).changeLevel hcn = ψ

######## PAG210.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part210
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part210

### PAG210::liftc（def、25 行）
noncomputable def liftc {c : ℕ} (χ : DirichletCharacter ℂ c) (m : ℕ) : DirichletCharacter ℂ m :=
  if h : c ∣ m then χ.changeLevel h else 1

######## PAG212.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part212
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part212

### PAG212::inner_sum_smul_right（theorem、25 行）
theorem inner_sum_smul_right {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (v : ZMod N → ℂ) (b : ι → ℂ)
    (w : ι → ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (v x) * (∑ j ∈ S, b j • w j) x =
      ∑ j ∈ S, b j * ∑ x, starRingEnd ℂ (v x) * w j x

### PAG212::inner_sum_smul_left（theorem、34 行）
theorem inner_sum_smul_left {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ZMod N → ℂ)
    (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ ((∑ s ∈ S, a s • v s) x) * f x =
      ∑ s ∈ S, starRingEnd ℂ (a s) * ∑ x, starRingEnd ℂ (v s x) * f x

### PAG212::dvd_div_iff_dvd（theorem、67 行）
theorem dvd_div_iff_dvd (s r e : ℕ) (hs : 0 < s) (he : e ∣ s * r) : s ∣ s * r / e ↔ e ∣ r

######## PAG213.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part213
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part213

### PAG213::conj_inv_apply（theorem、29 行）
theorem conj_inv_apply {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (x : ZMod c) :
    starRingEnd ℂ (χ⁻¹ x) = χ x

######## PAG215.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part215
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part215

### PAG215::inner_conj_symm（theorem、35 行）
theorem inner_conj_symm {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (a x) * b x = starRingEnd ℂ (∑ x, starRingEnd ℂ (b x) * a x)

######## PAG216.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part216
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part216

### PAG216::blockProjG（def、116 行）
noncomputable def blockProjG (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  ∑ v ∈ (N / c).divisors,
    ((N : ℂ) / (Nat.totient (v * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x) • gblock N c χ v

######## PAG217.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part217
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part217

### PAG217::inner_smul_left'（theorem、48 行）
theorem inner_smul_left' {N : ℕ} [NeZero N] (r : ℂ) (a b : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ ((r • a) x) * b x = starRingEnd ℂ r * ∑ x, starRingEnd ℂ (a x) * b x

######## PAG218.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part218
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part218

### PAG218::liftc_mul_liftc_inv（theorem、52 行）
theorem liftc_mul_liftc_inv (N : ℕ) {c : ℕ} (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ) :
    liftc χ N (a : ZMod N) * liftc χ⁻¹ N (a : ZMod N) = 1

### PAG218::dil（def、68 行）
def dil {N : ℕ} (a : (ZMod N)ˣ) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => (a : ZMod N) * x)

### PAG218::dil_one（theorem、76 行）
theorem dil_one {N : ℕ} (f : ZMod N → ℂ) : dil (1 : (ZMod N)ˣ) f = f

### PAG218::dil_dil（theorem、81 行）
theorem dil_dil {N : ℕ} (a b : (ZMod N)ˣ) (f : ZMod N → ℂ) : dil a (dil b f) = dil (a * b) f

### PAG218::blockProjL（def、151 行）
noncomputable def blockProjL (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) :
    (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := blockProj N c χ
  map_add' f g := by
    simp only [blockProj, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' r f := by
    simp only [blockProj, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by ring)

### PAG218::blockProjL_eq_sum_dil（theorem、203 行）
theorem blockProjL_eq_sum_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    blockProjL N c χ = ((Nat.totient N : ℂ))⁻¹ • ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) • dil a

### PAG218::dft_dil（theorem、304 行）
theorem dft_dil {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : 𝓕 (dil a f) = dil a⁻¹ (𝓕 f)

######## PAG219.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part219
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part219

### PAG219::sum_changeLevel_mul_conj（theorem、107 行）
theorem sum_changeLevel_mul_conj {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (m : ℕ) [NeZero m]
    (hdvd : c ∣ m) :
    ∑ y : ZMod m, χ.changeLevel hdvd y * starRingEnd ℂ (χ ((y.val : ℕ) : ZMod c)) = Nat.totient m

### PAG219::inner_gblock_one_dft_ne_zero（theorem、157 行）
theorem inner_gblock_one_dft_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c)
    (hcop : Nat.Coprime (N / (w * c)) c) :
    ∑ x, starRingEnd ℂ (gblock N c χ 1 x) * 𝓕 (gblock N c χ⁻¹ w) x ≠ 0

######## PAG220.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part220
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part220

### PAG220::InLayer（abbrev、31 行）
abbrev InLayer (c d n : ℕ) : Prop := ∃ e : ℕ, n = d * e ∧ Nat.Coprime e c

######## PAG223.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part223
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part223

### PAG223::eq_of_inLayer_inLayer（theorem、200 行）
theorem eq_of_inLayer_inLayer {c c' d d' : ℕ} (hd0 : 0 < d) (h1 : InLayer c' d' d) (h2 : InLayer c d d') :
    d = d'

### PAG223::blockHomExt（def、396 行）
noncomputable def blockHomExt (N c c' : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c)
    (χ' : DirichletCharacter ℂ c') (T : blockSpan N c χ →ₗ[ℂ] blockSpan N c' χ') : Module.End ℂ (ZMod N → ℂ) :=
  (blockSpan N c' χ').subtype ∘ₗ T ∘ₗ LinearMap.codRestrict (blockSpan N c χ) (blockProjL N c χ) (blockProjL_mem N c χ)

######## PAG224.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part224
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part224

### PAG224::top_shellInvariant（theorem、379 行）
theorem top_shellInvariant (N : ℕ) [NeZero N] : ShellInvariant (⊤ : Submodule ℂ (ZMod N → ℂ))

### PAG224::mem_dilCommute（theorem、420 行）
theorem mem_dilCommute (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilCommute N ↔ ∀ (a : (ZMod N)ˣ) (f : ZMod N → ℂ), T (dil a f) = dil a (T f)

### PAG224::mem_dilComm（theorem、428 行）
theorem mem_dilComm (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilComm N ↔ T ∈ fullComm N ∧ T ∈ dilCommute N

### PAG224::blockHomExt_mem_dilCommute（theorem、433 行）
theorem blockHomExt_mem_dilCommute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (Y : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ) : blockHomExt N c c χ χ Y ∈ dilCommute N

### PAG224::finrank_dilComm_eq_sum（theorem、577 行）
theorem finrank_dilComm_eq_sum (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] :
    Module.finrank ℂ (dilComm N) = ∑ b : BlockIdx N,
      ∏ q ∈ (Nat.gcd b.1 (N / b.1)).primeFactors, ((N / b.1).factorization q + 1)

### PAG224::finrank_dilComm（theorem、587 行）
theorem finrank_dilComm (N : ℕ) [NeZero N] :
    Module.finrank ℂ (dilComm N) = ∑ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} *
      ∏ q ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization q + 1)

######## PAG225.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part225
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part225

### PAG225::dilCommute_preserves（theorem、72 行）
theorem dilCommute_preserves (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ dilCommute N)
    (b : BlockIdx N) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N b.1 b.2.1) : T f ∈ blockSpan N b.1 b.2.1

### PAG225::dilComm_commute（theorem、79 行）
theorem dilComm_commute (N : ℕ) [NeZero N] {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ dilComm N)
    (hT' : T' ∈ dilComm N) : Commute T T'

### PAG225::not_commute_of_ne（theorem、147 行）
theorem not_commute_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hne : χ ≠ χ') :
    blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id) ∈ fullComm N ∧
      blockHomExt N c c χ χ LinearMap.id ∈ fullComm N ∧
      ¬ Commute (blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id))
        (blockHomExt N c c χ χ LinearMap.id)

######## PAG226.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part226
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part226

### PAG226::layerScalar（def、205 行）
noncomputable def layerScalar (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (d : ℕ)
    (Z : Module.End ℂ (ZMod N → ℂ)) : ℂ :=
  (N : ℂ) / (Nat.totient (d * c) : ℂ) * ∑ x, starRingEnd ℂ (gblock N c χ d x) * Z (gblock N c χ d) x

######## PAG227.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part227
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part227

### PAG227::decEqPrim（instance、212 行）
noncomputable instance decEqPrim (c : ℕ) : DecidableEq (Prim c) := Classical.decEq _

### PAG227::matUnit_mul_matSum_mul_matUnit（theorem、351 行）
theorem matUnit_mul_matSum_mul_matUnit (N : ℕ) [NeZero N]
    (M : Π p : centerIdx N, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) (p : centerIdx N) (i j : Prim p.1.1) :
    matUnit N p.1.1 p.1.2 i.1 i.1 * matSum N M * matUnit N p.1.1 p.1.2 j.1 j.1 =
      M p i j • matUnit N p.1.1 p.1.2 j.1 i.1

######## PAG229.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part229
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part229

### PAG229::herm（def、34 行）
noncomputable def herm (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

### PAG229::conj_dind（theorem、91 行）
theorem conj_dind (N s : ℕ) (x : ZMod N) : starRingEnd ℂ (dind N s x) = dind N s x

### PAG229::AdjClosed（def、134 行）
def AdjClosed (N : ℕ) [NeZero N] (B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) : Prop :=
  ∀ T ∈ B, ∃ T' ∈ B, ∀ f g, herm N (T f) g = herm N f (T' g)

### PAG229::adjOp（def、171 行）
noncomputable def adjOp (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod N → ℂ) where
  toFun g y := ∑ x, starRingEnd ℂ (T (Pi.single y 1) x) * g x
  map_add' g g' := by
    funext y
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring

######## PAG231.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part231
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part231

### PAG231::exists_unit_liftc_ne（theorem、215 行）
theorem exists_unit_liftc_ne (N c : ℕ) [NeZero N] (hcN : c ∣ N) {χ χ' : DirichletCharacter ℂ c} (h : χ ≠ χ') :
    ∃ a : (ZMod N)ˣ, liftc χ N (a : ZMod N) ≠ liftc χ' N (a : ZMod N)

######## PAG232.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part232
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part232

### PAG232::leftOp（def、187 行）
noncomputable def leftOp {a : ℕ} (b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := S (fun x => F (x, p.2)) p.1
  map_add' F G := by
    funext p
    show S ((fun x => F (x, p.2)) + (fun x => G (x, p.2))) p.1 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show S (c • (fun x => F (x, p.2))) p.1 = _
    rw [map_smul]
    rfl

### PAG232::rightOp（def、201 行）
noncomputable def rightOp (a : ℕ) {b : ℕ} (T : Module.End ℂ (ZMod b → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := T (fun y => F (p.1, y)) p.2
  map_add' F G := by
    funext p
    show T ((fun y => F (p.1, y)) + (fun y => G (p.1, y))) p.2 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show T (c • (fun y => F (p.1, y))) p.2 = _
    rw [map_smul]
    rfl

######## PAG234.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part234
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part234

### PAG234::inclY（def、43 行）
noncomputable def inclY {a b : ℕ} (y' : ZMod b) : (ZMod a → ℂ) →ₗ[ℂ] (ZMod a × ZMod b → ℂ) where
  toFun f q := if q.2 = y' then f q.1 else 0
  map_add' f g := by
    funext q
    by_cases hq : q.2 = y' <;> simp [hq]
  map_smul' c f := by
    funext q
    by_cases hq : q.2 = y' <;> simp [hq]

### PAG234::restrY（def、57 行）
noncomputable def restrY {a b : ℕ} (y : ZMod b) : (ZMod a × ZMod b → ℂ) →ₗ[ℂ] (ZMod a → ℂ) where
  toFun F x := F (x, y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

### PAG234::exists_basis_subalg（theorem、177 行）
theorem exists_basis_subalg {X : Type*} [Fintype X] (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    ∃ (n : ℕ) (u : Fin n → Module.End ℂ (X → ℂ)), LinearIndependent ℂ u ∧ (∀ i, u i ∈ B) ∧
      ∀ T ∈ B, ∃ c : Fin n → ℂ, T = ∑ i, c i • u i

### PAG234::leftOp_sum_smul（theorem、195 行）
theorem leftOp_sum_smul {a b : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℂ) (u : ι → Module.End ℂ (ZMod a → ℂ)) :
    leftOp b (∑ i, c i • u i) = ∑ i, c i • leftOp b (u i)

### PAG234::rightOp_sum_smul（theorem、202 行）
theorem rightOp_sum_smul {a b : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → Module.End ℂ (ZMod b → ℂ)) :
    rightOp a (∑ i, c i • v i) = ∑ i, c i • rightOp a (v i)

######## PAG235.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part235
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part235

### PAG235::unitLeft（def、75 行）
noncomputable def unitLeft {a b : ℕ} (hab : Nat.Coprime a b) (v : (ZMod a)ˣ) : (ZMod (a * b))ˣ where
  val := (ZMod.chineseRemainder hab).symm ((v : ZMod a), 1)
  inv := (ZMod.chineseRemainder hab).symm (((v⁻¹ : (ZMod a)ˣ) : ZMod a), 1)
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, mul_one]
    exact map_one _
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, mul_one]
    exact map_one _

### PAG235::unitRight（def、86 行）
noncomputable def unitRight {a b : ℕ} (hab : Nat.Coprime a b) (w : (ZMod b)ˣ) : (ZMod (a * b))ˣ where
  val := (ZMod.chineseRemainder hab).symm (1, (w : ZMod b))
  inv := (ZMod.chineseRemainder hab).symm (1, ((w⁻¹ : (ZMod b)ˣ) : ZMod b))
  val_inv := by
    rw [← map_mul, Prod.mk_mul_mk, Units.mul_inv, mul_one]
    exact map_one _
  inv_val := by
    rw [← map_mul, Prod.mk_mul_mk, Units.inv_mul, mul_one]
    exact map_one _

### PAG235::crt_unitLeft（theorem、97 行）
theorem crt_unitLeft {a b : ℕ} (hab : Nat.Coprime a b) (v : (ZMod a)ˣ) :
    ZMod.chineseRemainder hab (unitLeft hab v : ZMod (a * b)) = ((v : ZMod a), 1)

### PAG235::crt_unitRight（theorem、102 行）
theorem crt_unitRight {a b : ℕ} (hab : Nat.Coprime a b) (w : (ZMod b)ˣ) :
    ZMod.chineseRemainder hab (unitRight hab w : ZMod (a * b)) = (1, (w : ZMod b))

### PAG235::finrank_dilComm_mul（theorem、251 行）
theorem finrank_dilComm_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (dilComm (a * b)) = Module.finrank ℂ (dilComm a) * Module.finrank ℂ (dilComm b)

### PAG235::inLayer_iff_dvd（theorem、279 行）
theorem inLayer_iff_dvd {c d n : ℕ} (hd : 0 < d) : InLayer c d n ↔ d ∣ n ∧ Nat.Coprime (n / d) c

######## PAG244.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part244
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part244

### PAG244::sum_divisors_primePow_moebius_int（theorem、294 行）
theorem sum_divisors_primePow_moebius_int {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℤ) :
    ∑ e ∈ (q ^ n).divisors, ArithmeticFunction.moebius e * g e = g 1 - g q

######## PAG247.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part247
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part247

### PAG247::abs_ramSum_primePow_le（theorem、311 行）
theorem abs_ramSum_primePow_le {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (n : ℕ) :
    |ramSum n (p ^ k)| ≤ (p : ℤ) ^ k - (p : ℤ) ^ (k - 1)

######## PAG249.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part249
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part249

### PAG249::ineq_odd（theorem、193 行）
theorem ineq_odd {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : 2 * (x * y) + x ^ 2 + 1 < x ^ 2 * y + y ^ 2 + y + 2

######## PAG251.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part251
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part251

### PAG251::convL_geps_self_mul_mulLeft_dind_self（theorem、85 行）
theorem convL_geps_self_mul_mulLeft_dind_self (N : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N N) * LinearMap.mulLeft ℂ (dind N N) * PAG.Part15.convL (geps N N) =
      (1 / (N : ℂ)) • PAG.Part15.convL (geps N N)

### PAG251::leftOp_smul'（theorem、192 行）
theorem leftOp_smul' {a : ℕ} (b : ℕ) (c : ℂ) (S : Module.End ℂ (ZMod a → ℂ)) :
    PAG.Part232.leftOp b (c • S) = c • PAG.Part232.leftOp b S

### PAG251::convL_geps_of_two_mul（theorem、316 行）
theorem convL_geps_of_two_mul {n M t : ℕ} [NeZero n] (hn : n = 2 * M) (hM : Nat.Coprime 2 M) (ht : t ∣ M) :
    PAG.Part15.convL (geps n t) =
      (4 : ℂ) • ((1 - PAG.Part15.convL (geps n (2 * t))) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (2 * v))) * PAG.Part15.convL (geps n (2 * t)) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (2 * v))) * (1 - PAG.Part15.convL (geps n (2 * t))))

######## PAG253.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### PAG253::exists_cls_near（theorem、213 行）
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε

### PAG253::exists_cls_near_of_dvd（theorem、291 行）
theorem exists_cls_near_of_dvd {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : (ZMod N)ˣ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime M) (hn : n.Coprime M), 0 < m ∧ 0 < n ∧
      kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹ = a ∧
      |Real.log n - Real.log m - t| < ε

### PAG253::invariant_kUnit（theorem、305 行）
theorem invariant_kUnit {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u) :
    ∀ (n : ℕ) (hn : n.Coprime M), 0 < n → ∀ (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit n (Nat.Coprime.coprime_dvd_right hNM hn)) (u - Real.log n) = f k u

### PAG253::invariant_cls（theorem、335 行）
theorem invariant_cls {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    {m n : ℕ} (hm : m.Coprime M) (hn : n.Coprime M) (hm0 : 0 < m) (hn0 : 0 < n) (k : (ZMod N)ˣ) (u : ℝ) :
    f (k * (kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹))
      (u + (Real.log n - Real.log m)) = f k u

### PAG253::eq_of_prime_invariant（theorem、352 行）
theorem eq_of_prime_invariant {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂

### PAG253::eq_of_prime_invariant'（theorem、371 行）
theorem eq_of_prime_invariant' {N : ℕ} [NeZero N] (f : (ZMod N)ˣ → ℝ → ℂ) (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p hpN) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂

### PAG253::primeShift（def、454 行）
noncomputable def primeShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * kUnit p hp) (u - Real.log p)

### PAG253::primeShiftInv（def、458 行）
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)

### PAG253::shift_invariant_of_prime_invariant（theorem、695 行）
theorem shift_invariant_of_prime_invariant {N : ℕ} [NeZero N] (F : (ZMod N)ˣ → ℝ → ℂ)
    (hF : ∀ k, Continuous (F k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), primeShift p hpN F = F)
    (a : (ZMod N)ˣ) (s : ℝ) : unitShift a F = F ∧ scaleShift s F = F
