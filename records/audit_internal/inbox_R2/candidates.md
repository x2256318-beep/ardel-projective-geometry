
######## PAG2.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Kloosterman
variable {N : ℕ} [NeZero N]
open scoped Classical in
end PAG.Kloosterman

### PAG2::addChar_sum（lemma、23 行）
omit [NeZero N] in
lemma addChar_sum {ι : Type*} (ψ : AddChar (ZMod N) ℂ) (s : Finset ι) (x : ι → ZMod N) :
    ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i)

### PAG2::cas（def、121 行）
noncomputable def cas (z : ℂ) : ℂ := ((z.re + z.im : ℝ) : ℂ)

### PAG2::Wpow（def、124 行）
noncomputable def Wpow (χ : DirichletCharacter ℂ N) (r : ℕ) : ℂ :=
  ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 * gaussSum χ ZMod.stdAddChar ^ r
    / (Real.sqrt N : ℂ) ^ r

### PAG2::parity_weight（lemma、131 行）
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r

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

### PAG8::p_dvd_val_of_not_isUnit（theorem、69 行）
theorem p_dvd_val_of_not_isUnit (s : ZMod (p ^ (n + 1))) (hs : ¬ IsUnit s) : p ∣ s.val

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

### PAG9::chi_neg_one_sq（theorem、40 行）
omit [NeZero N] in
theorem chi_neg_one_sq (χ : MulChar (ZMod N) ℂ) : χ (-1) * χ (-1) = 1

### PAG9::inv_apply_neg_one（theorem、45 行）
omit [NeZero N] in
theorem inv_apply_neg_one (χ : MulChar (ZMod N) ℂ) : χ⁻¹ (-1) = χ (-1)

### PAG9::ker_pow_p（theorem、108 行）
theorem ker_pow_p (hn : 1 ≤ n) (u : (ZMod (p ^ (n + 1)))ˣ)
    (hu : ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1) :
    (u : ZMod (p ^ (n + 1))) ^ p = 1

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

### PAG14::stationary_phase（theorem、181 行）
theorem stationary_phase (A y : ZMod M) :
    ∑ t : ZMod M, ZMod.stdAddChar (-A * t) * ZMod.stdAddChar (y * t)
      = if y = A then (M : ℂ) else 0

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

### PAG15::shellSize（def、158 行）
def shellSize (p K v : ℕ) : ℕ := p ^ (K - 1 - v) * (p - 1)

### PAG15::abs_F_eq（theorem、195 行）
theorem abs_F_eq (p K v : ℕ) (hp : 2 ≤ p) (hv : v < K) :
    Real.sqrt (((shellSize p K v : ℝ) / shellSize p K (K - 1 - v)) * (p : ℝ) ^ (2 * v) / (p : ℝ) ^ K)
      = (Real.sqrt p)⁻¹

### PAG15::radial_column_unitary（theorem、201 行）
theorem radial_column_unitary (p : ℕ) (hp : 2 ≤ p) (L : ℕ) :
    (1 : ℝ) / p + ∑ k ∈ range L, ((p : ℝ) - 1) ^ 2 / (p : ℝ) ^ (k + 2) + ((p : ℝ) - 1) / (p : ℝ) ^ (L + 1) = 1

######## PAG16.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part16
open ZMod Finset
variable {N : ℕ} [NeZero N]
variable {p n : ℕ} [hp : Fact p.Prime]
end PAG.Part16

### PAG16::gaussSum_ne_zero（theorem、25 行）
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar ≠ 0

### PAG16::normSq_gaussSum（theorem、53 行）
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N

### PAG16::conv_char_inv（theorem、107 行）
omit hp in
theorem conv_char_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (x : ZMod N) :
    PAG.Part15.conv (χ : ZMod N → ℂ) (χ⁻¹ : DirichletCharacter ℂ N) x
      = χ (-1) * ∑ k : ZMod N, stdAddChar (k * x) * (1 : DirichletCharacter ℂ N) (-k)

######## PAG19.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part19
open ZMod Finset PAG.Part17 PAG.Part18
section ThmB
variable {N : ℕ} [NeZero N]
end ThmB
section Kernel
end Kernel
section Coef
end Coef
section Ramanujan
variable {p n : ℕ} [hp : Fact p.Prime]
end Ramanujan
end PAG.Part19

### PAG19::sz（def、76 行）
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)

### PAG19::coef_identity_real（theorem、93 行）
theorem coef_identity_real (p K c w v c'' a : ℕ) (hp : 2 ≤ p) (hc : c = v + c'' + 1) (hK : K = w + c + a) :
    (sz p K (w + v) : ℝ) * ((p : ℝ) ^ (K - w - c)) ^ 2 * (p : ℝ) ^ (c + v) / (sz p K w : ℝ) ^ 2
      = (p : ℝ) ^ K / sz p K (K - c - w)

######## PAG20.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part20
open ZMod Finset PAG.Part17 PAG.Part18 PAG.Part19
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part20

### PAG20::coef_sqrt（theorem、17 行）
theorem coef_sqrt (p K c w v c'' a : ℕ) (hp : 2 ≤ p) (hc : c = v + c'' + 1) (hK : K = w + c + a) :
    ((p : ℝ) ^ (K - w - c)) * Real.sqrt ((p : ℝ) ^ (c + v)) / (sz p K w : ℝ)
      = Real.sqrt ((p : ℝ) ^ K / (sz p K (K - c - w) : ℝ)) / Real.sqrt (sz p K (w + v) : ℝ)

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

### PAG25::chi_inv_neg_one（theorem、75 行）
omit hp in
theorem chi_inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)

######## PAG29.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part29
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part24
open Classical
variable {p : ℕ} [hp : Fact p.Prime]
section ProjKets
variable (K : ℕ) (hK : 1 ≤ K)
end ProjKets
section Absorb
end Absorb
section ThmBEps
variable (K : ℕ) (hK1 : 1 ≤ K)
end ThmBEps
end PAG.Part29

### PAG29::cB（def、207 行）
noncomputable def cB (K w n : ℕ) (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ℂ :=
  χ (-1) * ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ))

### PAG29::chi_neg_one_sq'（theorem、236 行）
theorem chi_neg_one_sq' {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1

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

### PAG30::fourLe（theorem、125 行）
theorem fourLe (hc : 1 ≤ c) : 1 < 2 ^ c

### PAG30::kk（def、128 行）
def kk (c : ℕ) : ZMod (2 ^ (c + 1)) := 1 + ((2 ^ c : ℕ) : ZMod (2 ^ (c + 1)))

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

### PAG31::mod4_mul_trivial（theorem、240 行）
theorem mod4_mul_trivial (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (1 + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : χ₁ * χ₂ = 1

### PAG31::gg（def、260 行）
def gg (d : ℕ) : ZMod (2 ^ (d + 2)) := 1 + ((2 ^ d : ℕ) : ZMod (2 ^ (d + 2)))

######## PAG32.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part32
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part25 PAG.Part26
section ProjTilde
variable {N : ℕ}
end ProjTilde
section ProjTildeK
variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)
end ProjTildeK
section Prim
variable {p : ℕ} [hp : Fact p.Prime] {c : ℕ}
end Prim
end PAG.Part32

### PAG32::gp（def、126 行）
def gp (p c : ℕ) : ZMod (p ^ (c + 1)) := 1 + ((p ^ c : ℕ) : ZMod (p ^ (c + 1)))

### PAG32::prim_level_p_iff（theorem、244 行）
theorem prim_level_p_iff (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1

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

### PAG37::unitsMap_neg_one（theorem、78 行）
theorem unitsMap_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.unitsMap h (-1) = -1

### PAG37::toFour（def、88 行）
noncomputable def toFour (d : ℕ) : (ZMod (2 ^ (d + 3)))ˣ →* (ZMod (2 ^ 2))ˣ :=
  ZMod.unitsMap (pow_dvd_pow 2 (show 2 ≤ d + 3 by omega))

### PAG37::ker_five（theorem、132 行）
theorem ker_five {m : ℕ} (hm2 : 2 ≤ m) (hm : m ≤ d + 3) (u : (ZMod (2 ^ (d + 3)))ˣ)
    (hu : u ∈ (ZMod.unitsMap (pow_dvd_pow 2 hm)).ker) :
    ∃ t : ℕ, u = (five (d + 3)) ^ (2 ^ (m - 2) * t)

######## PAG42.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part42
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part18 PAG.Part19 PAG.Part21
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part42

### PAG42::normSq_mixed_coef（theorem、83 行）
theorem normSq_mixed_coef (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1))) (hψ : ψ.IsPrimitive) :
    Complex.normSq ((((Real.sqrt (sz p K (w + v)))⁻¹ : ℝ) * (((p ^ (K - w - (n + 1)) : ℕ) : ℂ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar / gaussSum ψ stdAddChar)) : ℂ))
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)

######## PAG44.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part44
open ZMod Finset PAG.Part37 Complex
variable {d : ℕ}
end PAG.Part44

### PAG44::zeta（def、61 行）
noncomputable def zeta (d : ℕ) : ℂ := exp (2 * Real.pi * I / ((2 ^ (d + 1) : ℕ) : ℂ))

######## PAG45.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part45
open ZMod Finset PAG.Part37 PAG.Part44 Complex
variable {d : ℕ}
end PAG.Part45

### PAG45::char_ext（theorem、24 行）
theorem char_ext (χ χ' : DirichletCharacter ℂ (2 ^ (d + 3)))
    (h5 : χ 5 = χ' 5) (h1 : χ (-1) = χ' (-1)) : χ = χ'

######## PAG47.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part47
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part40
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part47

### PAG47::normSq_coef_of（theorem、40 行）
theorem normSq_coef_of {N : ℕ} [NeZero N] (F k : ZMod N → ℂ) (C : ℂ) (lam : ℝ) (hF : F = C • k)
    (hk : ∑ x, Complex.normSq (k x) = 1) (hn : ∑ x, Complex.normSq (F x) = lam) : Complex.normSq C = lam

######## PAG57.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part57
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part48 PAG.Part49 PAG.Part52 PAG.Part54 PAG.Part55
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part57

### PAG57::not_dvd_val_of_unit（theorem、18 行）
theorem not_dvd_val_of_unit {m : ℕ} (hm : 1 ≤ m) (y : ZMod (p ^ m)) (hy : IsUnit y) : ¬ p ∣ y.val

######## PAG61.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part61
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part32 Complex
variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ)
variable (hp2 : p ≠ 2)
end PAG.Part61

### PAG61::zeta（def、26 行）
noncomputable def zeta : ℂ := exp (2 * Real.pi * I / (phi (p := p) c : ℂ))

### PAG61::gen（def、44 行）
noncomputable def gen : (ZMod (p ^ (c + 1)))ˣ :=
  have := isCyclic_units c hp2
  Classical.choose (IsCyclic.exists_generator (α := (ZMod (p ^ (c + 1)))ˣ))

######## PAG62.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part62
open ZMod Finset PAG.Part61
variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ) (hp2 : p ≠ 2)
end PAG.Part62

### PAG62::card_ker_mul（theorem、18 行）
theorem card_ker_mul (m : ℕ) (hm : m ≤ c + 1) :
    Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker * (p ^ m).totient = (p ^ (c + 1)).totient

### PAG62::card_ker（theorem、30 行）
theorem card_ker (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ c + 1) :
    Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker = p ^ (c + 1 - m)

######## PAG67.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part67
open ZMod Finset PAG.Part61 PAG.Part62
variable {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (c c' : ℕ) (hcc : c' ≤ c)
end PAG.Part67

### PAG67::red（abbrev、18 行）
noncomputable abbrev red : (ZMod (p ^ (c + 1)))ˣ →* (ZMod (p ^ (c' + 1)))ˣ :=
  ZMod.unitsMap (pow_dvd_pow p (by omega : c' + 1 ≤ c + 1))

include hp2 hcc

### PAG67::omegaLow（def、54 行）
noncomputable def omegaLow : DirichletCharacter ℂ (p ^ (c' + 1)) :=
  MulChar.ofRootOfUnity (zeta_pow_mem c c' hcc) (red_gen_spec hp2 c c' hcc)

######## PAG68.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part68
open ZMod Finset PAG.Part32 PAG.Part61 PAG.Part62 PAG.Part67
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part68

### PAG68::faithful_pow_factors_iff（theorem、45 行）
theorem faithful_pow_factors_iff (hp2 : p ≠ 2) {c : ℕ} (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : Faithful χ)
    (m : ℕ) (hm : m ≤ c + 1) (j : ℕ) :
    (χ ^ j).FactorsThrough (p ^ m) ↔ Nat.card (ZMod.unitsMap (pow_dvd_pow p hm)).ker ∣ j

######## PAG72.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part72
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part44 PAG.Part47 PAG.Part50
end PAG.Part72

### PAG72::prim4_neg_one（theorem、16 行）
theorem prim4_neg_one (ψ : DirichletCharacter ℂ (2 ^ 2)) (hψ : ψ.IsPrimitive) : ψ (-1) = -1

### PAG72::prim4_unique（theorem、35 行）
theorem prim4_unique (ψ ψ' : DirichletCharacter ℂ (2 ^ 2)) (hψ : ψ.IsPrimitive) (hψ' : ψ'.IsPrimitive) :
    ψ = ψ'

### PAG72::exists_prim4（theorem、44 行）
theorem exists_prim4 : ∃ ψ : DirichletCharacter ℂ (2 ^ 2), ψ.IsPrimitive

######## PAG75.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part75
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part48 PAG.Part49 PAG.Part51 PAG.Part61 PAG.Part67
variable {p : ℕ} [hp : Fact p.Prime]
variable (hp2 : p ≠ 2) (c : ℕ)
end PAG.Part75

### PAG75::chi_neg_one_ne_zero（theorem、27 行）
theorem chi_neg_one_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) ≠ 0

######## PAG80.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part80
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part58
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part80

### PAG80::mu（def、33 行）
noncomputable def mu (K w c v : ℕ) : ℂ :=
  (if w + c ≤ v then (p : ℂ) ^ (K - v) else 0) - (if w + c ≤ v + 1 then (p : ℂ) ^ (K - (v + 1)) else 0)

######## PAG81.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part81
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part80
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
open Classical in
end PAG.Part81

### PAG81::inv_neg_one（theorem、22 行）
theorem inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)

######## PAG85.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part85
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part44 PAG.Part45 PAG.Part66 PAG.Part72
end PAG.Part85

### PAG85::p2_mixed_general（theorem、32 行）
theorem p2_mixed_general (K w₁ n₁ w₂ n₂ : ℕ) (h₁ : w₁ + (n₁ + 1) ≤ K) (h₂ : w₂ + (n₂ + 1) ≤ K)
    (χ₁ : DirichletCharacter ℂ (2 ^ (n₁ + 1))) (χ₂ : DirichletCharacter ℂ (2 ^ (n₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive) (hab : K - (n₁ + 1) - w₁ = K - (n₂ + 1) - w₂)
    (hw : w₁ < w₂) :
    ∃ ψ : DirichletCharacter ℂ (2 ^ (n₁ + 1)), ψ.IsPrimitive ∧ ∃ C : ℂ,
      Complex.normSq C = (2 : ℝ) ^ K / (sz 2 K (K - (n₁ + 1) - w₁) : ℝ) ∧
      conv (ket (p := 2) K w₁ (n₁ + 1) h₁ χ₁) (ket (p := 2) K w₂ (n₂ + 1) h₂ χ₂)
        = C • ket (p := 2) K w₁ (n₁ + 1) h₁ ψ

######## PAG95.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part95
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part52 PAG.Part54 PAG.Part55 PAG.Part59
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part95

### PAG95::J（def、110 行）
def J (K a : ℕ) := {x : (n : Fin K) × DirichletCharacter ℂ (p ^ ((n : ℕ) + 1)) // x.2.IsPrimitive ∧ (x.1 : ℕ) + 1 ≤ K - a}

######## PAG98.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part98
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part51 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part59 PAG.Part89 PAG.Part90
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part98

### PAG98::Equivariant（def、27 行）
def Equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), f (u * x) = α u * f x

######## PAG106.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part106
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part105
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part106

### PAG106::sz_succ（theorem、62 行）
omit hp in
theorem sz_succ (K w : ℕ) (hw : w < K) : sz p (K + 1) w = p * sz p K w

######## PAG116.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part116
open ZMod Finset Polynomial PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part116

### PAG116::cnorm（def、89 行）
noncomputable def cnorm (p K a : ℕ) : ℂ := (((Real.sqrt ((p : ℝ) ^ K / (sz p K a : ℝ)))⁻¹ : ℝ) : ℂ)

######## PAG117.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part117
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part55 PAG.Part59 PAG.Part90 PAG.Part95 PAG.Part116
section Pullback
variable {M M' : ℕ} [NeZero M] [NeZero M']
end Pullback
section Ket
variable {p : ℕ} [hp : Fact p.Prime]
end Ket
end PAG.Part117

### PAG117::stdAddChar_mul_cast（theorem、19 行）
theorem stdAddChar_mul_cast (h : M ∣ M') (d : ℕ) (hd : M' = M * d) (z : ZMod M') :
    stdAddChar ((d : ZMod M') * z) = stdAddChar (ZMod.castHom h (ZMod M) z)

### PAG117::inv_neg_one_pow（theorem、80 行）
omit hp in
theorem inv_neg_one_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : (χ⁻¹ (-1)) ^ orderOf χ = 1

### PAG117::normSq_inv_neg_one（theorem、85 行）
omit hp in
theorem normSq_inv_neg_one {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : Complex.normSq (χ⁻¹ (-1)) = 1

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

### PAG118::gauss_even_root（theorem、161 行）
theorem gauss_even_root (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ M = 1

######## PAG119.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part119
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part119

### PAG119::quad_root'（theorem、148 行）
theorem quad_root' (hp2 : p ≠ 2) (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ)) ^ (4 * p) = 1

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

### PAG120::psi_two_one（theorem、21 行）
theorem psi_two_one : stdAddChar (1 : ZMod 2) = -1

### PAG120::quad_root_two（theorem、26 行）
theorem quad_root_two (F : ZMod 2 → ℂ) (a : ZMod 2) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt 2 : ℝ) : ℂ)) ^ (4 * 2) = 1

### PAG120::quad_root_all（theorem、52 行）
theorem quad_root_all (F : ZMod p → ℂ) (a : ZMod p) (ha : a ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t s, F (t + s) = F t * F s * stdAddChar (a * t * s)) :
    ((∑ t, F t) / ((Real.sqrt p : ℝ) : ℂ)) ^ (4 * p) = 1

### PAG120::gauss_root_ge_two（theorem、348 行）
theorem gauss_root_ge_two (c : ℕ) (hc : 2 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ M : ℕ, 0 < M ∧ (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ)) ^ M = 1

######## PAG121.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part121
open ZMod Finset Polynomial PAG.Part15 PAG.Part108 PAG.Part109 PAG.Part113
section Char
variable {N : ℕ} [NeZero N]
end Char
section Prod
variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
end Prod
section Ket
open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part90 PAG.Part95
variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
end Ket
end PAG.Part121

### PAG121::sum_chr_mul（theorem、31 行）
theorem sum_chr_mul (s s' : ZMod N) :
    ∑ x, chr s x * chr (-s') x = if s = s' then (N : ℂ) else 0

######## PAG127.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part127
open ZMod Finset PAG.Part118
variable {p : ℕ} [hp : Fact p.Prime]
section Even
variable {c m : ℕ} (hc : c = 2 * m)
end Even
end PAG.Part127

### PAG127::stdAddChar_pow_eq_one_iff（theorem、18 行）
theorem stdAddChar_pow_eq_one_iff {c : ℕ} (u : ZMod (p ^ c)) (hu : IsUnit u) (n : ℕ) :
    stdAddChar u ^ n = 1 ↔ p ^ c ∣ n

### PAG127::gauss_even_phase（theorem、75 行）
theorem gauss_even_phase (χ : DirichletCharacter ℂ (p ^ c)) (hχ : χ.IsPrimitive) :
    ∃ u₀ : ZMod (p ^ c), IsUnit u₀ ∧
      gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ) = χ u₀ * stdAddChar u₀

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

######## PAG140.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part140
open ZMod Finset PAG.Part118
variable {p : ℕ} [hp : Fact p.Prime]
section Even
variable {c m : ℕ} (hc : c = 2 * m)
end Even
end PAG.Part140

### PAG140::exists_delta（theorem、46 行）
theorem exists_delta (ψ : DirichletCharacter ℂ (p ^ c)) :
    ∃ δ : ZMod (p ^ c), ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y)

######## PAG142.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part142
open ZMod Finset PAG.Part120
variable {p : ℕ} [hp : Fact p.Prime]
section Freq
variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)
end Freq
end PAG.Part142

### PAG142::freq_mul（theorem、23 行）
theorem freq_mul (χ ψ : DirichletCharacter ℂ (p ^ c)) (δ₁ δ₂ : ZMod (p ^ c))
    (h₁ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₁ * y))
    (h₂ : ∀ y, ψ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ₂ * y)) :
    ∀ y, (χ * ψ) (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * (δ₁ + δ₂) * y)

######## PAG143.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part143
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
section Freq
variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)
end Freq
end PAG.Part143

### PAG143::freqHom（def、110 行）
noncomputable def freqHom : DirichletCharacter ℂ (p ^ c) →* Multiplicative (ZMod (p ^ (c - k))) where
  toFun χ := Multiplicative.ofAdd (freq hkc h2k χ)
  map_one' := by rw [freq_one]; rfl
  map_mul' χ ψ := by rw [freq_mul]; rfl

######## PAG144.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part144
open ZMod Finset PAG.Part143
variable {p : ℕ} [hp : Fact p.Prime]
section Surj
variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)
end Surj
end PAG.Part144

### PAG144::exists_primitive（theorem、53 行）
theorem exists_primitive (c : ℕ) (hc : 2 ≤ c) : ∃ χ : DirichletCharacter ℂ (p ^ c), χ.IsPrimitive

######## PAG147.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part147
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part147

### PAG147::eq_of_dvd_not_dvd_div（theorem、17 行）
theorem eq_of_dvd_not_dvd_div (e d : ℕ) (hd : 0 < d) (he : e ∣ d)
    (h : ∀ q, q.Prime → q ∣ d → ¬ e ∣ d / q) : e = d

######## PAG151.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part151
open ZMod Finset
section Single
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117
variable {p : ℕ} [hp : Fact p.Prime]
end Single
end PAG.Part151

### PAG151::real_phase_sq（theorem、24 行）
theorem real_phase_sq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (h2 : χ ^ 2 = 1) :
    (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ 2 = χ (-1)

### PAG151::neg_one_mod4（theorem、61 行）
theorem neg_one_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : χ (-1) = -1

### PAG151::phase_mod8（theorem、111 行）
theorem phase_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt (8 : ℕ) : ℝ) : ℂ)) ^ 2 = χ (-1)

######## PAG152.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part152
open ZMod Finset Complex Real
end PAG.Part152

### PAG152::e4_pow（theorem、21 行）
theorem e4_pow (k : ℕ) : stdAddChar ((k : ZMod 4)) = I ^ k

### PAG152::gauss_mod4（theorem、25 行）
theorem gauss_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar = 2 * I

### PAG152::phase_mod4_eq（theorem、41 行）
theorem phase_mod4_eq (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ) = I

### PAG152::e8_one（theorem、49 行）
theorem e8_one : stdAddChar (1 : ZMod 8) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I)

### PAG152::e8_pow（theorem、56 行）
theorem e8_pow (k : ℕ) : stdAddChar ((k : ZMod 8)) = stdAddChar (1 : ZMod 8) ^ k

### PAG152::e8_sq（theorem、59 行）
theorem e8_sq : stdAddChar (1 : ZMod 8) ^ 2 = I

### PAG152::gauss_mod8（theorem、89 行）
theorem gauss_mod8 (χ : DirichletCharacter ℂ 8) (hχ : χ.IsPrimitive) :
    (χ (-1) = 1 → gaussSum χ stdAddChar = 2 * ((Real.sqrt 2 : ℝ) : ℂ)) ∧
    (χ (-1) = -1 → gaussSum χ stdAddChar = 2 * ((Real.sqrt 2 : ℝ) : ℂ) * I)

######## PAG154.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part154
open ZMod Finset PAG.Part118 PAG.Part127
variable {p : ℕ} [hp : Fact p.Prime]
section Even
variable {c m : ℕ} (hc : c = 2 * m)
end Even
end PAG.Part154

### PAG154::orderOf_gauss_freq（theorem、153 行）
theorem orderOf_gauss_freq {c m : ℕ} (hc : c = 2 * m) (hm : 1 ≤ m) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) (δ : ZMod (p ^ c))
    (hδ : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ m * y) = stdAddChar ((p : ZMod (p ^ c)) ^ m * δ * y)) :
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt ((p : ℝ) ^ c) : ℝ) : ℂ))
      = p ^ c * orderOf (χ (-δ) ^ (p ^ (c - 1)))

######## PAG165.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part165
open Complex Finset Polynomial Real
variable (p : ℕ) [hp : Fact p.Prime]
end PAG.Part165

### PAG165::zp（def、46 行）
noncomputable def zp : ℂ := Complex.exp (2 * π * I / p)

### PAG165::gb（def、54 行）
noncomputable def gb (b : ℕ) : ℂ := zp p ^ b - (zp p ^ b)⁻¹

### PAG165::gb_sin（theorem、112 行）
omit hp in
theorem gb_sin (b : ℕ) : gb p b = 2 * I * (Real.sin (2 * π * b / p) : ℂ)

######## PAG166.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part166
open Finset Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
end PAG.Part166

### PAG166::factorial_sq（theorem、146 行）
theorem factorial_sq (m : ℕ) (hpm : p = 2 * m + 1) : ((m.factorial : ZMod p)) ^ 2 = (-1) ^ (m + 1)

######## PAG169.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part169
open Finset
open ZMod PAG.Part125 PAG.Part126 PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)
end PAG.Part169

### PAG169::ord_split（theorem、18 行）
theorem ord_split (x : ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) (hx : x ^ (a * b) = 1) :
    orderOf x = orderOf (x ^ a) * orderOf (x ^ b)

######## PAG171.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part171
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part171

### PAG171::ω（def、32 行）
noncomputable def ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2

### PAG171::ω_sq（theorem、34 行）
theorem ω_sq : ω ^ 2 = -1 - ω

### PAG171::conj_ω（theorem、40 行）
theorem conj_ω : (starRingEnd ℂ) ω = -1 - ω

### PAG171::cube_eq_one（theorem、45 行）
theorem cube_eq_one (u : ℂ) (hu : u ^ 3 = 1) : u = 1 ∨ u = ω ∨ u = -1 - ω

### PAG171::primitive_of_ne_one（theorem、108 行）
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive

######## PAG172.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part172
open Complex Finset Polynomial PAG.Part171
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
end PAG.Part172

### PAG172::InZi（def、28 行）
def InZi (y : ℂ) : Prop := ∃ a b : ℤ, y = a + b * I

######## PAG180.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part180
open Complex Finset PAG.Part171 PAG.Part174 PAG.Part177 PAG.Part179
open ZMod (stdAddChar)
variable {P : ℕ} (μ : ZMod P)
variable {μ}
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]
end PAG.Part180

### PAG180::Rep2（def、17 行）
def Rep2 (w : ℂ) (e e' : ZMod P) : Prop :=
  ∃ C D : ℤ, w = C + D * ω ∧ ((C : ZMod P) + D * μ = e) ∧ ((C : ZMod P) + D * (-1 - μ) = e')

######## PAG184.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part184
open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part173 PAG.Part180 PAG.Part181 PAG.Part182 PAG.Part183
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part184

### PAG184::zOf（def、24 行）
noncomputable def zOf (χ : DirichletCharacter ℂ p) : ℂ := gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)

######## PAG185.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part185
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part185

### PAG185::sum_pow_lt（theorem、27 行）
theorem sum_pow_lt (e : ℕ) (he : e < p - 1) : ∑ x : ZMod p, x ^ e = 0

### PAG185::sqrt_ne_zero（theorem、264 行）
theorem sqrt_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0

### PAG185::aux_ineq（theorem、346 行）
theorem aux_ineq (k n i : ℕ) (hk : 0 < k) (hi1 : 1 ≤ i) (hin : i + 2 ≤ n) :
    0 < k * (n - 1) ∧ 0 < k * (n - i) ∧ k * (n - 1) < k * n ∧ k * (n - i) < k * n ∧
      k * n ≤ k * (n - 1) + k * (n - i)

######## PAG188.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part188
open Complex Finset
open ZMod (stdAddChar)
variable {ι : Type*} [Fintype ι] (P : ι → ℕ) [hP : ∀ i, Fact (P i).Prime]
end PAG.Part188

### PAG188::prod_root_of_root（theorem、51 行）
theorem prod_root_of_root {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∃ N : ℕ, 0 < N ∧ f i ^ N = 1) : ∃ N : ℕ, 0 < N ∧ (∏ i ∈ s, f i) ^ N = 1

######## PAG195.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part195
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194
end PAG.Part195

### PAG195::ne_one_of_isPrimitive（theorem、103 行）
theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : χ ≠ 1

### PAG195::factorsThrough_sq_iff_units（theorem、178 行）
theorem factorsThrough_sq_iff_units {N d : ℕ} [NeZero N] (hd : d ∣ N) (χ : DirichletCharacter ℂ N) :
    (χ ^ 2).FactorsThrough d ↔ ∀ u : (ZMod N)ˣ, ZMod.unitsMap hd u = 1 → χ u ^ 2 = 1

### PAG195::general_root_iff_units（theorem、196 行）
theorem general_root_iff_units (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1) ↔
      ∀ q : ℕ, q.Prime → ∀ hq : q ∣ N, ¬ q ^ 2 ∣ N →
        ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hq) u = 1 → χ u ^ 2 = 1

### PAG195::squarefull_root（theorem、207 行）
theorem squarefull_root (N : ℕ) [NeZero N] (hN : ∀ q : ℕ, q.Prime → q ∣ N → q ^ 2 ∣ N)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1

######## PAG196.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part196
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194
end PAG.Part196

### PAG196::zN（def、23 行）
noncomputable def zN {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)



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

### PAG198::gs（def、22 行）
noncomputable def gs {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ := if χ (-1) = 1 then 1 else I

### PAG198::level_two_trivial（theorem、107 行）
theorem level_two_trivial {L : ℕ} (hL : L = 2) (φ : DirichletCharacter ℂ L) : φ = 1

### PAG198::castHom_neg_one（theorem、402 行）
theorem castHom_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.castHom h (ZMod m) (-1) = -1

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

### PAG199::thmAConst（def、363 行）
noncomputable def thmAConst (N u c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) : ℂ :=
  ((Real.sqrt ((N : ℝ) / (Nat.totient (u * c) : ℝ)) : ℝ) : ℂ) *
    (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar) /
      ((Real.sqrt ((c * (c / d) : ℕ) : ℝ) : ℝ) : ℂ)

### PAG199::normSq_chi_natCast（theorem、493 行）
theorem normSq_chi_natCast {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Complex.normSq (Ψ (n : ZMod d)) = 1

######## PAG200.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part200
open Complex Finset PAG.Part199
open ZMod (stdAddChar)
end PAG.Part200

### PAG200::exists_split（theorem、23 行）
theorem exists_split {p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) : ∃ a x₂, ¬ p ∣ x₂ ∧ x = p ^ a * x₂

### PAG200::split_dvd（theorem、44 行）
theorem split_dvd {p a b x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ a * x ∣ p ^ b * y) : a ≤ b ∧ x ∣ y

######## PAG201.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part201
open Complex Finset PAG.Part199 PAG.Part200
open ZMod (stdAddChar)
end PAG.Part201

### PAG201::jt（def、191 行）
noncomputable def jt (c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) : ℂ :=
  gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar /
    ((Real.sqrt ((c * (c / d) : ℕ) : ℝ) : ℝ) : ℂ)

######## PAG202.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part202
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part202

### PAG202::normSq_chi_unit（theorem、188 行）
theorem normSq_chi_unit {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (a : (ZMod d)ˣ) :
    Complex.normSq (Ψ a) = 1

######## PAG204.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part204
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202 PAG.Part203
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part204

### PAG204::normSq_mixed_coef（theorem、446 行）
theorem normSq_mixed_coef (M₁ M₂ c₁ c₂ d : ℕ) [NeZero M₁] [NeZero M₂] [NeZero c₁] [NeZero c₂] [NeZero d]
    (A : DirichletCharacter ℂ c₁) (B : DirichletCharacter ℂ c₂) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hcop₁ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁)).Coprime c₁)
    (hcop₂ : (Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂)).Coprime c₂) :
    Complex.normSq ((((Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℕ) : ℂ) *
          ((Real.sqrt (Nat.totient (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d)) : ℝ) : ℂ) /
          ((Real.sqrt ((Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ)) : ℝ) : ℂ) *
        (A⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₁ / c₁) : ℕ) : ZMod c₁) *
          B⁻¹ ((Nat.lcm (M₁ / c₁) (M₂ / c₂) / (M₂ / c₂) : ℕ) : ZMod c₂)) *
        (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar))) =
      (Nat.gcd (M₁ / c₁) (M₂ / c₂) : ℝ) ^ 2 * (Nat.totient (Nat.lcm (M₁ / c₁) (M₂ / c₂) * d) : ℝ) *
          ((c₁ : ℝ) * c₂) / ((Nat.totient M₁ : ℝ) * Nat.totient M₂ * d)

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

### PAG208::ket_coef_ne_zero（theorem、352 行）
theorem ket_coef_ne_zero (s c : ℕ) [NeZero c] (hs : s ≠ 0) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (((Real.sqrt (Nat.totient (s * c)))⁻¹ : ℝ) : ℂ) * (s : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar ≠ 0

######## PAG209.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part209
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part209

### PAG209::kcoef_ne_zero（theorem、34 行）
theorem kcoef_ne_zero (M c : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : kcoef M c χ ≠ 0

### PAG209::normSq_kcoef（theorem、47 行）
theorem normSq_kcoef (M c : ℕ) [NeZero c] (hM : M ≠ 0) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    Complex.normSq (kcoef M c χ) = ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M

### PAG209::kcoef_div（theorem、367 行）
theorem kcoef_div (M c t : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (ht : t ≠ 0)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    kcoef M c χ / kcoef (M * t) c χ =
      ((Real.sqrt (Nat.totient (M * t)) / (Real.sqrt (Nat.totient M) * t) : ℝ) : ℂ)

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

### PAG210::kcoef_mul_kcoef_inv（theorem、181 行）
theorem kcoef_mul_kcoef_inv (M c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    kcoef M c χ * kcoef M c χ⁻¹ = χ (-1) * (((M / c : ℕ) : ℂ) ^ 2 * c / Nat.totient M)

######## PAG212.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part212
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part212

### PAG212::mul_div_div_cancel（theorem、77 行）
theorem mul_div_div_cancel (s r e : ℕ) (hs : 0 < s) (her : e ∣ r) : s * r / e / s = r / e

######## PAG213.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part213
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part213

### PAG213::sum_normSq_char（theorem、34 行）
theorem sum_normSq_char (c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) :
    ∑ z : ZMod c, (Complex.normSq (χ z) : ℂ) = (Nat.totient c : ℂ)

### PAG213::sum_normSq_char_comp（theorem、43 行）
theorem sum_normSq_char_comp (c M : ℕ) [NeZero c] [NeZero M] (hc : c ∣ M) (χ : DirichletCharacter ℂ c) :
    ∑ y : ZMod M, (Complex.normSq (χ (ZMod.castHom hc (ZMod c) y)) : ℂ) =
      ((M / c : ℕ) : ℂ) * (Nat.totient c : ℂ)

######## PAG214.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part214
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part214

### PAG214::div_mul_div_of_dvd（theorem、55 行）
theorem div_mul_div_of_dvd {u v w : ℕ} (hv : 0 < v) (hw : 0 < w) (hvu : v ∣ u) (hwv : w ∣ v) :
    u / v * (v / w) = u / w

### PAG214::gblock（def、148 行）
noncomputable def gblock (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (v : ℕ) : ZMod N → ℂ :=
  gbas (N / (v * c)) (v * c) N (liftc χ⁻¹ (v * c))

######## PAG215.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part215
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part215

### PAG215::div_ne_zero_of_dvd（theorem、28 行）
theorem div_ne_zero_of_dvd {N u : ℕ} (hN : N ≠ 0) (hu : u ∣ N) : N / u ≠ 0

### PAG215::chi_eq_zero_of_rad（theorem、317 行）
theorem chi_eq_zero_of_rad {L c x : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ L → p ∣ c) (hx : x ∣ L) (hx1 : x ≠ 1) : χ (x : ZMod c) = 0

######## PAG216.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part216
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part216

### PAG216::gblock_shell_inj（theorem、31 行）
theorem gblock_shell_inj {N c v w : ℕ} [NeZero N] (hc : 0 < c) (hcN : c ∣ N) (hv : v ∣ N / c)
    (hw : w ∣ N / c) (e : N / (v * c) = N / (w * c)) : v = w

######## PAG217.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part217
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part217

### PAG217::fcoef（def、63 行）
noncomputable def fcoef (N c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (u : ℕ) : ℂ :=
  ((Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient (N / u)) : ℝ) : ℂ) * ((N / u / c : ℕ) : ℂ) *
    χ⁻¹ (-1) * gaussSum χ stdAddChar

######## PAG218.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part218
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part218

### PAG218::dft_dil（theorem、304 行）
theorem dft_dil {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : 𝓕 (dil a f) = dil a⁻¹ (𝓕 f)

######## PAG222.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part222
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part222

### PAG222::twistConst（def、168 行）
noncomputable def twistConst {c : ℕ} [NeZero c] (χ χ' : DirichletCharacter ℂ c) : ℂ :=
  (χ'⁻¹ (-1) * gaussSum χ' stdAddChar) / (χ⁻¹ (-1) * gaussSum χ stdAddChar)

######## PAG234.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part234
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part234

### PAG234::centralizer_bot_eq_top（theorem、330 行）
theorem centralizer_bot_eq_top {X : Type*} :
    Subalgebra.centralizer ℂ ((⊥ : Subalgebra ℂ (Module.End ℂ (X → ℂ))) : Set (Module.End ℂ (X → ℂ))) = ⊤

### PAG234::centralizer_map_leftHom（theorem、340 行）
theorem centralizer_map_leftHom {a b : ℕ} [NeZero a] [NeZero b] (B : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))) :
    Subalgebra.centralizer ℂ ((B.map (leftHom a b) : Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
      Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (Subalgebra.centralizer ℂ (B : Set (Module.End ℂ (ZMod a → ℂ)))).map (leftHom a b) ⊔
        (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))).map (rightHom a b)

### PAG234::centralizer_map_rightHom（theorem、351 行）
theorem centralizer_map_rightHom {a b : ℕ} [NeZero a] [NeZero b] (B' : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))) :
    Subalgebra.centralizer ℂ ((B'.map (rightHom a b) : Subalgebra ℂ (Module.End ℂ (ZMod a × ZMod b → ℂ))) :
      Set (Module.End ℂ (ZMod a × ZMod b → ℂ))) =
      (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))).map (leftHom a b) ⊔
        (Subalgebra.centralizer ℂ (B' : Set (Module.End ℂ (ZMod b → ℂ)))).map (rightHom a b)

######## PAG240.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part240
open PAG.Part218 PAG.Part226 PAG.Part232 PAG.Part233 PAG.Part234 PAG.Part235
open scoped TensorProduct
end PAG.Part240

### PAG240::prodList（def、26 行）
@[implicit_reducible] def prodList : List ℕ+ → ℕ
  | [] => 1
  | a :: l => (a : ℕ) * prodList l

### PAG240::CoprimeList（def、50 行）
def CoprimeList (l : List ℕ+) : Prop := l.Pairwise (fun a b : ℕ+ => Nat.Coprime (a : ℕ) (b : ℕ))

### PAG240::liftL（def、175 行）
def liftL : (l : List ℕ+) → CoprimeList l → (k : Fin l.length) → ZMod (prodList l) →
    ZMod ((l.get k : ℕ+) : ℕ) → ZMod (prodList l)
  | _ :: _, h, ⟨0, _⟩, x, y => (ZMod.chineseRemainder h.head).symm (y, (ZMod.chineseRemainder h.head x).2)
  | _ :: l, h, ⟨k + 1, hk⟩, x, y => (ZMod.chineseRemainder h.head).symm
      ((ZMod.chineseRemainder h.head x).1,
        liftL l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩ (ZMod.chineseRemainder h.head x).2 y)

### PAG240::eq_bot_of_one（theorem、289 行）
theorem eq_bot_of_one (S : Subalgebra ℂ (Module.End ℂ (ZMod 1 → ℂ))) : S = ⊥

######## PAG247.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part247
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part247

### PAG247::testFn（def、145 行）
noncomputable def testFn (N : ℕ) : ZMod N → ℂ := Pi.single (1 : ZMod N) (1 : ℂ) - Pi.single (-1 : ZMod N) (1 : ℂ)

######## PAG249.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part249
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part249

### PAG249::half_mul_succ_add_one（theorem、82 行）
theorem half_mul_succ_add_one {k : ℕ} (hk : 1 ≤ k) : k * (k + 1) / 2 + 1 = 2 * k + (k - 1) * (k - 2) / 2

### PAG249::half_mul_succ_add_three（theorem、95 行）
theorem half_mul_succ_add_three {k : ℕ} (hk : 2 ≤ k) : k * (k + 1) / 2 + 3 = 3 * k + (k - 2) * (k - 3) / 2

### PAG249::ineq_odd（theorem、193 行）
theorem ineq_odd {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : 2 * (x * y) + x ^ 2 + 1 < x ^ 2 * y + y ^ 2 + y + 2

### PAG249::ineq_two（theorem、200 行）
theorem ineq_two {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y) : 2 * (x * y) + x ^ 2 ≤ x ^ 2 * y + 4

######## PAG250.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part250
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part250

### PAG250::dft_single（theorem、374 行）
theorem dft_single {N : ℕ} [NeZero N] (a k : ZMod N) :
    𝓕 (Pi.single a (1 : ℂ)) k = stdAddChar (-(a * k))

######## PAG253.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### PAG253::kUnit（def、34 行）
def kUnit {N : ℕ} (n : ℕ) (h : n.Coprime N) : (ZMod N)ˣ := (ZMod.unitOfCoprime n h)⁻¹

### PAG253::kUnit_mul_natCast（theorem、37 行）
theorem kUnit_mul_natCast {N : ℕ} (n : ℕ) (h : n.Coprime N) :
    ((kUnit n h : (ZMod N)ˣ) : ZMod N) * (n : ZMod N) = 1

### PAG253::kUnit_one（theorem、43 行）
theorem kUnit_one {N : ℕ} (h : (1 : ℕ).Coprime N) : kUnit 1 h = 1

### PAG253::kUnit_mul（theorem、50 行）
theorem kUnit_mul {N : ℕ} {a b : ℕ} (ha : a.Coprime N) (hb : b.Coprime N) (hab : (a * b).Coprime N) :
    kUnit (a * b) hab = kUnit a ha * kUnit b hb

### PAG253::unitsMap_kUnit（theorem、59 行）
theorem unitsMap_kUnit {N M : ℕ} (hNM : N ∣ M) (n : ℕ) (hM : n.Coprime M) :
    ZMod.unitsMap hNM (kUnit n hM) = kUnit n (Nat.Coprime.coprime_dvd_right hNM hM)

### PAG253::exists_kUnit_eq（theorem、68 行）
theorem exists_kUnit_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    ∃ (n : ℕ) (h : n.Coprime N), 0 < n ∧ kUnit n h = a

### PAG253::kUnit_mem_of_prime（theorem、81 行）
theorem kUnit_mem_of_prime {N : ℕ} (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) :
    ∀ (n : ℕ) (hn : n.Coprime N), kUnit n hn ∈ S

### PAG253::commSubmonoid（def、134 行）
def commSubmonoid {G : Type*} [CommGroup G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ)) : Submonoid G where
  carrier := {g | U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U}
  one_mem' := by
    show U ∘ₗ PAG.transl 1 = PAG.transl 1 ∘ₗ U
    rw [transl_one, LinearMap.comp_id, LinearMap.id_comp]
  mul_mem' := by
    intro g h hg hh
    have hg' : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U := hg
    have hh' : U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U := hh
    show U ∘ₗ PAG.transl (g * h) = PAG.transl (g * h) ∘ₗ U
    apply LinearMap.ext
    intro f
    have e1 := LinearMap.congr_fun hg' (PAG.transl h f)
    have e2 := LinearMap.congr_fun hh' f
    simp only [LinearMap.comp_apply] at e1 e2
    simp only [transl_mul, LinearMap.comp_apply]
    rw [e1, e2]

### PAG253::exists_cls_near（theorem、213 行）
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε

### PAG253::invariant_kUnit（theorem、305 行）
theorem invariant_kUnit {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u) :
    ∀ (n : ℕ) (hn : n.Coprime M), 0 < n → ∀ (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit n (Nat.Coprime.coprime_dvd_right hNM hn)) (u - Real.log n) = f k u

### PAG253::eq_of_prime_invariant'（theorem、371 行）
theorem eq_of_prime_invariant' {N : ℕ} [NeZero N] (f : (ZMod N)ˣ → ℝ → ℂ) (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p hpN) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂

### PAG253::eq_of_euler（theorem、379 行）
theorem eq_of_euler {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (χ₁ χ₂ : (ZMod N)ˣ →* ℂˣ) (l₁ l₂ : ℝ)
    (h : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M),
      (χ₁ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₁ * Real.log p : ℝ) : ℂ) * Complex.I) =
        (χ₂ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I)) :
    χ₁ = χ₂ ∧ l₁ = l₂

### PAG253::primeShift（def、454 行）
noncomputable def primeShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * kUnit p hp) (u - Real.log p)

### PAG253::primeShiftInv（def、458 行）
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)

### PAG253::globalInv（def、462 行）
def globalInv {N : ℕ} (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k⁻¹ (-u)

### PAG253::scaleShift（def、465 行）
def scaleShift {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k (u + s)

### PAG253::globalInv_scaleShift_globalInv（theorem、499 行）
theorem globalInv_scaleShift_globalInv {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    globalInv (scaleShift s (globalInv F)) = scaleShift (-s) F

######## PAG254.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part254
end PAG.Part254

### PAG254::dense_logSet（theorem、75 行）
theorem dense_logSet : Dense logSet

### PAG254::dense_closure_log_two_three（theorem、268 行）
theorem dense_closure_log_two_three :
    Dense ((AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)

######## PAG255.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part255
open PAG.Part253 Nat
end PAG.Part255

### PAG255::kUnit_congr（theorem、131 行）
theorem kUnit_congr {N : ℕ} {m n : ℕ} (hm : m.Coprime N) (hn : n.Coprime N)
    (h : (m : ZMod N) = (n : ZMod N)) : kUnit m hm = kUnit n hn
