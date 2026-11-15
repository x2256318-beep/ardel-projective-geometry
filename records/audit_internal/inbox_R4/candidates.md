
######## PAG2.lean
-- 文脈（open・variable・namespace の行の写し）
open Complex Finset
namespace PAG.Kloosterman
variable {N : ℕ} [NeZero N]
open scoped Classical in
end PAG.Kloosterman

### PAG2::Wpow（def、124 行）
noncomputable def Wpow (χ : DirichletCharacter ℂ N) (r : ℕ) : ℂ :=
  ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 * gaussSum χ ZMod.stdAddChar ^ r
    / (Real.sqrt N : ℂ) ^ r

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

### PAG7::push（def、153 行）
noncomputable def push (p : ZMod N) (f : ZMod N → ℂ) (w : ZMod N) : ℂ :=
  ∑ z, if p * z = w then f z else 0

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

### PAG8::unit_mul_eq_of_ker（theorem、74 行）
theorem unit_mul_eq_of_ker (u : (ZMod (p ^ (n + 1)))ˣ)
    (hu : ZMod.unitsMap (pow_dvd_pow p (Nat.le_succ n)) u = 1)
    (s : ZMod (p ^ (n + 1))) (hs : ¬ IsUnit s) : (u : ZMod (p ^ (n + 1))) * s = s

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

### PAG9::inv_apply_neg_one（theorem、45 行）
omit [NeZero N] in
theorem inv_apply_neg_one (χ : MulChar (ZMod N) ℂ) : χ⁻¹ (-1) = χ (-1)

### PAG9::conj_gaussSum（theorem、56 行）
theorem conj_gaussSum (χ : MulChar (ZMod N) ℂ) :
    starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar

### PAG9::gauss_mul_gauss_inv_of_norm（theorem、83 行）
theorem gauss_mul_gauss_inv_of_norm (χ : MulChar (ZMod N) ℂ) (M : ℝ)
    (hM : Complex.normSq (gaussSum χ ZMod.stdAddChar) = M) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = χ (-1) * M

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

### PAG14::conductor_pow_pn_dvd_p（theorem、34 行）
theorem conductor_pow_pn_dvd_p (hodd : Odd p) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    (χ ^ (p ^ n)).conductor ∣ p

######## PAG16.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part16
open ZMod Finset
variable {N : ℕ} [NeZero N]
variable {p n : ℕ} [hp : Fact p.Prime]
end PAG.Part16

### PAG16::gauss_mul_gauss_inv_eq（theorem、36 行）
theorem gauss_mul_gauss_inv_eq {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N

### PAG16::normSq_gaussSum（theorem、53 行）
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N

######## PAG18.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part18
open ZMod Finset PAG.Part17
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part18

### PAG18::stdAddChar_scale（theorem、16 行）
theorem stdAddChar_scale (N M d : ℕ) [NeZero N] [NeZero M] (hN : N = M * d) (hd : d ≠ 0) (j : ℤ) :
    stdAddChar (((d : ℤ) * j : ℤ) : ZMod N) = stdAddChar ((j : ℤ) : ZMod M)

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

### PAG30::star_chi_neg_one（theorem、29 行）
omit hp in
theorem star_chi_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : starRingEnd ℂ (χ (-1)) = χ (-1)

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

### PAG31::conductor_ne_two（theorem、233 行）
theorem conductor_ne_two {N : ℕ} (χ : DirichletCharacter ℂ N) : χ.conductor ≠ 2

######## PAG33.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part33
open ZMod Finset PAG.Part32
open Classical
section Factor
variable {N : ℕ} [NeZero N]
end Factor
section Count
variable {p : ℕ} [hp : Fact p.Prime] {c : ℕ}
end Count
end PAG.Part33

### PAG33::conductor_eq_iff（theorem、115 行）
theorem conductor_eq_iff {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ c + 1) (ψ : DirichletCharacter ℂ (p ^ (c + 1))) :
    ψ.conductor = p ^ m ↔ ψ.FactorsThrough (p ^ m) ∧ ¬ ψ.FactorsThrough (p ^ (m - 1))

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

### PAG37::unitsMap_five（theorem、34 行）
theorem unitsMap_five {m c : ℕ} (h : m ≤ c) :
    ZMod.unitsMap (pow_dvd_pow 2 h) (five c) = five m

### PAG37::unitsMap_neg_one（theorem、78 行）
theorem unitsMap_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.unitsMap h (-1) = -1

### PAG37::toFour（def、88 行）
noncomputable def toFour (d : ℕ) : (ZMod (2 ^ (d + 3)))ˣ →* (ZMod (2 ^ 2))ˣ :=
  ZMod.unitsMap (pow_dvd_pow 2 (show 2 ≤ d + 3 by omega))

######## PAG44.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part44
open ZMod Finset PAG.Part37 Complex
variable {d : ℕ}
end PAG.Part44

### PAG44::zeta（def、61 行）
noncomputable def zeta (d : ℕ) : ℂ := exp (2 * Real.pi * I / ((2 ^ (d + 1) : ℕ) : ℂ))

######## PAG47.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part47
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part40
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part47

### PAG47::exists_prim_of_conductor（theorem、19 行）
omit hp in
theorem exists_prim_of_conductor {M : ℕ} (χ : DirichletCharacter ℂ M) {N : ℕ} (hN : χ.conductor = N) :
    ∃ ψ : DirichletCharacter ℂ N, ψ.IsPrimitive ∧ ∃ h : N ∣ M, DirichletCharacter.changeLevel h ψ = χ

### PAG47::conductor_eq_pow（theorem、35 行）
theorem conductor_eq_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    ∃ i ≤ n + 1, χ.conductor = p ^ i

### PAG47::normSq_coef_of（theorem、40 行）
theorem normSq_coef_of {N : ℕ} [NeZero N] (F k : ZMod N → ℂ) (C : ℂ) (lam : ℝ) (hF : F = C • k)
    (hk : ∑ x, Complex.normSq (k x) = 1) (hn : ∑ x, Complex.normSq (F x) = lam) : Complex.normSq C = lam

######## PAG52.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part52
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part31 PAG.Part48 PAG.Part49
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
end PAG.Part52

### PAG52::ip（def、18 行）
noncomputable def ip {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

######## PAG61.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part61
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part32 Complex
variable {p : ℕ} [hp : Fact p.Prime] (c : ℕ)
variable (hp2 : p ≠ 2)
end PAG.Part61

### PAG61::phi（abbrev、21 行）
abbrev phi : ℕ := Fintype.card (ZMod (p ^ (c + 1)))ˣ

######## PAG64.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part64
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part47 PAG.Part48 PAG.Part50
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part64

### PAG64::exists_conductor_pow（theorem、42 行）
theorem exists_conductor_pow {n : ℕ} (χ : DirichletCharacter ℂ (p ^ (n + 1))) : ∃ i, χ.conductor = p ^ i

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

### PAG93::conv_add_right'（theorem、21 行）
theorem conv_add_right' {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv f (g + h) = conv f g + conv f h

######## PAG98.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part98
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part51 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part59 PAG.Part89 PAG.Part90
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part98

### PAG98::Equivariant（def、27 行）
def Equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), f (u * x) = α u * f x

######## PAG147.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part147
open ZMod Finset
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part147

### PAG147::eq_of_dvd_not_dvd_div（theorem、17 行）
theorem eq_of_dvd_not_dvd_div (e d : ℕ) (hd : 0 < d) (he : e ∣ d)
    (h : ∀ q, q.Prime → q ∣ d → ¬ e ∣ d / q) : e = d

######## PAG171.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part171
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part171

### PAG171::conj_jacobi（theorem、79 行）
theorem conj_jacobi (χ : MulChar (ZMod p) ℂ) : (starRingEnd ℂ) (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹

######## PAG173.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part173
open Finset Complex
open ZMod (stdAddChar)
open ZMod PAG.Part125 PAG.Part126 PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part120
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)
end PAG.Part173

### PAG173::gauss_inv_pair（theorem、42 行）
theorem gauss_inv_pair {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt N : ℝ) : ℂ)) * (gaussSum χ⁻¹ stdAddChar / ((Real.sqrt N : ℝ) : ℂ))
      = χ (-1)

######## PAG174.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part174
open Complex Finset PAG.Part171
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part174

### PAG174::not_root_mul（theorem、101 行）
theorem not_root_mul (A B : ℂ) (hA : ∀ N : ℕ, 0 < N → A ^ N ≠ 1) (M : ℕ) (hM : 0 < M) (hB : B ^ M = 1) :
    ∀ N : ℕ, 0 < N → (A * B) ^ N ≠ 1

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

### PAG185::sqrt_ne_zero（theorem、264 行）
theorem sqrt_ne_zero : ((Real.sqrt p : ℝ) : ℂ) ≠ 0

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

### PAG190::exists_nodes（theorem、187 行）
omit hp in
theorem exists_nodes (n d : ℕ) (hd : d = n.totient) :
    ∃ cc : Fin d → ℕ, Function.Injective cc ∧ ∀ k, cc k < n ∧ (cc k).Coprime n

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

### PAG196::zN（def、23 行）
noncomputable def zN {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)



######## PAG198.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part198
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196
end PAG.Part198

### PAG198::legendre_values（theorem、77 行）
theorem legendre_values {r L : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hL : L = r)
    (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) (a : ℤ) :
    φ (a : ZMod L) = (legendreSym r a : ℂ)

### PAG198::odd_base_values（theorem、85 行）
theorem odd_base_values {r k : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (φ : DirichletCharacter ℂ (r ^ k)) (hφ : φ.IsPrimitive) (h2 : φ ^ 2 = 1) :
    k = 1 ∧ ∀ a : ℤ, φ (a : ZMod (r ^ k)) = (legendreSym r a : ℂ)

### PAG198::two_ne_zero_zmod（theorem、302 行）
theorem two_ne_zero_zmod {t : ℕ} [ht : Fact t.Prime] (ht2 : t ≠ 2) : ((2 : ℤ) : ZMod t) ≠ 0

### PAG198::neg_one_ne_zero_zmod（theorem、308 行）
theorem neg_one_ne_zero_zmod {t : ℕ} [ht : Fact t.Prime] : ((-1 : ℤ) : ZMod t) ≠ 0

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

### PAG199::thmAConst（def、363 行）
noncomputable def thmAConst (N u c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) : ℂ :=
  ((Real.sqrt ((N : ℝ) / (Nat.totient (u * c) : ℝ)) : ℝ) : ℂ) *
    (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar) /
      ((Real.sqrt ((c * (c / d) : ℕ) : ℝ) : ℝ) : ℂ)

### PAG199::normSq_chi_natCast（theorem、493 行）
theorem normSq_chi_natCast {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Complex.normSq (Ψ (n : ZMod d)) = 1

######## PAG201.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part201
open Complex Finset PAG.Part199 PAG.Part200
open ZMod (stdAddChar)
end PAG.Part201

### PAG201::totient_mul_of_primes（theorem、53 行）
theorem totient_mul_of_primes (M : ℕ) : ∀ t : ℕ, (∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) →
    Nat.totient (M * t) = Nat.totient M * t

### PAG201::totient_ratio（theorem、78 行）
theorem totient_ratio {c M : ℕ} (hc : c ∣ M) (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) :
    Nat.totient M * c = Nat.totient c * M

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

######## PAG204.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part204
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201 PAG.Part202 PAG.Part203
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part204

### PAG204::div_mul_aux（theorem、51 行）
theorem div_mul_aux {s S : ℕ} (hs : 0 < s) (hsS : s ∣ S) (t : ℕ) : S * t / s = S / s * t

######## PAG207.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part207
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part207

### PAG207::Radial（def、21 行）
def Radial {N : ℕ} (f : ZMod N → ℂ) : Prop := ∀ (a : (ZMod N)ˣ) (x : ZMod N), f ((a : ZMod N) * x) = f x



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

### PAG208::conductor_changeLevel_inv（theorem、390 行）
theorem conductor_changeLevel_inv (n c : ℕ) [NeZero n] (hcn : c ∣ n) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : ((χ⁻¹).changeLevel hcn).conductor = c

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

######## PAG211.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part211
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part211

### PAG211::span_ketFam（theorem、293 行）
theorem span_ketFam (N : ℕ) [NeZero N] : ⊤ ≤ Submodule.span ℂ (Set.range (ketFam N))

######## PAG212.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part212
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part212

### PAG212::kcoef_inv（theorem、43 行）
theorem kcoef_inv (M c : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (kcoef M c χ)⁻¹ = gaussSum χ⁻¹ stdAddChar * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) / (M : ℂ)

### PAG212::mul_div_div_cancel（theorem、77 行）
theorem mul_div_div_cancel (s r e : ℕ) (hs : 0 < s) (her : e ∣ r) : s * r / e / s = r / e

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

### PAG214::totient_mul_eq_iff（theorem、292 行）
theorem totient_mul_eq_iff (s c : ℕ) (hs : s ≠ 0) (hc : c ≠ 0) :
    Nat.totient (s * c) = s * Nat.totient c ↔ ∀ p : ℕ, p.Prime → p ∣ s → p ∣ c

### PAG214::totient_mul_eq_iff'（theorem、362 行）
theorem totient_mul_eq_iff' (M t : ℕ) (hM : M ≠ 0) (ht : t ≠ 0) :
    Nat.totient (M * t) = Nat.totient M * t ↔ ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M

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

### PAG218::sum_units_char（theorem、32 行）
open Classical in
theorem sum_units_char (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ∑ a : (ZMod N)ˣ, ψ (a : ZMod N) = if ψ = 1 then (Nat.totient N : ℂ) else 0

### PAG218::liftc_mul_liftc_inv（theorem、52 行）
theorem liftc_mul_liftc_inv (N : ℕ) {c : ℕ} (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ) :
    liftc χ N (a : ZMod N) * liftc χ⁻¹ N (a : ZMod N) = 1

### PAG218::dil（def、68 行）
def dil {N : ℕ} (a : (ZMod N)ˣ) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => (a : ZMod N) * x)

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

######## PAG219.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part219
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part219

### PAG219::blockSpan（def、33 行）
noncomputable def blockSpan (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) : Submodule ℂ (ZMod N → ℂ) :=
  Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w)

### PAG219::sum_changeLevel_mul_conj（theorem、107 行）
theorem sum_changeLevel_mul_conj {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (m : ℕ) [NeZero m]
    (hdvd : c ∣ m) :
    ∑ y : ZMod m, χ.changeLevel hdvd y * starRingEnd ℂ (χ ((y.val : ℕ) : ZMod c)) = Nat.totient m

######## PAG220.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part220
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part220

### PAG220::layerPart_iSupIndep（theorem、493 行）
theorem layerPart_iSupIndep (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) :
    iSupIndep (fun d : layerIdx c (N / c) => layerPart N c χ (d : ℕ))

### PAG220::iSup_layerPart（theorem、518 行）
theorem iSup_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    (⨆ d ∈ layerIdx c (N / c), layerPart N c χ d) = blockSpan N c χ

### PAG220::block_decomposition（theorem、540 行）
theorem block_decomposition (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    iSupIndep (fun d : layerIdx c (N / c) => layerPart N c χ (d : ℕ)) ∧
      (⨆ d ∈ layerIdx c (N / c), layerPart N c χ d) = blockSpan N c χ ∧
      (∀ d ∈ layerIdx c (N / c), layerPart N c χ d ≠ ⊥ ∧ ShellInvariant (layerPart N c χ d) ∧
        ∀ W : Submodule ℂ (ZMod N → ℂ), ShellInvariant W → W ≤ layerPart N c χ d →
          W = ⊥ ∨ W = layerPart N c χ d) ∧
      (layerIdx c (N / c)).card = ∏ p ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization p + 1)

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

######## PAG224.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part224
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part224

### PAG224::top_shellInvariant（theorem、379 行）
theorem top_shellInvariant (N : ℕ) [NeZero N] : ShellInvariant (⊤ : Submodule ℂ (ZMod N → ℂ))

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

######## PAG229.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part229
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part229

### PAG229::herm（def、34 行）
noncomputable def herm (N : ℕ) [NeZero N] (f g : ZMod N → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

### PAG229::herm_add_left（theorem、44 行）
theorem herm_add_left (N : ℕ) [NeZero N] (f f' g : ZMod N → ℂ) :
    herm N (f + f') g = herm N f g + herm N f' g

### PAG229::herm_add_right（theorem、50 行）
theorem herm_add_right (N : ℕ) [NeZero N] (f g g' : ZMod N → ℂ) :
    herm N f (g + g') = herm N f g + herm N f g'

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

######## PAG236.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part236
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part236

### PAG236::dvd_conductor_of_eq_mul（theorem、80 行）
theorem dvd_conductor_of_eq_mul {N k l : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hk : k ∣ N) (hl : l ∣ N)
    (ψ₁ : DirichletCharacter ℂ k) (ψ₂ : DirichletCharacter ℂ l) (hψ₁ : ψ₁.IsPrimitive) (hkl : Nat.Coprime k l)
    (h : χ = DirichletCharacter.changeLevel hk ψ₁ * DirichletCharacter.changeLevel hl ψ₂) :
    k ∣ χ.conductor

######## PAG241.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part241
open PAG.Part218 PAG.Part226 PAG.Part232 PAG.Part233 PAG.Part234 PAG.Part235 PAG.Part240
open scoped TensorProduct
section TP
variable {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra ℂ (A i)]
variable [Fintype ι]
end TP
section TPR
variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]
end TPR
section Fam
variable (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
end Fam
section Fam2
variable (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
end Fam2
end PAG.Part241

### PAG241::range_tpLift（theorem、126 行）
theorem range_tpLift (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) :
    (tpLift φ hφ).range = ⨆ i, (φ i).range

######## PAG247.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part247
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part247

### PAG247::three_le_div（theorem、193 行）
theorem three_le_div {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) ≠ 1) : 3 ≤ N / s

######## PAG248.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part248
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part248

### PAG248::not_dvd_two_mul（theorem、144 行）
theorem not_dvd_two_mul {N t : ℕ} [NeZero N] (ht : t ∣ N) (hφ : Nat.totient (N / t) ≠ 1) : ¬ N ∣ 2 * t

######## PAG253.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### PAG253::unitsMap_kUnit（theorem、59 行）
theorem unitsMap_kUnit {N M : ℕ} (hNM : N ∣ M) (n : ℕ) (hM : n.Coprime M) :
    ZMod.unitsMap hNM (kUnit n hM) = kUnit n (Nat.Coprime.coprime_dvd_right hNM hM)

### PAG253::scaleShift（def、465 行）
def scaleShift {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k (u + s)

### PAG253::unitShift（def、468 行）
def unitShift {N : ℕ} (a : (ZMod N)ˣ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F (k * a) u

### PAG253::ipG（def、515 行）
noncomputable def ipG {G : Type*} [Fintype G] (f g : G → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

######## PAG255.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part255
open PAG.Part253 Nat
end PAG.Part255

### PAG255::units_eq_of_coprime_parts（theorem、309 行）
theorem units_eq_of_coprime_parts {N A B : ℕ} [NeZero N] (hN : N = A * B) (hAB : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (b c : (ZMod N)ˣ)
    (h1 : ZMod.unitsMap hA b = ZMod.unitsMap hA c) (h2 : ZMod.unitsMap hB b = ZMod.unitsMap hB c) :
    b = c

######## PAG256.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part256
open ZMod Complex Finset
variable {N : ℕ} [NeZero N]
open Classical in
end PAG.Part256

### PAG256::rootNum（def、125 行）
open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

### PAG256::rootNum_eq（theorem、129 行）
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)

### PAG256::JH_eq_rootNum_mul（theorem、161 行）
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u

### PAG256::normSq_rootNum（theorem、168 行）
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1

### PAG256::JH_eq_rootNum_mul_any（theorem、228 行）
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u

### PAG256::exists_primitive_even_five（theorem、259 行）
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1

### PAG256::removal_counterexample_normSq（theorem、308 行）
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2

######## PAG257.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part257
open ZMod Complex Finset PAG.Part256
variable {N : ℕ} [NeZero N]
open Classical in
open Classical in
open Classical in
end PAG.Part257

### PAG257::extL（def、61 行）
open Classical in
noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]

### PAG257::charU（def、96 行）
def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

### PAG257::extL_charU（theorem、99 行）
theorem extL_charU (χ : DirichletCharacter ℂ N) : extL (charU χ) = (χ : ZMod N → ℂ)

### PAG257::TopL_charU（theorem、107 行）
theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ

### PAG257::ip（def、116 行）
noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

### PAG257::ip_smul_smul（theorem、119 行）
theorem ip_smul_smul (a b : ℂ) (f g : (ZMod N)ˣ → ℂ) :
    ip (a • f) (b • g) = (starRingEnd ℂ) a * b * ip f g

### PAG257::ip_sum_sum（theorem、128 行）
theorem ip_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℂ) (v : ι → (ZMod N)ˣ → ℂ)
    (b : κ → ℂ) (w : κ → (ZMod N)ˣ → ℂ) :
    ip (N := N) (∑ i, a i • v i) (∑ j, b j • w j) =
      ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * ip (v i) (w j)

### PAG257::ip_charU（theorem、145 行）
open Classical in
theorem ip_charU (χ ψ : DirichletCharacter ℂ N) :
    ip (charU χ) (charU ψ) = if χ = ψ then (Nat.totient N : ℂ) else 0

### PAG257::Vprim（def、162 行）
noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)

### PAG257::Vimprim（def、166 行）
noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)

### PAG257::TopL_mem_Vprim（theorem、170 行）
theorem TopL_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : TopL f ∈ Vprim N

### PAG257::TopL_mem_Vimprim（theorem、180 行）
theorem TopL_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : TopL f ∈ Vimprim N

### PAG257::rootNum_ne_zero（theorem、190 行）
theorem rootNum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNum χ ≠ 0

### PAG257::map_TopL_Vprim（theorem、197 行）
theorem map_TopL_Vprim : (Vprim N).map TopL = Vprim N

### PAG257::ip_TopL_charU_prim（theorem、210 行）
theorem ip_TopL_charU_prim {χ ψ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ip (TopL (charU χ)) (TopL (charU ψ)) = ip (charU χ) (charU ψ)

### PAG257::ip_TopL_of_mem_Vprim（theorem、223 行）
theorem ip_TopL_of_mem_Vprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vprim N) :
    ip (TopL f) (TopL g) = ip f g

### PAG257::TopL_eq_of_A1（theorem、237 行）
theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f

### PAG257::ip_Vprim_Vimprim（theorem、247 行）
theorem ip_Vprim_Vimprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vimprim N) :
    ip f g = 0

### PAG257::ip_sum_right（theorem、261 行）
theorem ip_sum_right {κ : Type*} [Fintype κ] (f : (ZMod N)ˣ → ℂ) (b : κ → ℂ)
    (w : κ → (ZMod N)ˣ → ℂ) : ip (N := N) f (∑ j, b j • w j) = ∑ j, b j * ip f (w j)

### PAG257::linearIndependent_charU（theorem、270 行）
theorem linearIndependent_charU :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ N => charU χ)

### PAG257::span_charU_eq_top（theorem、285 行）
theorem span_charU_eq_top :
    Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) = ⊤

### PAG257::Vprim_sup_Vimprim（theorem、293 行）
theorem Vprim_sup_Vimprim : Vprim N ⊔ Vimprim N = ⊤

### PAG257::eq_zero_of_ip_self（theorem、305 行）
theorem eq_zero_of_ip_self (f : (ZMod N)ˣ → ℂ) (h : ip f f = 0) : f = 0

### PAG257::Vprim_inf_Vimprim（theorem、319 行）
theorem Vprim_inf_Vimprim : Vprim N ⊓ Vimprim N = ⊥

### PAG257::isCompl_Vprim_Vimprim（theorem、327 行）
theorem isCompl_Vprim_Vimprim : IsCompl (Vprim N) (Vimprim N)

### PAG257::Vprim_ne_bot_three（theorem、333 行）
theorem Vprim_ne_bot_three : Vprim 3 ≠ ⊥

### PAG257::not_isometry_Vimprim_two（theorem、343 行）
theorem not_isometry_Vimprim_two : ∃ f ∈ Vimprim 2, ip (TopL f) (TopL f) ≠ ip f f

### PAG257::TopL_charU_one_four（theorem、363 行）
theorem TopL_charU_one_four :
    TopL (charU (1 : DirichletCharacter ℂ 4)) = 0 ∧ charU (1 : DirichletCharacter ℂ 4) ≠ 0

### PAG257::unitary_Vprim（theorem、375 行）
theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ)

### PAG257::gaussSum_one_prime（theorem、408 行）
theorem gaussSum_one_prime (p : ℕ) [Fact p.Prime] :
    gaussSum (1 : DirichletCharacter ℂ p) (stdAddChar (N := p)) = -1

### PAG257::normSq_rootNum_one_prime（theorem、428 行）
theorem normSq_rootNum_one_prime (p : ℕ) [hp : Fact p.Prime] :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ p)) = 1 / p

### PAG257::not_isometry_Vimprim_prime（theorem、444 行）
theorem not_isometry_Vimprim_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f ∈ Vimprim p, ip (TopL f) (TopL f) ≠ ip f f

### PAG257::Vprim_ne_bot_prime（theorem、472 行）
theorem Vprim_ne_bot_prime (p : ℕ) [hp : Fact p.Prime] (h3 : 3 ≤ p) : Vprim p ≠ ⊥

### PAG257::charU_one_mem_Vimprim（theorem、494 行）
theorem charU_one_mem_Vimprim (hN : 2 ≤ N) : charU (1 : DirichletCharacter ℂ N) ∈ Vimprim N

### PAG257::Vprim_two（theorem、505 行）
theorem Vprim_two : Vprim 2 = ⊥
