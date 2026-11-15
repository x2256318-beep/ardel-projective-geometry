
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

### PAG2::Wpow（def、124 行）
noncomputable def Wpow (χ : DirichletCharacter ℂ N) (r : ℕ) : ℂ :=
  ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 * gaussSum χ ZMod.stdAddChar ^ r
    / (Real.sqrt N : ℂ) ^ r

### PAG2::parity_weight（lemma、131 行）
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r

######## PAG12.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part12
open Finset
section Int
variable {p : ℕ}
end Int
section Cond
variable {p n : ℕ} [hp : Fact p.Prime]
end Cond
end PAG.Part12

### PAG12::one_add_pow_expand（theorem、21 行）
theorem one_add_pow_expand (hp2 : 2 ≤ p) (d : ℤ) :
    (1 + d) ^ p = 1 + p * d + ∑ m ∈ range (p - 1), d ^ (m + 2) * (p.choose (m + 2) : ℤ)

### PAG12::key_binom（theorem、31 行）
theorem key_binom (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (d : ℤ)
    (hd : (p : ℤ) ^ k ∣ d) : (p : ℤ) ^ (k + 2) ∣ (1 + d) ^ p - 1 - p * d

### PAG12::pow_p_congr（theorem、53 行）
theorem pow_p_congr (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (x t : ℤ)
    (hx : x - 1 = (p : ℤ) ^ k * t) : ∃ s, x ^ p - 1 = (p : ℤ) ^ (k + 1) * t + (p : ℤ) ^ (k + 2) * s

### PAG12::pow_p_pow_congr（theorem、63 行）
theorem pow_p_pow_congr (hp : p.Prime) (hodd : Odd p) {k : ℕ} (hk : 1 ≤ k) (x t s₀ : ℤ)
    (hx : x - 1 = (p : ℤ) ^ k * t + (p : ℤ) ^ (k + 1) * s₀) (r : ℕ) :
    ∃ s, x ^ (p ^ r) - 1 = (p : ℤ) ^ (k + r) * t + (p : ℤ) ^ (k + r + 1) * s

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

### PAG15::F_sq_eq_inv_p（theorem、179 行）
theorem F_sq_eq_inv_p (p K v : ℕ) (hp : 2 ≤ p) (hv : v < K) :
    ((shellSize p K v : ℝ) / shellSize p K (K - 1 - v)) * (p : ℝ) ^ (2 * v) / (p : ℝ) ^ K = 1 / p

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

######## PAG23.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part23
open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21
section Model
variable {N : ℕ}
open Classical in
open Classical in
variable [Fintype (ZMod N)]
end Model
section Mirror
variable {p : ℕ} [hp : Fact p.Prime]
end Mirror
end PAG.Part23

### PAG23::P1F（abbrev、20 行）
abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)

### PAG23::Compat（def、23 行）
def Compat (F : P1F N) : Prop := ∀ y : ZMod N, IsUnit y → F.2 y = F.1 y⁻¹

### PAG23::W（def、26 行）
def W (F : P1F N) : P1F N := (F.2, F.1)

######## PAG27.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part27
open ZMod PAG.Part23 PAG.Part26
open Classical
variable {N : ℕ}
variable {p : ℕ} [hp : Fact p.Prime]
section Iso
variable (K : ℕ) (hK : 1 ≤ K)
end Iso
end PAG.Part27

### PAG27::Unimod（def、20 行）
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

### PAG27::swap_unimod（theorem、164 行）
omit hp in
theorem swap_unimod (v : Unimod N) : ∃ s t : ZMod N, s * v.1.2 + t * v.1.1 = 1

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

### PAG37::pm5_bijective（theorem、120 行）
theorem pm5_bijective : Function.Bijective (pm5 d)

######## PAG46.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part46
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part42
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part46

### PAG46::lam_pos（theorem、17 行）
theorem lam_pos (K u : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K u : ℝ)

######## PAG55.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part55
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part52 PAG.Part54
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part55

### PAG55::family_linearIndependent（theorem、222 行）
theorem family_linearIndependent (K : ℕ) :
    LinearIndependent ℂ (fun v : family (p := p) K => (v : ZMod (p ^ K) → ℂ))

######## PAG56.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part56
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part52 PAG.Part54 PAG.Part55
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part56

### PAG56::expand（theorem、74 行）
theorem expand (K : ℕ) (f : ZMod (p ^ K) → ℂ) :
    f = ∑ b : family (p := p) K,
      (ip (b : ZMod (p ^ K) → ℂ) f / ip (b : ZMod (p ^ K) → ℂ) b) • (b : ZMod (p ^ K) → ℂ)

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

######## PAG89.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part89
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part41
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part89

### PAG89::lam_nonneg（theorem、47 行）
omit hp in
theorem lam_nonneg (K a : ℕ) : 0 ≤ (p : ℝ) ^ K / (sz p K a : ℝ)

######## PAG108.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part108
open Finset PAG.Part15
section Generic
variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
end Generic
section TwoPrimes
open PAG.Part59 PAG.Part89
variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
end TwoPrimes
end PAG.Part108

### PAG108::tens（def、22 行）
def tens (f : G → ℂ) (g : H → ℂ) : G × H → ℂ := fun z => f z.1 * g z.2

### PAG108::tens_sum（theorem、51 行）
omit [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] in
theorem tens_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → G → ℂ) (g : κ → H → ℂ) :
    ∑ i ∈ s, ∑ j ∈ t, tens (f i) (g j) = tens (∑ i ∈ s, f i) (∑ j ∈ t, g j)

######## PAG114.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part114
open ZMod Finset PAG.Part15 PAG.Part105 PAG.Part107 PAG.Part108 PAG.Part109 PAG.Part110 PAG.Part113
section Level
open PAG.Part59 PAG.Part93 PAG.Part95
variable {p : ℕ} [hp : Fact p.Prime] {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
end Level
section Equiv
open PAG.Part21 PAG.Part98
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K : Fin n → ℕ)
end Equiv
end PAG.Part114

### PAG114::tens_smul_left（theorem、60 行）
omit hp [AddCommGroup H] [Fintype H] [DecidableEq H] in
theorem tens_smul_left (c : ℂ) (f : ZMod (p ^ (K + 1)) → ℂ) (g : H → ℂ) :
    tens (c • f) g = c • tens f g

######## PAG116.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part116
open ZMod Finset Polynomial PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part95
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part116

### PAG116::lam_pos（theorem、60 行）
theorem lam_pos (K a : ℕ) : (0 : ℝ) < (p : ℝ) ^ K / (sz p K a : ℝ)

### PAG116::cnorm_ne_zero（theorem、91 行）
theorem cnorm_ne_zero (K a : ℕ) : cnorm p K a ≠ 0

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

######## PAG139.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part139
open ZMod Finset PAG.Part120
variable {p : ℕ} [hp : Fact p.Prime]
section Gen
variable {c k : ℕ} (hk1 : 1 ≤ k) (hkc : k < c) (h2k : c ≤ 2 * k)
end Gen
end PAG.Part139

### PAG139::cast_eq_of_P（theorem、23 行）
theorem cast_eq_of_P (u u₀ : ZMod (p ^ c)) (h : (p : ZMod (p ^ c)) ^ k * u = (p : ZMod (p ^ c)) ^ k * u₀) :
    ((u : ZMod (p ^ c)).cast : ZMod p) = (u₀.cast : ZMod p)

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

### PAG140::isUnit_iff_cast_ne_zero（theorem、111 行）
theorem isUnit_iff_cast_ne_zero (c : ℕ) (hc : 1 ≤ c) (x : ZMod (p ^ c)) :
    IsUnit x ↔ ((x.cast : ZMod p) ≠ 0)

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

### PAG143::P_mul_eq_zero_iff（theorem、25 行）
theorem P_mul_eq_zero_iff (x : ZMod (p ^ c)) :
    (p : ZMod (p ^ c)) ^ k * x = 0 ↔ ((x.cast : ZMod (p ^ (c - k))) = 0)

### PAG143::freq_unique（theorem、38 行）
theorem freq_unique (χ : DirichletCharacter ℂ (p ^ c)) (δ δ' : ZMod (p ^ c))
    (h : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ * y))
    (h' : ∀ y, χ (1 + (p : ZMod (p ^ c)) ^ k * y) = stdAddChar ((p : ZMod (p ^ c)) ^ k * δ' * y)) :
    ((δ.cast : ZMod (p ^ (c - k)))) = (δ'.cast : ZMod (p ^ (c - k)))

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

######## PAG149.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part149
open ZMod Finset
variable {q : ℕ} [hq : Fact q.Prime]
end PAG.Part149

### PAG149::fiber_digit（theorem、35 行）
theorem fiber_digit (a : (ZMod q)ˣ) (N : ℕ) (x : ℂ)
    (hx : x ∈ Set.range fun ψ : DirichletCharacter ℂ q => ψ (a : ZMod q) ^ N) :
    #{ψ : DirichletCharacter ℂ q | ψ (a : ZMod q) ^ N = x} * (orderOf a / Nat.gcd (orderOf a) N) = q - 1

######## PAG151.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part151
open ZMod Finset
section Single
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117
variable {p : ℕ} [hp : Fact p.Prime]
end Single
end PAG.Part151

### PAG151::neg_one_mod4（theorem、61 行）
theorem neg_one_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) : χ (-1) = -1

### PAG151::phase_mod4（theorem、83 行）
theorem phase_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) ^ 2 = -1 ∧
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) = 4

######## PAG152.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part152
open ZMod Finset Complex Real
end PAG.Part152

### PAG152::e8_pow（theorem、56 行）
theorem e8_pow (k : ℕ) : stdAddChar ((k : ZMod 8)) = stdAddChar (1 : ZMod 8) ^ k

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

######## PAG154.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part154
open ZMod Finset PAG.Part118 PAG.Part127
variable {p : ℕ} [hp : Fact p.Prime]
section Even
variable {c m : ℕ} (hc : c = 2 * m)
end Even
end PAG.Part154

### PAG154::chi_pow_of_cast_eq（theorem、145 行）
theorem chi_pow_of_cast_eq (c : ℕ) (hc1 : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c)) (u v : ZMod (p ^ c))
    (hu : IsUnit u) (hv : IsUnit v) (h : (u.cast : ZMod p) = (v.cast : ZMod p)) :
    χ u ^ (p ^ (c - 1)) = χ v ^ (p ^ (c - 1))

######## PAG162.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part162
open ZMod Finset PAG.Part119 PAG.Part143 PAG.Part144 PAG.Part160
variable {p : ℕ} [hp : Fact p.Prime]
section Gen
variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)
open Classical in
open Classical in
end Gen
open Classical in
open Classical in
end PAG.Part162

### PAG162::count_set（theorem、61 行）
open Classical in
theorem count_set (N : ℕ) (hω : ∀ t : ZMod p, ∃ ω : DirichletCharacter ℂ (p ^ c), ω ^ N = 1 ∧ fp hkc h2k ω = t)
    (S : Finset (ZMod p)) :
    #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ ∈ S}
      = S.card * #{χ : DirichletCharacter ℂ (p ^ c) | χ ^ N = 1 ∧ fp hkc h2k χ = 0}

######## PAG171.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part171
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part171

### PAG171::ω（def、32 行）
noncomputable def ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * I) / 2

### PAG171::InZω（def、55 行）
def InZω (y : ℂ) : Prop := ∃ a b : ℤ, y = a + b * ω

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

######## PAG175.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part175
open Complex Finset PAG.Part171 PAG.Part172
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part175

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

######## PAG178.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part178
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part175
open ZMod (stdAddChar)
variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime]
end PAG.Part178

### PAG178::Tlin4_not_dvd（theorem、23 行）
theorem Tlin4_not_dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a b C D : ℤ)
    (hab : a ^ 2 + b ^ 2 = p) (hCD : ¬ (p : ℤ) ∣ C ^ 2 + D ^ 2) : ¬ (p : ℤ) ∣ Tlin4 a b C D

######## PAG179.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part179
open Complex Finset PAG.Part171 PAG.Part172 PAG.Part174 PAG.Part175 PAG.Part176 PAG.Part177 PAG.Part178
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part179

### PAG179::InQi_prod（theorem、26 行）
theorem InQi_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, InQi (f i)) : InQi (∏ i ∈ s, f i)

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

### PAG180::zpow_six_comm（theorem、55 行）
theorem zpow_six_comm (z : ℂ) (k : ℤ) : (z ^ k) ^ 6 = (z ^ 6) ^ k

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

### PAG181::zpow_four_comm（theorem、48 行）
theorem zpow_four_comm (z : ℂ) (k : ℤ) : (z ^ k) ^ 4 = (z ^ 4) ^ k

######## PAG188.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part188
open Complex Finset
open ZMod (stdAddChar)
variable {ι : Type*} [Fintype ι] (P : ι → ℕ) [hP : ∀ i, Fact (P i).Prime]
end PAG.Part188

### PAG188::zpow_root（theorem、45 行）
theorem zpow_root (x : ℂ) (k : ℤ) (h : ∃ N : ℕ, 0 < N ∧ x ^ N = 1) : ∃ N : ℕ, 0 < N ∧ (x ^ k) ^ N = 1

### PAG188::prod_root_of_root（theorem、51 行）
theorem prod_root_of_root {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, ∃ N : ℕ, 0 < N ∧ f i ^ N = 1) : ∃ N : ℕ, 0 < N ∧ (∏ i ∈ s, f i) ^ N = 1

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

### PAG189::norm_eq_one_of_toZMod_ne_zero（theorem、34 行）
theorem norm_eq_one_of_toZMod_ne_zero (x : ℤ_[p]) (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1

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

### PAG190::finite_of_bounded（theorem、136 行）
theorem finite_of_bounded {A : Subalgebra ℤ ℂ} (pb : PowerBasis ℤ A) (σ : Fin pb.dim → (A →+* ℂ))
    (hv : (vandermonde (fun k => σ k pb.gen)).det ≠ 0) :
    {y : A | ∀ k, ‖σ k y‖ ≤ 1}.Finite

### PAG190::norm_z（theorem、347 行）
theorem norm_z (φ : MulChar (ZMod p) ℂ) (hφ : φ ≠ 1) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum φ ψ / ((Real.sqrt p : ℝ) : ℂ)‖ = 1

### PAG190::norm_prod_z（theorem、437 行）
theorem norm_prod_z (χ' : MulChar (ZMod p) ℂ) (n : ℕ) (hord : orderOf χ' = n) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (a : ℕ → ℤ) :
    ‖∏ j ∈ Ico 1 n, ((gaussSum (χ' ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j‖ = 1

######## PAG193.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part193
open Complex Finset
open ZMod (stdAddChar)
variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
end PAG.Part193

### PAG193::param（def、24 行）
noncomputable def param (N₁ N₂ : ℕ) (x : ZMod N₁ × ZMod N₂) : ZMod (N₁ * N₂) :=
  ((x.1.val * N₂ + x.2.val * N₁ : ℕ) : ZMod (N₁ * N₂))

### PAG193::param_bijective（theorem、46 行）
theorem param_bijective (hcop : N₁.Coprime N₂) : Function.Bijective (param N₁ N₂)

### PAG193::mul_changeLevel_apply（theorem、62 行）
theorem mul_changeLevel_apply (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (x : ZMod (N₁ * N₂)) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) x
      = χ₁ (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x) *
        χ₂ (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x)

### PAG193::stdAddChar_param（theorem、92 行）
theorem stdAddChar_param (x : ZMod N₁ × ZMod N₂) :
    stdAddChar (param N₁ N₂ x) = stdAddChar x.1 * stdAddChar x.2

### PAG193::gaussSum_mul_coprime（theorem、110 行）
theorem gaussSum_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar

### PAG193::z_mul_coprime（theorem、128 行）
theorem z_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
        / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) *
        ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
          (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ∧
      ∃ M : ℕ, 0 < M ∧ (χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂)) ^ M = 1

### PAG193::composite_root_iff（theorem、156 行）
theorem composite_root_iff (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) *
        χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)) ^ N
          = 1) ↔
      ∃ N : ℕ, 0 < N ∧ ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
        (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ^ N = 1

### PAG193::pq_root_iff（theorem、171 行）
theorem pq_root_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (χ₁ : DirichletCharacter ℂ p) (χ₂ : DirichletCharacter ℂ q) (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ₁.changeLevel (dvd_mul_right p q) *
        χ₂.changeLevel (dvd_mul_left q p)) stdAddChar / ((Real.sqrt ((p * q : ℕ) : ℝ) : ℝ) : ℂ)) ^ N
          = 1) ↔ orderOf χ₁ = 2 ∧ orderOf χ₂ = 2

######## PAG194.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part194
open Complex Finset
open ZMod (stdAddChar)
variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
end PAG.Part194

### PAG194::rho（def、28 行）
noncomputable def rho (N₁ N₂ : ℕ) : ZMod (N₁ * N₂) →+* ZMod N₁ × ZMod N₂ :=
  RingHom.prod (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁)) (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂))

### PAG194::rho_bijective（theorem、34 行）
theorem rho_bijective (hcop : N₁.Coprime N₂) : Function.Bijective (rho N₁ N₂)

### PAG194::isPrimitive_left（theorem、132 行）
theorem isPrimitive_left (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂)
    (h : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive) :
    χ₁.IsPrimitive

### PAG194::isPrimitive_right（theorem、158 行）
theorem isPrimitive_right (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂)
    (h : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive) :
    χ₂.IsPrimitive

### PAG194::isPrimitive_mul（theorem、217 行）
theorem isPrimitive_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive

######## PAG195.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part195
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194
end PAG.Part195

### PAG195::sq_mul_changeLevel（theorem、38 行）
theorem sq_mul_changeLevel {N₁ N₂ : ℕ} (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) ^ 2 =
      (χ₁ ^ 2).changeLevel (dvd_mul_right N₁ N₂) * (χ₂ ^ 2).changeLevel (dvd_mul_left N₂ N₁)

### PAG195::squarefull_root（theorem、207 行）
theorem squarefull_root (N : ℕ) [NeZero N] (hN : ∀ q : ℕ, q.Prime → q ∣ N → q ^ 2 ∣ N)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ∃ K : ℕ, 0 < K ∧ (gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ^ K = 1

######## PAG197.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part197
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196
end PAG.Part197

### PAG197::pow_two_zpow（theorem、140 行）
theorem pow_two_zpow (w : ℂ) (a : ℤ) : (w ^ a) ^ 2 = (w ^ 2) ^ a

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

### PAG199::cmul（def、143 行）
noncomputable def cmul {c₁ c₂ : ℕ} (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) :
    DirichletCharacter ℂ (c₁ * c₂) :=
  X₁.changeLevel (dvd_mul_right c₁ c₂) * X₂.changeLevel (dvd_mul_left c₂ c₁)

### PAG199::tens_smul_smul（theorem、271 行）
theorem tens_smul_smul {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (a b : ℂ) (f : G → ℂ) (g : H → ℂ) :
    PAG.Part108.tens (a • f) (b • g) = (a * b) • PAG.Part108.tens f g

######## PAG200.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part200
open Complex Finset PAG.Part199
open ZMod (stdAddChar)
end PAG.Part200

### PAG200::exists_split（theorem、23 行）
theorem exists_split {p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) : ∃ a x₂, ¬ p ∣ x₂ ∧ x = p ^ a * x₂

######## PAG209.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part209
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part209

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

######## PAG215.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part215
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part215

### PAG215::chi_eq_zero_of_rad（theorem、317 行）
theorem chi_eq_zero_of_rad {L c x : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ L → p ∣ c) (hx : x ∣ L) (hx1 : x ≠ 1) : χ (x : ZMod c) = 0

######## PAG219.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part219
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part219

### PAG219::not_dvd_of_chi_ne_zero（theorem、93 行）
theorem not_dvd_of_chi_ne_zero {c : ℕ} (ψ : DirichletCharacter ℂ c) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c)
    {m : ℕ} (hm : ψ (m : ZMod c) ≠ 0) : ¬ p ∣ m

######## PAG220.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part220
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part220

### PAG220::layerIdx（def、83 行）
open Classical in
noncomputable def layerIdx (c L : ℕ) : Finset ℕ := L.divisors.filter (fun d => RadDvd d c)

######## PAG221.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part221
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part221

### PAG221::layerInd（def、32 行）
open Classical in
noncomputable def layerInd (N c d : ℕ) : ZMod N → ℂ := fun x => if InLayer c d x.val then 1 else 0

### PAG221::layerDivs（def、173 行）
open Classical in
noncomputable def layerDivs (c d L : ℕ) : Finset ℕ := L.divisors.filter (fun v => InLayer c d v)

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

######## PAG236.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part236
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part236

### PAG236::charMul（def、34 行）
noncomputable def charMul {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ * DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂

### PAG236::charMul_apply_unit（theorem、47 行）
theorem charMul_apply_unit {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n)
    (u : (ZMod (m * n))ˣ) :
    charMul χ₁ χ₂ (u : ZMod (m * n)) =
      χ₁ (ZMod.cast (u : ZMod (m * n))) * χ₂ (ZMod.cast (u : ZMod (m * n)))

### PAG236::charMul_apply（theorem、55 行）
theorem charMul_apply {m n : ℕ} [NeZero m] [NeZero n] (χ₁ : DirichletCharacter ℂ m)
    (χ₂ : DirichletCharacter ℂ n) (x : ZMod (m * n)) :
    charMul χ₁ χ₂ x = χ₁ (ZMod.cast x) * χ₂ (ZMod.cast x)

### PAG236::charMul_mul（theorem、69 行）
theorem charMul_mul {m n : ℕ} (χ₁ ψ₁ : DirichletCharacter ℂ m) (χ₂ ψ₂ : DirichletCharacter ℂ n) :
    charMul (χ₁ * ψ₁) (χ₂ * ψ₂) = charMul χ₁ χ₂ * charMul ψ₁ ψ₂

### PAG236::charMul_inv（theorem、75 行）
theorem charMul_inv {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    charMul χ₁⁻¹ χ₂⁻¹ = (charMul χ₁ χ₂)⁻¹

### PAG236::isPrimitive_charMul（theorem、100 行）
theorem isPrimitive_charMul {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ : DirichletCharacter ℂ m} {χ₂ : DirichletCharacter ℂ n} (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (charMul χ₁ χ₂).IsPrimitive

### PAG236::charMul_injective（theorem、111 行）
theorem charMul_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ χ₁' : DirichletCharacter ℂ m} {χ₂ χ₂' : DirichletCharacter ℂ n}
    (h : charMul χ₁ χ₂ = charMul χ₁' χ₂') : χ₁ = χ₁' ∧ χ₂ = χ₂'

### PAG236::primMul（def、127 行）
noncomputable def primMul {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) (p : Prim m × Prim n) :
    Prim (m * n) :=
  ⟨charMul p.1.1 p.2.1, isPrimitive_charMul hmn p.1.2 p.2.2⟩

### PAG236::primMul_bijective（theorem、139 行）
theorem primMul_bijective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Function.Bijective (primMul hmn)

### PAG236::primEquiv（def、148 行）
noncomputable def primEquiv {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Prim m × Prim n ≃ Prim (m * n) :=
  Equiv.ofBijective (primMul hmn) (primMul_bijective hmn)

### PAG236::cast_crt_fst（theorem、161 行）
theorem cast_crt_fst {a b c : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hc : c ∣ a) (x : ZMod (a * b)) :
    (ZMod.cast (ZMod.chineseRemainder hab x).1 : ZMod c) = ZMod.cast x

### PAG236::cast_crt_snd（theorem、167 行）
theorem cast_crt_snd {a b c : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hc : c ∣ b) (x : ZMod (a * b)) :
    (ZMod.cast (ZMod.chineseRemainder hab x).2 : ZMod c) = ZMod.cast x

### PAG236::tens（def、185 行）
def tens {a b : ℕ} (f : ZMod a → ℂ) (g : ZMod b → ℂ) : ZMod a × ZMod b → ℂ := fun p => f p.1 * g p.2

######## PAG237.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part237
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part237

### PAG237::gaugeUnit（def、248 行）
noncomputable def gaugeUnit (a b ca da cb db : ℕ) [NeZero a] [NeZero b] [NeZero ca] [NeZero cb]
    (χa χa' : DirichletCharacter ℂ ca) (χb χb' : DirichletCharacter ℂ cb) : Module.End ℂ (ZMod (a * b) → ℂ) :=
  (gaugeFactor da db χa' χb' / gaugeFactor da db χa χb) •
    matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa' χb')

######## PAG238.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part238
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part238

### PAG238::gaugeP（def、49 行）
noncomputable def gaugeP {ca cb : ℕ} (da db : ℕ) (x : Prim ca × Prim cb) : ℂ := gaugeFactor da db x.1.1 x.2.1

### PAG238::kronG（def、56 行）
noncomputable def kronG {ca cb : ℕ} [NeZero ca] [NeZero cb] (hcop : Nat.Coprime ca cb) (da db : ℕ)
    (A : Matrix (Prim ca) (Prim ca) ℂ) (B : Matrix (Prim cb) (Prim cb) ℂ) :
    Matrix (Prim (ca * cb)) (Prim (ca * cb)) ℂ :=
  fun χ χ' => (gaugeP da db ((primEquiv hcop).symm χ) / gaugeP da db ((primEquiv hcop).symm χ')) *
    (A ((primEquiv hcop).symm χ).1 ((primEquiv hcop).symm χ').1 *
      B ((primEquiv hcop).symm χ).2 ((primEquiv hcop).symm χ').2)

######## PAG240.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part240
open PAG.Part218 PAG.Part226 PAG.Part232 PAG.Part233 PAG.Part234 PAG.Part235
open scoped TensorProduct
end PAG.Part240

### PAG240::eq_bot_of_one（theorem、289 行）
theorem eq_bot_of_one (S : Subalgebra ℂ (Module.End ℂ (ZMod 1 → ℂ))) : S = ⊥

######## PAG253.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### PAG253::eigenFun_of_commute_prime（theorem、176 行）
theorem eigenFun_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧
      ((∀ χ, ‖c χ‖ = 1) → (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) → ∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1)

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

### PAG253::primeShiftInv（def、458 行）
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)

### PAG253::norm_eq_one_of_isometry（theorem、549 行）
theorem norm_eq_one_of_isometry {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g) (χ : G →* ℂˣ) {c : ℂ}
    (hc : U (PAG.charFun χ) = c • PAG.charFun χ) : ‖c‖ = 1

### PAG253::thm26_full_of_commute（theorem、581 行）
theorem thm26_full_of_commute {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hU : ∀ h, U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : (G →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1)

######## PAG254.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part254
end PAG.Part254

### PAG254::logSet（def、32 行）
def logSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}

### PAG254::log_inj（theorem、35 行）
theorem log_inj {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (h : Real.log q = Real.log r) : q = r

### PAG254::logSet_countable（theorem、42 行）
theorem logSet_countable : logSet.Countable

### PAG254::not_Icc_subset_logSet（theorem、49 行）
theorem not_Icc_subset_logSet {a b : ℝ} (hab : a < b) : ¬ Set.Icc a b ⊆ logSet

### PAG254::subsingleton_of_isPreconnected（theorem、65 行）
theorem subsingleton_of_isPreconnected {S : Set ℝ} (hS : IsPreconnected S) (hSL : S ⊆ logSet) :
    S.Subsingleton

### PAG254::dense_logSet（theorem、75 行）
theorem dense_logSet : Dense logSet

### PAG254::chainIn_refl（theorem、99 行）
theorem chainIn_refl {α : Type*} {S : Set α} (d : α → α → ℝ) (ε : ℝ) {x : α} (hx : x ∈ S) :
    chainIn S d ε x x

### PAG254::chainIn_mono（theorem、104 行）
theorem chainIn_mono {α : Type*} {S : Set α} {d : α → α → ℝ} {ε ε' : ℝ} (h : ε ≤ ε') {x y : α}
    (hc : chainIn S d ε x y) : chainIn S d ε' x y

### PAG254::chainIn_of_lt（theorem、110 行）
theorem chainIn_of_lt {α : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (h : d x y < ε) : chainIn S d ε x y

### PAG254::chainIn_invariant（theorem、123 行）
theorem chainIn_invariant {α β : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} (f : α → β)
    (hf : ∀ x y, x ∈ S → y ∈ S → d x y < ε → f x = f y) {x y : α} (hc : chainIn S d ε x y) :
    f x = f y

### PAG254::posRat（def、142 行）
def posRat : Set ℚ := {q | 0 < q}

### PAG254::dInf（def、145 行）
noncomputable def dInf (q r : ℚ) : ℝ := |Real.log q - Real.log r|

### PAG254::dInf_mul_left（theorem、148 行）
theorem dInf_mul_left {s q r : ℚ} (hs : 0 < s) (hq : 0 < q) (hr : 0 < r) :
    dInf (s * q) (s * r) = dInf q r

### PAG254::abs_log_sub_log_le（theorem、159 行）
theorem abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m

### PAG254::chainIn_dInf（theorem、187 行）
theorem chainIn_dInf {ε : ℝ} (hε : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat dInf ε q r

### PAG254::primePow（def、236 行）
def primePow (p : ℕ) : Set ℚ := {q | ∃ k : ℤ, q = (p : ℚ) ^ k}

### PAG254::dInf_zpow（theorem、239 行）
theorem dInf_zpow {p : ℕ} (a b : ℤ) :
    dInf ((p : ℚ) ^ a) ((p : ℚ) ^ b) = |((a - b : ℤ) : ℝ)| * |Real.log p|

### PAG254::eq_of_chainIn_primePow（theorem、247 行）
theorem eq_of_chainIn_primePow {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : ε ≤ Real.log p) {x y : ℚ}
    (hc : chainIn (primePow p) dInf ε x y) : x = y

### PAG254::dense_closure_log_two_three（theorem、268 行）
theorem dense_closure_log_two_three :
    Dense ((AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)

### PAG254::dP（def、334 行）
noncomputable def dP (p : ℕ) (q r : ℚ) : ℝ := |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|

### PAG254::dP_mul_left（theorem、337 行）
theorem dP_mul_left (p : ℕ) [Fact p.Prime] {s q r : ℚ} (hs : s ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    dP p (s * q) (s * r) = dP p q r

### PAG254::dP_lt_one_iff（theorem、345 行）
theorem dP_lt_one_iff (p : ℕ) (q r : ℚ) : dP p q r < 1 ↔ padicValRat p q = padicValRat p r

### PAG254::padicValRat_eq_of_chainIn（theorem、361 行）
theorem padicValRat_eq_of_chainIn (p : ℕ) {ε : ℝ} (hε : ε ≤ 1) {q r : ℚ}
    (hc : chainIn posRat (dP p) ε q r) : padicValRat p q = padicValRat p r

### PAG254::chainIn_dP_iff（theorem、367 行）
theorem chainIn_dP_iff (p : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ padicValRat p q = padicValRat p r

### PAG254::exists_padicValRat_eq（theorem、378 行）
theorem exists_padicValRat_eq (p : ℕ) [hp : Fact p.Prime] (k : ℤ) :
    ∃ q : ℚ, 0 < q ∧ padicValRat p q = k

### PAG254::chainIn_dP_of_one_lt（theorem、387 行）
theorem chainIn_dP_of_one_lt (p : ℕ) [hp : Fact p.Prime] {ε : ℝ} (hε : 1 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r

### PAG254::chainIn_dP_classification（theorem、440 行）
theorem chainIn_dP_classification (p : ℕ) [Fact p.Prime] {ε : ℝ} (hε0 : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ (ε ≤ 1 → padicValRat p q = padicValRat p r)

### PAG254::emergence_contrast（theorem、454 行）
theorem emergence_contrast :
    (∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat dInf ε q r) ∧
    (∀ p : ℕ, p.Prime → ¬ chainIn posRat (dP p) 1 1 (p : ℚ))

### PAG254::dense_logSet_coprime（theorem、465 行）
theorem dense_logSet_coprime {N : ℕ} [NeZero N] (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m.Coprime N ∧ n.Coprime N ∧ |Real.log n - Real.log m - t| < ε

### PAG254::dP_eq_dist（theorem、479 行）
theorem dP_eq_dist (p : ℕ) (q r : ℚ) :
    dP p q r = dist ((padicValRat p q : ℤ) : ℝ) ((padicValRat p r : ℤ) : ℝ)

### PAG254::half_le_abs_padicValRat_sub_half（theorem、487 行）
theorem half_le_abs_padicValRat_sub_half (p : ℕ) (q : ℚ) :
    (1 / 2 : ℝ) ≤ |((padicValRat p q : ℤ) : ℝ) - 1 / 2|

### PAG254::not_forall_chainIn_dP（theorem、500 行）
theorem not_forall_chainIn_dP (p : ℕ) (hp : p.Prime) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat (dP p) ε q r

######## PAG255.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part255
open PAG.Part253 Nat
end PAG.Part255

### PAG255::exists_level（theorem、243 行）
theorem exists_level {u : Set unitSys} (hu : IsOpen u) {a : unitSys} (ha : a ∈ u) :
    ∃ N : ℕ+, ∀ b : unitSys, (b : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N → b ∈ u

### PAG255::dense_closure_primeGens（theorem、260 行）
theorem dense_closure_primeGens (L : ℕ+) :
    Dense ((Subgroup.closure (primeGens L) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ))

### PAG255::dense_closure_allPrimes（theorem、301 行）
theorem dense_closure_allPrimes :
    Dense ((Subgroup.closure (primeGens 1) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ))

######## PAG256.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part256
open ZMod Complex Finset
variable {N : ℕ} [NeZero N]
open Classical in
end PAG.Part256

### PAG256::parFac_of_even（theorem、68 行）
omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1

### PAG256::parFac_of_odd（theorem、74 行）
omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I

### PAG256::exists_primitive_odd_three（theorem、246 行）
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd

### PAG256::exists_primitive_even_five（theorem、259 行）
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1

######## PAG257.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part257
open ZMod Complex Finset PAG.Part256
variable {N : ℕ} [NeZero N]
open Classical in
open Classical in
open Classical in
end PAG.Part257

### PAG257::rootNum_ne_zero（theorem、190 行）
theorem rootNum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNum χ ≠ 0

### PAG257::gaussSum_one_prime（theorem、408 行）
theorem gaussSum_one_prime (p : ℕ) [Fact p.Prime] :
    gaussSum (1 : DirichletCharacter ℂ p) (stdAddChar (N := p)) = -1

######## PAG258.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part258
open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter
variable {N : ℕ} [NeZero N]
end PAG.Part258

### PAG258::phaseA1_of_isPrimitive（theorem、99 行）
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ

### PAG258::phaseA1_changeLevel（theorem、114 行）
theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ

### PAG258::phaseA1_one（theorem、136 行）
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1

### PAG258::UA1_charU（theorem、171 行）
theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ

### PAG258::ip_UA1（theorem、189 行）
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g

### PAG258::UA1_mem_Vprim（theorem、290 行）
theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N

### PAG258::UA1_mem_Vimprim（theorem、300 行）
theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N

### PAG258::rootNum_one_prime（theorem、320 行）
theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ)

### PAG258::phaseA1_inv（theorem、395 行）
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ)

### PAG258::UA1_star（theorem、401 行）
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u)

### PAG258::UA1_bijective（theorem、470 行）
theorem UA1_bijective : Function.Bijective (UA1 (N := N))

### PAG258::UA1_mem_condPart（theorem、795 行）
theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q
