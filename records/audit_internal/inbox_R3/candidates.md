
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

### PAG17::AS_sup_AN（theorem、50 行）
theorem AS_sup_AN {X : Type*} (S Nn : Set X) (hdisj : Disjoint S Nn) :
    AS (K := K) Nn ⊔ AS S = ⊤

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

### PAG23::extS（def、44 行）
open Classical in
noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)

### PAG23::extN（def、48 行）
open Classical in
noncomputable def extN (h : ZMod N → ℂ) : P1F N := (fun x => if IsUnit x then h x⁻¹ else 0, h)

### PAG23::BS（def、67 行）
noncomputable def BS (F G : P1F N) : P1F N := extS (PAG.Part15.conv F.1 G.1)

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

### PAG27::isUnit_units_mul_iff（theorem、64 行）
omit hp in
theorem isUnit_units_mul_iff (u : (ZMod N)ˣ) (x : ZMod N) : IsUnit ((u : ZMod N) * x) ↔ IsUnit x

### PAG27::ofRep（def、97 行）
noncomputable def ofRep (v : Unimod (p ^ K)) : Pt (p ^ K) :=
  if h : IsUnit v.1.2 then Sum.inl (v.1.1 * v.1.2⁻¹)
  else Sum.inr ⟨v.1.2 * v.1.1⁻¹, nonunit_div (a_unit_of K hK h) h⟩

include hK in

### PAG27::ofProj（def、116 行）
noncomputable def ofProj : ProjLine (p ^ K) → Pt (p ^ K) :=
  Quotient.lift (ofRep K hK) (ofRep_resp K hK)

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

### PAG30::two_mul_not_prim（theorem、205 行）
theorem two_mul_not_prim (hc : 1 ≤ c) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (c + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : ¬ (χ₁ * χ₂).IsPrimitive

### PAG30::no_prim_mod_two（theorem、213 行）
theorem no_prim_mod_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive

### PAG30::two_equator_vacuous（theorem、225 行）
theorem two_equator_vacuous (n : ℕ) (hn : 1 ≤ n + 1) (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : ¬ (χ₁ * χ₂).IsPrimitive

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

### PAG31::tildeP1（def、151 行）
noncomputable def tildeP1 {N : ℕ} (F : P1F N) : P1F N := (tilde F.1, tilde F.2)

### PAG31::mod4_mul_trivial（theorem、240 行）
theorem mod4_mul_trivial (χ₁ χ₂ : DirichletCharacter ℂ (2 ^ (1 + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) : χ₁ * χ₂ = 1

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

### PAG32::prim_level_p_iff（theorem、244 行）
theorem prim_level_p_iff (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1

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

######## PAG47.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part47
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part40
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part47

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

######## PAG54.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part54
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part47
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part54

### PAG54::span_family_eq_top（theorem、97 行）
theorem span_family_eq_top (K : ℕ) : Submodule.span ℂ (family (p := p) K) = ⊤

######## PAG55.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part55
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part52 PAG.Part54
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part55

### PAG55::VanishNU（def、82 行）
def VanishNU {N : ℕ} (f : ZMod N → ℂ) : Prop := ∀ y, ¬ IsUnit y → f y = 0

######## PAG59.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part59
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part58
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part59

### PAG59::EpsSpan（def、20 行）
noncomputable def EpsSpan (K : ℕ) : Submodule ℂ (ZMod (p ^ K) → ℂ) :=
  Submodule.span ℂ (Set.range (fun b : Fin (K + 1) => eps (p := p) K b))

### PAG59::eps_linearIndependent（theorem、105 行）
theorem eps_linearIndependent (K : ℕ) :
    LinearIndependent ℂ (fun b : Fin (K + 1) => eps (p := p) K b)

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

######## PAG85.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part85
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part44 PAG.Part45 PAG.Part66 PAG.Part72
end PAG.Part85

### PAG85::no_prim_mod2（theorem、18 行）
theorem no_prim_mod2 (χ : DirichletCharacter ℂ (2 ^ (0 + 1))) : ¬ χ.IsPrimitive

######## PAG98.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part98
open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part51 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part59 PAG.Part89 PAG.Part90
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part98

### PAG98::Equivariant（def、27 行）
def Equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), f (u * x) = α u * f x

######## PAG100.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part100
open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part93 PAG.Part98
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part100

### PAG100::char_eq_one_of_units（theorem、30 行）
theorem char_eq_one_of_units (K n : ℕ) (h : n + 1 ≤ K) (ψ : DirichletCharacter ℂ (p ^ (n + 1)))
    (H : ∀ u : (ZMod (p ^ K))ˣ, ψ (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ (n + 1))) u) = 1) : ψ = 1

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

### PAG120::psi_two_one（theorem、21 行）
theorem psi_two_one : stdAddChar (1 : ZMod 2) = -1

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

### PAG121::Psi_linearIndependent（theorem、65 行）
theorem Psi_linearIndependent {ι : Type*} [Fintype ι] (v : ι → ZMod N₁ × ZMod N₂) (hv : Function.Injective v) :
    LinearIndependent ℂ (fun i => Psi (v i))

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

######## PAG145.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part145
open ZMod Finset PAG.Part143 PAG.Part144
variable {p : ℕ} [hp : Fact p.Prime]
section Count
variable {c k : ℕ} (hkc : k < c) (h2k : c ≤ 2 * k)
open Classical in
open Classical in
end Count
end PAG.Part145

### PAG145::card_units_filter（theorem、44 行）
theorem card_units_filter (n : ℕ) [NeZero n] : #{x : ZMod n | IsUnit x} = Nat.totient n

######## PAG151.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part151
open ZMod Finset
section Single
open PAG.Part19 PAG.Part21 PAG.Part95 PAG.Part116 PAG.Part117
variable {p : ℕ} [hp : Fact p.Prime]
end Single
end PAG.Part151

### PAG151::sq_eq_one_mod4（theorem、54 行）
theorem sq_eq_one_mod4 (χ : DirichletCharacter ℂ 4) : χ ^ 2 = 1

### PAG151::phase_mod4（theorem、83 行）
theorem phase_mod4 (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) ^ 2 = -1 ∧
    orderOf (gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ)) = 4

### PAG151::sq_eq_one_mod8（theorem、103 行）
theorem sq_eq_one_mod8 (χ : DirichletCharacter ℂ 8) : χ ^ 2 = 1

######## PAG152.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part152
open ZMod Finset Complex Real
end PAG.Part152

### PAG152::phase_mod4_eq（theorem、41 行）
theorem phase_mod4_eq (χ : DirichletCharacter ℂ 4) (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar / ((Real.sqrt (4 : ℕ) : ℝ) : ℂ) = I

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

### PAG172::zeta_quartic_infinite（theorem、173 行）
theorem zeta_quartic_infinite (χ : DirichletCharacter ℂ p) (h4 : orderOf χ = 4) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ orderOf χ) = 0

######## PAG182.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part182
open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part173
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
open Classical in
open Classical in
end PAG.Part182

### PAG182::sextic_general（theorem、191 行）
theorem sextic_general (χ : DirichletCharacter ℂ p) (h6 : orderOf χ = 6) :
    ∀ N : ℕ, 0 < N → (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1

######## PAG184.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part184
open Complex Finset PAG.Part119 PAG.Part160 PAG.Part171 PAG.Part173 PAG.Part180 PAG.Part181 PAG.Part182 PAG.Part183
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
variable {nc nq : ℕ} (pc : Fin nc → ℕ) [hpc : ∀ i, Fact (pc i).Prime] (pq : Fin nq → ℕ) [hpq : ∀ j, Fact (pq j).Prime]
end PAG.Part184

### PAG184::zOf_ne_zero（theorem、26 行）
theorem zOf_ne_zero (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : zOf χ ≠ 0

######## PAG185.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part185
open Complex Finset Polynomial
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part185

### PAG185::zeta_infinite（theorem、491 行）
theorem zeta_infinite (χ : DirichletCharacter ℂ p) (hn : 3 ≤ orderOf χ) :
    orderOf ((gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ orderOf χ) = 0

### PAG185::quintic_not_root（theorem、499 行）
theorem quintic_not_root (χ : DirichletCharacter ℂ p) (h5 : orderOf χ = 5) (N : ℕ) (hN : 0 < N) :
    (gaussSum χ stdAddChar / ((Real.sqrt p : ℝ) : ℂ)) ^ N ≠ 1

######## PAG187.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part187
open Complex Finset
open ZMod (stdAddChar)
variable {p : ℕ} [hp : Fact p.Prime]
end PAG.Part187

### PAG187::chi_sq_eight（theorem、57 行）
omit hp in
theorem chi_sq_eight (χ : DirichletCharacter ℂ (2 ^ 3)) : χ ^ 2 = 1

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

######## PAG198.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part198
open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196
end PAG.Part198

### PAG198::level_two_trivial（theorem、107 行）
theorem level_two_trivial {L : ℕ} (hL : L = 2) (φ : DirichletCharacter ℂ L) : φ = 1

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

### PAG199::normSq_chi_natCast（theorem、493 行）
theorem normSq_chi_natCast {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Complex.normSq (Ψ (n : ZMod d)) = 1

######## PAG200.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part200
open Complex Finset PAG.Part199
open ZMod (stdAddChar)
end PAG.Part200

### PAG200::split_dvd（theorem、44 行）
theorem split_dvd {p a b x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ a * x ∣ p ^ b * y) : a ≤ b ∧ x ∣ y

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

### PAG207::geps_linearIndependent（theorem、167 行）
theorem geps_linearIndependent (N : ℕ) [NeZero N] :
    LinearIndependent ℂ (fun s : N.divisors => geps N (s : ℕ))

######## PAG208.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part208
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part208

### PAG208::gbas_linearIndependent（theorem、150 行）
theorem gbas_linearIndependent (s n N : ℕ) [NeZero N] (h : s * n = N) :
    LinearIndependent ℂ (gbas s n N)

### PAG208::inner_smul_smul（theorem、370 行）
theorem inner_smul_smul {N : ℕ} [NeZero N] (a b : ℂ) (u v : ZMod N → ℂ) :
    ∑ j, starRingEnd ℂ ((a • u) j) * (b • v) j = starRingEnd ℂ a * b * ∑ j, starRingEnd ℂ (u j) * v j

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

### PAG214::card_isUnit_castHom（theorem、252 行）
theorem card_isUnit_castHom (s c : ℕ) [NeZero s] [NeZero c] :
    ((Finset.univ.filter (fun x : ZMod (s * c) =>
        IsUnit (ZMod.castHom (dvd_mul_left c s) (ZMod c) x))).card : ℂ) = (s : ℂ) * Nat.totient c

### PAG214::card_isUnit（theorem、281 行）
theorem card_isUnit (n : ℕ) [NeZero n] :
    ((Finset.univ.filter (fun x : ZMod n => IsUnit x)).card : ℂ) = Nat.totient n

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

### PAG218::dil（def、68 行）
def dil {N : ℕ} (a : (ZMod N)ˣ) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => (a : ZMod N) * x)

### PAG218::dil_of_mem_span（theorem、137 行）
theorem dil_of_mem_span (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ)
    {f : ZMod N → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w)) :
    dil a f = liftc χ N (a : ZMod N) • f

### PAG218::mem_span_iff_dil（theorem、257 行）
theorem mem_span_iff_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    f ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w) ↔
      ∀ a : (ZMod N)ˣ, dil a f = liftc χ N (a : ZMod N) • f

### PAG218::radial_iff_mem_span（theorem、323 行）
theorem radial_iff_mem_span (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    Radial f ↔ f ∈ Submodule.span ℂ
      (Set.range fun w : (N / 1).divisors => kblock N 1 (1 : DirichletCharacter ℂ 1) w)

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

### PAG219::blockIrreducible_of_coprime（theorem、200 行）
theorem blockIrreducible_of_coprime (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hcop : Nat.Coprime c (N / c)) : BlockIrreducible N c χ

### PAG219::pPart_ne_bot（theorem、348 行）
theorem pPart_ne_bot (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) : pPart N c χ p ≠ ⊥

### PAG219::not_blockIrreducible_of_dvd（theorem、365 行）
theorem not_blockIrreducible_of_dvd (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hpL : p ∣ N / c) :
    ¬ BlockIrreducible N c χ

### PAG219::blockIrreducible_iff（theorem、377 行）
theorem blockIrreducible_iff (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : BlockIrreducible N c χ ↔ Nat.Coprime c (N / c)

######## PAG220.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part220
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
end PAG.Part220

### PAG220::layerPart（def、323 行）
noncomputable def layerPart (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (d : ℕ) :
    Submodule ℂ (ZMod N → ℂ) where
  carrier := {f | f ∈ blockSpan N c χ ∧ ∀ x : ZMod N, ¬ InLayer c d x.val → f x = 0}
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun x hx => by
    rw [Pi.add_apply, ha.2 x hx, hb.2 x hx, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun r {f} hf => ⟨Submodule.smul_mem _ r hf.1, fun x hx => by
    rw [Pi.smul_apply, hf.2 x hx, smul_zero]⟩

### PAG220::layerPart_ne_bot（theorem、399 行）
theorem layerPart_ne_bot (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {d : ℕ} (hdL : d ∣ N / c) : layerPart N c χ d ≠ ⊥

### PAG220::layerPart_irreducible（theorem、408 行）
theorem layerPart_irreducible (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (W : Submodule ℂ (ZMod N → ℂ))
    (hW : ShellInvariant W) (hWd : W ≤ layerPart N c χ d) : W = ⊥ ∨ W = layerPart N c χ d

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

######## PAG221.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part221
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
open Classical in
open Classical in
end PAG.Part221

### PAG221::gblock_linearIndependent（theorem、205 行）
theorem gblock_linearIndependent (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    LinearIndependent ℂ (fun v : (N / c).divisors => gblock N c χ v)

######## PAG223.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part223
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part223

### PAG223::blockHom_eq_bot_of_ne（theorem、409 行）
theorem blockHom_eq_bot_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hcc : c ≠ c') : blockHom N c c' χ χ' = ⊥

######## PAG224.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part224
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part224

### PAG224::top_shellInvariant（theorem、379 行）
theorem top_shellInvariant (N : ℕ) [NeZero N] : ShellInvariant (⊤ : Submodule ℂ (ZMod N → ℂ))

### PAG224::mem_dilComm（theorem、428 行）
theorem mem_dilComm (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) :
    T ∈ dilComm N ↔ T ∈ fullComm N ∧ T ∈ dilCommute N

######## PAG227.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part227
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part227

### PAG227::Prim（abbrev、206 行）
abbrev Prim (c : ℕ) : Type := {χ : DirichletCharacter ℂ c // χ.IsPrimitive}

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

### PAG229::isCompl_perpSub（theorem、256 行）
theorem isCompl_perpSub (N : ℕ) [NeZero N] {B : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))}
    (hB : AdjClosed N B) (K : Submodule B (ZMod N → ℂ)) : IsCompl K (perpSub N hB K)

######## PAG232.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part232
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part232

### PAG232::sum_mulLeft_dind（theorem、334 行）
theorem sum_mulLeft_dind (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, LinearMap.mulLeft ℂ (dind N s) = 1

######## PAG233.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part233
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part233

### PAG233::exists_linearIndependent_subalg（theorem、173 行）
theorem exists_linearIndependent_subalg {X : Type*} [Fintype X] (B : Subalgebra ℂ (Module.End ℂ (X → ℂ))) :
    ∃ u : Fin (Module.finrank ℂ B) → Module.End ℂ (X → ℂ), LinearIndependent ℂ u ∧ ∀ i, u i ∈ B

######## PAG239.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part239
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod TensorProduct
end PAG.Part239

### PAG239::span_tensorFamily_eq_top（theorem、89 行）
theorem span_tensorFamily_eq_top {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Submodule.span ℂ (Set.range fun x : (Π p : centerIdx a, Matrix (Prim p.1.1) (Prim p.1.1) ℂ) ×
        (Π q : centerIdx b, Matrix (Prim q.1.1) (Prim q.1.1) ℂ) => tensorFamily hab x.1 x.2) = ⊤

######## PAG244.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part244
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part244

### PAG244::card_fiber_eq（theorem、31 行）
theorem card_fiber_eq {N : ℕ} [NeZero N] (x y : ZMod N) (h : Nat.gcd N y.val = Nat.gcd N x.val) :
    (Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = y)).card =
      (Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card

### PAG244::card_stab_mul_totient（theorem、83 行）
theorem card_stab_mul_totient {N : ℕ} [NeZero N] (x : ZMod N) :
    ((Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card : ℂ) *
      (Nat.totient (N / Nat.gcd N x.val) : ℂ) = Nat.totient N

######## PAG248.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part248
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part248

### PAG248::finrank_sup_add_one（theorem、405 行）
theorem finrank_sup_add_one {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    Module.finrank ℂ ↥(Subalgebra.toSubmodule (oneEAlg N N) ⊔ Subalgebra.toSubmodule (dualOneEAlg N)) + 1 =
      N.divisors.card ^ 2 + 2 * (devSet N).card

######## PAG249.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part249
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part249

### PAG249::finrank_sumSub_primePow_add（theorem、108 行）
theorem finrank_sumSub_primePow_add {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (h3 : 3 ≤ p ^ k) [NeZero (p ^ k)] :
    Module.finrank ℂ (sumSub (p ^ k)) + 3 + 2 * (if p = 2 then 1 else 0) = (k + 1) ^ 2 + 2 * (k + 1)

######## PAG251.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part251
open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
open ZMod (stdAddChar)
open scoped ZMod
end PAG.Part251

### PAG251::mulLeft_dind_mul_self（theorem、71 行）
theorem mulLeft_dind_mul_self (N s : ℕ) :
    LinearMap.mulLeft ℂ (dind N s) * LinearMap.mulLeft ℂ (dind N s) = LinearMap.mulLeft ℂ (dind N s)

######## PAG253.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part253
open Complex PAG.Part218 PAG.Part224
end PAG.Part253

### PAG253::kUnit（def、34 行）
def kUnit {N : ℕ} (n : ℕ) (h : n.Coprime N) : (ZMod N)ˣ := (ZMod.unitOfCoprime n h)⁻¹

### PAG253::eq_top_of_prime（theorem、107 行）
theorem eq_top_of_prime {N : ℕ} [NeZero N] (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) : S = ⊤

### PAG253::primeShiftInv（def、458 行）
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)

### PAG253::scaleShift（def、465 行）
def scaleShift {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k (u + s)

### PAG253::ipG（def、515 行）
noncomputable def ipG {G : Type*} [Fintype G] (f g : G → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

######## PAG256.lean
-- 文脈（open・variable・namespace の行の写し）
namespace PAG.Part256
open ZMod Complex Finset
variable {N : ℕ} [NeZero N]
open Classical in
end PAG.Part256

### PAG256::casKer（def、38 行）
noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

### PAG256::hartley（def、42 行）
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

### PAG256::casKer_eq（theorem、46 行）
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2

### PAG256::parFac（def、65 行）
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

### PAG256::hartley_eq_of_isPrimitive（theorem、95 行）
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y

### PAG256::hartley_eq_zero_of_not_isUnit（theorem、116 行）
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0

### PAG256::rootNum_eq（theorem、129 行）
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)

### PAG256::JH（def、147 行）
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)

### PAG256::JH_eq_rootNum_mul（theorem、161 行）
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u

### PAG256::normSq_rootNum（theorem、168 行）
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1

### PAG256::hartley_units_inv（theorem、187 行）
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1

### PAG256::hartley_one（theorem、214 行）
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar

### PAG256::JH_eq_rootNum_mul_any（theorem、228 行）
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u

### PAG256::isPrimitive_of_prime_of_ne_one（theorem、237 行）
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive

### PAG256::exists_primitive_even_five（theorem、259 行）
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1

### PAG256::removal_counterexample（theorem、288 行）
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1

### PAG256::removal_counterexample_normSq（theorem、308 行）
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2

### PAG256::removal_counterexample_four（theorem、331 行）
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0
