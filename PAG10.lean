/-
  PAG 2.0 Part 6（2026-10-18）
  1. 殻分割の指示関数の点ごとの直交べき等性と、F で定義した畳み込みに対する双対基底のべき等性
  2. gcd(m, p) = 1 なら χ^m も原始的（PAG9 の sq_isPrimitive の一般化）、および χ^p は必ず p^n を経由する
-/
import PAG9

namespace PAG.Part10

/-! ## 1. 双対べき等性（抽象版） -/

section Idem

variable {R : Type*} [CommRing R]

/-- 殻分割 `shell : X → W` の殻 w の（重み a w の）指示関数。 -/
def ind {X W : Type*} [DecidableEq W] (shell : X → W) (a : W → R) (w : W) : X → R :=
  fun x => if shell x = w then a w else 0

/-- 点ごとの直交べき等性: e_{w₀} · e_{w₁} = δ a_{w₀} e_{w₀}。 -/
theorem ind_mul_ind {X W : Type*} [DecidableEq W] (shell : X → W) (a : W → R) (w₀ w₁ : W) :
    ind shell a w₀ * ind shell a w₁ = if w₀ = w₁ then a w₀ • ind shell a w₀ else 0 := by
  funext x
  by_cases h : w₀ = w₁
  · subst h
    by_cases hx : shell x = w₀ <;> simp [ind, hx]
  · simp only [h, ↓reduceIte]
    by_cases hx : shell x = w₀
    · simp [ind, hx, h]
    · simp [ind, hx]

variable {A : Type*} [CommRing A] [Algebra R A]

/-- F で定義した畳み込み B(f, g) = α F⁻¹(F f · F g)。 -/
def Bcv (F : A ≃ₗ[R] A) (α : R) (f g : A) : A := α • F.symm (F f * F g)

theorem Bcv_comm (F : A ≃ₗ[R] A) (α : R) (f g : A) : Bcv F α f g = Bcv F α g f := by
  unfold Bcv; rw [mul_comm]

theorem Bcv_assoc (F : A ≃ₗ[R] A) (α : R) (f g h : A) :
    Bcv F α (Bcv F α f g) h = Bcv F α f (Bcv F α g h) := by
  unfold Bcv
  simp only [map_smul, LinearEquiv.apply_symm_apply, smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- **双対基底の直交べき等性**: ẽ_w = F⁻¹ e_w は B(ẽ_{w₀}, ẽ_{w₁}) = δ α c_{w₀} ẽ_{w₀} を満たす。 -/
theorem Bcv_dual {W : Type*} [DecidableEq W] (F : A ≃ₗ[R] A) (α : R) (e : W → A) (c : W → R)
    (he : ∀ w₀ w₁, e w₀ * e w₁ = if w₀ = w₁ then c w₀ • e w₀ else 0) (w₀ w₁ : W) :
    Bcv F α (F.symm (e w₀)) (F.symm (e w₁)) =
      if w₀ = w₁ then (α * c w₀) • F.symm (e w₀) else 0 := by
  unfold Bcv
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, he]
  split_ifs
  · rw [map_smul, smul_smul]
  · rw [map_zero, smul_zero]

/-- n 重畳み込み f^{*(n+1)}。 -/
def cvpow (F : A ≃ₗ[R] A) (α : R) (f : A) : ℕ → A
  | 0 => f
  | n + 1 => Bcv F α f (cvpow F α f n)

/-- **n 重べき**: e_w² = c_w e_w なら ẽ_w^{*(n+1)} = (α c_w)^n ẽ_w。 -/
theorem cvpow_dual (F : A ≃ₗ[R] A) (α : R) (e : A) (c : R) (he : e * e = c • e) (n : ℕ) :
    cvpow F α (F.symm e) n = (α * c) ^ n • F.symm e := by
  induction n with
  | zero => simp [cvpow]
  | succ n ih =>
    rw [cvpow, ih]
    unfold Bcv
    rw [map_smul, LinearEquiv.apply_symm_apply, mul_smul_comm, he, smul_smul, map_smul, smul_smul]
    congr 1; ring

/-- 正規化 ε = (α c)⁻¹ ẽ はべき等元: B(ε, ε) = ε（α c = 0 なら両辺 0 なので仮定不要）。 -/
theorem Bcv_idempotent {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B]
    (F : B ≃ₗ[K] B) (α : K) (e : B) (c : K) (he : e * e = c • e) :
    Bcv F α ((α * c)⁻¹ • F.symm e) ((α * c)⁻¹ • F.symm e) = (α * c)⁻¹ • F.symm e := by
  unfold Bcv
  simp only [map_smul, LinearEquiv.apply_symm_apply, smul_mul_smul_comm, he, smul_smul]
  congr 1
  field_simp

/-- 殻分割の指示関数への適用（A = X → R）。 -/
theorem Bcv_dual_ind {X W : Type*} [DecidableEq W] (shell : X → W) (a : W → R)
    (F : (X → R) ≃ₗ[R] (X → R)) (α : R) (w₀ w₁ : W) :
    Bcv F α (F.symm (ind shell a w₀)) (F.symm (ind shell a w₁)) =
      if w₀ = w₁ then (α * a w₀) • F.symm (ind shell a w₀) else 0 :=
  Bcv_dual F α (ind shell a) a (ind_mul_ind shell a) w₀ w₁

end Idem

/-! ## 2. 互いに素なべきでの原始性の保存と、p 乗での降下 -/

section Pow

variable {p n : ℕ} [hp : Fact p.Prime]

/-- z^m = 1 かつ z^p = 1、gcd(m, p) = 1 ⇒ z = 1。 -/
theorem eq_one_of_pow_coprime {M : Type*} [Monoid M] {z : M} {m q : ℕ} (hc : Nat.Coprime m q)
    (hm : z ^ m = 1) (hq : z ^ q = 1) : z = 1 := by
  have := pow_gcd_eq_one.mpr ⟨hm, hq⟩
  rwa [Nat.Coprime.gcd_eq_one hc, pow_one] at this

/-- **gcd(m, p) = 1 なら χ^m は原始的**（法 p^(n+1)、n ≥ 1）。p が奇数である必要はない。 -/
theorem pow_isPrimitive_of_coprime (hn : 1 ≤ n) {m : ℕ} (hcop : Nat.Coprime m p)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) : (χ ^ m).IsPrimitive := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hp.out.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hcop)
  obtain ⟨u, hker, hne⟩ := PAG.Part8.exists_ker_ne_one_of_primitive χ hχ
  have hup : (u : ZMod (p ^ (n + 1))) ^ p = 1 := PAG.Part9.ker_pow_p hn u hker
  have hχp : χ u ^ p = 1 := by rw [← map_pow, hup, map_one]
  have hpow : (χ ^ m) u ≠ 1 := by
    intro h
    apply hne
    rw [MulChar.pow_apply' χ hm0] at h
    exact eq_one_of_pow_coprime hcop h hχp
  rw [DirichletCharacter.isPrimitive_def]
  obtain ⟨k, hk, hkeq⟩ :=
    (Nat.dvd_prime_pow hp.out).mp (DirichletCharacter.conductor_dvd_level (χ ^ m))
  by_contra hne'
  have hkn : k ≤ n := by
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · omega
    · exact absurd (by rw [hkeq, show k = n + 1 by omega]) hne'
  have hft := DirichletCharacter.factorsThrough_conductor (χ ^ m)
  rw [hkeq] at hft
  have hdk : p ^ k ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ m) hdk] at hft
  have hmem : u ∈ (ZMod.unitsMap hdk).ker := by
    rw [MonoidHom.mem_ker, ← ZMod.unitsMap_comp (pow_dvd_pow p hkn) (pow_dvd_pow p (Nat.le_succ n)),
      MonoidHom.comp_apply, hker, map_one]
  have := hft hmem
  rw [MonoidHom.mem_ker] at this
  apply hpow
  have h' := congrArg (fun w : ℂˣ => (w : ℂ)) this
  simpa [MulChar.coe_toUnitHom] using h'

/-- 系: PAG9 の sq_isPrimitive（m = 2、p 奇数）の再導出。 -/
theorem sq_isPrimitive' (hodd : Odd p) (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) : (χ ^ 2).IsPrimitive :=
  pow_isPrimitive_of_coprime hn (Nat.coprime_two_left.mpr hodd) χ hχ

/-- **p 乗での降下**: 任意の χ（法 p^(n+1)、n ≥ 1）について χ^p は p^n を経由する。 -/
theorem pow_p_factorsThrough (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    (χ ^ p).FactorsThrough (p ^ n) := by
  have hd : p ^ n ∣ p ^ (n + 1) := pow_dvd_pow p (Nat.le_succ n)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ ^ p) hd]
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have hup : (u : ZMod (p ^ (n + 1))) ^ p = 1 := PAG.Part9.ker_pow_p hn u hu
  ext
  simp only [MulChar.coe_toUnitHom, Units.val_one]
  rw [MulChar.pow_apply' χ hp.out.ne_zero, ← map_pow, hup, map_one]

/-- 系: n ≥ 1 なら χ^p は法 p^(n+1) で原始的でない（導手が真に下がる）。 -/
theorem pow_p_not_isPrimitive (hn : 1 ≤ n) (χ : DirichletCharacter ℂ (p ^ (n + 1))) :
    ¬ (χ ^ p).IsPrimitive := by
  intro h
  rw [DirichletCharacter.isPrimitive_def] at h
  have hle : (χ ^ p).conductor ≤ p ^ n :=
    Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr (pow_p_factorsThrough hn χ))
  rw [h] at hle
  have : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp.out.one_lt (Nat.lt_succ_self n)
  omega

end Pow

end PAG.Part10

#print axioms PAG.Part10.ind_mul_ind
#print axioms PAG.Part10.Bcv_comm
#print axioms PAG.Part10.Bcv_assoc
#print axioms PAG.Part10.Bcv_dual
#print axioms PAG.Part10.cvpow_dual
#print axioms PAG.Part10.Bcv_idempotent
#print axioms PAG.Part10.Bcv_dual_ind
#print axioms PAG.Part10.eq_one_of_pow_coprime
#print axioms PAG.Part10.pow_isPrimitive_of_coprime
#print axioms PAG.Part10.sq_isPrimitive'
#print axioms PAG.Part10.pow_p_factorsThrough
#print axioms PAG.Part10.pow_p_not_isPrimitive
