/-
  PAG 2.0 Part 190（2026-10-23）— 互いに素な法の指標の分解・原始性と、素数冪をはがす判定
  N₁, N₂ ≥ 1 は互いに素、ρ(x) = (x mod N₁, x mod N₂)、z(χ) = τ(χ)/√N（stdAddChar）。
  1. rho_bijective：ρ は全単射（Part 189 の param から）。crt：環の同型 ZMod (N₁N₂) ≃ ZMod N₁ × ZMod N₂
  2. decomp：法 N₁N₂ の指標 χ は χ = χ₁′χ₂′（χ₁(a) = χ(crt⁻¹(a, 1))、χ₂(b) = χ(crt⁻¹(1, b))）。
     comp₁_mul / comp₂_mul：分け方は一通り（comp₁(χ₁′χ₂′) = χ₁、comp₂(χ₁′χ₂′) = χ₂）
  3. isPrimitive_left / isPrimitive_right：χ₁′χ₂′ が原始的なら χ₁, χ₂ も原始的（互いに素は不要）。
     factorsThrough_mul_iff：χ₁′χ₂′ が d₁d₂ を経由 ⇔ χ₁ が d₁ を、χ₂ が d₂ を経由。
     isPrimitive_mul / isPrimitive_iff：χ が原始的 ⇔ 2 つの成分がどちらも原始的
  4. isIntegral_gaussSum：ガウス和は代数的整数
  5. sep_not_root：素数 q の位数 ≥ 3 の指標 χ₁ と、法 M（q と互いに素）の原始指標 χ₂ について、
     z(χ₁)z(χ₂) は 1 の冪根でない（ベズーと ℤ_q の付値、Part 187 の方法）
  6. peel_root_iff：p 素数、e ≥ 1、p^e と M が互いに素、χ₁ 原始的（法 p^e）、χ₂ 原始的（法 M）で
     z(χ₁′χ₂′) が 1 の冪根 ⇔ (e ≥ 2 または ord χ₁ = 2) かつ z(χ₂) が 1 の冪根
  7. two_prime_power_root_iff：法 p^e q^f（p ≠ q）の原始指標 χ で、z(χ) が 1 の冪根 ⇔
     (e ≥ 2 または ord χ₁ = 2) かつ (f ≥ 2 または ord χ₂ = 2)（χ₁, χ₂ は χ の成分）
-/
import PAG193

namespace PAG.Part194

open Complex Finset
open ZMod (stdAddChar)

/-! ### 1. 中国剰余定理 -/

/-- 還元の組 ρ(x) = (x mod N₁, x mod N₂)。 -/
noncomputable def rho (N₁ N₂ : ℕ) : ZMod (N₁ * N₂) →+* ZMod N₁ × ZMod N₂ :=
  RingHom.prod (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁)) (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂))

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- **1.** N₁, N₂ が互いに素なら ρ は全単射。 -/
theorem rho_bijective (hcop : N₁.Coprime N₂) : Function.Bijective (rho N₁ N₂) := by
  have hinj : Function.Injective (rho N₁ N₂) := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := (PAG.Part193.param_bijective hcop).2 x
    obtain ⟨b, rfl⟩ := (PAG.Part193.param_bijective hcop).2 y
    have h1 := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    simp only [rho, RingHom.prod_apply, PAG.Part193.param_cast₁, PAG.Part193.param_cast₂] at h1 h2
    have u₁ : IsUnit (N₂ : ZMod N₁) := (ZMod.isUnit_iff_coprime N₂ N₁).mpr hcop.symm
    have u₂ : IsUnit (N₁ : ZMod N₂) := (ZMod.isUnit_iff_coprime N₁ N₂).mpr hcop
    rw [Prod.ext (u₁.mul_left_inj.mp h1) (u₂.mul_left_inj.mp h2)]
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [ZMod.card]

/-- 環の同型 ZMod (N₁N₂) ≃ ZMod N₁ × ZMod N₂。 -/
noncomputable def crt (hcop : N₁.Coprime N₂) : ZMod (N₁ * N₂) ≃+* ZMod N₁ × ZMod N₂ :=
  RingEquiv.ofBijective (rho N₁ N₂) (rho_bijective hcop)

theorem crt_apply (hcop : N₁.Coprime N₂) (x : ZMod (N₁ * N₂)) :
    crt hcop x = (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x,
      ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x) := rfl

/-! ### 2. 指標の分解 -/

/-- 第 1 成分 χ₁(a) = χ(crt⁻¹(a, 1))。 -/
noncomputable def comp₁ (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    DirichletCharacter ℂ N₁ where
  toFun a := χ ((crt hcop).symm (a, 1))
  map_one' := by
    show χ ((crt hcop).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((crt hcop).symm (a * b, 1)) = χ ((crt hcop).symm (a, 1)) * χ ((crt hcop).symm (b, 1))
    rw [show ((a * b, 1) : ZMod N₁ × ZMod N₂) = (a, 1) * (b, 1) by simp, map_mul, map_mul]
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have := hu.map (crt hcop)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).1

/-- 第 2 成分 χ₂(b) = χ(crt⁻¹(1, b))。 -/
noncomputable def comp₂ (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    DirichletCharacter ℂ N₂ where
  toFun b := χ ((crt hcop).symm (1, b))
  map_one' := by
    show χ ((crt hcop).symm 1) = 1
    rw [map_one, map_one]
  map_mul' a b := by
    show χ ((crt hcop).symm (1, a * b)) = χ ((crt hcop).symm (1, a)) * χ ((crt hcop).symm (1, b))
    rw [show ((1, a * b) : ZMod N₁ × ZMod N₂) = (1, a) * (1, b) by simp, map_mul, map_mul]
  map_nonunit' b hb := by
    apply MulChar.map_nonunit
    intro hu
    apply hb
    have := hu.map (crt hcop)
    rw [RingEquiv.apply_symm_apply] at this
    exact (Prod.isUnit_iff.mp this).2

theorem comp₁_apply (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) (a : ZMod N₁) :
    comp₁ hcop χ a = χ ((crt hcop).symm (a, 1)) := rfl

theorem comp₂_apply (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) (b : ZMod N₂) :
    comp₂ hcop χ b = χ ((crt hcop).symm (1, b)) := rfl

/-- **2. 分解**：χ = χ₁′χ₂′（χ₁ = comp₁、χ₂ = comp₂ を法 N₁N₂ に持ち上げた積）。 -/
theorem decomp (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    χ = (comp₁ hcop χ).changeLevel (dvd_mul_right N₁ N₂) *
      (comp₂ hcop χ).changeLevel (dvd_mul_left N₂ N₁) := by
  refine MulChar.ext' (fun x => ?_)
  rw [PAG.Part193.mul_changeLevel_apply, comp₁_apply, comp₂_apply, ← map_mul, ← map_mul,
    Prod.mk_mul_mk, mul_one, one_mul]
  congr 1
  apply (crt hcop).injective
  rw [RingEquiv.apply_symm_apply, crt_apply]

/-- **2b. 一意性**：comp₁ (χ₁′χ₂′) = χ₁。 -/
theorem comp₁_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    comp₁ hcop (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) = χ₁ := by
  refine MulChar.ext' (fun a => ?_)
  have h := (crt hcop).apply_symm_apply (a, 1)
  rw [crt_apply, Prod.mk.injEq] at h
  rw [comp₁_apply, PAG.Part193.mul_changeLevel_apply, h.1, h.2, map_one, mul_one]

/-- **2b. 一意性**：comp₂ (χ₁′χ₂′) = χ₂。 -/
theorem comp₂_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    comp₂ hcop (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) = χ₂ := by
  refine MulChar.ext' (fun b => ?_)
  have h := (crt hcop).apply_symm_apply (1, b)
  rw [crt_apply, Prod.mk.injEq] at h
  rw [comp₂_apply, PAG.Part193.mul_changeLevel_apply, h.1, h.2, map_one, one_mul]

/-! ### 3. 原始性 -/

/-- **3a.** χ₁′χ₂′ が原始的なら χ₁ も原始的（互いに素の仮定は要らない）。 -/
theorem isPrimitive_left (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂)
    (h : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive) :
    χ₁.IsPrimitive := by
  by_contra hχ₁
  set d := χ₁.conductor with hd_def
  have hd : d ∣ N₁ := DirichletCharacter.conductor_dvd_level χ₁
  have hN₁ : 0 < N₁ := Nat.pos_of_ne_zero (NeZero.ne N₁)
  have hN₂ : 0 < N₂ := Nat.pos_of_ne_zero (NeZero.ne N₂)
  have hdlt : d < N₁ := lt_of_le_of_ne (Nat.le_of_dvd hN₁ hd) hχ₁
  obtain ⟨hd', χ₀, hχ₀⟩ := DirichletCharacter.factorsThrough_conductor χ₁
  have hfac : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).FactorsThrough
      (d * N₂) := by
    refine ⟨Nat.mul_dvd_mul_right hd N₂,
      χ₀.changeLevel (dvd_mul_right d N₂) * χ₂.changeLevel (dvd_mul_left N₂ d), ?_⟩
    rw [map_mul]
    congr 1
    · rw [hχ₀, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    · rw [← DirichletCharacter.changeLevel_trans]
  have hle : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).conductor
      ≤ d * N₂ := Nat.sInf_le hfac
  rw [(DirichletCharacter.isPrimitive_def _).mp h] at hle
  have := Nat.le_of_mul_le_mul_right hle hN₂
  omega

/-- **3b.** χ₁′χ₂′ が原始的なら χ₂ も原始的（互いに素の仮定は要らない）。 -/
theorem isPrimitive_right (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂)
    (h : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive) :
    χ₂.IsPrimitive := by
  by_contra hχ₂
  set d := χ₂.conductor with hd_def
  have hd : d ∣ N₂ := DirichletCharacter.conductor_dvd_level χ₂
  have hN₁ : 0 < N₁ := Nat.pos_of_ne_zero (NeZero.ne N₁)
  have hN₂ : 0 < N₂ := Nat.pos_of_ne_zero (NeZero.ne N₂)
  have hdlt : d < N₂ := lt_of_le_of_ne (Nat.le_of_dvd hN₂ hd) hχ₂
  obtain ⟨hd', χ₀, hχ₀⟩ := DirichletCharacter.factorsThrough_conductor χ₂
  have hfac : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).FactorsThrough
      (N₁ * d) := by
    refine ⟨Nat.mul_dvd_mul_left N₁ hd,
      χ₁.changeLevel (dvd_mul_right N₁ d) * χ₀.changeLevel (dvd_mul_left d N₁), ?_⟩
    rw [map_mul]
    congr 1
    · rw [← DirichletCharacter.changeLevel_trans]
    · rw [hχ₀, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
  have hle : (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).conductor
      ≤ N₁ * d := Nat.sInf_le hfac
  rw [(DirichletCharacter.isPrimitive_def _).mp h] at hle
  have := Nat.le_of_mul_le_mul_left hle hN₁
  omega

omit [NeZero N₁] [NeZero N₂] in
/-- 成分ごとの持ち上げ：法 d₁d₂ の積 ψ₁′ψ₂′ を法 N₁N₂ に持ち上げたものは、ψ₁ を N₁ に、ψ₂ を N₂ に
  持ち上げてから掛けたものに等しい。 -/
theorem changeLevel_mul_split {d₁ d₂ : ℕ} (h₁ : d₁ ∣ N₁) (h₂ : d₂ ∣ N₂)
    (ψ₁ : DirichletCharacter ℂ d₁) (ψ₂ : DirichletCharacter ℂ d₂) :
    DirichletCharacter.changeLevel (Nat.mul_dvd_mul h₁ h₂)
        (ψ₁.changeLevel (dvd_mul_right d₁ d₂) * ψ₂.changeLevel (dvd_mul_left d₂ d₁)) =
      (ψ₁.changeLevel h₁).changeLevel (dvd_mul_right N₁ N₂) *
        (ψ₂.changeLevel h₂).changeLevel (dvd_mul_left N₂ N₁) := by
  rw [map_mul, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans,
    ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]

/-- **3c.** d₁ ∣ N₁、d₂ ∣ N₂ のとき、χ₁′χ₂′ が d₁d₂ を経由 ⇔ χ₁ が d₁ を、χ₂ が d₂ を経由。 -/
theorem factorsThrough_mul_iff (hcop : N₁.Coprime N₂) {d₁ d₂ : ℕ} (h₁ : d₁ ∣ N₁) (h₂ : d₂ ∣ N₂)
    (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).FactorsThrough
        (d₁ * d₂) ↔ χ₁.FactorsThrough d₁ ∧ χ₂.FactorsThrough d₂ := by
  constructor
  · rintro ⟨hd, ψ, hψ⟩
    have : NeZero d₁ := ⟨fun h0 => NeZero.ne N₁ (Nat.eq_zero_of_zero_dvd (h0 ▸ h₁))⟩
    have : NeZero d₂ := ⟨fun h0 => NeZero.ne N₂ (Nat.eq_zero_of_zero_dvd (h0 ▸ h₂))⟩
    have hcop' : d₁.Coprime d₂ := Nat.Coprime.coprime_dvd_left h₁ (Nat.Coprime.coprime_dvd_right h₂ hcop)
    rw [decomp hcop' ψ, changeLevel_mul_split h₁ h₂] at hψ
    refine ⟨⟨h₁, comp₁ hcop' ψ, ?_⟩, ⟨h₂, comp₂ hcop' ψ, ?_⟩⟩
    · have := congrArg (comp₁ hcop) hψ
      rwa [comp₁_mul, comp₁_mul] at this
    · have := congrArg (comp₂ hcop) hψ
      rwa [comp₂_mul, comp₂_mul] at this
  · rintro ⟨⟨hd₁, ψ₁, hψ₁⟩, ⟨hd₂, ψ₂, hψ₂⟩⟩
    refine ⟨Nat.mul_dvd_mul h₁ h₂,
      ψ₁.changeLevel (dvd_mul_right d₁ d₂) * ψ₂.changeLevel (dvd_mul_left d₂ d₁), ?_⟩
    rw [changeLevel_mul_split h₁ h₂, ← hψ₁, ← hψ₂]

/-- **3d.** χ₁, χ₂ が原始的なら χ₁′χ₂′ も原始的。 -/
theorem isPrimitive_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive := by
  set χ := χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁) with hχ
  set d := χ.conductor with hd_def
  have hd : d ∣ N₁ * N₂ := DirichletCharacter.conductor_dvd_level χ
  have hsplit : d = d.gcd N₁ * d.gcd N₂ := by
    rw [← Nat.Coprime.gcd_mul d hcop, Nat.gcd_eq_left hd]
  have hfac : χ.FactorsThrough (d.gcd N₁ * d.gcd N₂) := by
    rw [← hsplit]; exact DirichletCharacter.factorsThrough_conductor χ
  obtain ⟨f₁, f₂⟩ :=
    (factorsThrough_mul_iff hcop (Nat.gcd_dvd_right d N₁) (Nat.gcd_dvd_right d N₂) χ₁ χ₂).mp hfac
  have c₁ : χ₁.conductor ≤ d.gcd N₁ := Nat.sInf_le f₁
  have c₂ : χ₂.conductor ≤ d.gcd N₂ := Nat.sInf_le f₂
  rw [(DirichletCharacter.isPrimitive_def _).mp h₁] at c₁
  rw [(DirichletCharacter.isPrimitive_def _).mp h₂] at c₂
  have e₁ : d.gcd N₁ = N₁ :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N₁)) (Nat.gcd_dvd_right _ _)) c₁
  have e₂ : d.gcd N₂ = N₂ :=
    le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N₂)) (Nat.gcd_dvd_right _ _)) c₂
  rw [DirichletCharacter.isPrimitive_def, ← hd_def, hsplit, e₁, e₂]

/-- **3e.** 法 N₁N₂ の指標 χ が原始的 ⇔ 成分 comp₁ χ, comp₂ χ がどちらも原始的。 -/
theorem isPrimitive_iff (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    χ.IsPrimitive ↔ (comp₁ hcop χ).IsPrimitive ∧ (comp₂ hcop χ).IsPrimitive := by
  constructor
  · intro h
    rw [decomp hcop χ] at h
    exact ⟨isPrimitive_left _ _ h, isPrimitive_right _ _ h⟩
  · rintro ⟨h₁, h₂⟩
    rw [decomp hcop χ]
    exact isPrimitive_mul hcop _ _ h₁ h₂

/-! ### 4. ガウス和は代数的整数 -/

/-- **4.** 法 N のディリクレ指標のガウス和（stdAddChar）は代数的整数。 -/
theorem isIntegral_gaussSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsIntegral ℤ (gaussSum χ stdAddChar) := by
  have hχv : ∀ x : ZMod N, IsIntegral ℤ (χ x) := by
    intro x
    by_cases hx : IsUnit x
    · obtain ⟨u, rfl⟩ := hx
      exact IsIntegral.of_pow (orderOf_pos u) (by rw [PAG.Part193.chi_unit_root]; exact isIntegral_one)
    · rw [MulChar.map_nonunit _ hx]; exact isIntegral_zero
  have hψv : ∀ x : ZMod N, IsIntegral ℤ (stdAddChar x : ℂ) := by
    intro x
    have hpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    refine IsIntegral.of_pow hpos ?_
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    exact isIntegral_one
  have : gaussSum χ stdAddChar ∈ integralClosure ℤ ℂ :=
    sum_mem (fun x _ => mul_mem ((mem_integralClosure_iff ℤ ℂ).mpr (hχv x))
      ((mem_integralClosure_iff ℤ ℂ).mpr (hψv x)))
  exact (mem_integralClosure_iff ℤ ℂ).mp this

/-! ### 5. 素数の部分を分離する -/

/-- **5.** q 素数、M ≥ 1 は q と互いに素、χ₁（法 q）の位数 ≥ 3、χ₂（法 M）原始的なら、
  z(χ₁)z(χ₂) は 1 の冪根でない。
  証明：Y = z₁^{2n} = U/V（Part 187 の `exists_UV`、a = 1 の位置だけ 1）、W = z₂^{2n}。
  Y^N W^N = 1 から Y^N = W^{−N}。q^{M₀}Y^{±1} は代数的整数、M^n W^{±1} は τ(χ₂^{±1})^{2n} で代数的整数。
  ベズーで Y^{±N} が代数的整数になり、ℤ_q の付値で S_1(a) = n − 2 = 0、n ≥ 3 に反する。 -/
theorem sep_not_root {q M : ℕ} [hq : Fact q.Prime] [NeZero M] (hqM : q.Coprime M)
    (χ₁ : DirichletCharacter ℂ q) (hn : 3 ≤ orderOf χ₁) (χ₂ : DirichletCharacter ℂ M)
    (hχ₂ : χ₂.IsPrimitive) (N : ℕ) (hN : 0 < N) :
    ((gaussSum χ₁ stdAddChar / ((Real.sqrt (q : ℝ) : ℝ) : ℂ)) *
      (gaussSum χ₂ stdAddChar / ((Real.sqrt (M : ℝ) : ℝ) : ℂ))) ^ N ≠ 1 := by
  intro h
  set a : ℕ → ℤ := fun j => if j = 1 then 1 else 0 with ha
  obtain ⟨A, U, V, M₀, hYUV, h1, h2, hU0, hV0, hval⟩ :=
    PAG.Part191.exists_UV (p := q) χ₁ (ZMod.isPrimitive_stdAddChar q) (by omega) a
  obtain ⟨φ, hφU, hφV, hdiff⟩ := hval 1 (Nat.coprime_one_left _)
  set n := orderOf χ₁ with hn_def
  have h1n : 1 < n := by omega
  -- a の積は z₁
  have hprod : ∏ j ∈ Ico 1 n, (gaussSum (χ₁ ^ j) stdAddChar / ((Real.sqrt q : ℝ) : ℂ)) ^ a j
      = gaussSum χ₁ stdAddChar / ((Real.sqrt q : ℝ) : ℂ) := by
    rw [prod_eq_single 1]
    · simp [ha]
    · intro j _ hj; simp [ha, hj]
    · intro hnot; exact absurd (mem_Ico.mpr ⟨le_refl 1, h1n⟩) hnot
  set z₁ := gaussSum χ₁ stdAddChar / ((Real.sqrt q : ℝ) : ℂ) with hz₁
  set z₂ := gaussSum χ₂ stdAddChar / ((Real.sqrt M : ℝ) : ℂ) with hz₂
  set Y := z₁ ^ (2 * n) with hY_def
  set W := z₂ ^ (2 * n) with hW_def
  have hYUV' : Y = (U : ℂ) / (V : ℂ) := by rw [hY_def, ← hprod]; exact hYUV
  -- W = τ₂^{2n}/M^n、W⁻¹ = τ(χ₂⁻¹)^{2n}/M^n
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hsqM : ((Real.sqrt (M : ℝ) : ℝ) : ℂ) ^ 2 = (M : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have hWe : W = gaussSum χ₂ stdAddChar ^ (2 * n) / (M : ℂ) ^ n := by
    rw [hW_def, hz₂, div_pow, pow_mul ((Real.sqrt (M : ℝ) : ℝ) : ℂ) 2 n, hsqM]
  have hτ0 : gaussSum χ₂ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hχ₂
  have hgg := PAG.Part16.gauss_mul_gauss_inv_eq hχ₂
  have hc2 : χ₂ (-1) ^ 2 = 1 := by rw [sq]; exact PAG.Part9.chi_neg_one_sq χ₂
  have hτ' : gaussSum χ₂⁻¹ stdAddChar = χ₂ (-1) * M / gaussSum χ₂ stdAddChar := by
    rw [← hgg]; field_simp
  have hMW : (M : ℂ) ^ n * W = gaussSum χ₂ stdAddChar ^ (2 * n) := by
    rw [hWe]; field_simp
  have hMWinv : (M : ℂ) ^ n * W⁻¹ = gaussSum χ₂⁻¹ stdAddChar ^ (2 * n) := by
    rw [hWe, hτ', div_pow, mul_pow, pow_mul (χ₂ (-1)) 2 n, hc2, one_pow, one_mul, inv_div]
    field_simp
    ring
  -- Y^N W^N = 1
  have hYW : Y ^ N * W ^ N = 1 := by
    rw [hY_def, hW_def, ← pow_mul, ← pow_mul, ← mul_pow, mul_comm (2 * n) N, pow_mul, h, one_pow]
  have hYN : Y ^ N = W⁻¹ ^ N := by rw [inv_pow]; exact eq_inv_of_mul_eq_one_left hYW
  have hYNinv : Y⁻¹ ^ N = W ^ N := by rw [inv_pow, hYN, inv_pow, inv_inv]
  -- ベズー
  have hcop : IsCoprime ((q : ℤ) ^ (M₀ * N)) ((M : ℤ) ^ (n * N)) :=
    (Nat.isCoprime_iff_coprime.mpr hqM).pow
  have hq1 : IsIntegral ℤ ((q : ℂ) ^ M₀ * Y) := by rw [hYUV']; exact h1
  have hq2 : IsIntegral ℤ ((q : ℂ) ^ M₀ * Y⁻¹) := by rw [hYUV', inv_div]; exact h2
  have hint : IsIntegral ℤ (Y ^ N) := by
    apply PAG.Part191.isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [pow_mul, ← mul_pow]
      exact hq1.pow _
    · push_cast
      rw [hYN, pow_mul, ← mul_pow, hMWinv]
      exact (PAG.Part194.isIntegral_gaussSum χ₂⁻¹).pow _ |>.pow _
  have hint' : IsIntegral ℤ (Y⁻¹ ^ N) := by
    apply PAG.Part191.isIntegral_of_coprime _ _ _ hcop
    · push_cast
      rw [pow_mul, ← mul_pow]
      exact hq2.pow _
    · push_cast
      rw [hYNinv, pow_mul, ← mul_pow, hMW]
      exact (PAG.Part194.isIntegral_gaussSum χ₂).pow _ |>.pow _
  -- ℤ_q の付値
  have hZ : IsIntegral ℤ (((U ^ N : A) : ℂ) / ((V ^ N : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow, ← hYUV']; exact hint
  have hZinv : IsIntegral ℤ (((V ^ N : A) : ℂ) / ((U ^ N : A) : ℂ)) := by
    rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← div_pow, ← inv_div, ← hYUV']; exact hint'
  have v1 := PAG.Part191.val_le_of_isIntegral φ (U ^ N) (V ^ N)
    (by rw [map_pow]; exact pow_ne_zero _ hφU) (by rw [map_pow]; exact pow_ne_zero _ hφV) hZ
  have v2 := PAG.Part191.val_le_of_isIntegral φ (V ^ N) (U ^ N)
    (by rw [map_pow]; exact pow_ne_zero _ hφV) (by rw [map_pow]; exact pow_ne_zero _ hφU) hZinv
  rw [map_pow, map_pow, PadicInt.valuation_pow, PadicInt.valuation_pow] at v1 v2
  have heq : (φ U).valuation = (φ V).valuation :=
    le_antisymm (Nat.le_of_mul_le_mul_left v2 hN) (Nat.le_of_mul_le_mul_left v1 hN)
  have h1mod : 1 % n = 1 := Nat.mod_eq_of_lt h1n
  have hS : ∑ j ∈ Ico 1 n, a j * ((n : ℤ) - 2 * ((1 * j % n : ℕ) : ℤ)) = (n : ℤ) - 2 := by
    rw [sum_eq_single 1]
    · simp [ha, h1mod]
    · intro j _ hj; simp [ha, hj]
    · intro hnot; exact absurd (mem_Ico.mpr ⟨le_refl 1, h1n⟩) hnot
  rw [hS, heq, sub_self] at hdiff
  omega

/-! ### 6. 素数冪をはがす -/

/-- **6. はがす判定**：p 素数、e ≥ 1、p^e と M が互いに素、χ₁（法 p^e）と χ₂（法 M）が原始的なら、
  z(χ₁′χ₂′) が 1 の冪根 ⇔ (e ≥ 2 または ord χ₁ = 2) かつ z(χ₂) が 1 の冪根。 -/
theorem peel_root_iff {p M : ℕ} [hp : Fact p.Prime] [NeZero M] (e : ℕ) (he : 1 ≤ e)
    (hcop : (p ^ e).Coprime M) (χ₁ : DirichletCharacter ℂ (p ^ e)) (hχ₁ : χ₁.IsPrimitive)
    (χ₂ : DirichletCharacter ℂ M) (hχ₂ : χ₂.IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧ (gaussSum (χ₁.changeLevel (dvd_mul_right (p ^ e) M) *
        χ₂.changeLevel (dvd_mul_left M (p ^ e))) stdAddChar /
          ((Real.sqrt ((p ^ e * M : ℕ) : ℝ) : ℝ) : ℂ)) ^ N = 1) ↔
      (2 ≤ e ∨ orderOf χ₁ = 2) ∧
        ∃ N : ℕ, 0 < N ∧ (gaussSum χ₂ stdAddChar / ((Real.sqrt (M : ℝ) : ℝ) : ℂ)) ^ N = 1 := by
  rw [PAG.Part193.composite_root_iff hcop]
  have hs : (∃ N : ℕ, 0 < N ∧ (gaussSum χ₁ stdAddChar / ((Real.sqrt ((p ^ e : ℕ) : ℝ) : ℝ) : ℂ)) ^ N
      = 1) ↔ (2 ≤ e ∨ orderOf χ₁ = 2) := by
    rw [Nat.cast_pow]; exact PAG.Part187.single_root_iff (p := p) e he χ₁ hχ₁
  constructor
  · intro h
    by_cases hc : 2 ≤ e ∨ orderOf χ₁ = 2
    · obtain ⟨K, hK, hz1⟩ := hs.mpr hc
      exact ⟨hc, (PAG.Part183.root_mul_iff _ _ K hK hz1).mp h⟩
    · exfalso
      obtain ⟨hc1, hc2⟩ := not_or.mp hc
      have he1 : e = 1 := by omega
      subst he1
      have hp1 : Fact (p ^ 1).Prime := ⟨by rw [pow_one]; exact hp.out⟩
      -- 原始的なので χ₁ ≠ 1、よって位数 ≥ 3
      have hne : χ₁ ≠ 1 := by
        intro h1
        have hcond := (DirichletCharacter.isPrimitive_def _).mp hχ₁
        rw [h1, DirichletCharacter.conductor_one] at hcond
        have := hp1.out.two_le
        omega
      have hpos := PAG.Part185.orderOf_pos_chi (p := p ^ 1) χ₁
      have hne1 : orderOf χ₁ ≠ 1 := fun h1 => hne (orderOf_eq_one_iff.mp h1)
      have o3 : 3 ≤ orderOf χ₁ := by omega
      obtain ⟨N, hN, hh⟩ := h
      exact sep_not_root (q := p ^ 1) hcop χ₁ o3 χ₂ hχ₂ N hN hh
  · rintro ⟨hc, hz2⟩
    obtain ⟨K, hK, hz1⟩ := hs.mpr hc
    exact (PAG.Part183.root_mul_iff _ _ K hK hz1).mpr hz2

/-! ### 7. 法 p^e q^f -/

/-- **7.** 法 p^e q^f（p^e と q^f が互いに素、p, q 素数、e, f ≥ 1）の原始指標 χ について、
  z(χ) が 1 の冪根 ⇔ (e ≥ 2 または ord χ₁ = 2) かつ (f ≥ 2 または ord χ₂ = 2)。
  χ₁ = comp₁ χ、χ₂ = comp₂ χ は χ の成分。 -/
theorem two_prime_power_root_iff {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (e f : ℕ)
    (he : 1 ≤ e) (hf : 1 ≤ f) (hcop : (p ^ e).Coprime (q ^ f))
    (χ : DirichletCharacter ℂ (p ^ e * q ^ f)) (hχ : χ.IsPrimitive) :
    (∃ N : ℕ, 0 < N ∧
      (gaussSum χ stdAddChar / ((Real.sqrt ((p ^ e * q ^ f : ℕ) : ℝ) : ℝ) : ℂ)) ^ N = 1) ↔
      (2 ≤ e ∨ orderOf (comp₁ hcop χ) = 2) ∧ (2 ≤ f ∨ orderOf (comp₂ hcop χ) = 2) := by
  have hdec := decomp hcop χ
  have hχ' : ((comp₁ hcop χ).changeLevel (dvd_mul_right (p ^ e) (q ^ f)) *
      (comp₂ hcop χ).changeLevel (dvd_mul_left (q ^ f) (p ^ e))).IsPrimitive := hdec ▸ hχ
  have h₁ := isPrimitive_left _ _ hχ'
  have h₂ := isPrimitive_right _ _ hχ'
  have hz : gaussSum χ stdAddChar = gaussSum ((comp₁ hcop χ).changeLevel (dvd_mul_right (p ^ e) (q ^ f)) *
      (comp₂ hcop χ).changeLevel (dvd_mul_left (q ^ f) (p ^ e))) stdAddChar :=
    congrArg (fun φ => gaussSum φ stdAddChar) hdec
  rw [hz, peel_root_iff e he hcop _ h₁ _ h₂]
  have hs := PAG.Part187.single_root_iff (p := q) f hf (comp₂ hcop χ) h₂
  rw [← Nat.cast_pow] at hs
  rw [hs]

end PAG.Part194

#print axioms PAG.Part194.rho_bijective
#print axioms PAG.Part194.crt_apply
#print axioms PAG.Part194.comp₁_apply
#print axioms PAG.Part194.comp₂_apply
#print axioms PAG.Part194.decomp
#print axioms PAG.Part194.comp₁_mul
#print axioms PAG.Part194.comp₂_mul
#print axioms PAG.Part194.isPrimitive_left
#print axioms PAG.Part194.isPrimitive_right
#print axioms PAG.Part194.changeLevel_mul_split
#print axioms PAG.Part194.factorsThrough_mul_iff
#print axioms PAG.Part194.isPrimitive_mul
#print axioms PAG.Part194.isPrimitive_iff
#print axioms PAG.Part194.isIntegral_gaussSum
#print axioms PAG.Part194.sep_not_root
#print axioms PAG.Part194.peel_root_iff
#print axioms PAG.Part194.two_prime_power_root_iff
