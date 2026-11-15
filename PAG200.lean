/-
  PAG 2.0 Part 196（2026-10-23）— 任意の N での ℤ/N の定理 A
  uM = N、c ∣ M、d ∣ c、u′ = u·c/d、u′M′ = N、d ∣ M′。A, B は法 c で原始的、Ψ は法 d で原始的、
  AB = Ψ∘π、N を割るすべての素数が d を割るとき
      |u, A⟩_N ⋆ |u, B⟩_N = C·|u′, Ψ⟩_N、C = √(N/φ(uc))·τ(A)τ(B)/(τ(Ψ)√(c·c/d))
  （Part 195 の `ThmA`。素数の個数によらない）。
  1. p 進の分け方：x = p^a x₂（p ∤ x₂）、p^a x = p^b y ⇒ a = b ∧ x = y、p^a x ∣ p^b y ⇒ a ≤ b ∧ x ∣ y
  2. prod_split：A₁′A₂′·B₁′B₂′ = (Ψ₁′Ψ₂′)∘π なら A_iB_i = Ψ_i∘π（成分の一意性、Part 190）
  3. thmA_one（N = 1）、thmA_pp（素数冪、殻・法を変数のまま）
  4. thmA_general：N についての強い帰納法（最小素因数 p の冪をはがし、Part 195 の `thmA_mul`）
  5. normSq_thmAConst：|C|² = N/φ(uc)（作用素ノルムの飽和の大域版）
-/
import PAG199

namespace PAG.Part200

open Complex Finset PAG.Part199
open ZMod (stdAddChar)

/-! ### 1. p 進の分け方 -/

/-- x ≠ 0 は x = p^a x₂（p ∤ x₂）と書ける。 -/
theorem exists_split {p x : ℕ} (hp : p.Prime) (hx : x ≠ 0) : ∃ a x₂, ¬ p ∣ x₂ ∧ x = p ^ a * x₂ :=
  ⟨x.factorization p, x / p ^ x.factorization p, Nat.not_dvd_ordCompl hp hx,
    (Nat.ordProj_mul_ordCompl_eq_self x p).symm⟩

theorem not_dvd_mul' {p x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y) : ¬ p ∣ x * y :=
  fun h => (hp.dvd_mul.mp h).elim hx hy

/-- p^a x = p^b y（p ∤ x, y）なら a = b かつ x = y。 -/
theorem split_eq {p a b x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ a * x = p ^ b * y) : a = b ∧ x = y := by
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ dvd_zero p)
  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ dvd_zero p)
  have e := congrArg (fun n => n.factorization p) h
  simp only [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hx0,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hy0, Finsupp.add_apply, hp.factorization_pow,
    Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hx,
    Nat.factorization_eq_zero_of_not_dvd hy, add_zero] at e
  subst e
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) h⟩

/-- p^a x ∣ p^b y（p ∤ x, y）なら a ≤ b かつ x ∣ y。 -/
theorem split_dvd {p a b x y : ℕ} (hp : p.Prime) (hx : ¬ p ∣ x) (hy : ¬ p ∣ y)
    (h : p ^ a * x ∣ p ^ b * y) : a ≤ b ∧ x ∣ y := by
  constructor
  · have h1 : p ^ a ∣ p ^ b * y := (Dvd.intro _ rfl).trans h
    have hcop : (p ^ a).Coprime y := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hy)
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (hcop.dvd_of_dvd_mul_right h1)
  · have h1 : x ∣ p ^ b * y := (Dvd.intro_left _ rfl).trans h
    have hcop : x.Coprime (p ^ b) :=
      Nat.Coprime.pow_right b (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hx))
    exact hcop.dvd_of_dvd_mul_left h1

/-! ### 2. 積の関係の成分 -/

/-- A₁′A₂′·B₁′B₂′ = (A₁B₁)′(A₂B₂)′。 -/
theorem cmul_mul_cmul {c₁ c₂ : ℕ} (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂) :
    cmul A₁ A₂ * cmul B₁ B₂ = cmul (A₁ * B₁) (A₂ * B₂) := by
  unfold cmul
  rw [map_mul, map_mul]
  exact mul_mul_mul_comm _ _ _ _

/-- **2. 成分の積の関係**：A₁′A₂′·B₁′B₂′ = (Ψ₁′Ψ₂′)∘π なら A₁B₁ = Ψ₁∘π、A₂B₂ = Ψ₂∘π。 -/
theorem prod_split {c₁ c₂ d₁ d₂ : ℕ} [NeZero c₁] [NeZero c₂] (hcop : c₁.Coprime c₂)
    (h₁ : d₁ ∣ c₁) (h₂ : d₂ ∣ c₂)
    (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂)
    (Ψ₁ : DirichletCharacter ℂ d₁) (Ψ₂ : DirichletCharacter ℂ d₂) (hdc : d₁ * d₂ ∣ c₁ * c₂)
    (h : cmul A₁ A₂ * cmul B₁ B₂ = (cmul Ψ₁ Ψ₂).changeLevel hdc) :
    A₁ * B₁ = Ψ₁.changeLevel h₁ ∧ A₂ * B₂ = Ψ₂.changeLevel h₂ := by
  rw [cmul_mul_cmul] at h
  unfold cmul at h
  rw [PAG.Part194.changeLevel_mul_split h₁ h₂] at h
  have k₁ := congrArg (PAG.Part194.comp₁ hcop) h
  rw [PAG.Part194.comp₁_mul, PAG.Part194.comp₁_mul] at k₁
  have k₂ := congrArg (PAG.Part194.comp₂ hcop) h
  rw [PAG.Part194.comp₂_mul, PAG.Part194.comp₂_mul] at k₂
  exact ⟨k₁, k₂⟩

/-! ### 3. 帰納法の出発点 -/

/-- 法 1 の指標の値はすべて 1。 -/
theorem chi_level_one (χ : DirichletCharacter ℂ 1) (y : ZMod 1) : χ y = 1 := by
  rw [Subsingleton.elim y 1, map_one]

/-- **3a. N = 1**：|1, A⟩ ⋆ |1, B⟩ = C·|1, Ψ⟩（すべて 1）。 -/
theorem thmA_one (h : 1 * 1 = 1) (hc : 1 ∣ 1) (h' : 1 * 1 = 1) (hd : 1 ∣ 1)
    (A B Ψ : DirichletCharacter ℂ 1) : ThmA 1 1 1 1 1 1 1 h hc h' hd A B Ψ := by
  have hg : ∀ χ : DirichletCharacter ℂ 1, gaussSum χ stdAddChar = 1 := by
    intro χ
    rw [gaussSum, Fintype.sum_subsingleton _ 0, chi_level_one, AddChar.map_zero_eq_one, mul_one]
  have hk : ∀ (χ : DirichletCharacter ℂ 1) (y : ZMod 1), gket 1 1 1 h 1 hc χ y = 1 := by
    intro χ y
    rw [gket_apply, ite_eq_left (one_dvd _), chi_level_one, Nat.totient_one, Nat.cast_one, Real.sqrt_one,
      inv_one, Complex.ofReal_one, one_mul]
  unfold ThmA thmAConst
  funext x
  rw [hg, hg, hg]
  simp only [PAG.Part15.conv, Pi.smul_apply, smul_eq_mul, hk, mul_one, Fintype.sum_subsingleton _ (0 : ZMod 1)]
  norm_num

/-- **3b. 素数冪**（殻・法を変数のまま）：δ ≥ 1、δ ≤ γ ≤ b、w + b = K、a′ = w + (γ − δ)、a′ + b′ = K。 -/
theorem thmA_pp {p : ℕ} [hp : Fact p.Prime] (K w b γ δ a' b' : ℕ) (hb : w + b = K) (hab' : a' + b' = K)
    (hδ : 1 ≤ δ) (hδγ : δ ≤ γ) (hγb : γ ≤ b) (ha' : a' = w + (γ - δ))
    (h : p ^ w * p ^ b = p ^ K) (hc : p ^ γ ∣ p ^ b) (h' : p ^ a' * p ^ b' = p ^ K) (hd : p ^ δ ∣ p ^ b')
    (A B : DirichletCharacter ℂ (p ^ γ)) (Ψ : DirichletCharacter ℂ (p ^ δ))
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive)
    (hprod : A * B = Ψ.changeLevel (pow_dvd_pow p hδγ)) :
    ThmA (p ^ K) (p ^ w) (p ^ b) (p ^ γ) (p ^ δ) (p ^ a') (p ^ b') h hc h' hd A B Ψ := by
  obtain ⟨n, rfl⟩ : ∃ n, γ = n + 1 := ⟨γ - 1, by omega⟩
  obtain ⟨v, hv, rfl⟩ : ∃ v, v ≤ n ∧ δ = n + 1 - v := ⟨n + 1 - δ, by omega, by omega⟩
  obtain rfl : b = K - w := by omega
  obtain rfl : a' = w + v := by omega
  obtain rfl : b' = K - (w + v) := by omega
  exact thmA_prime_power K w n v hv (by omega) A B hA hB Ψ hΨ hprod

/-! ### 4. 任意の N -/

/-- 帰納法の形（インスタンスの仮定を明示的な引数に）。 -/
theorem thmA_general_aux (N : ℕ) : ∀ (_ : NeZero N) (u M c d u' M' : ℕ) (h : u * M = N) (hc : c ∣ M)
    (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (_ : NeZero c) (_ : NeZero d),
    u' = u * (c / d) → (∀ q : ℕ, q.Prime → q ∣ N → q ∣ d) →
    ∀ (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d),
      A.IsPrimitive → B.IsPrimitive → Ψ.IsPrimitive → A * B = Ψ.changeLevel hdc →
      ThmA N u M c d u' M' h hc h' hd A B Ψ := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro hNZ u M c d u' M' h hc hdc h' hd hcZ hdZ hu' hprimes A B Ψ hA hB hΨ hprod
  by_cases hN1 : N = 1
  · subst hN1
    obtain rfl := Nat.eq_one_of_mul_eq_one_right h
    obtain rfl := Nat.eq_one_of_mul_eq_one_left h
    obtain rfl := Nat.dvd_one.mp hc
    obtain rfl := Nat.dvd_one.mp hdc
    obtain rfl := Nat.eq_one_of_mul_eq_one_right h'
    obtain rfl := Nat.eq_one_of_mul_eq_one_left h'
    exact thmA_one h hc h' hd A B Ψ
  · have hN0 : N ≠ 0 := NeZero.ne N
    obtain ⟨p, e, N', hp, he, hpN', rfl⟩ : ∃ p e N' : ℕ, p.Prime ∧ 1 ≤ e ∧ ¬ p ∣ N' ∧ N = p ^ e * N' := by
      have hp := Nat.minFac_prime hN1
      exact ⟨N.minFac, N.factorization N.minFac, N / N.minFac ^ N.factorization N.minFac, hp,
        hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N), Nat.not_dvd_ordCompl hp hN0,
        (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm⟩
    have : Fact p.Prime := ⟨hp⟩
    have hN'0 : N' ≠ 0 := fun h0 => hN0 (by rw [h0, mul_zero])
    have hN'Z : NeZero N' := ⟨hN'0⟩
    have hN'lt : N' < p ^ e * N' := by
      have h2 : 2 ≤ p ^ e := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
      have : 0 < N' := Nat.pos_of_ne_zero hN'0
      nlinarith
    have hcopN : (p ^ e).Coprime N' := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN')
    -- 数の分け方
    have hu0 : u ≠ 0 := fun h0 => hN0 (by rw [← h, h0, zero_mul])
    have hM0 : M ≠ 0 := fun h0 => hN0 (by rw [← h, h0, mul_zero])
    have hu'0 : u' ≠ 0 := fun h0 => hN0 (by rw [← h', h0, zero_mul])
    have hM'0 : M' ≠ 0 := fun h0 => hN0 (by rw [← h', h0, mul_zero])
    obtain ⟨a, u₂, hu₂, rfl⟩ := exists_split hp hu0
    obtain ⟨b, M₂, hM₂, rfl⟩ := exists_split hp hM0
    obtain ⟨γ, c₂, hc₂, rfl⟩ := exists_split hp (NeZero.ne c)
    obtain ⟨δ, d₂, hd₂, rfl⟩ := exists_split hp (NeZero.ne d)
    obtain ⟨a', u₂', hu₂', rfl⟩ := exists_split hp hu'0
    obtain ⟨b', M₂', hM₂', rfl⟩ := exists_split hp hM'0
    obtain ⟨hab, huM⟩ := split_eq hp (not_dvd_mul' hp hu₂ hM₂) hpN'
      (by rw [← h]; ring : p ^ (a + b) * (u₂ * M₂) = p ^ e * N')
    obtain ⟨hab', huM'⟩ := split_eq hp (not_dvd_mul' hp hu₂' hM₂') hpN'
      (by rw [← h']; ring : p ^ (a' + b') * (u₂' * M₂') = p ^ e * N')
    obtain ⟨hγb, hcM⟩ := split_dvd hp hc₂ hM₂ hc
    obtain ⟨hδγ, hdc₂⟩ := split_dvd hp hd₂ hc₂ hdc
    obtain ⟨hδb', hdM⟩ := split_dvd hp hd₂ hM₂' hd
    have hq₂ : ¬ p ∣ c₂ / d₂ := fun hpq => hc₂ (hpq.trans (Nat.div_dvd_of_dvd hdc₂))
    have hdiv : p ^ γ * c₂ / (p ^ δ * d₂) = p ^ (γ - δ) * (c₂ / d₂) := by
      rw [← Nat.div_mul_div_comm (pow_dvd_pow p hδγ) hdc₂, Nat.pow_div hδγ hp.pos]
    obtain ⟨ha', hu₂'eq⟩ := split_eq hp hu₂' (not_dvd_mul' hp hu₂ hq₂)
      (by rw [hu', hdiv]; ring : p ^ a' * u₂' = p ^ (a + (γ - δ)) * (u₂ * (c₂ / d₂)))
    -- 素数の条件
    have hδ : 1 ≤ δ := by
      by_contra h0
      have hδ0 : δ = 0 := by omega
      have := hprimes p hp (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) N')
      rw [hδ0, pow_zero, one_mul] at this
      exact hd₂ this
    have hprimes₂ : ∀ q : ℕ, q.Prime → q ∣ N' → q ∣ d₂ := by
      intro q hq hqN
      have h1 := hprimes q hq (dvd_mul_of_dvd_right hqN _)
      rcases hq.dvd_mul.mp h1 with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h2)
        subst this
        exact absurd hqN hpN'
      · exact h2
    -- 指標の分け方
    have hcopc : (p ^ γ).Coprime c₂ := Nat.Coprime.pow_left γ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hc₂)
    have hcopd : (p ^ δ).Coprime d₂ := Nat.Coprime.pow_left δ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hd₂)
    have hc₂Z : NeZero c₂ := ⟨fun h0 => hc₂ (h0 ▸ dvd_zero p)⟩
    have hd₂Z : NeZero d₂ := ⟨fun h0 => hd₂ (h0 ▸ dvd_zero p)⟩
    obtain ⟨A₁, A₂, rfl⟩ : ∃ A₁ A₂, A = cmul A₁ A₂ :=
      ⟨PAG.Part194.comp₁ hcopc A, PAG.Part194.comp₂ hcopc A, PAG.Part194.decomp hcopc A⟩
    obtain ⟨B₁, B₂, rfl⟩ : ∃ B₁ B₂, B = cmul B₁ B₂ :=
      ⟨PAG.Part194.comp₁ hcopc B, PAG.Part194.comp₂ hcopc B, PAG.Part194.decomp hcopc B⟩
    obtain ⟨Ψ₁, Ψ₂, rfl⟩ : ∃ Ψ₁ Ψ₂, Ψ = cmul Ψ₁ Ψ₂ :=
      ⟨PAG.Part194.comp₁ hcopd Ψ, PAG.Part194.comp₂ hcopd Ψ, PAG.Part194.decomp hcopd Ψ⟩
    obtain ⟨hΨ₁, hΨ₂⟩ := prod_split hcopc (pow_dvd_pow p hδγ) hdc₂ A₁ B₁ A₂ B₂ Ψ₁ Ψ₂ hdc hprod
    have hA₁ := PAG.Part194.isPrimitive_left A₁ A₂ hA
    have hA₂ := PAG.Part194.isPrimitive_right A₁ A₂ hA
    have hB₁ := PAG.Part194.isPrimitive_left B₁ B₂ hB
    have hB₂ := PAG.Part194.isPrimitive_right B₁ B₂ hB
    have hΨ₁' := PAG.Part194.isPrimitive_left Ψ₁ Ψ₂ hΨ
    have hΨ₂' := PAG.Part194.isPrimitive_right Ψ₁ Ψ₂ hΨ
    -- 2 つの因子での定理 A
    have h₁ : p ^ a * p ^ b = p ^ e := by rw [← pow_add, hab]
    have h₁' : p ^ a' * p ^ b' = p ^ e := by rw [← pow_add, hab']
    have H₁ := thmA_pp e a b γ δ a' b' hab hab' hδ hδγ hγb ha' h₁ (pow_dvd_pow p hγb) h₁' (pow_dvd_pow p hδb')
      A₁ B₁ Ψ₁ hA₁ hB₁ hΨ₁' hΨ₁
    have H₂ := IH N' hN'lt hN'Z u₂ M₂ c₂ d₂ u₂' M₂' huM hcM hdc₂ huM' hdM hc₂Z hd₂Z hu₂'eq hprimes₂
      A₂ B₂ Ψ₂ hA₂ hB₂ hΨ₂' hΨ₂
    have hu₁' : p ^ a' = p ^ a * (p ^ γ / p ^ δ) := by
      rw [Nat.pow_div hδγ hp.pos, ← pow_add, ha']
    exact thmA_mul hcopN h₁ huM (pow_dvd_pow p hγb) hcM h₁' huM' (pow_dvd_pow p hδb') hdM
      (pow_dvd_pow p hδγ) hdc₂ hu₁' hu₂'eq A₁ B₁ A₂ B₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ H₁ H₂

/-- **4. 任意の N での ℤ/N の定理 A**：uM = N、c ∣ M、d ∣ c、u′ = u·c/d、u′M′ = N、d ∣ M′、
A, B は法 c で原始的、Ψ は法 d で原始的、AB = Ψ∘π、N を割るすべての素数が d を割るなら
|u, A⟩_N ⋆ |u, B⟩_N = √(N/φ(uc))·τ(A)τ(B)/(τ(Ψ)√(c·c/d))·|u′, Ψ⟩_N。 -/
theorem thmA_general (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N) (hc : c ∣ M)
    (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (hu' : u' = u * (c / d))
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ d)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    ThmA N u M c d u' M' h hc h' hd A B Ψ :=
  thmA_general_aux N inferInstance u M c d u' M' h hc hdc h' hd inferInstance inferInstance hu' hprimes
    A B Ψ hA hB hΨ hprod

/-! ### 5. 定数の大きさ -/

/-- **5. |C|² = N/φ(uc)**（A, B, Ψ 原始的）。定理 A の定数の位相部分 τ(A)τ(B)/(τ(Ψ)√(c·c/d)) は絶対値 1。 -/
theorem normSq_thmAConst (N u c d : ℕ) [NeZero c] [NeZero d] (hdc : d ∣ c)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) :
    Complex.normSq (thmAConst N u c d A B Ψ) = (N : ℝ) / (Nat.totient (u * c) : ℝ) := by
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold thmAConst
  simp only [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [PAG.Part16.normSq_gaussSum hA, PAG.Part16.normSq_gaussSum hB, PAG.Part16.normSq_gaussSum hΨ,
    Real.mul_self_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
    Real.mul_self_sqrt (Nat.cast_nonneg _), Nat.cast_mul, Nat.cast_div hdc hd0]
  rw [mul_div_assoc, show (c : ℝ) * c / d / (c * (c / d)) = 1 by field_simp, mul_one]

/-! ### 6. ノルムと作用素ノルムの飽和 -/

/-- ‖|u, χ⟩_N‖² は ZMod M の上の和 Σ_y |φ(M)^(−1/2) χ(y mod c)|²。 -/
theorem sum_normSq_gket (u M N : ℕ) [NeZero N] [NeZero M] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x)
      = ∑ y : ZMod M, Complex.normSq
          ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * χ (ZMod.castHom hc (ZMod c) y)) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (memb u M N h))) (fun x _ hx => by
      have hx' : ¬ ∃ y, memb u M N h y = x :=
        fun ⟨y, hy⟩ => hx (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩)
      rw [gket_apply, ite_eq_right (fun hd => hx' ((exists_memb_iff u M N h x).mpr hd)), map_zero]),
    Finset.sum_image (fun a _ b _ hab => memb_injective u M N h hab)]
  exact Finset.sum_congr rfl (fun y _ => by rw [gket_memb])

/-- **6a. ケットは単位ベクトル**：M を割るすべての素数が c を割るなら ‖|u, χ⟩_N‖² = 1。 -/
theorem norm_gket (u M N : ℕ) [NeZero N] [NeZero M] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x) = 1 := by
  classical
  have hφ0 : (Nat.totient M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  have hiff : ∀ k : ℕ, k.Coprime c ↔ k.Coprime M := by
    intro k
    constructor
    · intro hk
      apply Nat.coprime_of_dvd
      intro q hq hqk hqM
      have h1 : q ∣ Nat.gcd k c := Nat.dvd_gcd hqk (hrad q hq hqM)
      rw [Nat.Coprime.gcd_eq_one hk] at h1
      exact hq.not_dvd_one h1
    · intro hk
      exact hk.coprime_dvd_right hc
  have hterm : ∀ y : ZMod M, Complex.normSq
      ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * χ (ZMod.castHom hc (ZMod c) y))
      = (Nat.totient M : ℝ)⁻¹ * (if y.val.Coprime M then 1 else 0) := by
    intro y
    rw [Complex.normSq_mul, Complex.normSq_ofReal, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _),
      ZMod.castHom_apply, ZMod.cast_eq_val]
    by_cases hy : y.val.Coprime M
    · rw [ite_eq_left hy, normSq_chi_natCast χ y.val ((hiff y.val).mpr hy)]
    · rw [ite_eq_right hy, MulChar.map_nonunit χ (fun hu => hy ((hiff y.val).mp
        ((ZMod.isUnit_iff_coprime _ _).mp hu))), map_zero]
  have hcard : (Finset.univ.filter (fun y : ZMod M => y.val.Coprime M)).card = Nat.totient M := by
    rw [← Fintype.card_subtype]
    exact (Fintype.card_congr ZMod.unitsEquivCoprime).symm.trans (ZMod.card_units_eq_totient M)
  rw [sum_normSq_gket, Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, Finset.sum_boole,
    hcard]
  exact inv_mul_cancel₀ hφ0

/-- **6b. 作用素ノルムの飽和（任意の N）**：thmA_general の仮定のもとで ‖|u, A⟩ ⋆ |u, B⟩‖² = N/φ(uc)。 -/
theorem thmA_general_norm (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N)
    (hc : c ∣ M) (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (hu' : u' = u * (c / d))
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ d)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    ∑ x, Complex.normSq (PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc B) x)
      = (N : ℝ) / (Nat.totient (u * c) : ℝ) := by
  have H := thmA_general N u M c d u' M' h hc hdc h' hd hu' hprimes A B Ψ hA hB hΨ hprod
  unfold ThmA at H
  have := neZero_of_mul h'
  have hrad : ∀ q : ℕ, q.Prime → q ∣ M' → q ∣ d :=
    fun q hq hqM => hprimes q hq (hqM.trans (Dvd.intro_left _ h'))
  rw [H]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, norm_gket u' M' N h' d hd Ψ hrad, mul_one,
    normSq_thmAConst N u c d hdc A B Ψ hA hB hΨ]

end PAG.Part200

#print axioms PAG.Part200.exists_split
#print axioms PAG.Part200.not_dvd_mul'
#print axioms PAG.Part200.split_eq
#print axioms PAG.Part200.split_dvd
#print axioms PAG.Part200.cmul_mul_cmul
#print axioms PAG.Part200.prod_split
#print axioms PAG.Part200.chi_level_one
#print axioms PAG.Part200.thmA_one
#print axioms PAG.Part200.thmA_pp
#print axioms PAG.Part200.thmA_general_aux
#print axioms PAG.Part200.thmA_general
#print axioms PAG.Part200.normSq_thmAConst
#print axioms PAG.Part200.sum_normSq_gket
#print axioms PAG.Part200.norm_gket
#print axioms PAG.Part200.thmA_general_norm
