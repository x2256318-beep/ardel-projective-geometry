/-
  PAG 2.0 Part 192（2026-10-23）— ホール成分：法 N = A·B の指標の成分と z の分解
  A·B = N（A, B 互いに素）を等式で与え、法 N のまま中国剰余定理を使う（法の書き換えをしない）。
  z(χ) = τ(χ)/√N（stdAddChar）を zN χ と書く。
  1. crt_unique / crt_exists：x ∈ ZMod N は (x mod A, x mod B) で決まり、どの組も現れる
  2. hall：χ の A 成分 χ_A(a) = χ(x)（x ≡ a mod A、x ≡ 1 mod B）。hall_spec（この性質）、
     hall_decomp（χ(x) = χ_A(x mod A)·χ_B(x mod B)）
  3. z_hall：z(χ) = ζ·z(χ_A)·z(χ_B)（ζ は 1 の冪根）。hall_isPrimitive：χ 原始的なら χ_A も原始的
  4. hall_hall：成分の成分は成分（N = A·B、A = Q·C、N = Q·D、D = C·B のとき (χ_A)_Q = χ_Q）
  5. pcomp：素数 q ∥ N のときの q 成分（法 q）。zN_hall_congr：成分の z は分解の書き方によらない
  6. exists_generator：法 p の指標はすべて位数 p − 1 の 1 つの指標 ω の冪
  7. isIntegral_zN_sq：χ 原始的（法 M）なら M·z² と M·z⁻² は代数的整数
-/
import PAG195

namespace PAG.Part196

open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194

/-- 法 N の z：z(χ) = τ(χ)/√N。 -/
noncomputable def zN {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)

/-! ### 1. 中国剰余定理（N = A·B を等式で与える） -/

/-- **1a.** A·B = N（互いに素）なら、x ∈ ZMod N は (x mod A, x mod B) で決まる。 -/
theorem crt_unique {N A B : ℕ} [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) {x y : ZMod N}
    (h₁ : ZMod.castHom hA (ZMod A) x = ZMod.castHom hA (ZMod A) y)
    (h₂ : ZMod.castHom hB (ZMod B) x = ZMod.castHom hB (ZMod B) y) : x = y := by
  subst hAB
  exact (rho_bijective hcop).1 (Prod.ext h₁ h₂)

/-- **1b.** A·B = N（互いに素）なら、どの組 (a, b) にも x ≡ a (mod A)、x ≡ b (mod B) となる x がある。 -/
theorem crt_exists {N A B : ℕ} [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (a : ZMod A) (b : ZMod B) :
    ∃ x : ZMod N, ZMod.castHom hA (ZMod A) x = a ∧ ZMod.castHom hB (ZMod B) x = b := by
  subst hAB
  obtain ⟨x, hx⟩ := (rho_bijective hcop).2 (a, b)
  exact ⟨x, congrArg Prod.fst hx, congrArg Prod.snd hx⟩

/-- 還元の合成。 -/
theorem castHom_castHom {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) (hac : a ∣ c) (x : ZMod c) :
    ZMod.castHom hab (ZMod a) (ZMod.castHom hbc (ZMod b) x) = ZMod.castHom hac (ZMod a) x := by
  rw [← RingHom.comp_apply, ZMod.castHom_comp]

/-! ### 2. ホール成分 -/

/-- x ≡ a (mod A)、x ≡ 1 (mod B) となる x ∈ ZMod N（1 つ選ぶ）。 -/
noncomputable def lift {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N)
    (hcop : A.Coprime B) (a : ZMod A) : ZMod N :=
  Classical.choose (crt_exists hAB hcop ⟨B, hAB.symm⟩ ⟨A, by rw [← hAB, mul_comm]⟩ a 1)

theorem lift_spec {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (a : ZMod A) :
    ZMod.castHom hA (ZMod A) (lift A B hAB hcop a) = a ∧
      ZMod.castHom hB (ZMod B) (lift A B hAB hcop a) = 1 :=
  Classical.choose_spec (crt_exists hAB hcop ⟨B, hAB.symm⟩ ⟨A, by rw [← hAB, mul_comm]⟩ a 1)

/-- x ≡ 1 (mod B) なら、x は x mod A の持ち上げ。 -/
theorem eq_lift {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (x : ZMod N) (hx : ZMod.castHom hB (ZMod B) x = 1) :
    lift A B hAB hcop (ZMod.castHom hA (ZMod A) x) = x := by
  obtain ⟨h1, h2⟩ := lift_spec A B hAB hcop hA hB (ZMod.castHom hA (ZMod A) x)
  exact crt_unique hAB hcop hA hB h1 (h2.trans hx.symm)

/-- **2. ホール成分**：χ_A(a) = χ(x)（x ≡ a mod A、x ≡ 1 mod B）。 -/
noncomputable def hall {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N)
    (hcop : A.Coprime B) (χ : DirichletCharacter ℂ N) : DirichletCharacter ℂ A where
  toFun a := χ (lift A B hAB hcop a)
  map_one' := by
    show χ (lift A B hAB hcop 1) = 1
    have hA : A ∣ N := ⟨B, hAB.symm⟩
    have hB : B ∣ N := ⟨A, by rw [← hAB, mul_comm]⟩
    have h1 := eq_lift A B hAB hcop hA hB 1 (map_one _)
    rw [map_one] at h1
    rw [h1, map_one]
  map_mul' a b := by
    show χ (lift A B hAB hcop (a * b)) = χ (lift A B hAB hcop a) * χ (lift A B hAB hcop b)
    have hA : A ∣ N := ⟨B, hAB.symm⟩
    have hB : B ∣ N := ⟨A, by rw [← hAB, mul_comm]⟩
    have ha := lift_spec A B hAB hcop hA hB a
    have hb := lift_spec A B hAB hcop hA hB b
    have h1 := eq_lift A B hAB hcop hA hB (lift A B hAB hcop a * lift A B hAB hcop b)
      (by rw [map_mul, ha.2, hb.2, mul_one])
    rw [map_mul, ha.1, hb.1] at h1
    rw [h1, map_mul]
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have hA : A ∣ N := ⟨B, hAB.symm⟩
    have hB : B ∣ N := ⟨A, by rw [← hAB, mul_comm]⟩
    have := hu.map (ZMod.castHom hA (ZMod A))
    rwa [(lift_spec A B hAB hcop hA hB a).1] at this

theorem hall_apply {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (χ : DirichletCharacter ℂ N) (a : ZMod A) : hall A B hAB hcop χ a = χ (lift A B hAB hcop a) := rfl

/-- **2a.** x ≡ 1 (mod B) なら χ_A(x mod A) = χ(x)。 -/
theorem hall_spec {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (χ : DirichletCharacter ℂ N) (x : ZMod N)
    (hx : ZMod.castHom hB (ZMod B) x = 1) :
    hall A B hAB hcop χ (ZMod.castHom hA (ZMod A) x) = χ x := by
  rw [hall_apply, eq_lift A B hAB hcop hA hB x hx]

/-- **2b. 分解**：χ(x) = χ_A(x mod A)·χ_B(x mod B)。 -/
theorem hall_decomp {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    χ x = hall A B hAB hcop χ (ZMod.castHom hA (ZMod A) x) *
      hall B A ((mul_comm B A).trans hAB) hcop.symm χ (ZMod.castHom hB (ZMod B) x) := by
  have s₁ := lift_spec A B hAB hcop hA hB (ZMod.castHom hA (ZMod A) x)
  have s₂ := lift_spec B A ((mul_comm B A).trans hAB) hcop.symm hB hA (ZMod.castHom hB (ZMod B) x)
  have hx : x = lift A B hAB hcop (ZMod.castHom hA (ZMod A) x) *
      lift B A ((mul_comm B A).trans hAB) hcop.symm (ZMod.castHom hB (ZMod B) x) :=
    crt_unique hAB hcop hA hB (by rw [map_mul, s₁.1, s₂.2, mul_one])
      (by rw [map_mul, s₁.2, s₂.1, one_mul])
  rw [hall_apply, hall_apply, ← map_mul, ← hx]

/-- 法 A·B の指標は 2 つのホール成分の積。 -/
theorem hall_mul_eq (A B : ℕ) [NeZero A] [NeZero B] (hcop : A.Coprime B)
    (χ : DirichletCharacter ℂ (A * B)) :
    χ = (hall A B rfl hcop χ).changeLevel (dvd_mul_right A B) *
      (hall B A (mul_comm B A) hcop.symm χ).changeLevel (dvd_mul_left B A) := by
  refine MulChar.ext' (fun x => ?_)
  rw [PAG.Part193.mul_changeLevel_apply]
  exact hall_decomp A B rfl hcop (dvd_mul_right A B) (dvd_mul_left B A) χ x

/-! ### 3. z の分解と原始性 -/

/-- **3a.** z(χ) = ζ·z(χ_A)·z(χ_B)（ζ は 1 の冪根）。 -/
theorem z_hall {N : ℕ} [NeZero N] (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N)
    (hcop : A.Coprime B) (χ : DirichletCharacter ℂ N) :
    ∃ ζ : ℂ, (∃ K : ℕ, 0 < K ∧ ζ ^ K = 1) ∧
      zN χ = ζ * (zN (hall A B hAB hcop χ) * zN (hall B A ((mul_comm B A).trans hAB) hcop.symm χ)) := by
  subst hAB
  obtain ⟨hz, M, hM, hc⟩ := PAG.Part193.z_mul_coprime hcop (hall A B rfl hcop χ)
    (hall B A (mul_comm B A) hcop.symm χ)
  refine ⟨_, ⟨M, hM, hc⟩, ?_⟩
  have e1 : zN χ = gaussSum ((hall A B rfl hcop χ).changeLevel (dvd_mul_right A B) *
      (hall B A (mul_comm B A) hcop.symm χ).changeLevel (dvd_mul_left B A)) stdAddChar /
      ((Real.sqrt ((A * B : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold zN
    conv_lhs => rw [hall_mul_eq A B hcop χ]
  rw [e1, hz]
  rfl

/-- **3b.** χ が原始的なら、ホール成分 χ_A も原始的。 -/
theorem hall_isPrimitive {N : ℕ} (A B : ℕ) [NeZero A] [NeZero B] (hAB : A * B = N)
    (hcop : A.Coprime B) (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (hall A B hAB hcop χ).IsPrimitive := by
  subst hAB
  rw [hall_mul_eq A B hcop χ] at hχ
  exact isPrimitive_left _ _ hχ

/-- 法 1 では z = 1。 -/
theorem zN_level_one {L : ℕ} [NeZero L] (hL : L = 1) (φ : DirichletCharacter ℂ L) : zN φ = 1 := by
  subst hL
  exact PAG.Part195.z_level_one φ

/-! ### 4. 成分の成分 -/

/-- **4.** N = A·B、A = Q·C、N = Q·D、D = C·B（それぞれ互いに素）なら (χ_A)_Q = χ_Q。 -/
theorem hall_hall {N A B Q C D : ℕ} [NeZero A] [NeZero B] [NeZero Q] [NeZero C] [NeZero D]
    (hAB : A * B = N) (hcopAB : A.Coprime B) (hQC : Q * C = A) (hcopQC : Q.Coprime C)
    (hQD : Q * D = N) (hcopQD : Q.Coprime D) (hCB : C * B = D) (hcopCB : C.Coprime B)
    (χ : DirichletCharacter ℂ N) :
    hall Q C hQC hcopQC (hall A B hAB hcopAB χ) = hall Q D hQD hcopQD χ := by
  refine MulChar.ext' (fun a => ?_)
  simp only [hall_apply]
  congr 1
  have hA : A ∣ N := ⟨B, hAB.symm⟩
  have hB : B ∣ N := ⟨A, by rw [← hAB, mul_comm]⟩
  have hQA : Q ∣ A := ⟨C, hQC.symm⟩
  have hCA : C ∣ A := ⟨Q, by rw [← hQC, mul_comm]⟩
  have hQN : Q ∣ N := ⟨D, hQD.symm⟩
  have hDN : D ∣ N := ⟨Q, by rw [← hQD, mul_comm]⟩
  have hCD : C ∣ D := ⟨B, hCB.symm⟩
  have hBD : B ∣ D := ⟨C, by rw [← hCB, mul_comm]⟩
  have sy := lift_spec Q C hQC hcopQC hQA hCA a
  have sx := lift_spec A B hAB hcopAB hA hB (lift Q C hQC hcopQC a)
  have sz := lift_spec Q D hQD hcopQD hQN hDN a
  apply crt_unique hQD hcopQD hQN hDN
  · rw [sz.1, ← castHom_castHom hQA hA hQN, sx.1, sy.1]
  · rw [sz.2]
    apply crt_unique hCB hcopCB hCD hBD
    · rw [map_one, castHom_castHom hCD hDN (dvd_trans hCA hA), ← castHom_castHom hCA hA, sx.1, sy.2]
    · rw [map_one, castHom_castHom hBD hDN hB, sx.2]

/-! ### 5. 素数成分 -/

/-- 成分の z は分解の書き方によらない（A = A′、B = B′）。 -/
theorem zN_hall_congr {N A A' B B' : ℕ} [NeZero A] [NeZero A'] [NeZero B] [NeZero B']
    (hA : A = A') (hB : B = B') (hAB : A * B = N) (hA'B' : A' * B' = N) (hcop : A.Coprime B)
    (hcop' : A'.Coprime B') (χ : DirichletCharacter ℂ N) :
    zN (hall A B hAB hcop χ) = zN (hall A' B' hA'B' hcop' χ) := by
  subst hA hB
  rfl

theorem pcomp_aux {q N : ℕ} (hq : q.Prime) (h : q ∣ N ∧ ¬ q ^ 2 ∣ N) :
    0 < N / q ∧ q.Coprime (N / q) := by
  have hN0 : N ≠ 0 := fun h0 => h.2 (h0 ▸ dvd_zero _)
  refine ⟨Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) h.1) hq.pos,
    (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h' => h.2 ?_)⟩
  rw [sq]
  exact Nat.mul_dvd_of_dvd_div h.1 h'

/-- **5. 素数成分**：q ∥ N なら χ の q 成分（法 q）、そうでなければ 1。 -/
noncomputable def pcomp (q : ℕ) [hq : Fact q.Prime] {N : ℕ} (χ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ q :=
  if h : q ∣ N ∧ ¬ q ^ 2 ∣ N then
    haveI : NeZero (N / q) := ⟨(pcomp_aux hq.out h).1.ne'⟩
    hall q (N / q) (Nat.mul_div_cancel' h.1) (pcomp_aux hq.out h).2 χ
  else 1

theorem pcomp_of (q : ℕ) [hq : Fact q.Prime] {N : ℕ} (χ : DirichletCharacter ℂ N)
    (h : q ∣ N ∧ ¬ q ^ 2 ∣ N) [NeZero (N / q)] :
    pcomp q χ = hall q (N / q) (Nat.mul_div_cancel' h.1) (pcomp_aux hq.out h).2 χ := by
  rw [pcomp, dite_eq_left h]

/-! ### 6. 生成指標 -/

/-- **6.** 法 p の指標には位数 p − 1 のもの ω があり、すべての指標は ω の冪。 -/
theorem exists_generator (p : ℕ) [hp : Fact p.Prime] :
    ∃ ω : DirichletCharacter ℂ p, orderOf ω = p - 1 ∧
      ∀ φ : DirichletCharacter ℂ p, ∃ k : ℕ, φ = ω ^ k := by
  classical
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  obtain ⟨ω, hω⟩ := MulChar.exists_mulChar_orderOf_eq_card_units (ZMod p)
    (Complex.isPrimitiveRoot_exp (Fintype.card (ZMod p)ˣ) (by rw [hcard]; exact hp1))
  rw [hcard] at hω
  refine ⟨ω, hω, fun φ => ?_⟩
  obtain ⟨g, hg⟩ := PAG.Part185.exists_gen (p := p)
  have hμ := PAG.Part185.isPrimitiveRoot_gen ω g hg
  rw [hω] at hμ
  have hφg : (φ g) ^ (p - 1) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one,
      map_one]
  have : NeZero (p - 1) := ⟨hp1⟩
  obtain ⟨k, -, hk⟩ := hμ.eq_pow_of_pow_eq_one hφg
  refine ⟨k, MulChar.ext (fun u => ?_)⟩
  obtain ⟨j, rfl⟩ := hg u
  rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow, map_pow, ← hk, ← pow_mul, ← pow_mul,
    mul_comm]

/-! ### 7. 整数性 -/

/-- **7.** χ が原始的（法 M）なら、M·z² と M·z⁻² は代数的整数で、z ≠ 0。 -/
theorem isIntegral_zN_sq {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M) (hφ : φ.IsPrimitive) :
    zN φ ≠ 0 ∧ IsIntegral ℤ ((M : ℂ) * zN φ ^ 2) ∧ IsIntegral ℤ ((M : ℂ) * (zN φ ^ 2)⁻¹) := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hsqM : ((Real.sqrt (M : ℝ) : ℝ) : ℂ) ^ 2 = (M : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have hs0 : ((Real.sqrt (M : ℝ) : ℝ) : ℂ) ≠ 0 := by
    intro h0; rw [h0, zero_pow two_ne_zero] at hsqM; exact hMC hsqM.symm
  have hτ0 : gaussSum φ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero hφ
  have hgg := PAG.Part16.gauss_mul_gauss_inv_eq hφ
  have hc2 : φ (-1) ^ 2 = 1 := by rw [sq]; exact PAG.Part9.chi_neg_one_sq φ
  have hz2 : zN φ ^ 2 = gaussSum φ stdAddChar ^ 2 / (M : ℂ) := by
    rw [zN, div_pow, hsqM]
  refine ⟨div_ne_zero hτ0 hs0, ?_, ?_⟩
  · rw [hz2, mul_div_cancel₀ _ hMC]
    exact (isIntegral_gaussSum φ).pow 2
  · have hτ' : gaussSum φ⁻¹ stdAddChar = φ (-1) * M / gaussSum φ stdAddChar := by
      rw [← hgg]; field_simp
    have : (M : ℂ) * (zN φ ^ 2)⁻¹ = gaussSum φ⁻¹ stdAddChar ^ 2 := by
      rw [hz2, hτ', div_pow, mul_pow, hc2, one_mul, inv_div]
      field_simp
    rw [this]
    exact (isIntegral_gaussSum φ⁻¹).pow 2

/-! ### 8. 単独ケットの判定（成分の形） -/

/-- (pcomp q χ)² = 1 ⇔ x ≡ 1 (mod N/q) の単数 x で χ(x)² = 1（q ∥ N）。 -/
theorem pcomp_sq_eq_one_iff (q : ℕ) [hq : Fact q.Prime] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (h : q ∣ N ∧ ¬ q ^ 2 ∣ N) :
    pcomp q χ ^ 2 = 1 ↔
      ∀ u : (ZMod N)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd h.1) u = 1 → χ u ^ 2 = 1 := by
  have hpos := pcomp_aux hq.out h
  have : NeZero (N / q) := ⟨hpos.1.ne'⟩
  have hqN : q ∣ N := h.1
  have hBN : N / q ∣ N := Nat.div_dvd_of_dvd h.1
  have hAB : q * (N / q) = N := Nat.mul_div_cancel' h.1
  rw [pcomp_of q χ h]
  constructor
  · intro h2 u hu
    have hu' : ZMod.castHom hBN (ZMod (N / q)) (u : ZMod N) = 1 := congrArg Units.val hu
    rw [← hall_spec q (N / q) hAB hpos.2 hqN hBN χ u hu', ← MulChar.pow_apply' _ two_ne_zero, h2]
    exact MulChar.one_apply ((ZMod.unitsMap hqN u).isUnit)
  · intro H
    refine MulChar.ext (fun a => ?_)
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, hall_apply]
    obtain ⟨s1, s2⟩ := lift_spec q (N / q) hAB hpos.2 hqN hBN (a : ZMod q)
    obtain ⟨t1, t2⟩ := lift_spec q (N / q) hAB hpos.2 hqN hBN ((a⁻¹ : (ZMod q)ˣ) : ZMod q)
    have hw : lift q (N / q) hAB hpos.2 (a : ZMod q) * lift q (N / q) hAB hpos.2 ((a⁻¹ : (ZMod q)ˣ) : ZMod q)
        = 1 := by
      apply crt_unique hAB hpos.2 hqN hBN
      · rw [map_mul, s1, t1, map_one, Units.mul_inv]
      · rw [map_mul, s2, t2, map_one, mul_one]
    have hunit : IsUnit (lift q (N / q) hAB hpos.2 (a : ZMod q)) := IsUnit.of_mul_eq_one _ hw
    have := H hunit.unit (Units.ext (by
      show ZMod.castHom hBN (ZMod (N / q)) (lift q (N / q) hAB hpos.2 (a : ZMod q)) = 1
      exact s2))
    rwa [IsUnit.unit_spec] at this

/-- **8. 単独ケットの判定（成分の形）**：法 N の原始指標 χ で、z(χ) が 1 の冪根 ⇔
  N をちょうど 1 回割る素数 q ごとに、q 成分の位数が 2。 -/
theorem root_iff_pcomp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (∃ K : ℕ, 0 < K ∧ zN χ ^ K = 1) ↔
      ∀ (q : ℕ) [Fact q.Prime], q ∣ N → ¬ q ^ 2 ∣ N → orderOf (pcomp q χ) = 2 := by
  have key := PAG.Part195.general_root_iff_units N χ hχ
  unfold zN
  rw [key]
  constructor
  · intro H q hq hqN hq2
    have h : q ∣ N ∧ ¬ q ^ 2 ∣ N := ⟨hqN, hq2⟩
    have hsq := (pcomp_sq_eq_one_iff q χ h).mpr (H q hq.out hqN hq2)
    have hprim : (pcomp q χ).IsPrimitive := by
      have : NeZero (N / q) := ⟨(pcomp_aux hq.out h).1.ne'⟩
      rw [pcomp_of q χ h]
      exact hall_isPrimitive _ _ _ _ χ hχ
    exact orderOf_eq_prime hsq (PAG.Part195.ne_one_of_isPrimitive hq.out.two_le _ hprim)
  · intro H q hq hqN hq2
    have : Fact q.Prime := ⟨hq⟩
    have h : q ∣ N ∧ ¬ q ^ 2 ∣ N := ⟨hqN, hq2⟩
    apply (pcomp_sq_eq_one_iff q χ h).mp
    rw [← H q hqN hq2]
    exact pow_orderOf_eq_one _

end PAG.Part196

#print axioms PAG.Part196.crt_unique
#print axioms PAG.Part196.crt_exists
#print axioms PAG.Part196.castHom_castHom
#print axioms PAG.Part196.lift_spec
#print axioms PAG.Part196.eq_lift
#print axioms PAG.Part196.hall_apply
#print axioms PAG.Part196.hall_spec
#print axioms PAG.Part196.hall_decomp
#print axioms PAG.Part196.hall_mul_eq
#print axioms PAG.Part196.z_hall
#print axioms PAG.Part196.hall_isPrimitive
#print axioms PAG.Part196.zN_level_one
#print axioms PAG.Part196.hall_hall
#print axioms PAG.Part196.zN_hall_congr
#print axioms PAG.Part196.pcomp_aux
#print axioms PAG.Part196.pcomp_of
#print axioms PAG.Part196.exists_generator
#print axioms PAG.Part196.isIntegral_zN_sq
#print axioms PAG.Part196.pcomp_sq_eq_one_iff
#print axioms PAG.Part196.root_iff_pcomp
