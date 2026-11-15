/-
  PAG 2.0 Part 194（2026-10-23）— ガウスの符号決定：すべての実原始指標
  χ が法 N の原始指標で χ² = 1（実指標）なら、z(χ) = τ(χ)/√N は χ(−1) = 1 で 1、χ(−1) = −1 で i。
  gs χ = (χ(−1) = 1 なら 1、そうでなければ i)、rs ψ χ = (ψ(−1) = 1 なら 1、そうでなければ χ(−1)) と書く。
  1. 素数冪の実原始指標の分類：奇素数 r では法 r の 2 次指標（ルジャンドル記号）だけ、2 冪では法 4 の χ₄ と
     法 8 の χ₈, χ₈′ だけ（odd_base_values, two_base_values）
  2. 素数冪の場合の z（odd_base_z, two_base_z：Part 163・148 の結果から）
  3. 素数冪どうしの相互法則（bb_rec）：ψ(p^e)·φ(q^f) = rs ψ φ（平方剰余の相互法則と第 1・第 2 補充法則）
  4. gauss_sign_real：N についての強い帰納法（素数冪をはがし、Part 189 の積公式と 3 の相互法則で符号を運ぶ）
  5. real_reciprocity：互いに素な法の実原始指標 χ₁, χ₂ で χ₁(N₂)χ₂(N₁) = rs χ₁ χ₂（一般の相互法則）
-/
import PAG197
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace PAG.Part198

open Complex Finset
open ZMod (stdAddChar)
open PAG.Part194 PAG.Part196

/-- 実指標の z の値（予想される値）：χ(−1) = 1 なら 1、そうでなければ i。 -/
noncomputable def gs {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ := if χ (-1) = 1 then 1 else I

/-- 相互法則の符号：ψ(−1) = 1 なら 1、そうでなければ χ(−1)。 -/
noncomputable def rs {M N : ℕ} (ψ : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ N) : ℂ :=
  if ψ (-1) = 1 then 1 else χ (-1)

/-! ### 0. 符号の計算 -/

theorem neg_one_sq_eq {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h := PAG.Part9.chi_neg_one_sq χ
  have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

/-- gs(χ₁χ₂) = rs χ₁ χ₂ · gs χ₁ · gs χ₂（値 s₁, s₂ = ±1 で）。 -/
theorem gs_combine (s₁ s₂ : ℂ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) :
    (if s₁ * s₂ = 1 then (1 : ℂ) else I) =
      (if s₁ = 1 then (1 : ℂ) else s₂) * (if s₁ = 1 then (1 : ℂ) else I) * (if s₂ = 1 then (1 : ℂ) else I) := by
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp [hne, I_mul_I]

/-- rs ψ (χ₁χ₂) = rs ψ χ₁ · rs ψ χ₂（値で）。 -/
theorem rs_combine (t s₁ s₂ : ℂ) :
    (if t = 1 then (1 : ℂ) else s₁ * s₂) = (if t = 1 then (1 : ℂ) else s₁) * (if t = 1 then (1 : ℂ) else s₂) := by
  split_ifs <;> simp

/-! ### 1. 素数冪の実原始指標の分類 -/

/-- 法 p の自明でない実指標どうしは等しい（生成元での値は −1）。 -/
theorem real_val_gen {p : ℕ} [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, g ^ j = x)
    (φ : DirichletCharacter ℂ p) (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) : φ g = -1 := by
  have hsq : φ g ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]
  have : (φ g - 1) * (φ g + 1) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exfalso
    apply hφ
    refine MulChar.ext (fun u => ?_)
    obtain ⟨j, rfl⟩ := hg u
    rw [MulChar.one_apply_coe, Units.val_pow_eq_pow_val, map_pow, show φ g = 1 by linear_combination h,
      one_pow]
  · linear_combination h

theorem real_char_eq_Lc {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (φ : DirichletCharacter ℂ p)
    (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) : φ = PAG.Part119.Lc p := by
  obtain ⟨g, hg⟩ := PAG.Part185.exists_gen (p := p)
  have hL2 : PAG.Part119.Lc p ^ 2 = 1 := (PAG.Part119.Lc_isQuadratic (p := p)).sq_eq_one
  have h1 := real_val_gen g hg φ hφ h2
  have h2' := real_val_gen g hg _ (PAG.Part119.Lc_ne_one hp2) hL2
  refine MulChar.ext (fun u => ?_)
  obtain ⟨j, rfl⟩ := hg u
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h1, h2']

/-- 法 L = r（奇素数）の自明でない実指標の値はルジャンドル記号。 -/
theorem legendre_values {r L : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hL : L = r)
    (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) (a : ℤ) :
    φ (a : ZMod L) = (legendreSym r a : ℂ) := by
  subst hL
  rw [real_char_eq_Lc hr2 φ hφ h2, PAG.Part119.Lc_apply]
  rfl

/-- **1a.** 奇素数 r、法 r^k（k ≥ 1）の実原始指標：k = 1 で、値はルジャンドル記号。 -/
theorem odd_base_values {r k : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (φ : DirichletCharacter ℂ (r ^ k)) (hφ : φ.IsPrimitive) (h2 : φ ^ 2 = 1) :
    k = 1 ∧ ∀ a : ℤ, φ (a : ZMod (r ^ k)) = (legendreSym r a : ℂ) := by
  have hodd : Odd r := hr.out.eq_two_or_odd'.resolve_left hr2
  have hr3 : 3 ≤ r := by
    have := hr.out.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  have hk1 : k = 1 := by
    by_contra hne
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    have hc : 1 ≤ c := by omega
    have hdvd := PAG.Part133.pc_dvd_orderOf c hc hodd φ hφ
    have hord : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hle := Nat.le_of_dvd two_pos (dvd_trans hdvd hord)
    have : r ≤ r ^ c := Nat.le_self_pow (by omega) r
    omega
  refine ⟨hk1, fun a => ?_⟩
  have h2le : 2 ≤ r ^ k := by rw [hk1, pow_one]; exact hr.out.two_le
  exact legendre_values hr2 (by rw [hk1, pow_one]) φ (PAG.Part195.ne_one_of_isPrimitive h2le φ hφ) h2 a

/-- 法 2 の指標は自明。 -/
theorem level_two_trivial {L : ℕ} (hL : L = 2) (φ : DirichletCharacter ℂ L) : φ = 1 := by
  subst hL
  refine MulChar.ext (fun u => ?_)
  have hu : (u : ZMod 2) = 1 := by
    have h0 : (u : ZMod 2) ≠ 0 := u.ne_zero
    revert h0
    generalize (u : ZMod 2) = x
    revert x
    decide
  rw [hu, map_one, map_one]

/-- 法 4 の原始指標の値は χ₄。 -/
theorem mod4_values {L : ℕ} (hL : L = 4) (φ : DirichletCharacter ℂ L) (hφ : φ.IsPrimitive) (a : ℤ) :
    φ (a : ZMod L) = ((ZMod.χ₄ (a : ZMod 4) : ℤ) : ℂ) := by
  subst hL
  have : Fact (1 < 4) := ⟨by norm_num⟩
  have hm1 := PAG.Part151.neg_one_mod4 φ hφ
  have key : ∀ x : ZMod 4, φ x = ((ZMod.χ₄ x : ℤ) : ℂ) := by
    have hx : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
    intro x
    rcases hx x with rfl | rfl | rfl | rfl
    · rw [MulChar.map_zero, show ZMod.χ₄ (0 : ZMod 4) = 0 from rfl, Int.cast_zero]
    · rw [map_one, map_one, Int.cast_one]
    · rw [MulChar.map_nonunit φ (by
        rw [show (2 : ZMod 4) = ((2 : ℕ) : ZMod 4) from rfl, ZMod.isUnit_iff_coprime]; decide),
        show ZMod.χ₄ (2 : ZMod 4) = 0 from rfl, Int.cast_zero]
    · rw [show (3 : ZMod 4) = -1 from rfl, hm1, show ZMod.χ₄ (-1 : ZMod 4) = -1 from rfl]
      push_cast; rfl
  exact key _

/-- 法 8 の原始指標の値は χ₈（偶）か χ₈′（奇）。 -/
theorem mod8_values {L : ℕ} (hL : L = 8) (φ : DirichletCharacter ℂ L) (hφ : φ.IsPrimitive) :
    (φ (-1) = 1 ∧ ∀ a : ℤ, φ (a : ZMod L) = ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ)) ∨
    (φ (-1) = -1 ∧ ∀ a : ℤ, φ (a : ZMod L) = ((ZMod.χ₈' (a : ZMod 8) : ℤ) : ℂ)) := by
  subst hL
  have : Fact (1 < 8) := ⟨by norm_num⟩
  have h5 := PAG.Part152.five_mod8 φ hφ
  have h7 : φ 7 = φ (-1) := rfl
  have h3 : φ 3 = φ 7 * φ 5 := by rw [← map_mul]; rfl
  have hu2 : ∀ x : ZMod 8, x = 2 ∨ x = 4 ∨ x = 6 → φ x = 0 := by
    intro x hx
    apply MulChar.map_nonunit
    rcases hx with rfl | rfl | rfl
    · rw [show (2 : ZMod 8) = ((2 : ℕ) : ZMod 8) from rfl, ZMod.isUnit_iff_coprime]; decide
    · rw [show (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) from rfl, ZMod.isUnit_iff_coprime]; decide
    · rw [show (6 : ZMod 8) = ((6 : ℕ) : ZMod 8) from rfl, ZMod.isUnit_iff_coprime]; decide
  have hx : ∀ x : ZMod 8, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by decide
  rcases neg_one_sq_eq φ with hm | hm
  · left
    refine ⟨hm, fun a => ?_⟩
    have key : ∀ x : ZMod 8, φ x = ((ZMod.χ₈ x : ℤ) : ℂ) := by
      intro x
      rcases hx x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [MulChar.map_zero, show ZMod.χ₈ (0 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [map_one, map_one, Int.cast_one]
      · rw [hu2 2 (Or.inl rfl), show ZMod.χ₈ (2 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h3, h7, hm, h5, show ZMod.χ₈ (3 : ZMod 8) = -1 from rfl]; push_cast; ring
      · rw [hu2 4 (Or.inr (Or.inl rfl)), show ZMod.χ₈ (4 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h5, show ZMod.χ₈ (5 : ZMod 8) = -1 from rfl]; push_cast; rfl
      · rw [hu2 6 (Or.inr (Or.inr rfl)), show ZMod.χ₈ (6 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h7, hm, show ZMod.χ₈ (7 : ZMod 8) = 1 from rfl, Int.cast_one]
    exact key _
  · right
    refine ⟨hm, fun a => ?_⟩
    have key : ∀ x : ZMod 8, φ x = ((ZMod.χ₈' x : ℤ) : ℂ) := by
      intro x
      rcases hx x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [MulChar.map_zero, show ZMod.χ₈' (0 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [map_one, map_one, Int.cast_one]
      · rw [hu2 2 (Or.inl rfl), show ZMod.χ₈' (2 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h3, h7, hm, h5, show ZMod.χ₈' (3 : ZMod 8) = 1 from rfl]; push_cast; ring
      · rw [hu2 4 (Or.inr (Or.inl rfl)), show ZMod.χ₈' (4 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h5, show ZMod.χ₈' (5 : ZMod 8) = -1 from rfl]; push_cast; rfl
      · rw [hu2 6 (Or.inr (Or.inr rfl)), show ZMod.χ₈' (6 : ZMod 8) = 0 from rfl, Int.cast_zero]
      · rw [h7, hm, show ZMod.χ₈' (7 : ZMod 8) = -1 from rfl]; push_cast; rfl
    exact key _

/-- **1b.** 法 2^k（k ≥ 1）の実原始指標：k = 2（χ₄）か、k = 3（χ₈ または χ₈′）。 -/
theorem two_base_values {k : ℕ} (hk : 1 ≤ k) (φ : DirichletCharacter ℂ (2 ^ k)) (hφ : φ.IsPrimitive)
    (h2 : φ ^ 2 = 1) :
    (k = 2 ∧ φ (-1) = -1 ∧ ∀ a : ℤ, φ (a : ZMod (2 ^ k)) = ((ZMod.χ₄ (a : ZMod 4) : ℤ) : ℂ)) ∨
    (k = 3 ∧ φ (-1) = 1 ∧ ∀ a : ℤ, φ (a : ZMod (2 ^ k)) = ((ZMod.χ₈ (a : ZMod 8) : ℤ) : ℂ)) ∨
    (k = 3 ∧ φ (-1) = -1 ∧ ∀ a : ℤ, φ (a : ZMod (2 ^ k)) = ((ZMod.χ₈' (a : ZMod 8) : ℤ) : ℂ)) := by
  have hk1 : k ≠ 1 := by
    rintro rfl
    have h1 := level_two_trivial (by norm_num : 2 ^ 1 = 2) φ
    exact PAG.Part195.ne_one_of_isPrimitive (by norm_num) φ hφ h1
  have hk4 : k < 4 := by
    by_contra hne
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
    have hord := PAG.Part135.orderOf_chi_two c (by omega) φ hφ
    have hdvd : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at hdvd
    have := Nat.le_of_dvd two_pos hdvd
    have : 2 ^ 2 ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right two_pos (by omega)
    omega
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl
  · left
    refine ⟨rfl, ?_, mod4_values (by norm_num) φ hφ⟩
    have := mod4_values (by norm_num : 2 ^ 2 = 4) φ hφ (-1)
    rw [show ((-1 : ℤ) : ZMod (2 ^ 2)) = -1 by push_cast; rfl] at this
    rw [this, show ZMod.χ₄ (-1 : ZMod 4) = -1 from rfl, Int.cast_neg, Int.cast_one]
  · rcases mod8_values (by norm_num : 2 ^ 3 = 8) φ hφ with ⟨hm, hv⟩ | ⟨hm, hv⟩
    · exact Or.inr (Or.inl ⟨rfl, hm, hv⟩)
    · exact Or.inr (Or.inr ⟨rfl, hm, hv⟩)

/-! ### 2. 素数冪の場合の z -/

/-- 法 L = r（奇素数）の自明でない実指標：z = gs（Part 163 のガウスの符号）。 -/
theorem odd_prime_z {r L : ℕ} [hr : Fact r.Prime] [NeZero L] (hr2 : r ≠ 2) (hL : L = r)
    (φ : DirichletCharacter ℂ L) (hφ : φ ≠ 1) (h2 : φ ^ 2 = 1) : zN φ = gs φ := by
  subst hL
  rw [real_char_eq_Lc hr2 φ hφ h2]
  have hodd : L % 2 = 1 := Nat.odd_iff.mp (hr.out.eq_two_or_odd'.resolve_left hr2)
  set m := L / 2 with hm_def
  have hrm : L = 2 * m + 1 := by omega
  have hneg := PAG.Part167.Lc_neg_one_pow L m hrm
  have hz : zN (PAG.Part119.Lc L) = PAG.Part160.epsG L := rfl
  unfold gs
  rw [hz, hneg]
  rcases (show L % 4 = 1 ∨ L % 4 = 3 by omega) with h4 | h4
  · have hm : Even m := ⟨m / 2, by omega⟩
    rw [PAG.Part167.epsG_one L h4, hm.neg_one_pow, ite_eq_left rfl]
  · have hm : Odd m := ⟨m / 2, by omega⟩
    rw [PAG.Part167.epsG_three L h4, hm.neg_one_pow, ite_eq_right (by norm_num)]

/-- **2a.** 奇素数 r、法 r^k の実原始指標：z = gs。 -/
theorem odd_base_z {r k : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hk : 1 ≤ k)
    (φ : DirichletCharacter ℂ (r ^ k)) (hφ : φ.IsPrimitive) (h2 : φ ^ 2 = 1) : zN φ = gs φ := by
  obtain ⟨hk1, -⟩ := odd_base_values hr2 hk φ hφ h2
  have h2le : 2 ≤ r ^ k := by rw [hk1, pow_one]; exact hr.out.two_le
  exact odd_prime_z hr2 (by rw [hk1, pow_one]) φ (PAG.Part195.ne_one_of_isPrimitive h2le φ hφ) h2

/-- 法 4 の原始指標：z = i = gs（Part 148）。 -/
theorem mod4_z {L : ℕ} [NeZero L] (hL : L = 4) (φ : DirichletCharacter ℂ L) (hφ : φ.IsPrimitive) :
    zN φ = gs φ := by
  subst hL
  have hm1 := PAG.Part151.neg_one_mod4 φ hφ
  unfold gs zN
  rw [hm1, ite_eq_right (by norm_num)]
  exact PAG.Part152.phase_mod4_eq φ hφ

/-- 法 8 の原始指標：z = gs（Part 148）。 -/
theorem mod8_z {L : ℕ} [NeZero L] (hL : L = 8) (φ : DirichletCharacter ℂ L) (hφ : φ.IsPrimitive) :
    zN φ = gs φ := by
  subst hL
  have hs8 : ((Real.sqrt ((8 : ℕ) : ℝ) : ℝ) : ℂ) = 2 * ((Real.sqrt 2 : ℝ) : ℂ) := by
    rw [show ((8 : ℕ) : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    push_cast; ring
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact_mod_cast this.ne'
  obtain ⟨he, ho⟩ := PAG.Part152.gauss_mod8 φ hφ
  unfold gs zN
  rw [hs8]
  rcases neg_one_sq_eq φ with hm | hm
  · rw [he hm, ite_eq_left hm]; field_simp
  · rw [ho hm, ite_eq_right (by rw [hm]; norm_num)]; field_simp

/-- **2b.** 法 2^k の実原始指標：z = gs。 -/
theorem two_base_z {k : ℕ} (hk : 1 ≤ k) (φ : DirichletCharacter ℂ (2 ^ k)) (hφ : φ.IsPrimitive)
    (h2 : φ ^ 2 = 1) : zN φ = gs φ := by
  rcases two_base_values hk φ hφ h2 with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · exact mod4_z (by norm_num) φ hφ
  · exact mod8_z (by norm_num) φ hφ
  · exact mod8_z (by norm_num) φ hφ

/-- **2.** 素数冪の実原始指標：z = gs。 -/
theorem base_z {r k : ℕ} [hr : Fact r.Prime] (hk : 1 ≤ k) (φ : DirichletCharacter ℂ (r ^ k))
    (hφ : φ.IsPrimitive) (h2 : φ ^ 2 = 1) : zN φ = gs φ := by
  by_cases hr2 : r = 2
  · subst hr2; exact two_base_z hk φ hφ h2
  · exact odd_base_z hr2 hk φ hφ h2

/-! ### 3. 素数冪どうしの相互法則 -/

theorem rs_symm_val (s s' : ℂ) (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) :
    (if s = 1 then (1 : ℂ) else s') = (if s' = 1 then (1 : ℂ) else s) := by
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;> simp [hne]

theorem leg_pm_one {t : ℕ} [Fact t.Prime] {a : ℤ} (ha : (a : ZMod t) ≠ 0) :
    (legendreSym t a : ℂ) = 1 ∨ (legendreSym t a : ℂ) = -1 := by
  rcases legendreSym.eq_one_or_neg_one t ha with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

theorem leg_pow {t : ℕ} [Fact t.Prime] (a : ℤ) (k : ℕ) :
    (legendreSym t (a ^ k) : ℂ) = (legendreSym t a : ℂ) ^ k := by
  unfold legendreSym
  push_cast
  rw [map_pow]
  push_cast
  rfl

theorem two_ne_zero_zmod {t : ℕ} [ht : Fact t.Prime] (ht2 : t ≠ 2) : ((2 : ℤ) : ZMod t) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod t) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact ht2 ((Nat.prime_dvd_prime_iff_eq ht.out Nat.prime_two).mp this)

theorem neg_one_ne_zero_zmod {t : ℕ} [ht : Fact t.Prime] : ((-1 : ℤ) : ZMod t) ≠ 0 := by
  push_cast
  exact neg_ne_zero.mpr one_ne_zero

/-- **3a.** 奇素数 t と法 2^k の実原始指標 θ：θ(t)·(2^k/t) は、(−1/t) = 1 なら 1、そうでなければ θ(−1)。 -/
theorem two_odd_rec {t k : ℕ} [ht : Fact t.Prime] (ht2 : t ≠ 2) (hk : 1 ≤ k)
    (θ : DirichletCharacter ℂ (2 ^ k)) (hθ : θ.IsPrimitive) (hθ2 : θ ^ 2 = 1) :
    θ ((t : ℤ) : ZMod (2 ^ k)) * (legendreSym t ((2 : ℤ) ^ k) : ℂ) =
      (if (legendreSym t (-1) : ℂ) = 1 then (1 : ℂ) else θ (-1)) := by
  have hL2 : (legendreSym t 2 : ℂ) ^ 2 = 1 := by
    exact_mod_cast legendreSym.sq_one t (two_ne_zero_zmod ht2)
  have hLm := leg_pm_one (t := t) (neg_one_ne_zero_zmod (t := t))
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rw [leg_pow]
  have hc4 : ((ZMod.χ₄ ((t : ℤ) : ZMod 4) : ℤ) : ℂ) = (legendreSym t (-1) : ℂ) := by
    rw [legendreSym.at_neg_one ht2]; push_cast; rfl
  have hc8 : ((ZMod.χ₈ ((t : ℤ) : ZMod 8) : ℤ) : ℂ) = (legendreSym t 2 : ℂ) := by
    rw [legendreSym.at_two ht2]; push_cast; rfl
  have hc8' : ((ZMod.χ₈' ((t : ℤ) : ZMod 8) : ℤ) : ℂ) = (legendreSym t (-1) : ℂ) * (legendreSym t 2 : ℂ) := by
    rw [← Int.cast_mul, ← legendreSym.mul, show (-1 : ℤ) * 2 = -2 by norm_num, legendreSym.at_neg_two ht2]
    push_cast; rfl
  rcases two_base_values hk θ hθ hθ2 with ⟨rfl, hm, hv⟩ | ⟨rfl, hm, hv⟩ | ⟨rfl, hm, hv⟩
  · rw [hv, hc4, hm, hL2, mul_one]
    rcases hLm with h | h <;> rw [h] <;> simp [hne]
  · rw [hv, hc8, hm, ite_self]
    linear_combination ((legendreSym t 2 : ℂ) ^ 2 + 1) * hL2
  · rw [hv, hc8', hm]
    have : (legendreSym t (-1) : ℂ) * (legendreSym t 2 : ℂ) * (legendreSym t 2 : ℂ) ^ 3
        = (legendreSym t (-1) : ℂ) := by
      linear_combination (legendreSym t (-1) : ℂ) * ((legendreSym t 2 : ℂ) ^ 2 + 1) * hL2
    rw [this]
    rcases hLm with h | h <;> rw [h] <;> simp [hne]

/-- **3b.** 相異なる奇素数 p, q：(p/q)(q/p) は、(−1/q) = 1 なら 1、そうでなければ (−1/p)（平方剰余の相互法則）。 -/
theorem odd_odd_rec {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) :
    (legendreSym q p : ℂ) * (legendreSym p q : ℂ) =
      (if (legendreSym q (-1) : ℂ) = 1 then (1 : ℂ) else (legendreSym p (-1) : ℂ)) := by
  have hqr := legendreSym.quadratic_reciprocity hp2 hq2 hpq
  have hp1 : p % 2 = 1 := Nat.odd_iff.mp (hp.out.eq_two_or_odd'.resolve_left hp2)
  have hq1 : q % 2 = 1 := Nat.odd_iff.mp (hq.out.eq_two_or_odd'.resolve_left hq2)
  rw [legendreSym.at_neg_one hq2, legendreSym.at_neg_one hp2, ZMod.χ₄_eq_neg_one_pow hq1,
    ZMod.χ₄_eq_neg_one_pow hp1]
  rw [← Int.cast_mul, hqr]
  push_cast
  rcases Nat.even_or_odd (q / 2) with h | h
  · rw [h.neg_one_pow, ite_eq_left rfl, (h.mul_left (p / 2)).neg_one_pow]
  · rw [h.neg_one_pow, ite_eq_right (by norm_num), pow_mul', h.neg_one_pow]

/-- **3. 素数冪どうしの相互法則**：相異なる素数 p, q、法 p^e, q^f の実原始指標 φ, ψ で
  ψ(p^e)·φ(q^f) = rs ψ φ。 -/
theorem bb_rec {p q e f : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q) (he : 1 ≤ e)
    (hf : 1 ≤ f) (φ : DirichletCharacter ℂ (p ^ e)) (hφ : φ.IsPrimitive) (hφ2 : φ ^ 2 = 1)
    (ψ : DirichletCharacter ℂ (q ^ f)) (hψ : ψ.IsPrimitive) (hψ2 : ψ ^ 2 = 1) :
    ψ ((p ^ e : ℕ) : ZMod (q ^ f)) * φ ((q ^ f : ℕ) : ZMod (p ^ e)) = rs ψ φ := by
  have hm1 : ∀ (L : ℕ), (-1 : ZMod L) = ((-1 : ℤ) : ZMod L) := fun L => by push_cast; rfl
  have hpow : ∀ (a k L : ℕ), ((a ^ k : ℕ) : ZMod L) = (((a : ℤ) ^ k : ℤ) : ZMod L) :=
    fun a k L => by push_cast; rfl
  unfold rs
  by_cases hp2 : p = 2
  · subst hp2
    have hq2 : q ≠ 2 := fun h => hpq h.symm
    obtain ⟨hf1, hψv⟩ := odd_base_values hq2 hf ψ hψ hψ2
    subst hf1
    have e1 : ψ ((2 ^ e : ℕ) : ZMod (q ^ 1)) = (legendreSym q ((2 : ℤ) ^ e) : ℂ) := by
      rw [hpow, hψv]; push_cast; rfl
    have e2 : φ ((q ^ 1 : ℕ) : ZMod (2 ^ e)) = φ ((q : ℤ) : ZMod (2 ^ e)) := by
      rw [hpow, pow_one (q : ℤ)]
    have e3 : ψ (-1) = (legendreSym q (-1) : ℂ) := by rw [hm1, hψv]
    rw [e1, e2, e3, mul_comm]
    exact two_odd_rec hq2 he φ hφ hφ2
  · by_cases hq2 : q = 2
    · subst hq2
      obtain ⟨he1, hφv⟩ := odd_base_values hp2 he φ hφ hφ2
      subst he1
      have e1 : ψ ((p ^ 1 : ℕ) : ZMod (2 ^ f)) = ψ ((p : ℤ) : ZMod (2 ^ f)) := by
        rw [hpow, pow_one (p : ℤ)]
      have e2 : φ ((2 ^ f : ℕ) : ZMod (p ^ 1)) = (legendreSym p ((2 : ℤ) ^ f) : ℂ) := by
        rw [hpow, hφv]; push_cast; rfl
      have e3 : φ (-1) = (legendreSym p (-1) : ℂ) := by rw [hm1, hφv]
      rw [e1, e2, e3, two_odd_rec hp2 hf ψ hψ hψ2]
      exact rs_symm_val _ _ (leg_pm_one (neg_one_ne_zero_zmod (t := p))) (neg_one_sq_eq ψ)
    · obtain ⟨he1, hφv⟩ := odd_base_values hp2 he φ hφ hφ2
      obtain ⟨hf1, hψv⟩ := odd_base_values hq2 hf ψ hψ hψ2
      subst he1 hf1
      have e1 : ψ ((p ^ 1 : ℕ) : ZMod (q ^ 1)) = (legendreSym q p : ℂ) := by
        rw [hpow, pow_one (p : ℤ), hψv]
      have e2 : φ ((q ^ 1 : ℕ) : ZMod (p ^ 1)) = (legendreSym p q : ℂ) := by
        rw [hpow, pow_one (q : ℤ), hφv]
      have e3 : ψ (-1) = (legendreSym q (-1) : ℂ) := by rw [hm1, hψv]
      have e4 : φ (-1) = (legendreSym p (-1) : ℂ) := by rw [hm1, hφv]
      rw [e1, e2, e3, e4]
      exact odd_odd_rec hp2 hq2 hpq

theorem castHom_neg_one {m n : ℕ} (h : m ∣ n) : ZMod.castHom h (ZMod m) (-1) = -1 := by
  rw [map_neg, map_one]

/-! ### 4. 主定理：帰納法 -/

/-- 帰納法の形：z(χ) = gs χ と、素数冪の実原始指標 ψ（法 q^f、q ∤ N）との相互法則 ψ(N)·χ(q^f) = rs ψ χ。 -/
theorem gauss_sign_aux (N : ℕ) : ∀ (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    χ ^ 2 = 1 → zN χ = gs χ ∧
      ∀ (q f : ℕ) (_ : Fact q.Prime), 1 ≤ f → q.Coprime N →
        ∀ ψ : DirichletCharacter ℂ (q ^ f), ψ.IsPrimitive → ψ ^ 2 = 1 →
          ψ ((N : ℕ) : ZMod (q ^ f)) * χ ((q ^ f : ℕ) : ZMod N) = rs ψ χ := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro hNZ χ hχ h2
  by_cases hN1 : N = 1
  · subst hN1
    have hχ1 : χ = 1 := DirichletCharacter.level_one χ
    have hall : ∀ x : ZMod 1, χ x = 1 := by
      intro x
      rw [show x = 1 from Subsingleton.elim _ _, map_one]
    refine ⟨?_, ?_⟩
    · rw [zN_level_one rfl χ]
      unfold gs
      rw [ite_eq_left (hall _)]
    · intro q f _ _ _ ψ _ _
      unfold rs
      rw [Nat.cast_one, map_one, one_mul, hall, hall]
      split_ifs <;> rfl
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨p, e, M, hp, he, hcop, rfl⟩ : ∃ p e M : ℕ, p.Prime ∧ 1 ≤ e ∧ (p ^ e).Coprime M ∧
      N = p ^ e * M := by
    have hp := Nat.minFac_prime hN1
    refine ⟨N.minFac, N.factorization N.minFac, N / N.minFac ^ N.factorization N.minFac, hp,
      hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N), ?_, ?_⟩
    · exact Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hN0)
    · exact (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm
  have : Fact p.Prime := ⟨hp⟩
  have hMZ : NeZero M := ⟨fun h0 => NeZero.ne (p ^ e * M) (by rw [h0, mul_zero])⟩
  have hMlt : M < p ^ e * M := by
    have h2' : 2 ≤ p ^ e := le_trans hp.two_le (le_self_pow hp.one_lt.le (by omega))
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    nlinarith
  set χ₁ := comp₁ hcop χ with hχ₁
  set χ₂ := comp₂ hcop χ with hχ₂
  have hdec : χ = χ₁.changeLevel (dvd_mul_right (p ^ e) M) * χ₂.changeLevel (dvd_mul_left M (p ^ e)) :=
    decomp hcop χ
  obtain ⟨h₁, h₂⟩ := (isPrimitive_iff hcop χ).mp hχ
  have hsq' : (χ₁ ^ 2).changeLevel (dvd_mul_right (p ^ e) M) * (χ₂ ^ 2).changeLevel (dvd_mul_left M (p ^ e))
      = (1 : DirichletCharacter ℂ (p ^ e)).changeLevel (dvd_mul_right (p ^ e) M) *
        (1 : DirichletCharacter ℂ M).changeLevel (dvd_mul_left M (p ^ e)) := by
    rw [← PAG.Part195.sq_mul_changeLevel, ← hdec, h2, map_one, map_one, one_mul]
  have h₁2 : χ₁ ^ 2 = 1 := by
    have := congrArg (comp₁ hcop) hsq'
    rwa [comp₁_mul, comp₁_mul] at this
  have h₂2 : χ₂ ^ 2 = 1 := by
    have := congrArg (comp₂ hcop) hsq'
    rwa [comp₂_mul, comp₂_mul] at this
  have hval : ∀ x : ZMod (p ^ e * M), χ x =
      χ₁ (ZMod.castHom (dvd_mul_right (p ^ e) M) (ZMod (p ^ e)) x) *
        χ₂ (ZMod.castHom (dvd_mul_left M (p ^ e)) (ZMod M) x) := by
    intro x
    conv_lhs => rw [hdec]
    exact PAG.Part193.mul_changeLevel_apply _ _ x
  have hm : χ (-1) = χ₁ (-1) * χ₂ (-1) := by rw [hval, castHom_neg_one, castHom_neg_one]
  obtain ⟨IHz, IHr⟩ := IH M hMlt hMZ χ₂ h₂ h₂2
  have hpM : p.Coprime M := Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) hcop
  refine ⟨?_, ?_⟩
  · obtain ⟨hz, -⟩ := PAG.Part193.z_mul_coprime hcop χ₁ χ₂
    have e1 : zN χ = gaussSum (χ₁.changeLevel (dvd_mul_right (p ^ e) M) *
        χ₂.changeLevel (dvd_mul_left M (p ^ e))) stdAddChar /
        ((Real.sqrt ((p ^ e * M : ℕ) : ℝ) : ℝ) : ℂ) := by
      unfold zN
      conv_lhs => rw [hdec]
    have hc := IHr p e this he hpM χ₁ h₁ h₁2
    have hz1 : zN χ₁ = gs χ₁ := base_z he χ₁ h₁ h₁2
    rw [e1, hz, hc]
    show rs χ₁ χ₂ * (zN χ₁ * zN χ₂) = gs χ
    rw [hz1, IHz]
    unfold gs rs
    rw [hm, gs_combine _ _ (neg_one_sq_eq χ₁) (neg_one_sq_eq χ₂)]
    ring
  · intro q f hqF hf hqN ψ hψ hψ2
    have hqp : q ≠ p := by
      intro hqp
      rw [hqp] at hqN
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hqN
        (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) M))
    have hqM : q.Coprime M := Nat.Coprime.coprime_dvd_right (dvd_mul_left M (p ^ e)) hqN
    have hψN : ψ ((p ^ e * M : ℕ) : ZMod (q ^ f)) =
        ψ ((p ^ e : ℕ) : ZMod (q ^ f)) * ψ ((M : ℕ) : ZMod (q ^ f)) := by
      rw [Nat.cast_mul, map_mul]
    have hχq : χ ((q ^ f : ℕ) : ZMod (p ^ e * M)) =
        χ₁ ((q ^ f : ℕ) : ZMod (p ^ e)) * χ₂ ((q ^ f : ℕ) : ZMod M) := by
      rw [hval, map_natCast (ZMod.castHom _ (ZMod (p ^ e))), map_natCast (ZMod.castHom _ (ZMod M))]
    rw [hψN, hχq]
    have hbb := bb_rec (p := p) (q := q) hqp.symm he hf χ₁ h₁ h₁2 ψ hψ hψ2
    have hih := IHr q f hqF hf hqM ψ hψ hψ2
    calc ψ ((p ^ e : ℕ) : ZMod (q ^ f)) * ψ ((M : ℕ) : ZMod (q ^ f)) *
          (χ₁ ((q ^ f : ℕ) : ZMod (p ^ e)) * χ₂ ((q ^ f : ℕ) : ZMod M))
        = (ψ ((p ^ e : ℕ) : ZMod (q ^ f)) * χ₁ ((q ^ f : ℕ) : ZMod (p ^ e))) *
          (ψ ((M : ℕ) : ZMod (q ^ f)) * χ₂ ((q ^ f : ℕ) : ZMod M)) := by ring
      _ = rs ψ χ₁ * rs ψ χ₂ := by rw [hbb, hih]
      _ = rs ψ χ := by
        unfold rs
        rw [hm, rs_combine]

/-- **4. ガウスの符号決定（すべての実原始指標）**：法 N の原始指標 χ で χ² = 1 なら、
  z(χ) = τ(χ)/√N は χ(−1) = 1 で 1、χ(−1) = −1 で i。 -/
theorem gauss_sign_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : zN χ = gs χ :=
  (gauss_sign_aux N inferInstance χ hχ h2).1

/-- **4′.** 同じことをガウス和で：τ(χ) = √N（χ(−1) = 1）、τ(χ) = i√N（χ(−1) = −1）。 -/
theorem gaussSum_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) :
    (χ (-1) = 1 → gaussSum χ stdAddChar = ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) ∧
    (χ (-1) = -1 → gaussSum χ stdAddChar = I * ((Real.sqrt (N : ℝ) : ℝ) : ℂ)) := by
  have hs : ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    exact_mod_cast this.ne'
  have hz := gauss_sign_real N χ hχ h2
  unfold zN gs at hz
  constructor
  · intro hm
    rw [ite_eq_left hm, div_eq_one_iff_eq hs] at hz
    exact hz
  · intro hm
    rw [ite_eq_right (by rw [hm]; norm_num), div_eq_iff hs] at hz
    exact hz

/-! ### 5. 一般の相互法則 -/

/-- **5. 実原始指標の相互法則**：互いに素な法 N₁, N₂ の実原始指標 χ₁, χ₂ で、
  χ₁(N₂)·χ₂(N₁) = rs χ₁ χ₂（両方が奇なら −1、そうでなければ 1）。 -/
theorem real_reciprocity {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (h₁2 : χ₁ ^ 2 = 1) (h₂2 : χ₂ ^ 2 = 1) :
    χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) = rs χ₁ χ₂ := by
  set χ := χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁) with hχ_def
  have hχ : χ.IsPrimitive := isPrimitive_mul hcop χ₁ χ₂ h₁ h₂
  have hχ2 : χ ^ 2 = 1 := by
    rw [hχ_def, PAG.Part195.sq_mul_changeLevel, h₁2, h₂2, map_one, map_one, one_mul]
  have hm : χ (-1) = χ₁ (-1) * χ₂ (-1) := by
    rw [hχ_def, PAG.Part193.mul_changeLevel_apply, castHom_neg_one, castHom_neg_one]
  obtain ⟨hz, -⟩ := PAG.Part193.z_mul_coprime hcop χ₁ χ₂
  have hzχ := gauss_sign_real (N₁ * N₂) χ hχ hχ2
  have hz1 := gauss_sign_real N₁ χ₁ h₁ h₁2
  have hz2 := gauss_sign_real N₂ χ₂ h₂ h₂2
  have hgs1 : gs χ₁ ≠ 0 := by unfold gs; split_ifs <;> simp [I_ne_zero]
  have hgs2 : gs χ₂ ≠ 0 := by unfold gs; split_ifs <;> simp [I_ne_zero]
  have key : χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * (gs χ₁ * gs χ₂) = rs χ₁ χ₂ * (gs χ₁ * gs χ₂) := by
    have h1 : zN χ = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * (zN χ₁ * zN χ₂) := hz
    rw [hzχ, hz1, hz2] at h1
    rw [← h1]
    unfold gs rs
    rw [hm, gs_combine _ _ (neg_one_sq_eq χ₁) (neg_one_sq_eq χ₂)]
    ring
  exact mul_right_cancel₀ (mul_ne_zero hgs1 hgs2) key

end PAG.Part198

#print axioms PAG.Part198.neg_one_sq_eq
#print axioms PAG.Part198.gs_combine
#print axioms PAG.Part198.rs_combine
#print axioms PAG.Part198.real_val_gen
#print axioms PAG.Part198.real_char_eq_Lc
#print axioms PAG.Part198.legendre_values
#print axioms PAG.Part198.odd_base_values
#print axioms PAG.Part198.level_two_trivial
#print axioms PAG.Part198.mod4_values
#print axioms PAG.Part198.mod8_values
#print axioms PAG.Part198.two_base_values
#print axioms PAG.Part198.odd_prime_z
#print axioms PAG.Part198.odd_base_z
#print axioms PAG.Part198.mod4_z
#print axioms PAG.Part198.mod8_z
#print axioms PAG.Part198.two_base_z
#print axioms PAG.Part198.base_z
#print axioms PAG.Part198.rs_symm_val
#print axioms PAG.Part198.leg_pm_one
#print axioms PAG.Part198.leg_pow
#print axioms PAG.Part198.two_ne_zero_zmod
#print axioms PAG.Part198.neg_one_ne_zero_zmod
#print axioms PAG.Part198.two_odd_rec
#print axioms PAG.Part198.odd_odd_rec
#print axioms PAG.Part198.bb_rec
#print axioms PAG.Part198.castHom_neg_one
#print axioms PAG.Part198.gauss_sign_aux
#print axioms PAG.Part198.gauss_sign_real
#print axioms PAG.Part198.gaussSum_real
#print axioms PAG.Part198.real_reciprocity
