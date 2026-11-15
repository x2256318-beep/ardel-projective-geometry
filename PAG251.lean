/-
  PAG 2.0 Part 247（2026-11-06）— 平方因子なしの N では ⟨D_u, E_1⟩ = A_N。B_s = ⟨D_u, E_N, E_s⟩ = A_N の分類（2 種類の組を除く）
  A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）、⟨D_u, E_s⟩（Part 240 の oneEAlg N s）、B_s = ⟨D_u, E_N, E_s⟩（Part 246 の addEAlg）、
  S′ = {t ∣ N : φ(N/t) ≠ 1}、G_q = Σ_{v ∣ N/q} D_{qv}（q の倍数の指示関数の掛け算）。
  1. 法 N の式：ε_N ≡ 1/N、E_N D_N E_N = (1/N)E_N、E_s² = E_s。法 q（素数）で (1 − E_1)D_qE_1D_q(1 − E_1) = ((q − 1)/q²)E_q、
     法 2 で 4(1 − E_2)D_2E_2D_2(1 − E_2) = 1 − E_2
  2. 中国剰余定理の共役（Part 228 の crtConj）で L(·)R(·) に分け、はさみうちの式（sandwich）で恒等式を示した：
     q 素数、gcd(q, M) = 1、t ∣ M なら E_{qt} = (q²/(q − 1))·(1 − E_t)G_qE_tG_q(1 − E_t)（法 qM、convL_geps_prime_mul）。
     q = 2 では逆向きに E_t = 4·(1 − E_{2t})G_2E_{2t}G_2(1 − E_{2t})（convL_geps_of_two_mul）
  3. 平方因子なしの N：D_u と E_1 を含む部分代数はすべての E_t を含む（t についての帰納法）。⟨D_u, E_1⟩ = A_N、
     偶数なら ⟨D_u, E_2⟩ = A_N。s ∈ S′ で B_s = A_N ⇔ s = 1 ∨ s = 2（addEAlg_eq_shellAlg_iff_of_squarefree）
  4. p² ∣ N/s なら ε_s は p の倍数の上にしかなく、⟨D_u, E_s⟩ は ψ(y) = e(y/p) の掛け算と可換。E_N は可換でないので
     E_N ∉ ⟨D_u, E_s⟩。とくに ⟨D_u, E_1⟩ = A_N ⇔ N は平方因子なし（oneEAlg_one_eq_shellAlg_iff）
  5. 単数の殻の上の証拠 f = Σ_{c < p^m}(δ_{1+cM} − δ_{−(1+cM)})（M = N/p^m）：p^{m+1} ∣ N、p^m ∤ s、N ∤ 2p^{m+1}
     （または N = 2p^{m+1}、p ≠ 2）なら E_{p^m} ∉ B_s（convL_geps_primePow_not_mem_addEAlg）。m = 1 では、p² ∣ N、p ∤ s、
     N ≠ p²、N ≠ 8 なら B_s ≠ A_N（addEAlg_ne_shellAlg_of_sq）
  6. 素冪 N = p^k、s = p^j（2 ≤ j < k）では、Part 246 の 2 点の証拠（q = p）で E_1 ∉ B_s
  7. 分類：B_1 = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²（addEAlg_one_eq_shellAlg_iff）。主定理：s ∈ S′ で、
     (N, s) が (p³, p)（p は奇素数）・(16, 2) でなければ、B_s = A_N ⇔ |S′| ≤ 2 ∨（N が平方因子なし ∧ s ∈ {1, 2}）
     （addEAlg_eq_shellAlg_iff）
  8. フーリエ双対：𝓕⟨D_u, E_s⟩𝓕⁻¹ = ⟨E_u, D_s⟩、⟨E_u, D_1⟩ = A_N ⇔ 平方因子なし。⟨E_u, D_N, D_1⟩ も 7 と同じ条件
  除いた (p³, p)（p は奇素数）・(16, 2) は数値だけ（step270：N = 27, 125, 343, 16 で B_s ≠ A_N）
-/
import PAG250

namespace PAG.Part251

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246 PAG.Part247 PAG.Part248 PAG.Part249 PAG.Part250
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 法 N での基本形と、法 q（素数）・法 2 での恒等式 -/

/-- **1a.** ε_N ≡ 1/N。 -/
theorem geps_self_apply (N : ℕ) [NeZero N] (y : ZMod N) : geps N N y = 1 / (N : ℂ) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h := natCast_mul_geps_eq_ramSum (dvd_refl N) y.val
  rw [ZMod.natCast_zmod_val, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N)), ramSum_of_dvd (one_dvd _),
    Nat.totient_one, Nat.cast_one, Int.cast_one] at h
  rw [eq_div_iff hN, mul_comm]
  exact h

/-- **1b.** (E_N f)(x) = (Σ_z f(z))/N。 -/
theorem convL_geps_self_apply (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (x : ZMod N) :
    PAG.Part15.convL (geps N N) f x = (∑ z, f z) / N := by
  show ∑ y, geps N N y * f (x - y) = _
  simp only [geps_self_apply, one_div]
  rw [← Finset.mul_sum, div_eq_inv_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y => rfl)

/-- **1c.** 1_{D_N} = δ_0。 -/
theorem dind_self_apply (N : ℕ) [NeZero N] (y : ZMod N) : dind N N y = if y = 0 then 1 else 0 := by
  have h : Nat.gcd N y.val = N ↔ y = 0 := by
    rw [← ZMod.val_eq_zero]
    constructor
    · intro hg
      have hd : N ∣ y.val := by
        have := Nat.gcd_dvd_right N y.val
        rwa [hg] at this
      exact Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt y)
    · intro h0
      rw [h0, Nat.gcd_zero_right]
  exact if_congr h rfl rfl

/-- **1d.** D_s D_s = D_s。 -/
theorem mulLeft_dind_mul_self (N s : ℕ) :
    LinearMap.mulLeft ℂ (dind N s) * LinearMap.mulLeft ℂ (dind N s) = LinearMap.mulLeft ℂ (dind N s) := by
  apply LinearMap.ext
  intro f
  show dind N s * (dind N s * f) = dind N s * f
  rw [← mul_assoc, dind_mul, ite_eq_left rfl]

/-- **1e.** E_s E_s = E_s（𝓕 で D_s D_s = D_s に移す）。 -/
theorem convL_geps_mul_self (N s : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N s) * PAG.Part15.convL (geps N s) = PAG.Part15.convL (geps N s) := by
  apply (fourierConj N).injective
  rw [map_mul, fourierConj_convL_geps, mulLeft_dind_mul_self]

/-- **1f.** E_N D_N E_N = (1/N)·E_N。 -/
theorem convL_geps_self_mul_mulLeft_dind_self (N : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N N) * LinearMap.mulLeft ℂ (dind N N) * PAG.Part15.convL (geps N N) =
      (1 / (N : ℂ)) • PAG.Part15.convL (geps N N) := by
  apply LinearMap.ext
  intro f
  funext x
  show PAG.Part15.convL (geps N N) (LinearMap.mulLeft ℂ (dind N N) (PAG.Part15.convL (geps N N) f)) x =
    (1 / (N : ℂ)) * PAG.Part15.convL (geps N N) f x
  have hsum : ∑ z : ZMod N, dind N N z = 1 := by
    simp only [dind_self_apply]
    simp
  have hE : ∀ z, PAG.Part15.convL (geps N N) f z = (∑ w, f w) / N := fun z => convL_geps_self_apply N f z
  rw [convL_geps_self_apply]
  simp only [LinearMap.mulLeft_apply, Pi.mul_apply, hE]
  rw [← Finset.sum_mul, hsum, one_mul]
  ring

/-- **1g.** 素数 q では E_1 + E_q = 1（法 q）。 -/
theorem convL_geps_one_add_self_of_prime {q : ℕ} [NeZero q] (hq : q.Prime) :
    PAG.Part15.convL (geps q 1) + PAG.Part15.convL (geps q q) = 1 := by
  have h := sum_convL_geps q
  rw [hq.divisors, Finset.sum_pair (Ne.symm hq.one_lt.ne')] at h
  exact h

/-- **1h.** 法 q（素数）での恒等式 (1 − E_1)D_qE_1D_q(1 − E_1) = ((q − 1)/q²)·E_q
（1 − E_1 = E_q と E_qD_qE_q = (1/q)E_q、D_q² = D_q）。 -/
theorem level_identity {q : ℕ} [NeZero q] (hq : q.Prime) :
    (1 - PAG.Part15.convL (geps q 1)) * LinearMap.mulLeft ℂ (dind q q) * PAG.Part15.convL (geps q 1) *
      LinearMap.mulLeft ℂ (dind q q) * (1 - PAG.Part15.convL (geps q 1)) =
      (((q : ℂ) - 1) / (q : ℂ) ^ 2) • PAG.Part15.convL (geps q q) := by
  have hsum := convL_geps_one_add_self_of_prime hq
  have h1 : 1 - PAG.Part15.convL (geps q 1) = PAG.Part15.convL (geps q q) := by
    rw [← hsum]
    abel
  have h2 : PAG.Part15.convL (geps q 1) = 1 - PAG.Part15.convL (geps q q) := by
    rw [← hsum]
    abel
  rw [h1, h2]
  have hPP := mulLeft_dind_mul_self q q
  have hEPE := convL_geps_self_mul_mulLeft_dind_self q
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  calc PAG.Part15.convL (geps q q) * LinearMap.mulLeft ℂ (dind q q) * (1 - PAG.Part15.convL (geps q q)) *
        LinearMap.mulLeft ℂ (dind q q) * PAG.Part15.convL (geps q q)
      = PAG.Part15.convL (geps q q) * LinearMap.mulLeft ℂ (dind q q) * LinearMap.mulLeft ℂ (dind q q) *
          PAG.Part15.convL (geps q q) -
        PAG.Part15.convL (geps q q) * LinearMap.mulLeft ℂ (dind q q) * PAG.Part15.convL (geps q q) *
          LinearMap.mulLeft ℂ (dind q q) * PAG.Part15.convL (geps q q) := by
        rw [mul_sub, mul_one, sub_mul, sub_mul]
    _ = (1 / (q : ℂ)) • PAG.Part15.convL (geps q q) -
        (1 / (q : ℂ)) • ((1 / (q : ℂ)) • PAG.Part15.convL (geps q q)) := by
        rw [mul_assoc (PAG.Part15.convL (geps q q)) (LinearMap.mulLeft ℂ (dind q q)), hPP, hEPE, smul_mul_assoc,
          smul_mul_assoc, hEPE]
    _ = (((q : ℂ) - 1) / (q : ℂ) ^ 2) • PAG.Part15.convL (geps q q) := by
        apply LinearMap.ext
        intro f
        funext x
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp

/-- **1i.** 法 2 での恒等式 4·(1 − E_2)D_2E_2D_2(1 − E_2) = 1 − E_2（ℂ² の上で値を比べる）。 -/
theorem two_level_identity :
    (4 : ℂ) • ((1 - PAG.Part15.convL (geps 2 2)) * LinearMap.mulLeft ℂ (dind 2 2) * PAG.Part15.convL (geps 2 2) *
      LinearMap.mulLeft ℂ (dind 2 2) * (1 - PAG.Part15.convL (geps 2 2))) = 1 - PAG.Part15.convL (geps 2 2) := by
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have h01 : (0 : ZMod 2) ≠ 1 := by decide
  have hE : ∀ (g : ZMod 2 → ℂ) (y : ZMod 2), PAG.Part15.convL (geps 2 2) g y = (g 0 + g 1) / 2 := by
    intro g y
    rw [convL_geps_self_apply, huniv, Finset.sum_pair h01]
    norm_num
  have hP : ∀ (g : ZMod 2 → ℂ) (y : ZMod 2), LinearMap.mulLeft ℂ (dind 2 2) g y = (if y = 0 then 1 else 0) * g y := by
    intro g y
    rw [LinearMap.mulLeft_apply, Pi.mul_apply, dind_self_apply]
  have h10 : ¬ ((1 : ZMod 2) = 0) := h01.symm
  apply LinearMap.ext
  intro f
  funext x
  by_cases hx : x = 0
  · subst hx
    simp only [LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Pi.sub_apply, hE, hP, smul_eq_mul, h10, ↓reduceIte]
    ring
  · have hx1 : x = 1 := by
      revert hx
      revert x
      decide
    subst hx1
    simp only [LinearMap.smul_apply, Pi.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      Pi.sub_apply, hE, hP, smul_eq_mul, h10, ↓reduceIte]
    ring

/-! ### 2. 中国剰余定理による分解での計算 -/

/-- **2a.** L(ST) = L(S)L(T)。 -/
theorem leftOp_mul' {a : ℕ} (b : ℕ) (S T : Module.End ℂ (ZMod a → ℂ)) :
    PAG.Part232.leftOp b (S * T) = PAG.Part232.leftOp b S * PAG.Part232.leftOp b T :=
  map_mul (PAG.Part232.leftHom a b) S T

/-- **2b.** L(S − T) = L(S) − L(T)。 -/
theorem leftOp_sub' {a : ℕ} (b : ℕ) (S T : Module.End ℂ (ZMod a → ℂ)) :
    PAG.Part232.leftOp b (S - T) = PAG.Part232.leftOp b S - PAG.Part232.leftOp b T :=
  map_sub (PAG.Part232.leftHom a b) S T

/-- **2c.** L(1) = 1。 -/
theorem leftOp_one' {a : ℕ} (b : ℕ) : PAG.Part232.leftOp b (1 : Module.End ℂ (ZMod a → ℂ)) = 1 :=
  map_one (PAG.Part232.leftHom a b)

/-- **2d.** L(c·S) = c·L(S)。 -/
theorem leftOp_smul' {a : ℕ} (b : ℕ) (c : ℂ) (S : Module.End ℂ (ZMod a → ℂ)) :
    PAG.Part232.leftOp b (c • S) = c • PAG.Part232.leftOp b S :=
  map_smul (PAG.Part232.leftHom a b) c S

/-- **2e.** R(ST) = R(S)R(T)。 -/
theorem rightOp_mul' (a : ℕ) {b : ℕ} (S T : Module.End ℂ (ZMod b → ℂ)) :
    PAG.Part232.rightOp a (S * T) = PAG.Part232.rightOp a S * PAG.Part232.rightOp a T :=
  map_mul (PAG.Part232.rightHom a b) S T

/-- **2f.** R(1) = 1。 -/
theorem rightOp_one' (a : ℕ) {b : ℕ} : PAG.Part232.rightOp a (1 : Module.End ℂ (ZMod b → ℂ)) = 1 :=
  map_one (PAG.Part232.rightHom a b)

/-- **2g.** R(Σ S_i) = Σ R(S_i)。 -/
theorem rightOp_sum' (a : ℕ) {b : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ (ZMod b → ℂ)) :
    PAG.Part232.rightOp a (∑ i ∈ s, f i) = ∑ i ∈ s, PAG.Part232.rightOp a (f i) :=
  map_sum (PAG.Part232.rightHom a b) f s

/-- **2h.** はさみうちの式：z² = z なら、X = L(c)R(z) について
(1 − X)L(P)XL(P)(1 − X) = L((1 − c)PcP(1 − c))R(z)（L と R は可換）。 -/
theorem sandwich {a b : ℕ} [NeZero a] [NeZero b] (c P : Module.End ℂ (ZMod a → ℂ)) (z : Module.End ℂ (ZMod b → ℂ))
    (hz : z * z = z) :
    (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P *
      (PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P *
      (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) =
      PAG.Part232.leftOp b ((1 - c) * P * c * P * (1 - c)) * PAG.Part232.rightOp a z := by
  have hc : ∀ S, PAG.Part232.leftOp b S * PAG.Part232.rightOp a z =
      PAG.Part232.rightOp a z * PAG.Part232.leftOp b S := fun S => (PAG.Part232.leftOp_commute_rightOp S z).eq
  have hzz : PAG.Part232.rightOp a z * PAG.Part232.rightOp a z = PAG.Part232.rightOp a z := by
    rw [← rightOp_mul', hz]
  have h1 : PAG.Part232.leftOp b P * (PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P =
      PAG.Part232.leftOp b (P * c * P) * PAG.Part232.rightOp a z := by
    rw [leftOp_mul', leftOp_mul', mul_assoc (PAG.Part232.leftOp b P), mul_assoc (PAG.Part232.leftOp b c), ← hc P]
    simp only [mul_assoc]
  have h2 : ∀ x, (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) *
      (PAG.Part232.leftOp b x * PAG.Part232.rightOp a z) =
      PAG.Part232.leftOp b ((1 - c) * x) * PAG.Part232.rightOp a z := by
    intro x
    rw [sub_mul, one_mul, leftOp_mul', leftOp_sub', leftOp_one', sub_mul, sub_mul, one_mul]
    congr 1
    rw [mul_assoc, ← mul_assoc (PAG.Part232.rightOp a z), ← hc x, mul_assoc, hzz, ← mul_assoc]
  have h3 : ∀ y, PAG.Part232.leftOp b y * PAG.Part232.rightOp a z *
      (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) =
      PAG.Part232.leftOp b (y * (1 - c)) * PAG.Part232.rightOp a z := by
    intro y
    rw [mul_sub, mul_one, leftOp_mul', leftOp_sub', leftOp_one', mul_sub, mul_one, sub_mul]
    congr 1
    rw [mul_assoc, ← mul_assoc (PAG.Part232.rightOp a z), ← hc c, mul_assoc, hzz, ← mul_assoc]
  have e : (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P *
      (PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P *
      (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) =
      (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) *
        (PAG.Part232.leftOp b P * (PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) * PAG.Part232.leftOp b P) *
        (1 - PAG.Part232.leftOp b c * PAG.Part232.rightOp a z) := by
    simp only [mul_assoc]
  rw [e, h1, h2, h3]
  simp only [mul_assoc]

/-- **2i.** C(Σ_{v ∣ M} D_{qv}) = L(D_q)（gcd(q, M) = 1）。 -/
theorem crtConj_sum_dind {q M : ℕ} [NeZero q] [NeZero M] (hqM : q.Coprime M) :
    PAG.Part232.crtConj hqM (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind (q * M) (q * v))) =
      PAG.Part232.leftOp M (LinearMap.mulLeft ℂ (dind q q)) := by
  rw [map_sum]
  have h : ∀ v ∈ M.divisors, PAG.Part232.crtConj hqM (LinearMap.mulLeft ℂ (dind (q * M) (q * v))) =
      PAG.Part232.leftOp M (LinearMap.mulLeft ℂ (dind q q)) * PAG.Part232.rightOp q (LinearMap.mulLeft ℂ (dind M v)) :=
    fun v hv => PAG.Part232.crtConj_dind hqM (dvd_refl q) (Nat.dvd_of_mem_divisors hv)
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← rightOp_sum', PAG.Part232.sum_mulLeft_dind, rightOp_one', mul_one]

/-- **2j.** 恒等式（法 qM、q は素数で gcd(q, M) = 1、t ∣ M）：
E_{qt} = (q²/(q − 1))·(1 − E_t)G E_t G(1 − E_t)、G = Σ_{v ∣ M} D_{qv}（q の倍数の指示関数の掛け算）。 -/
theorem convL_geps_prime_mul_aux {q M t : ℕ} [NeZero q] [NeZero M] (hq : q.Prime) (hqM : q.Coprime M) (ht : t ∣ M) :
    PAG.Part15.convL (geps (q * M) (q * t)) =
      ((q : ℂ) ^ 2 / ((q : ℂ) - 1)) • ((1 - PAG.Part15.convL (geps (q * M) t)) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind (q * M) (q * v))) * PAG.Part15.convL (geps (q * M) t) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind (q * M) (q * v))) * (1 - PAG.Part15.convL (geps (q * M) t))) := by
  have hEt : PAG.Part232.crtConj hqM (PAG.Part15.convL (geps (q * M) t)) =
      PAG.Part232.leftOp M (PAG.Part15.convL (geps q 1)) * PAG.Part232.rightOp q (PAG.Part15.convL (geps M t)) := by
    have h := PAG.Part232.crtConj_geps hqM (one_dvd q) ht
    rwa [one_mul] at h
  have hEqt := PAG.Part232.crtConj_geps hqM (dvd_refl q) ht
  have hq1 : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.one_lt.ne')
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  apply (PAG.Part232.crtConj hqM).injective
  rw [map_smul, map_mul, map_mul, map_mul, map_mul, map_sub, map_one, crtConj_sum_dind hqM, hEt, hEqt,
    sandwich _ _ _ (convL_geps_mul_self M t), level_identity hq, leftOp_smul', smul_mul_assoc, smul_smul]
  have hc : (q : ℂ) ^ 2 / ((q : ℂ) - 1) * (((q : ℂ) - 1) / (q : ℂ) ^ 2) = 1 := by
    field_simp
  rw [hc, one_smul]

/-- **2k.** 同じ恒等式を N = qM の形で（N に依存する型の置き換えは subst で）。 -/
theorem convL_geps_prime_mul {n q M t : ℕ} [NeZero n] (hn : n = q * M) (hq : q.Prime) (hqM : q.Coprime M)
    (ht : t ∣ M) :
    PAG.Part15.convL (geps n (q * t)) =
      ((q : ℂ) ^ 2 / ((q : ℂ) - 1)) • ((1 - PAG.Part15.convL (geps n t)) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (q * v))) * PAG.Part15.convL (geps n t) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (q * v))) * (1 - PAG.Part15.convL (geps n t))) := by
  subst hn
  have : NeZero q := ⟨hq.ne_zero⟩
  have : NeZero M := ⟨by
    rintro rfl
    exact NeZero.ne (q * 0) (mul_zero q)⟩
  exact convL_geps_prime_mul_aux hq hqM ht

/-- **2l.** q = 2 の逆向きの恒等式（法 2M、M は奇数、t ∣ M）：E_t = 4·(1 − E_{2t})G E_{2t} G(1 − E_{2t})、
G = Σ_{v ∣ M} D_{2v}。 -/
theorem convL_geps_of_two_mul_aux {M t : ℕ} [NeZero M] (hM : Nat.Coprime 2 M) (ht : t ∣ M) :
    PAG.Part15.convL (geps (2 * M) t) =
      (4 : ℂ) • ((1 - PAG.Part15.convL (geps (2 * M) (2 * t))) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind (2 * M) (2 * v))) * PAG.Part15.convL (geps (2 * M) (2 * t)) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind (2 * M) (2 * v))) *
        (1 - PAG.Part15.convL (geps (2 * M) (2 * t)))) := by
  have hEt : PAG.Part232.crtConj hM (PAG.Part15.convL (geps (2 * M) t)) =
      PAG.Part232.leftOp M (PAG.Part15.convL (geps 2 1)) * PAG.Part232.rightOp 2 (PAG.Part15.convL (geps M t)) := by
    have h := PAG.Part232.crtConj_geps hM (one_dvd 2) ht
    rwa [one_mul] at h
  have hE2t := PAG.Part232.crtConj_geps hM (dvd_refl 2) ht
  have h21 : 1 - PAG.Part15.convL (geps 2 2) = PAG.Part15.convL (geps 2 1) := by
    rw [← convL_geps_one_add_self_of_prime Nat.prime_two]
    abel
  apply (PAG.Part232.crtConj hM).injective
  rw [map_smul, map_mul, map_mul, map_mul, map_mul, map_sub, map_one, crtConj_sum_dind hM, hE2t, hEt,
    sandwich _ _ _ (convL_geps_mul_self M t), ← smul_mul_assoc, ← leftOp_smul', two_level_identity, h21]

/-- **2m.** 同じ恒等式を N = 2M の形で。 -/
theorem convL_geps_of_two_mul {n M t : ℕ} [NeZero n] (hn : n = 2 * M) (hM : Nat.Coprime 2 M) (ht : t ∣ M) :
    PAG.Part15.convL (geps n t) =
      (4 : ℂ) • ((1 - PAG.Part15.convL (geps n (2 * t))) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (2 * v))) * PAG.Part15.convL (geps n (2 * t)) *
        (∑ v ∈ M.divisors, LinearMap.mulLeft ℂ (dind n (2 * v))) * (1 - PAG.Part15.convL (geps n (2 * t)))) := by
  subst hn
  have : NeZero M := ⟨by
    rintro rfl
    exact NeZero.ne (2 * 0) (mul_zero 2)⟩
  exact convL_geps_of_two_mul_aux hM ht

/-! ### 3. 平方因子なしの N：⟨D_u, E_1⟩ = A_N、偶数なら ⟨D_u, E_2⟩ = A_N -/

/-- **3a.** 平方因子なしの N で、すべての D_u と E_1 を含む部分代数は、すべての E_t を含む
（t の最小素因数 q で t = q·t′ と分け、2j の恒等式で E_{t′} から E_t を作る。t についての帰納法）。 -/
theorem convL_geps_mem_of_squarefree {N : ℕ} [NeZero N] (hsq : Squarefree N)
    (S : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) (hD : ∀ u, LinearMap.mulLeft ℂ (dind N u) ∈ S)
    (h1 : PAG.Part15.convL (geps N 1) ∈ S) (t : ℕ) : PAG.Part15.convL (geps N t) ∈ S := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases htN : t ∣ N
    · by_cases ht1 : t = 1
      · rw [ht1]
        exact h1
      · have hq := Nat.minFac_prime ht1
        have hqt : t.minFac ∣ t := Nat.minFac_dvd t
        have hqN : t.minFac ∣ N := dvd_trans hqt htN
        have ht0 : t ≠ 0 := by
          rintro rfl
          exact NeZero.ne N (Nat.eq_zero_of_zero_dvd htN)
        obtain ⟨t', ht'⟩ := hqt
        have hNM : N = t.minFac * (N / t.minFac) := (Nat.mul_div_cancel' hqN).symm
        have hcop : t.minFac.Coprime (N / t.minFac) := by
          rw [Nat.Prime.coprime_iff_not_dvd hq]
          intro h
          have h2 : t.minFac * t.minFac ∣ N := by
            have h3 := mul_dvd_mul_left t.minFac h
            rwa [← hNM] at h3
          exact (Nat.squarefree_iff_prime_squarefree.mp hsq) _ hq h2
        have ht'M : t' ∣ N / t.minFac := by
          have h2 : t.minFac * t' ∣ t.minFac * (N / t.minFac) := by
            rw [← ht', ← hNM]
            exact htN
          exact Nat.dvd_of_mul_dvd_mul_left hq.pos h2
        have hlt : t' < t := by
          have ht'0 : t' ≠ 0 := by
            rintro rfl
            rw [mul_zero] at ht'
            exact ht0 ht'
          have h2 := hq.two_le
          have h3 : t = t.minFac * t' := ht'
          have h4 : 0 < t' := Nat.pos_of_ne_zero ht'0
          nlinarith
        have hmem := ih t' hlt
        have hG : (∑ v ∈ (N / t.minFac).divisors, LinearMap.mulLeft ℂ (dind N (t.minFac * v))) ∈ S :=
          Subalgebra.sum_mem S (fun v _ => hD _)
        have e := convL_geps_prime_mul hNM hq hcop ht'M
        rw [← ht'] at e
        rw [e]
        refine Subalgebra.smul_mem S ?_ _
        refine Subalgebra.mul_mem S (Subalgebra.mul_mem S (Subalgebra.mul_mem S (Subalgebra.mul_mem S ?_ hG) hmem) hG) ?_
        · exact Subalgebra.sub_mem S (Subalgebra.one_mem S) hmem
        · exact Subalgebra.sub_mem S (Subalgebra.one_mem S) hmem
    · rw [convL_geps_of_not_dvd htN]
      exact Subalgebra.zero_mem S

/-- **3b.** 平方因子なしの N で ⟨D_u, E_1⟩ = A_N。 -/
theorem oneEAlg_one_eq_shellAlg {N : ℕ} [NeZero N] (hsq : Squarefree N) : oneEAlg N 1 = shellAlg N := by
  refine le_antisymm (oneEAlg_le N 1) ?_
  rw [PAG.Part232.shellAlg_eq_adjoin]
  apply Algebra.adjoin_le
  rintro X (⟨t, rfl⟩ | ⟨u, rfl⟩)
  · exact convL_geps_mem_of_squarefree hsq (oneEAlg N 1) (fun u => Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩))
      (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))) t
  · exact Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)

/-- **3c.** 平方因子なしの偶数 N で ⟨D_u, E_2⟩ = A_N（2l の逆向きの恒等式で E_1 が出る）。 -/
theorem oneEAlg_two_eq_shellAlg {N : ℕ} [NeZero N] (hsq : Squarefree N) (h2 : 2 ∣ N) :
    oneEAlg N 2 = shellAlg N := by
  have hD : ∀ u, LinearMap.mulLeft ℂ (dind N u) ∈ oneEAlg N 2 := fun u => Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)
  have hE2 : PAG.Part15.convL (geps N 2) ∈ oneEAlg N 2 := Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))
  have hNM : N = 2 * (N / 2) := (Nat.mul_div_cancel' h2).symm
  have hcop : Nat.Coprime 2 (N / 2) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    have h3 : 2 * 2 ∣ N := by
      have h4 := mul_dvd_mul_left 2 h
      rwa [← hNM] at h4
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) 2 Nat.prime_two h3
  have h1 : PAG.Part15.convL (geps N 1) ∈ oneEAlg N 2 := by
    have e := convL_geps_of_two_mul hNM hcop (one_dvd (N / 2))
    rw [mul_one] at e
    rw [e]
    have hG : (∑ v ∈ (N / 2).divisors, LinearMap.mulLeft ℂ (dind N (2 * v))) ∈ oneEAlg N 2 :=
      Subalgebra.sum_mem _ (fun v _ => hD _)
    refine Subalgebra.smul_mem _ ?_ _
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ hG) hE2) hG) ?_
    · exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE2
    · exact Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE2
  refine le_antisymm (oneEAlg_le N 2) ?_
  rw [PAG.Part232.shellAlg_eq_adjoin]
  apply Algebra.adjoin_le
  rintro X (⟨t, rfl⟩ | ⟨u, rfl⟩)
  · exact convL_geps_mem_of_squarefree hsq (oneEAlg N 2) hD h1 t
  · exact hD u

/-- **3d.** 平方因子なしの N で B_1 = A_N。 -/
theorem addEAlg_one_eq_shellAlg {N : ℕ} [NeZero N] (hsq : Squarefree N) : addEAlg N 1 = shellAlg N :=
  le_antisymm (addEAlg_le N 1) ((oneEAlg_one_eq_shellAlg hsq).symm.le.trans (oneEAlg_le_addEAlg' N 1))

/-- **3e.** 平方因子なしの偶数 N で B_2 = A_N。 -/
theorem addEAlg_two_eq_shellAlg {N : ℕ} [NeZero N] (hsq : Squarefree N) (h2 : 2 ∣ N) : addEAlg N 2 = shellAlg N :=
  le_antisymm (addEAlg_le N 2) ((oneEAlg_two_eq_shellAlg hsq h2).symm.le.trans (oneEAlg_le_addEAlg' N 2))

/-- **3f.** 平方因子なしの N、s ∈ S′ なら B_s = A_N ⇔ s = 1 ∨ s = 2（⇒ は Part 246 の 4l）。 -/
theorem addEAlg_eq_shellAlg_iff_of_squarefree {N s : ℕ} [NeZero N] (hsq : Squarefree N) (hs : s ∈ devSet N) :
    addEAlg N s = shellAlg N ↔ s = 1 ∨ s = 2 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact addEAlg_ne_shellAlg_of_squarefree hsq hs hcon.1 hcon.2 h
  · rintro (rfl | rfl)
    · exact addEAlg_one_eq_shellAlg hsq
    · exact addEAlg_two_eq_shellAlg hsq (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hs).1)

/-! ### 4. ⟨D_u, E_s⟩ に E_N が入らない条件：N/s が平方因子をもつ -/

/-- 指標 ψ(y) = e(y·(N/p)/N)（= e(y/p)）。 -/
noncomputable def charP (N p : ℕ) [NeZero N] : ZMod N → ℂ := fun y => stdAddChar (y * ((N / p : ℕ) : ZMod N))

/-- **4a.** p ∣ N、p ∣ y.val なら y·(N/p) = 0。 -/
theorem mul_div_eq_zero_of_dvd {N p : ℕ} [NeZero N] (hpN : p ∣ N) {y : ZMod N} (hy : p ∣ y.val) :
    y * ((N / p : ℕ) : ZMod N) = 0 := by
  obtain ⟨k, hk⟩ := hy
  have e : y = ((p * k : ℕ) : ZMod N) := by
    rw [← hk, ZMod.natCast_zmod_val]
  rw [e, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨k, by rw [mul_comm p k, mul_assoc, Nat.mul_div_cancel' hpN, mul_comm]⟩

/-- **4b.** p 素数、p² ∣ N/s、p ∤ y.val なら ε_s(y) = 0（c_{N/s}(y) = 0）。 -/
theorem geps_eq_zero_of_not_dvd_val {N s p : ℕ} [NeZero N] (hs : s ∣ N) (hp : p.Prime) (hpp : p * p ∣ N / s)
    {y : ZMod N} (hy : ¬ p ∣ y.val) : geps N s y = 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hs0 : 0 < s := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hs)
  have hq0 : N / s ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hs) hs0).ne'
  have hram : ramSum y.val (N / s) = 0 := by
    by_contra h
    rw [← ne_eq, ramSum_ne_zero_iff_squarefree hq0] at h
    have hg : ¬ p ∣ Nat.gcd (N / s) y.val := fun h' => hy (dvd_trans h' (Nat.gcd_dvd_right _ _))
    have hcop : Nat.Coprime (p * p) (Nat.gcd (N / s) y.val) :=
      Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hg, (Nat.Prime.coprime_iff_not_dvd hp).mpr hg⟩
    have hdiv : p * p ∣ Nat.gcd (N / s) y.val * ((N / s) / Nat.gcd (N / s) y.val) := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
      exact hpp
    exact (Nat.squarefree_iff_prime_squarefree.mp h) p hp (hcop.dvd_of_dvd_mul_left hdiv)
  have e := natCast_mul_geps_eq_ramSum hs y.val
  rw [ZMod.natCast_zmod_val, hram, Int.cast_zero] at e
  exact (mul_eq_zero.mp e).resolve_left hN

/-- **4c.** そのとき E_s は ψ の掛け算と可換。 -/
theorem convL_geps_commute_charP {N s p : ℕ} [NeZero N] (hs : s ∣ N) (hp : p.Prime) (hpN : p ∣ N)
    (hpp : p * p ∣ N / s) :
    Commute (PAG.Part15.convL (geps N s)) (LinearMap.mulLeft ℂ (charP N p)) := by
  show PAG.Part15.convL (geps N s) * LinearMap.mulLeft ℂ (charP N p) =
    LinearMap.mulLeft ℂ (charP N p) * PAG.Part15.convL (geps N s)
  apply LinearMap.ext
  intro f
  funext x
  show ∑ y, geps N s y * (charP N p * f) (x - y) = charP N p x * ∑ y, geps N s y * f (x - y)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : p ∣ y.val
  · have h0 := mul_div_eq_zero_of_dvd hpN hy
    simp only [Pi.mul_apply, charP]
    rw [sub_mul, h0, sub_zero]
    ring
  · rw [geps_eq_zero_of_not_dvd_val hs hp hpp hy]
    ring

/-- **4d.** ⟨D_u, E_s⟩ の元は ψ の掛け算と可換。 -/
theorem oneEAlg_le_centralizer {N s p : ℕ} [NeZero N] (hs : s ∣ N) (hp : p.Prime) (hpN : p ∣ N)
    (hpp : p * p ∣ N / s) :
    oneEAlg N s ≤ Subalgebra.centralizer ℂ {LinearMap.mulLeft ℂ (charP N p)} := by
  apply Algebra.adjoin_le
  rintro X (⟨u, rfl⟩ | hX)
  · refine (Subalgebra.mem_centralizer_iff ℂ).mpr ?_
    rintro g rfl
    apply LinearMap.ext
    intro f
    show charP N p * (dind N u * f) = dind N u * (charP N p * f)
    ring
  · rw [Set.mem_singleton_iff] at hX
    rw [hX]
    refine (Subalgebra.mem_centralizer_iff ℂ).mpr ?_
    rintro g rfl
    exact (convL_geps_commute_charP hs hp hpN hpp).eq.symm

/-- **4e.** E_N は ψ の掛け算と可換でない（p ∣ N、p は素数）。 -/
theorem convL_geps_self_not_commute_charP {N p : ℕ} [NeZero N] (hp : p.Prime) (hpN : p ∣ N) :
    ¬ Commute (PAG.Part15.convL (geps N N)) (LinearMap.mulLeft ℂ (charP N p)) := by
  intro h
  have hψδ : charP N p * Pi.single (0 : ZMod N) (1 : ℂ) = Pi.single (0 : ZMod N) (1 : ℂ) := by
    funext y
    rw [Pi.mul_apply]
    by_cases hy : y = 0
    · subst hy
      simp [charP]
    · rw [Pi.single_eq_of_ne hy, mul_zero]
  have hsum : ∑ z : ZMod N, (Pi.single (0 : ZMod N) (1 : ℂ) : ZMod N → ℂ) z = 1 := by simp
  have e := congrArg (fun T : Module.End ℂ (ZMod N → ℂ) => T (Pi.single (0 : ZMod N) (1 : ℂ)) 1) h.eq
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply] at e
  rw [hψδ, convL_geps_self_apply, Pi.mul_apply, convL_geps_self_apply, hsum] at e
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : charP N p 1 = 1 := by
    have h' : (1 : ℂ) / N ≠ 0 := div_ne_zero one_ne_zero hN
    exact mul_right_cancel₀ h' (by rw [one_mul]; exact e.symm)
  have h2 : ((N / p : ℕ) : ZMod N) = 0 := by
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_zero_eq_one]
    simpa [charP] using h1
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpN) hp.pos
  have hlt : N / p < N := Nat.div_lt_self (Nat.pos_of_ne_zero (NeZero.ne N)) hp.one_lt
  exact absurd (Nat.le_of_dvd hpos h2) (not_le.mpr hlt)

/-- **4f.** N/s が平方因子をもてば E_N ∉ ⟨D_u, E_s⟩（s ∣ N）。 -/
theorem convL_geps_self_not_mem_oneEAlg {N s : ℕ} [NeZero N] (hs : s ∣ N) (hsq : ¬ Squarefree (N / s)) :
    PAG.Part15.convL (geps N N) ∉ oneEAlg N s := by
  rw [Nat.squarefree_iff_prime_squarefree] at hsq
  push Not at hsq
  obtain ⟨p, hp, hpp⟩ := hsq
  have hpN : p ∣ N := dvd_trans (dvd_trans (dvd_mul_right p p) hpp) (Nat.div_dvd_of_dvd hs)
  intro hmem
  have hc := oneEAlg_le_centralizer hs hp hpN hpp hmem
  rw [Subalgebra.mem_centralizer_iff] at hc
  exact convL_geps_self_not_commute_charP hp hpN (hc _ (Set.mem_singleton _)).symm

/-- **4g.** そのとき ⟨D_u, E_s⟩ ≠ A_N。 -/
theorem oneEAlg_ne_shellAlg {N s : ℕ} [NeZero N] (hs : s ∣ N) (hsq : ¬ Squarefree (N / s)) :
    oneEAlg N s ≠ shellAlg N := by
  intro h
  apply convL_geps_self_not_mem_oneEAlg hs hsq
  rw [h]
  exact PAG.Part232.convL_geps_mem N N

/-- **4h.** ⟨D_u, E_1⟩ = A_N ⇔ N は平方因子なし。 -/
theorem oneEAlg_one_eq_shellAlg_iff (N : ℕ) [NeZero N] : oneEAlg N 1 = shellAlg N ↔ Squarefree N := by
  constructor
  · intro h
    by_contra hsq
    exact oneEAlg_ne_shellAlg (one_dvd N) (by rwa [Nat.div_one]) h
  · exact oneEAlg_one_eq_shellAlg

/-! ### 5. 単数の殻の上の証拠：p^{m+1} ∣ N、p^m ∤ s なら E_{p^m} ∉ B_s -/

/-- 証拠の関数 f = Σ_{c < p^m} (δ_{1+cM} − δ_{−(1+cM)})（M = N/p^m）。 -/
noncomputable def unitWit (N p m : ℕ) : ZMod N → ℂ :=
  ∑ c ∈ Finset.range (p ^ m), pairFn N (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N))

/-- **5a.** P f = 0。 -/
theorem shellAvg_unitWit (N p m : ℕ) [NeZero N] : shellAvg N (unitWit N p m) = 0 := by
  rw [unitWit, map_sum]
  exact Finset.sum_eq_zero (fun c _ => shellAvg_pairFn N _)

/-- **5b.** 単数 a では 1_{D_1}(a) = 1。 -/
theorem dind_one_of_isUnit {N : ℕ} [NeZero N] {a : ZMod N} (ha : IsUnit a) : dind N 1 a = 1 := by
  have h1 : dind N 1 (1 : ZMod N) = 1 := by
    have := dind_self N 1 (one_dvd N)
    rwa [Nat.cast_one] at this
  have hr := dind_radial N 1 ha.unit 1
  rw [IsUnit.unit_spec, mul_one] at hr
  rw [hr, h1]

/-- **5c.** 単数 a では 1_{D_1}·(δ_a − δ_{−a}) = δ_a − δ_{−a}。 -/
theorem dind_one_mul_pairFn {N : ℕ} [NeZero N] {a : ZMod N} (ha : IsUnit a) :
    dind N 1 * pairFn N a = pairFn N a := by
  have key : ∀ b : ZMod N, IsUnit b →
      dind N 1 * (Pi.single b (1 : ℂ) : ZMod N → ℂ) = (Pi.single b (1 : ℂ) : ZMod N → ℂ) := by
    intro b hb
    funext y
    rw [Pi.mul_apply]
    by_cases hy : y = b
    · subst hy
      rw [dind_one_of_isUnit hb, one_mul]
    · rw [Pi.single_eq_of_ne hy, mul_zero]
  rw [pairFn, mul_sub, key a ha, key (-a) ha.neg]

/-- **5d.** 𝓕(δ_a − δ_{−a})(k) = e(−ak) − e(ak)。 -/
theorem dft_pairFn {N : ℕ} [NeZero N] (a k : ZMod N) :
    𝓕 (pairFn N a) k = stdAddChar (-(a * k)) - stdAddChar (a * k) := by
  rw [pairFn, map_sub, Pi.sub_apply, dft_single, dft_single, neg_mul, neg_neg]

/-- **5e.** ζ ≠ 1、ζ^n = 1 なら Σ_{c < n} ζ^c = 0。 -/
theorem geom_sum_eq_zero_of_pow {ζ : ℂ} {n : ℕ} (h1 : ζ ≠ 1) (hn : ζ ^ n = 1) :
    ∑ c ∈ Finset.range n, ζ ^ c = 0 := by
  have h := geom_sum_mul ζ n
  rw [hn, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)

/-- **5f.** p 素数、p^{m+1} ∣ N なら、N のどの素因数も N/p^m を割る。 -/
theorem prime_dvd_div_of_dvd {N p m ℓ : ℕ} (hp : p.Prime) (hpm : p ^ (m + 1) ∣ N) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) :
    ℓ ∣ N / p ^ m := by
  have hpmN : p ^ m ∣ N := dvd_trans (pow_dvd_pow p (Nat.le_succ m)) hpm
  by_cases hℓp : ℓ = p
  · rw [hℓp]
    apply Nat.dvd_div_of_mul_dvd
    rw [← pow_succ]
    exact hpm
  · have hN : N = p ^ m * (N / p ^ m) := (Nat.mul_div_cancel' hpmN).symm
    rw [hN] at hℓN
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓN with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h)) hℓp
    · exact h

/-- **5g.** 1 + c·(N/p^m) は単数（p^{m+1} ∣ N）。 -/
theorem isUnit_one_add_mul {N p m : ℕ} [NeZero N] (hp : p.Prime) (hpm : p ^ (m + 1) ∣ N) (c : ℕ) :
    IsUnit (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N)) := by
  have e : (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N)) = ((1 + c * (N / p ^ m) : ℕ) : ZMod N) := by
    push_cast
    ring
  rw [e, ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro ℓ hℓ h1 hN
  have h2 : ℓ ∣ c * (N / p ^ m) := dvd_mul_of_dvd_right (prime_dvd_div_of_dvd hp hpm hℓ hN) c
  have h3 : ℓ ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [add_comm] at h1)
  exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)

/-- **5h.** f は単数の殻に載る：1_{D_1}·f = f。 -/
theorem dind_one_mul_unitWit {N p m : ℕ} [NeZero N] (hp : p.Prime) (hpm : p ^ (m + 1) ∣ N) :
    dind N 1 * unitWit N p m = unitWit N p m := by
  rw [unitWit, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => dind_one_mul_pairFn (isUnit_one_add_mul hp hpm c))

/-- **5i.** M·k = 0（M = N/p^m）なら p^m ∣ k.val。 -/
theorem dvd_val_of_mul_eq_zero {N p m : ℕ} [NeZero N] (hp : p.Prime) (hpm : p ^ m ∣ N) {k : ZMod N}
    (hk : ((N / p ^ m : ℕ) : ZMod N) * k = 0) : p ^ m ∣ k.val := by
  have e : ((N / p ^ m : ℕ) : ZMod N) * k = ((N / p ^ m * k.val : ℕ) : ZMod N) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [e, ZMod.natCast_eq_zero_iff] at hk
  have hM : 0 < N / p ^ m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hpm) (pow_pos hp.pos m)
  have h2 : p ^ m * (N / p ^ m) ∣ k.val * (N / p ^ m) := by
    rw [Nat.mul_div_cancel' hpm, mul_comm]
    exact hk
  exact Nat.dvd_of_mul_dvd_mul_right hM h2

/-- **5j.** M·k = 0 なら 𝓕f(k) = p^m·(e(−k) − e(k))。 -/
theorem dft_unitWit_of_mul_eq_zero {N p m : ℕ} [NeZero N] {k : ZMod N}
    (hk : ((N / p ^ m : ℕ) : ZMod N) * k = 0) :
    𝓕 (unitWit N p m) k = (p : ℂ) ^ m * (stdAddChar (-k) - stdAddChar k) := by
  rw [unitWit, map_sum, Finset.sum_apply]
  have h : ∀ c ∈ Finset.range (p ^ m), 𝓕 (pairFn N (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N))) k =
      stdAddChar (-k) - stdAddChar k := by
    intro c _
    rw [dft_pairFn]
    have e : (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N)) * k = k := by
      rw [add_mul, one_mul, mul_assoc, hk, mul_zero, add_zero]
    rw [e]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- **5k.** M·k ≠ 0 なら 𝓕f(k) = 0（ζ = e(Mk) は 1 でない p^m 乗根で、等比数列の和が 0）。 -/
theorem dft_unitWit_of_mul_ne_zero {N p m : ℕ} [NeZero N] (hpm : p ^ m ∣ N) {k : ZMod N}
    (hk : ((N / p ^ m : ℕ) : ZMod N) * k ≠ 0) : 𝓕 (unitWit N p m) k = 0 := by
  rw [unitWit, map_sum, Finset.sum_apply]
  simp only [dft_pairFn]
  have hterm : ∀ c : ℕ, (1 + (c : ZMod N) * ((N / p ^ m : ℕ) : ZMod N)) * k =
      k + c • (((N / p ^ m : ℕ) : ZMod N) * k) := by
    intro c
    rw [nsmul_eq_mul]
    ring
  simp only [hterm]
  have hζ : ∀ v : ZMod N, v ≠ 0 → (p ^ m : ℕ) • v = 0 → ∑ c ∈ Finset.range (p ^ m), stdAddChar v ^ c = 0 := by
    intro v hv hpv
    apply geom_sum_eq_zero_of_pow
    · intro h
      apply hv
      apply ZMod.injective_stdAddChar
      rw [h, AddChar.map_zero_eq_one]
    · rw [← AddChar.map_nsmul_eq_pow, hpv, AddChar.map_zero_eq_one]
  have hpw : (p ^ m : ℕ) • (((N / p ^ m : ℕ) : ZMod N) * k) = 0 := by
    rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hpm, ZMod.natCast_self, zero_mul]
  have hpw' : (p ^ m : ℕ) • (-(((N / p ^ m : ℕ) : ZMod N) * k)) = 0 := by
    rw [smul_neg, hpw, neg_zero]
  have hw0 : -(((N / p ^ m : ℕ) : ZMod N) * k) ≠ 0 := neg_ne_zero.mpr hk
  have e1 : ∀ c : ℕ, stdAddChar (-(k + c • (((N / p ^ m : ℕ) : ZMod N) * k))) =
      stdAddChar (-k) * stdAddChar (-(((N / p ^ m : ℕ) : ZMod N) * k)) ^ c := by
    intro c
    rw [neg_add, ← smul_neg, AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  have e2 : ∀ c : ℕ, stdAddChar (k + c • (((N / p ^ m : ℕ) : ZMod N) * k)) =
      stdAddChar k * stdAddChar (((N / p ^ m : ℕ) : ZMod N) * k) ^ c := by
    intro c
    rw [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  simp only [e1, e2]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hζ _ hw0 hpw', hζ _ hk hpw, mul_zero, mul_zero,
    sub_zero]

/-- **5l.** p^m ∤ s なら E_s f = 0（𝓕f は p^m の倍数の上にしかなく、そこでは 1_{D_s} = 0）。 -/
theorem convL_geps_unitWit {N s p m : ℕ} [NeZero N] (hp : p.Prime) (hpm : p ^ m ∣ N) (hps : ¬ p ^ m ∣ s) :
    PAG.Part15.convL (geps N s) (unitWit N p m) = 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [map_zero, PAG.Part15.convL_apply, dft_conv_geps]
  funext k
  rw [Pi.mul_apply, Pi.zero_apply]
  by_cases hk : ((N / p ^ m : ℕ) : ZMod N) * k = 0
  · have hd := dvd_val_of_mul_eq_zero hp hpm hk
    have hds : dind N s k = 0 := by
      have hg : Nat.gcd N k.val ≠ s := by
        intro hg
        have h2 := Nat.dvd_gcd hpm hd
        rw [hg] at h2
        exact hps h2
      exact ite_eq_right hg
    rw [hds, zero_mul]
  · rw [dft_unitWit_of_mul_ne_zero hpm hk, mul_zero]

/-- **5m.** 主定理：p 素数、p^{m+1} ∣ N、p^m ∤ s、N ∤ 2p^{m+1}（または N = 2p^{m+1} で p ≠ 2）なら E_{p^m} ∉ B_s。
f は U_s^⊥ に入り単数の殻に載るので、E_{p^m} ∈ B_s なら E_{p^m} f = c·f。𝓕f は p^m の倍数の上で p^m(e(−k) − e(k))。
k = p^m（D_{p^m} の中）で c = 1、k = p^{m+1}（または 2p^m、D_{p^m} の外）で 𝓕f(k) = 0 となり矛盾。 -/
theorem convL_geps_primePow_not_mem_addEAlg {N s p m : ℕ} [NeZero N] (hp : p.Prime) (hpm : p ^ (m + 1) ∣ N)
    (hps : ¬ p ^ m ∣ s) (hN : ¬ N ∣ 2 * p ^ (m + 1) ∨ (N = 2 * p ^ (m + 1) ∧ p ≠ 2)) :
    PAG.Part15.convL (geps N (p ^ m)) ∉ addEAlg N s := by
  intro hX
  have hpmN : p ^ m ∣ N := dvd_trans (pow_dvd_pow p (Nat.le_succ m)) hpm
  have hP := shellAvg_unitWit N p m
  have hsupp := dind_one_mul_unitWit hp hpm
  have hE0 := convL_geps_unitWit (s := s) hp hpmN hps
  have hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * unitWit N p m) = 0 := by
    intro u
    have e : dind N u * unitWit N p m = if u = 1 then unitWit N p m else 0 := by
      conv_lhs => rw [← hsupp]
      rw [← mul_assoc, dind_mul]
      split_ifs with h
      · rw [h, hsupp]
      · rw [zero_mul]
    rw [e]
    split_ifs
    · exact hE0
    · exact map_zero _
  obtain ⟨c, hc⟩ := exists_apply_eq_smul_of_mem_addEAlg hX hP hE hsupp
  rw [PAG.Part15.convL_apply] at hc
  have hF : dind N (p ^ m) * 𝓕 (unitWit N p m) = c • 𝓕 (unitWit N p m) := by
    rw [← dft_conv_geps, hc, map_smul]
  have hval : ∀ k : ZMod N, k + k ≠ 0 → stdAddChar (-k) - stdAddChar k ≠ 0 := by
    intro k hk h
    apply hk
    have h2 := ZMod.injective_stdAddChar (sub_eq_zero.mp h)
    linear_combination -h2
  have hp0 : (p : ℂ) ^ m ≠ 0 := pow_ne_zero m (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hcast : ∀ a : ℕ, ((a : ℕ) : ZMod N) + (a : ZMod N) = ((2 * a : ℕ) : ZMod N) := by
    intro a
    push_cast
    ring
  have hN2 : ¬ N ∣ 2 * p ^ m := by
    intro h
    have h1 : p ^ m * p ∣ p ^ m * 2 := by
      rw [← pow_succ, mul_comm (p ^ m) 2]
      exact dvd_trans hpm h
    have h2 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos m) h1
    have h3 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    rcases hN with hN | ⟨_, hN⟩
    · exact hN (dvd_trans h (mul_dvd_mul_left 2 (pow_dvd_pow p (Nat.le_succ m))))
    · exact hN h3
  have hk1 : ((N / p ^ m : ℕ) : ZMod N) * ((p ^ m : ℕ) : ZMod N) = 0 := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hpmN, ZMod.natCast_self]
  have hF1 := congrFun hF ((p ^ m : ℕ) : ZMod N)
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, dft_unitWit_of_mul_eq_zero hk1, dind_self N (p ^ m) hpmN,
    one_mul] at hF1
  have hne1 : (p : ℂ) ^ m * (stdAddChar (-((p ^ m : ℕ) : ZMod N)) - stdAddChar ((p ^ m : ℕ) : ZMod N)) ≠ 0 := by
    refine mul_ne_zero hp0 (hval _ ?_)
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
    exact hN2
  have hc1 : c = 1 := mul_right_cancel₀ hne1 (by rw [one_mul]; exact hF1.symm)
  rcases hN with hN | ⟨hNeq, hp2⟩
  · have hk2 : ((N / p ^ m : ℕ) : ZMod N) * ((p ^ (m + 1) : ℕ) : ZMod N) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, pow_succ, ← mul_assoc, Nat.div_mul_cancel hpmN]
      exact Dvd.intro p rfl
    have hF2 := congrFun hF ((p ^ (m + 1) : ℕ) : ZMod N)
    rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, dft_unitWit_of_mul_eq_zero hk2, hc1, one_mul] at hF2
    have hd2 : dind N (p ^ m) ((p ^ (m + 1) : ℕ) : ZMod N) = 0 := by
      have hg : Nat.gcd N ((p ^ (m + 1) : ℕ) : ZMod N).val ≠ p ^ m := by
        rw [gcd_natCast_self N _ hpm]
        intro h
        have h3 := Nat.pow_right_injective hp.two_le h
        omega
      exact ite_eq_right hg
    rw [hd2, zero_mul] at hF2
    refine mul_ne_zero hp0 (hval _ ?_) hF2.symm
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff]
    exact hN
  · have h2pm : 2 * p ^ m ∣ N := by
      rw [hNeq, pow_succ]
      exact Dvd.intro p (by ring)
    have hk2 : ((N / p ^ m : ℕ) : ZMod N) * ((2 * p ^ m : ℕ) : ZMod N) = 0 := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, mul_left_comm, Nat.div_mul_cancel hpmN]
      exact dvd_mul_left N 2
    have hF2 := congrFun hF ((2 * p ^ m : ℕ) : ZMod N)
    rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, dft_unitWit_of_mul_eq_zero hk2, hc1, one_mul] at hF2
    have hd2 : dind N (p ^ m) ((2 * p ^ m : ℕ) : ZMod N) = 0 := by
      have hg : Nat.gcd N ((2 * p ^ m : ℕ) : ZMod N).val ≠ p ^ m := by
        rw [gcd_natCast_self N _ h2pm]
        have h3 := pow_pos hp.pos m
        omega
      exact ite_eq_right hg
    rw [hd2, zero_mul] at hF2
    refine mul_ne_zero hp0 (hval _ ?_) hF2.symm
    rw [hcast, Ne, ZMod.natCast_eq_zero_iff, hNeq]
    intro h
    have h1 : p ^ m * (2 * p) ∣ p ^ m * (2 * 2) := by
      have e1 : 2 * p ^ (m + 1) = p ^ m * (2 * p) := by ring
      have e2 : 2 * (2 * p ^ m) = p ^ m * (2 * 2) := by ring
      rw [← e1, ← e2]
      exact h
    have h2 : 2 * p ∣ 2 * 2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos m) h1
    have h3 : p ∣ 2 := Nat.dvd_of_mul_dvd_mul_left two_pos h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

/-- **5n.** m = 1：p² ∣ N、p ∤ s、N ≠ p²、N ≠ 8 なら E_p ∉ B_s。 -/
theorem convL_geps_prime_not_mem_addEAlg {N s p : ℕ} [NeZero N] (hp : p.Prime) (hpp : p * p ∣ N)
    (hps : ¬ p ∣ s) (hN1 : N ≠ p * p) (hN8 : N ≠ 8) : PAG.Part15.convL (geps N p) ∉ addEAlg N s := by
  have hpm : p ^ (1 + 1) ∣ N := by
    rw [show p ^ (1 + 1) = p * p by ring]
    exact hpp
  have hps' : ¬ p ^ 1 ∣ s := by
    rw [pow_one]
    exact hps
  have hN : ¬ N ∣ 2 * p ^ (1 + 1) ∨ (N = 2 * p ^ (1 + 1) ∧ p ≠ 2) := by
    by_cases hdiv : N ∣ 2 * p ^ (1 + 1)
    · right
      obtain ⟨d, hd⟩ := hpp
      have h1 : p * p * d ∣ p * p * 2 := by
        rw [← hd, show p * p * 2 = 2 * p ^ (1 + 1) by ring]
        exact hdiv
      have h2 : d ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (Nat.mul_pos hp.pos hp.pos) h1
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
      · exfalso
        apply hN1
        rw [hd, h3, mul_one]
      · refine ⟨by rw [hd, h3]; ring, ?_⟩
        rintro rfl
        apply hN8
        rw [hd, h3]
    · left
      exact hdiv
  have h := convL_geps_primePow_not_mem_addEAlg hp hpm hps' hN
  rwa [pow_one] at h

/-- **5o.** 同じ仮定で B_s ≠ A_N。 -/
theorem addEAlg_ne_shellAlg_of_sq {N s p : ℕ} [NeZero N] (hp : p.Prime) (hpp : p * p ∣ N) (hps : ¬ p ∣ s)
    (hN1 : N ≠ p * p) (hN8 : N ≠ 8) : addEAlg N s ≠ shellAlg N := by
  intro h
  apply convL_geps_prime_not_mem_addEAlg hp hpp hps hN1 hN8
  rw [h]
  exact PAG.Part232.convL_geps_mem N p

/-! ### 6. 素冪 N = p^k、s = p^j（2 ≤ j < k）：E_1 ∉ B_s（Part 246 の 2 点の証拠を q = p、m = N/s で） -/

/-- **6a.** N = p^k、s = p^j、2 ≤ j < k なら E_1 ∉ B_s。 -/
theorem convL_geps_one_not_mem_addEAlg_primePow {N s p k j : ℕ} [NeZero N] (hp : p.Prime) (hN : N = p ^ k)
    (hs : s = p ^ j) (hj : 2 ≤ j) (hjk : j < k) : PAG.Part15.convL (geps N 1) ∉ addEAlg N s := by
  have hsN : s ∣ N := by
    rw [hs, hN]
    exact pow_dvd_pow p hjk.le
  have hdiv : N / s = p ^ (k - j) := by
    rw [hs, hN]
    exact Nat.pow_div hjk.le hp.pos
  have hpN : p ∣ N := by
    rw [hN]
    exact dvd_pow_self p (by omega)
  apply convL_geps_one_not_mem_addEAlg_of_witness (m := N / s) (q := p) hsN dvd_rfl ?_ hpN hp.one_lt.ne' ?_ ?_
  · have e : (1 + ((N / s : ℕ) : ZMod N)) = ((1 + N / s : ℕ) : ZMod N) := by
      push_cast
      ring
    rw [e, ZMod.isUnit_iff_coprime, hdiv, hN]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ p ^ (k - j) := dvd_pow_self p (by omega)
    have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [add_comm] at h)
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  · rw [Ne, ZMod.natCast_eq_zero_iff, hdiv, hN]
    intro h
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h
    omega
  · rw [Ne, ZMod.natCast_eq_zero_iff, hdiv, hN, ← pow_succ]
    intro h
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h
    omega

/-! ### 7. 分類 -/

/-- **7a.** |S′(p²)| ≤ 2。 -/
theorem card_devSet_sq_le {p : ℕ} (hp : p.Prime) : (devSet (p * p)).card ≤ 2 := by
  have : NeZero (p * p) := ⟨(Nat.mul_pos hp.pos hp.pos).ne'⟩
  rw [card_devSet_le_two_iff, show p * p = p ^ 2 by ring, card_divisors_primePow hp 2]
  split_ifs <;> omega

/-- **7b.** |S′(8)| ≤ 2。 -/
theorem card_devSet_eight_le : (devSet 8).card ≤ 2 := by
  rw [card_devSet_le_two_iff]
  decide

/-- **7c.** B_1 = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²（p は素数）。 -/
theorem addEAlg_one_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    addEAlg N 1 = shellAlg N ↔ Squarefree N ∨ N = 8 ∨ ∃ p, p.Prime ∧ N = p * p := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hsq, hN8, hNp⟩ := hcon
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpp⟩ := hsq
    exact addEAlg_ne_shellAlg_of_sq hp hpp (fun h1 => hp.one_lt.ne' (Nat.dvd_one.mp h1)) (hNp p hp) hN8 h
  · rintro (hsq | h8 | ⟨p, hp, rfl⟩)
    · exact addEAlg_one_eq_shellAlg hsq
    · subst h8
      exact addEAlg_eq_shellAlg_of_card_le_two card_devSet_eight_le (one_mem_devSet (by norm_num))
    · exact addEAlg_eq_shellAlg_of_card_le_two (card_devSet_sq_le hp)
        (one_mem_devSet (by nlinarith [hp.two_le]))

/-- **7d.** 主定理：s ∈ S′ で、(N, s) が (p³, p)（p は奇素数）・(16, 2) でなければ
B_s = A_N ⇔ |S′| ≤ 2 ∨ (N が平方因子なし ∧ (s = 1 ∨ s = 2))。 -/
theorem addEAlg_eq_shellAlg_iff {N s : ℕ} [NeZero N] (hs : s ∈ devSet N)
    (hex : ¬ ((∃ p, p.Prime ∧ p ≠ 2 ∧ N = p ^ 3 ∧ s = p) ∨ (N = 16 ∧ s = 2))) :
    addEAlg N s = shellAlg N ↔ (devSet N).card ≤ 2 ∨ (Squarefree N ∧ (s = 1 ∨ s = 2)) := by
  have hsN : s ∣ N := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hs).1
  have hφ : Nat.totient (N / s) ≠ 1 := (Finset.mem_filter.mp hs).2
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    obtain ⟨hcard, hsq12⟩ := hcon
    by_cases hsq : Squarefree N
    · obtain ⟨h1, h2⟩ := hsq12 hsq
      exact addEAlg_ne_shellAlg_of_squarefree hsq hs h1 h2 h
    · rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨p, hp, hpp⟩ := hsq
      have hN1 : N ≠ p * p := by
        rintro rfl
        exact absurd (card_devSet_sq_le hp) (not_le.mpr hcard)
      have hN8 : N ≠ 8 := by
        rintro rfl
        exact absurd card_devSet_eight_le (not_le.mpr hcard)
      by_cases hps : p ∣ s
      · by_cases hq : ∃ q, q.Prime ∧ q ∣ N ∧ q ≠ p
        · obtain ⟨q, hq, hqN, hqp⟩ := hq
          have hr2 : p ≠ 2 ∨ 4 ∣ N := by
            by_cases hp2 : p = 2
            · right
              rw [hp2] at hpp
              norm_num at hpp
              exact hpp
            · left
              exact hp2
          exact addEAlg_ne_shellAlg hsN hp hps hr2 hq hqN hqp h
        · push Not at hq
          have hNk : N = p ^ N.primeFactorsList.length :=
            Nat.eq_prime_pow_of_unique_prime_dvd (NeZero.ne N) (fun hd hdvd => hq _ hd hdvd)
          generalize N.primeFactorsList.length = k at hNk
          have hsN' : s ∣ p ^ k := by
            rw [← hNk]
            exact hsN
          obtain ⟨j, hjk, hsj⟩ := (Nat.dvd_prime_pow hp).mp hsN'
          have hj1 : 1 ≤ j := by
            rcases Nat.eq_zero_or_pos j with h0 | h0
            · rw [h0, pow_zero] at hsj
              rw [hsj] at hps
              exact absurd (Nat.dvd_one.mp hps) hp.one_lt.ne'
            · exact h0
          have hjk' : j < k := by
            rcases lt_or_eq_of_le hjk with h' | h'
            · exact h'
            · exfalso
              apply hφ
              rw [hsj, h', ← hNk, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N)), Nat.totient_one]
          by_cases hj2 : 2 ≤ j
          · exact convL_geps_one_not_mem_addEAlg_primePow hp hNk hsj hj2 hjk'
              (by rw [h]; exact PAG.Part232.convL_geps_mem N 1)
          · have hj : j = 1 := by omega
            rw [hj, pow_one] at hsj
            have hk2 : 2 ≤ k := by
              have h2 : p ^ 2 ∣ p ^ k := by
                rw [← hNk, show p ^ 2 = p * p by ring]
                exact hpp
              exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
            have hk3 : 3 ≤ k := by
              by_contra hk
              have hk' : k = 2 := by omega
              apply hN1
              rw [hNk, hk']
              ring
            have hpm : p ^ (2 + 1) ∣ N := by
              rw [hNk]
              exact pow_dvd_pow p hk3
            have hps2 : ¬ p ^ 2 ∣ s := by
              rw [hsj]
              intro h2
              have h3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (by rw [pow_one]; exact h2 : p ^ 2 ∣ p ^ 1)
              omega
            have hNd : ¬ N ∣ 2 * p ^ (2 + 1) ∨ (N = 2 * p ^ (2 + 1) ∧ p ≠ 2) := by
              left
              intro hdiv
              by_cases hp2 : p = 2
              · rw [hp2] at hNk hsj
                have h2 : 2 ^ k ∣ 2 ^ 4 := by
                  rw [← hNk]
                  rw [hp2] at hdiv
                  norm_num at hdiv ⊢
                  exact hdiv
                have hk4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
                have hk' : k = 3 ∨ k = 4 := by omega
                rcases hk' with hk' | hk'
                · apply hN8
                  rw [hNk, hk']
                  norm_num
                · apply hex
                  right
                  refine ⟨by rw [hNk, hk']; norm_num, hsj⟩
              · have hcop : Nat.Coprime (p ^ k) 2 := by
                  apply Nat.Coprime.pow_left
                  rw [Nat.Prime.coprime_iff_not_dvd hp]
                  intro h2
                  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
                have h2 : p ^ k ∣ p ^ (2 + 1) := by
                  rw [← hNk] at hcop ⊢
                  exact hcop.dvd_of_dvd_mul_left hdiv
                have hk' := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
                apply hex
                left
                refine ⟨p, hp, hp2, ?_, hsj⟩
                rw [hNk]
                congr 1
                omega
            exact convL_geps_primePow_not_mem_addEAlg hp hpm hps2 hNd
              (by rw [h]; exact PAG.Part232.convL_geps_mem N (p ^ 2))
      · exact addEAlg_ne_shellAlg_of_sq hp hpp hps hN1 hN8 h
  · rintro (hcard | ⟨hsq, rfl | rfl⟩)
    · exact addEAlg_eq_shellAlg_of_card_le_two hcard hs
    · exact addEAlg_one_eq_shellAlg hsq
    · exact addEAlg_two_eq_shellAlg hsq hsN

/-! ### 8. フーリエ双対 -/

/-- E_u（u ∈ ℕ）と D_s が生成する部分代数 ⟨E_u, D_s⟩（⟨D_u, E_s⟩ のフーリエ双対）。 -/
noncomputable def dualOneEAlgOf (N s : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : ℕ => PAG.Part15.convL (geps N u)) ∪ {LinearMap.mulLeft ℂ (dind N s)})

/-- **8a.** 𝓕⟨D_u, E_s⟩𝓕⁻¹ = ⟨E_u, D_s⟩。 -/
theorem map_fourierConj_oneEAlg_of (N s : ℕ) [NeZero N] :
    (oneEAlg N s).map (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) =
      dualOneEAlgOf N s := by
  rw [oneEAlg, dualOneEAlgOf, AlgHom.map_adjoin, Set.image_union, Set.image_singleton, ← Set.range_comp]
  have h1 : (⇑(fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ∘
      fun u : ℕ => LinearMap.mulLeft ℂ (dind N u)) = fun u => PAG.Part15.convL (geps N u) := by
    funext u
    exact fourierConj_mulLeft_dind N u
  have h2 : (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ))
      (PAG.Part15.convL (geps N s)) = LinearMap.mulLeft ℂ (dind N s) := fourierConj_convL_geps N s
  rw [h1, h2]

/-- **8b.** ⟨E_u, D_s⟩ = A_N ⇔ ⟨D_u, E_s⟩ = A_N。 -/
theorem dualOneEAlgOf_eq_shellAlg_iff (N s : ℕ) [NeZero N] :
    dualOneEAlgOf N s = shellAlg N ↔ oneEAlg N s = shellAlg N := by
  rw [← map_fourierConj_oneEAlg_of]
  conv_lhs => rw [← map_fourierConj_shellAlg]
  exact (Subalgebra.map_injective
    (f := (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)))
    (fourierConj N).injective).eq_iff

/-- **8c.** ⟨E_u, D_1⟩ = A_N ⇔ N は平方因子なし。 -/
theorem dualOneEAlgOf_one_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    dualOneEAlgOf N 1 = shellAlg N ↔ Squarefree N := by
  rw [dualOneEAlgOf_eq_shellAlg_iff, oneEAlg_one_eq_shellAlg_iff]

/-- **8d.** ⟨E_u, D_N, D_1⟩ = A_N ⇔ N は平方因子なし ∨ N = 8 ∨ N = p²（p は素数）。 -/
theorem dualAddEAlg_one_eq_shellAlg_iff (N : ℕ) [NeZero N] :
    dualAddEAlg N 1 = shellAlg N ↔ Squarefree N ∨ N = 8 ∨ ∃ p, p.Prime ∧ N = p * p := by
  rw [dualAddEAlg_eq_shellAlg_iff, addEAlg_one_eq_shellAlg_iff]

end PAG.Part251

#print axioms PAG.Part251.geps_self_apply
#print axioms PAG.Part251.convL_geps_self_apply
#print axioms PAG.Part251.dind_self_apply
#print axioms PAG.Part251.mulLeft_dind_mul_self
#print axioms PAG.Part251.convL_geps_mul_self
#print axioms PAG.Part251.convL_geps_self_mul_mulLeft_dind_self
#print axioms PAG.Part251.convL_geps_one_add_self_of_prime
#print axioms PAG.Part251.level_identity
#print axioms PAG.Part251.two_level_identity
#print axioms PAG.Part251.leftOp_mul'
#print axioms PAG.Part251.leftOp_sub'
#print axioms PAG.Part251.leftOp_one'
#print axioms PAG.Part251.leftOp_smul'
#print axioms PAG.Part251.rightOp_mul'
#print axioms PAG.Part251.rightOp_one'
#print axioms PAG.Part251.rightOp_sum'
#print axioms PAG.Part251.sandwich
#print axioms PAG.Part251.crtConj_sum_dind
#print axioms PAG.Part251.convL_geps_prime_mul_aux
#print axioms PAG.Part251.convL_geps_prime_mul
#print axioms PAG.Part251.convL_geps_of_two_mul_aux
#print axioms PAG.Part251.convL_geps_of_two_mul
#print axioms PAG.Part251.convL_geps_mem_of_squarefree
#print axioms PAG.Part251.oneEAlg_one_eq_shellAlg
#print axioms PAG.Part251.oneEAlg_two_eq_shellAlg
#print axioms PAG.Part251.addEAlg_one_eq_shellAlg
#print axioms PAG.Part251.addEAlg_two_eq_shellAlg
#print axioms PAG.Part251.addEAlg_eq_shellAlg_iff_of_squarefree
#print axioms PAG.Part251.charP
#print axioms PAG.Part251.mul_div_eq_zero_of_dvd
#print axioms PAG.Part251.geps_eq_zero_of_not_dvd_val
#print axioms PAG.Part251.convL_geps_commute_charP
#print axioms PAG.Part251.oneEAlg_le_centralizer
#print axioms PAG.Part251.convL_geps_self_not_commute_charP
#print axioms PAG.Part251.convL_geps_self_not_mem_oneEAlg
#print axioms PAG.Part251.oneEAlg_ne_shellAlg
#print axioms PAG.Part251.oneEAlg_one_eq_shellAlg_iff
#print axioms PAG.Part251.unitWit
#print axioms PAG.Part251.shellAvg_unitWit
#print axioms PAG.Part251.dind_one_of_isUnit
#print axioms PAG.Part251.dind_one_mul_pairFn
#print axioms PAG.Part251.dft_pairFn
#print axioms PAG.Part251.geom_sum_eq_zero_of_pow
#print axioms PAG.Part251.prime_dvd_div_of_dvd
#print axioms PAG.Part251.isUnit_one_add_mul
#print axioms PAG.Part251.dind_one_mul_unitWit
#print axioms PAG.Part251.dvd_val_of_mul_eq_zero
#print axioms PAG.Part251.dft_unitWit_of_mul_eq_zero
#print axioms PAG.Part251.dft_unitWit_of_mul_ne_zero
#print axioms PAG.Part251.convL_geps_unitWit
#print axioms PAG.Part251.convL_geps_primePow_not_mem_addEAlg
#print axioms PAG.Part251.convL_geps_prime_not_mem_addEAlg
#print axioms PAG.Part251.addEAlg_ne_shellAlg_of_sq
#print axioms PAG.Part251.convL_geps_one_not_mem_addEAlg_primePow
#print axioms PAG.Part251.card_devSet_sq_le
#print axioms PAG.Part251.card_devSet_eight_le
#print axioms PAG.Part251.addEAlg_one_eq_shellAlg_iff
#print axioms PAG.Part251.addEAlg_eq_shellAlg_iff
#print axioms PAG.Part251.dualOneEAlgOf
#print axioms PAG.Part251.map_fourierConj_oneEAlg_of
#print axioms PAG.Part251.dualOneEAlgOf_eq_shellAlg_iff
#print axioms PAG.Part251.dualOneEAlgOf_one_eq_shellAlg_iff
#print axioms PAG.Part251.dualAddEAlg_one_eq_shellAlg_iff
