/-
  PAG 2.0 Part 243（2026-11-05）— どの E_s が ⟨D_u, E_N⟩ に入るか：s ≠ 1 では φ(N/s) = 1 のときだけ、E_1 は N ∈ {1, 4} ∪ 素数 のときだけ
  A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）、⟨D_u, E_N⟩（Part 240 の oneEAlg N N。Part 241 で ≅ M_{d(N)}(ℂ) × ℂ^{S′}）。
  1. ラマヌジャン和：c_q(n) = φ(q) ⇔ q ∣ n（q ≠ 0、ramSum_eq_totient_iff）
  2. 殻の平均が 0（P f = 0）の f には、⟨D_u, E_N⟩ の元 X は殻ごとのスカラーとして働く：X f = Σ_{t ∈ S′} b_t·1_{D_t}·f
     （exists_apply_of_mem_oneEAlg）。逆に A_N の元でこの形なら ⟨D_u, E_N⟩ に入る（mem_oneEAlg_iff）。
     とくに X は P f = 0 の f の零点を保つ（apply_eq_zero_of_mem_oneEAlg）
  3. 証拠：f = δ_1 − δ_{−1}（P f = 0）、z = 1 + N/s。s ≠ 1、φ(N/s) ≠ 1 なら f(z) = 0 なのに
     (E_s f)(z) = (φ(q) − c_q(2))/N ≠ 0（q = N/s ≥ 3）。よって E_s ∉ ⟨D_u, E_N⟩（convL_geps_not_mem_oneEAlg）
  4. s ∣ N、s ≠ 1 なら E_s ∈ ⟨D_u, E_N⟩ ⇔ φ(N/s) = 1 ⇔ s = N ∨ 2s = N（convL_geps_mem_oneEAlg_iff, _iff_eq）。
     フーリエ双対：D_s ∈ ⟨E_u, D_N⟩ ⇔ φ(N/s) = 1（mulLeft_dind_mem_dualOneEAlg_iff）
  5. E_1：N ∉ {1, 4} ∪ 素数、p = minFac(N)、N = p^k M（p ∤ M）とすると c_N(N/p) = −p^{k−1}φ(M)、
     c_N(N/p + 2) = c_{p^k}(N/p + 2)·c_M(2)。M = 1 では c_{p^k}(p^{k−1} + 2) = 0、M > 1 では
     |c_N(N/p + 2)| ≤ p^k − p^{k−1} < p^{k−1}φ(M)（ramSum_div_minFac_ne）。z = 1 + N/p で E_1 ∉ ⟨D_u, E_N⟩。
     E_1 ∈ ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数（convL_geps_one_mem_oneEAlg_iff）、まとめは convL_geps_mem_oneEAlg_iff_all、
     双対は D_1 ∈ ⟨E_u, D_N⟩ ⇔ 同じ条件（mulLeft_dind_one_mem_dualOneEAlg_iff）
-/
import PAG246

namespace PAG.Part247

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. ラマヌジャン和が φ(q) になる条件 -/

/-- **1a.** c_q(n) = φ(q) ⇔ q ∣ n（q ≠ 0）。 -/
theorem ramSum_eq_totient_iff {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    ramSum n q = (Nat.totient q : ℤ) ↔ q ∣ n := by
  constructor
  · intro h
    have e := ramSum_mul_totient n q
    rw [h, mul_comm (ArithmeticFunction.moebius (q / Nat.gcd q n) : ℤ)] at e
    have hφ : (Nat.totient q : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
    have e2 : (Nat.totient (q / Nat.gcd q n) : ℤ) = ArithmeticFunction.moebius (q / Nat.gcd q n) :=
      mul_left_cancel₀ hφ e
    have hpos : 0 < Nat.totient (q / Nat.gcd q n) := Nat.totient_pos.mpr (div_gcd_pos hq n)
    have hμ := (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := q / Nat.gcd q n))).2
    have hφ1 : Nat.totient (q / Nat.gcd q n) = 1 := by omega
    have hμ1 : ArithmeticFunction.moebius (q / Nat.gcd q n) = 1 := by
      rw [← e2, hφ1, Nat.cast_one]
    rw [Nat.totient_eq_one_iff] at hφ1
    rcases hφ1 with h1 | h2
    · have hg : Nat.gcd q n = q := (Nat.eq_of_dvd_of_div_eq_one (Nat.gcd_dvd_left q n) h1)
      rw [← hg]
      exact Nat.gcd_dvd_right q n
    · rw [h2, ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hμ1
      norm_num at hμ1
  · intro h
    exact ramSum_of_dvd h

/-! ### 2. ⟨D_u, E_N⟩ の元は、殻の平均が 0 の関数に殻ごとのスカラーとして働く -/

/-- **2a.** P f = 0 なら、各殻の上の f の和は 0（t ∣ N）。 -/
theorem sum_dind_mul_eq_zero {N t : ℕ} [NeZero N] (ht : t ∣ N) {f : ZMod N → ℂ} (hf : shellAvg N f = 0) :
    ∑ y, dind N t y * f y = 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have h := congrFun hf (t : ZMod N)
  rw [shellAvg_apply, gcd_natCast_self N t ht, Pi.zero_apply] at h
  have hφ : (Nat.totient (N / t) : ℂ) ≠ 0 := by
    have h0 : 0 < N / t := Nat.div_pos (Nat.le_of_dvd hN ht) (Nat.pos_of_dvd_of_pos ht hN)
    exact_mod_cast (Nat.totient_pos.mpr h0).ne'
  exact (div_eq_zero_iff.mp h).resolve_right hφ

/-- **2b.** P f = 0 なら Φ(M) f = 0。 -/
theorem radialMatOp_apply_eq_zero {N : ℕ} [NeZero N] (M : Matrix N.divisors N.divisors ℂ) {f : ZMod N → ℂ}
    (hf : shellAvg N f = 0) : radialMatOp N M f = 0 := by
  rw [radialMatOp, LinearMap.sum_apply]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [LinearMap.sum_apply]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [LinearMap.smul_apply, shellTrans_apply, sum_dind_mul_eq_zero (Nat.dvd_of_mem_divisors v.2) hf, zero_div,
    zero_smul, smul_zero]

/-- **2c.** P f = 0 なら Q_t f = 1_{D_t}·f（t ∣ N）。 -/
theorem shellDev_apply_of_shellAvg_eq_zero {N t : ℕ} [NeZero N] (ht : t ∣ N) {f : ZMod N → ℂ}
    (hf : shellAvg N f = 0) : shellDev N t f = dind N t * f := by
  rw [shellDev_apply, sum_dind_mul_eq_zero ht hf, zero_div, zero_smul, sub_zero]

/-- **2d.** X ∈ ⟨D_u, E_N⟩ なら、ある b があって、P f = 0 のどの f にも X f = Σ_{t ∈ S′} b_t·1_{D_t}·f。 -/
theorem exists_apply_of_mem_oneEAlg {N : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)} (hX : X ∈ oneEAlg N N) :
    ∃ b : devSet N → ℂ, ∀ f : ZMod N → ℂ, shellAvg N f = 0 → X f = ∑ t : devSet N, b t • (dind N t * f) := by
  rw [← range_wholeHom] at hX
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hX
  refine ⟨p.2, fun f hf => ?_⟩
  rw [wholeHom_apply, wholeMap_apply, LinearMap.add_apply, radialMatOp_apply_eq_zero p.1 hf, zero_add,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [LinearMap.smul_apply, shellDev_apply_of_shellAvg_eq_zero (dvd_of_mem_devSet t) hf]

/-- **2e.** X ∈ ⟨D_u, E_N⟩、P f = 0、f(z) = 0 なら (X f)(z) = 0（X は f の台を広げない）。 -/
theorem apply_eq_zero_of_mem_oneEAlg {N : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)} (hX : X ∈ oneEAlg N N)
    {f : ZMod N → ℂ} (hf : shellAvg N f = 0) {z : ZMod N} (hz : f z = 0) : X f z = 0 := by
  obtain ⟨b, hb⟩ := exists_apply_of_mem_oneEAlg hX
  rw [hb f hf, Finset.sum_apply]
  refine Finset.sum_eq_zero (fun t _ => ?_)
  rw [Pi.smul_apply, Pi.mul_apply, hz, mul_zero, smul_zero]

/-- **2f.** D_t P = P_{t,t}（t ∣ N）。 -/
theorem mulLeft_dind_mul_shellAvg {N t : ℕ} [NeZero N] (ht : t ∣ N) :
    LinearMap.mulLeft ℂ (dind N t) * shellAvg N = shellTrans N t t := by
  rw [shellAvg, Finset.mul_sum]
  simp only [mulLeft_dind_mul_shellTrans]
  rw [Finset.sum_ite_eq, ite_eq_left (Nat.mem_divisors.mpr ⟨ht, NeZero.ne N⟩)]

/-- **2g.** ⟨D_u, E_N⟩ の特徴づけ：X ∈ ⟨D_u, E_N⟩ ⇔ X ∈ A_N で、P f = 0 の f には殻ごとのスカラー
Σ_{t ∈ S′} b_t·1_{D_t} として働く。 -/
theorem mem_oneEAlg_iff {N : ℕ} [NeZero N] (X : Module.End ℂ (ZMod N → ℂ)) :
    X ∈ oneEAlg N N ↔ X ∈ shellAlg N ∧
      ∃ b : devSet N → ℂ, ∀ f : ZMod N → ℂ, shellAvg N f = 0 → X f = ∑ t : devSet N, b t • (dind N t * f) := by
  constructor
  · intro hX
    exact ⟨oneEAlg_le N N hX, exists_apply_of_mem_oneEAlg hX⟩
  · rintro ⟨hA, b, hb⟩
    have key : X = wholeMap N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N ⟨X, hA⟩), b) := by
      apply LinearMap.ext
      intro g
      have hPg : shellAvg N (g - shellAvg N g) = 0 := by
        rw [map_sub, ← Module.End.mul_apply, shellAvg_mul_self, sub_self]
      rw [wholeMap_apply, LinearMap.add_apply, ← mul_shellAvg_eq N ⟨X, hA⟩]
      have e1 : X g = (X * shellAvg N) g + X (g - shellAvg N g) := by
        rw [Module.End.mul_apply, ← map_add, add_sub_cancel]
      rw [e1, hb _ hPg]
      show (X * shellAvg N) g + _ = (X * shellAvg N) g + _
      congr 1
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [LinearMap.smul_apply]
      congr 1
      have ht := dvd_of_mem_devSet t
      rw [shellDev, LinearMap.sub_apply, ← mulLeft_dind_mul_shellAvg ht, Module.End.mul_apply,
        LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, mul_sub]
    rw [key, ← range_wholeHom]
    exact (AlgHom.mem_range _).mpr ⟨_, rfl⟩

/-! ### 3. φ(N/s) ≠ 1 の E_s が入らないことの具体的な証拠 -/

/-- 試しの関数 f = δ_1 − δ_{−1}。 -/
noncomputable def testFn (N : ℕ) : ZMod N → ℂ := Pi.single (1 : ZMod N) (1 : ℂ) - Pi.single (-1 : ZMod N) (1 : ℂ)

/-- **3a.** Σ_y g(y)·δ_a(y) = g(a)。 -/
theorem sum_mul_single {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (a : ZMod N) :
    ∑ y, g y * (Pi.single a (1 : ℂ) : ZMod N → ℂ) y = g a := by
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, mul_one]
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- **3b.** P(δ_1 − δ_{−1}) = 0（1 と −1 は同じ殻）。 -/
theorem shellAvg_testFn (N : ℕ) [NeZero N] : shellAvg N (testFn N) = 0 := by
  funext x
  rw [shellAvg_apply, Pi.zero_apply]
  have h : ∑ y, dind N (Nat.gcd N x.val) y * testFn N y = 0 := by
    simp only [testFn, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sum_mul_single]
    have hr := dind_radial N (Nat.gcd N x.val) (-1 : (ZMod N)ˣ) 1
    simp only [Units.val_neg, Units.val_one, neg_mul, one_mul] at hr
    rw [hr, sub_self]
  rw [h, zero_div]

/-- **3c.** (g ⋆ δ_a)(z) = g(z − a)。 -/
theorem conv_single_apply {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (a z : ZMod N) :
    PAG.Part15.conv g (Pi.single a (1 : ℂ)) z = g (z - a) := by
  show ∑ y, g y * (Pi.single a (1 : ℂ) : ZMod N → ℂ) (z - y) = g (z - a)
  rw [Finset.sum_eq_single (z - a)]
  · rw [sub_sub_cancel, Pi.single_eq_same, mul_one]
  · intro y _ hy
    have hne : z - y ≠ a := fun h => hy (by rw [← h, sub_sub_cancel])
    rw [Pi.single_eq_of_ne hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **3d.** (E_s (δ_1 − δ_{−1}))(z) = ε_s(z − 1) − ε_s(z + 1)。 -/
theorem conv_geps_testFn_apply (N s : ℕ) [NeZero N] (z : ZMod N) :
    PAG.Part15.conv (geps N s) (testFn N) z = geps N s (z - 1) - geps N s (z + 1) := by
  have h : PAG.Part15.conv (geps N s) (testFn N) =
      PAG.Part15.conv (geps N s) (Pi.single (1 : ZMod N) (1 : ℂ)) -
        PAG.Part15.conv (geps N s) (Pi.single (-1 : ZMod N) (1 : ℂ)) := by
    show PAG.Part15.convL (geps N s) (testFn N) =
      PAG.Part15.convL (geps N s) (Pi.single (1 : ZMod N) (1 : ℂ)) -
        PAG.Part15.convL (geps N s) (Pi.single (-1 : ZMod N) (1 : ℂ))
    rw [testFn, map_sub]
  rw [h, Pi.sub_apply, conv_single_apply, conv_single_apply, sub_neg_eq_add]

/-- **3e.** s ∣ N で φ(N/s) ≠ 1 なら N/s ≥ 3。 -/
theorem three_le_div {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) ≠ 1) : 3 ≤ N / s := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hq0 : 0 < N / s := Nat.div_pos (Nat.le_of_dvd hN hs) (Nat.pos_of_dvd_of_pos hs hN)
  by_contra hlt
  apply hφ
  rw [Nat.totient_eq_one_iff]
  omega

/-- **3f.** s ∣ N、φ(N/s) ≠ 1 なら、z = 1 + N/s で (E_s(δ_1 − δ_{−1}))(z) = (φ(q) − c_q(2))/N ≠ 0（q = N/s）。 -/
theorem conv_geps_testFn_ne_zero {N s : ℕ} [NeZero N] (hs : s ∣ N) (hφ : Nat.totient (N / s) ≠ 1) :
    PAG.Part15.conv (geps N s) (testFn N) ((1 + N / s : ℕ) : ZMod N) ≠ 0 := by
  have hq3 := three_le_div hs hφ
  rw [conv_geps_testFn_apply]
  have e1 : ((1 + N / s : ℕ) : ZMod N) - 1 = ((N / s : ℕ) : ZMod N) := by
    push_cast
    ring
  have e2 : ((1 + N / s : ℕ) : ZMod N) + 1 = ((N / s + 2 : ℕ) : ZMod N) := by
    push_cast
    ring
  rw [e1, e2]
  intro h
  have h' : (N : ℂ) * geps N s ((N / s : ℕ) : ZMod N) = (N : ℂ) * geps N s ((N / s + 2 : ℕ) : ZMod N) := by
    rw [sub_eq_zero.mp h]
  rw [natCast_mul_geps_eq_ramSum hs, natCast_mul_geps_eq_ramSum hs] at h'
  have h1 : ramSum (N / s) (N / s) = (Nat.totient (N / s) : ℤ) := ramSum_of_dvd dvd_rfl
  have h2 : ramSum (N / s + 2) (N / s) = ramSum 2 (N / s) := by
    rw [← ramSum_mod (N / s + 2) (N / s), ← ramSum_mod 2 (N / s), Nat.add_mod_left]
  have h3 : ramSum 2 (N / s) ≠ (Nat.totient (N / s) : ℤ) := by
    intro e
    have hd := (ramSum_eq_totient_iff (by omega) 2).mp e
    have := Nat.le_of_dvd two_pos hd
    omega
  apply h3
  rw [← h2, ← h1]
  exact_mod_cast h'.symm

/-- **3g.** s ∣ N、s ≠ 1、φ(N/s) ≠ 1 なら (δ_1 − δ_{−1})(1 + N/s) = 0（1 + N/s ≠ ±1）。 -/
theorem testFn_apply_eq_zero {N s : ℕ} [NeZero N] (hs : s ∣ N) (h1 : s ≠ 1) (hφ : Nat.totient (N / s) ≠ 1) :
    testFn N ((1 + N / s : ℕ) : ZMod N) = 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hs)
  have hqlt : N / s < N := Nat.div_lt_self hN (by omega)
  have hq3 := three_le_div hs hφ
  have hqN : N / s ∣ N := Nat.div_dvd_of_dvd hs
  have hne1 : ((1 + N / s : ℕ) : ZMod N) ≠ 1 := by
    intro h
    have h0 : ((N / s : ℕ) : ZMod N) = 0 := by
      push_cast at h
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)
  have hne2 : ((1 + N / s : ℕ) : ZMod N) ≠ -1 := by
    intro h
    have h0 : ((N / s + 2 : ℕ) : ZMod N) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    have h2 : N / s ∣ 2 := (Nat.dvd_add_right (dvd_refl (N / s))).mp (dvd_trans hqN h0)
    exact absurd (Nat.le_of_dvd two_pos h2) (by omega)
  simp only [testFn, Pi.sub_apply]
  rw [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2, sub_zero]

/-- **3h.** s ∣ N、s ≠ 1、φ(N/s) ≠ 1 なら E_s ∉ ⟨D_u, E_N⟩。 -/
theorem convL_geps_not_mem_oneEAlg {N s : ℕ} [NeZero N] (hs : s ∣ N) (h1 : s ≠ 1)
    (hφ : Nat.totient (N / s) ≠ 1) : PAG.Part15.convL (geps N s) ∉ oneEAlg N N := by
  intro hmem
  exact conv_geps_testFn_ne_zero hs hφ
    (apply_eq_zero_of_mem_oneEAlg hmem (shellAvg_testFn N) (testFn_apply_eq_zero hs h1 hφ))

/-! ### 4. どの E_s が ⟨D_u, E_N⟩ に入るか -/

/-- **4a.** s ∣ N、s ≠ 1 なら E_s ∈ ⟨D_u, E_N⟩ ⇔ φ(N/s) = 1。 -/
theorem convL_geps_mem_oneEAlg_iff {N s : ℕ} [NeZero N] (hs : s ∣ N) (h1 : s ≠ 1) :
    PAG.Part15.convL (geps N s) ∈ oneEAlg N N ↔ Nat.totient (N / s) = 1 := by
  constructor
  · intro h
    by_contra hφ
    exact convL_geps_not_mem_oneEAlg hs h1 hφ h
  · exact convL_geps_mem_oneEAlg hs

/-- **4b.** s ∣ N、s ≠ 1 なら E_s ∈ ⟨D_u, E_N⟩ ⇔ s = N ∨ 2s = N。 -/
theorem convL_geps_mem_oneEAlg_iff_eq {N s : ℕ} [NeZero N] (hs : s ∣ N) (h1 : s ≠ 1) :
    PAG.Part15.convL (geps N s) ∈ oneEAlg N N ↔ s = N ∨ 2 * s = N := by
  rw [convL_geps_mem_oneEAlg_iff hs h1, Nat.totient_eq_one_iff]
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨k, hk⟩ := hs
  have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact hN hk)
  rw [hk, Nat.mul_div_cancel_left k hs0]
  constructor
  · rintro (rfl | rfl)
    · left; ring
    · right; ring
  · rintro (h | h)
    · left
      have : s * k = s * 1 := by rw [← h, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hs0 this
    · right
      have : s * k = s * 2 := by rw [← h, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hs0 this

/-- **4c.** フーリエ双対：s ∣ N、s ≠ 1 なら D_s ∈ ⟨E_u, D_N⟩ ⇔ φ(N/s) = 1。 -/
theorem mulLeft_dind_mem_dualOneEAlg_iff {N s : ℕ} [NeZero N] (hs : s ∣ N) (h1 : s ≠ 1) :
    LinearMap.mulLeft ℂ (dind N s) ∈ dualOneEAlg N ↔ Nat.totient (N / s) = 1 := by
  rw [← convL_geps_mem_oneEAlg_iff hs h1, ← map_fourierConj_oneEAlg, ← fourierConj_convL_geps]
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := Subalgebra.mem_map.mp h
    have hxe : x = PAG.Part15.convL (geps N s) := (fourierConj N).injective hfx
    rw [← hxe]
    exact hx
  · intro h
    exact Subalgebra.mem_map.mpr ⟨_, h, rfl⟩

/-! ### 5. E_1 が入る条件 -/

/-- **5a.** |c_{p^k}(n)| ≤ p^k − p^{k−1}（k ≥ 1）。 -/
theorem abs_ramSum_primePow_le {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (n : ℕ) :
    |ramSum n (p ^ k)| ≤ (p : ℤ) ^ k - (p : ℤ) ^ (k - 1) := by
  have hpk : (p : ℤ) ^ k = p * p ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : (0 : ℤ) < (p : ℤ) ^ (k - 1) := pow_pos (by exact_mod_cast hp.pos) _
  rw [ramSum_primePow hp hk]
  by_cases h1 : p ^ k ∣ n
  · rw [ite_eq_left h1, ite_eq_left (dvd_trans (Nat.pow_dvd_pow p (Nat.sub_le k 1)) h1)]
    push_cast
    rw [abs_of_nonneg (by nlinarith)]
  · rw [ite_eq_right h1]
    by_cases h2 : p ^ (k - 1) ∣ n
    · rw [ite_eq_left h2]
      push_cast
      rw [zero_sub, abs_neg, abs_of_pos hpos]
      nlinarith
    · rw [ite_eq_right h2]
      simp only [sub_zero, abs_zero]
      nlinarith

/-- **5b.** p 素数、k ≥ 1、p ∤ M なら c_{p^k M}(p^{k−1} M) = −p^{k−1}·φ(M)。 -/
theorem ramSum_mul_eq {p k M : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hpM : ¬ p ∣ M) :
    ramSum (p ^ (k - 1) * M) (p ^ k * M) = -((p ^ (k - 1) : ℕ) : ℤ) * (Nat.totient M : ℤ) := by
  have hcop : Nat.Coprime (p ^ k) M := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  rw [(isMultiplicative_ramSum _).map_mul_of_coprime hcop, ramSum_primePow hp hk,
    ramSum_of_dvd (dvd_mul_left M _)]
  have h1 : ¬ p ^ k ∣ p ^ (k - 1) * M := by
    intro h
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ] at h
    exact hpM (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos m) h)
  rw [ite_eq_right h1, ite_eq_left (dvd_mul_right _ _)]
  ring

/-- **5c.** p 素数、k ≥ 1、p ∤ M なら c_{p^k M}(p^{k−1} M + 2) = c_{p^k}(p^{k−1} M + 2)·c_M(2)。 -/
theorem ramSum_mul_add_two {p k M : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ramSum (p ^ (k - 1) * M + 2) (p ^ k * M) = ramSum (p ^ (k - 1) * M + 2) (p ^ k) * ramSum 2 M := by
  have hcop : Nat.Coprime (p ^ k) M := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  rw [(isMultiplicative_ramSum _).map_mul_of_coprime hcop, ← ramSum_mod (p ^ (k - 1) * M + 2) M,
    ← ramSum_mod 2 M, Nat.mul_add_mod']

/-- **5d.** N ∉ {1, 4} ∪ 素数、p = minFac(N) なら c_N(N/p) ≠ c_N(N/p + 2)。 -/
theorem ramSum_div_minFac_ne {N : ℕ} [NeZero N] (h1 : N ≠ 1) (h4 : N ≠ 4) (hpr : ¬ N.Prime) :
    ramSum (N / N.minFac) N ≠ ramSum (N / N.minFac + 2) N := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hp : N.minFac.Prime := Nat.minFac_prime h1
  have hk1 : 0 < N.factorization N.minFac := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
  have hNM := (Nat.ordProj_mul_ordCompl_eq_self N N.minFac).symm
  have hpM : ¬ N.minFac ∣ N / N.minFac ^ N.factorization N.minFac := Nat.not_dvd_ordCompl hp hN0
  have hM0 := Nat.ordCompl_pos N.minFac hN0
  have hmin : ∀ r, r.Prime → r ∣ N / N.minFac ^ N.factorization N.minFac → N.minFac < r := by
    intro r hr hrM
    have hrN : r ∣ N := dvd_trans hrM (Nat.ordCompl_dvd N N.minFac)
    have hle := Nat.minFac_le_of_dvd hr.two_le hrN
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (heq ▸ hrM) hpM
  have hodd : ¬ 2 ∣ N / N.minFac ^ N.factorization N.minFac := by
    intro h2
    have h3 := hmin 2 Nat.prime_two h2
    have h5 := hp.two_le
    omega
  generalize N.minFac = p at hp hk1 hNM hpM hM0 hmin hodd ⊢
  generalize N.factorization p = k at hk1 hNM hpM hM0 hmin hodd
  generalize N / p ^ k = M at hNM hpM hM0 hmin hodd
  have hNp : N / p = p ^ (k - 1) * M := by
    rw [hNM]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_comm (p ^ m) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [hNp, hNM, ramSum_mul_eq hp hk1 hpM, ramSum_mul_add_two hp hpM]
  by_cases hM1 : M = 1
  · subst hM1
    rw [mul_one] at hNM
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk : k = 1 := by omega
      exact hpr (by rw [hNM, hk, pow_one]; exact hp)
    have hpk3 : 3 ≤ p ^ (k - 1) := by
      by_cases hp2 : p = 2
      · have hk3 : 3 ≤ k := by
          by_contra hlt
          have hk : k = 2 := by omega
          exact h4 (by rw [hNM, hk, hp2]; norm_num)
        rw [hp2]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      · have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        calc 3 ≤ p := hp3
          _ = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ (k - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have hnd : ¬ p ^ (k - 1) ∣ p ^ (k - 1) * 1 + 2 := by
      intro h
      rw [mul_one] at h
      have h2 : p ^ (k - 1) ∣ 2 := (Nat.dvd_add_right (dvd_refl _)).mp h
      have := Nat.le_of_dvd two_pos h2
      omega
    have hnd' : ¬ p ^ k ∣ p ^ (k - 1) * 1 + 2 :=
      fun h => hnd (dvd_trans (Nat.pow_dvd_pow p (Nat.sub_le k 1)) h)
    rw [ramSum_primePow hp (by omega), ite_eq_right hnd', ite_eq_right hnd, (isMultiplicative_ramSum 2).map_one,
      Nat.totient_one]
    have hpos : (0 : ℤ) < ((p ^ (k - 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.pos _
    intro h
    push_cast at h hpos
    linarith
  · intro heq
    have hM2 : M ≠ 1 := hM1
    have hr := Nat.minFac_prime hM2
    have hrp : p < M.minFac := hmin _ hr (Nat.minFac_dvd M)
    have hφM : p ≤ Nat.totient M := by
      have hd : Nat.totient M.minFac ∣ Nat.totient M := Nat.totient_dvd_of_dvd (Nat.minFac_dvd M)
      have h2 := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) hd
      rw [Nat.totient_prime hr] at h2
      omega
    have hμ : |ramSum 2 M| ≤ 1 := by
      rw [ramSum_of_coprime (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))]
      exact ArithmeticFunction.abs_moebius_le_one
    have hpk := abs_ramSum_primePow_le hp hk1 (p ^ (k - 1) * M + 2)
    have hpk' : (p : ℤ) ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk1]
    have hpos : (0 : ℤ) < (p : ℤ) ^ (k - 1) := pow_pos (by exact_mod_cast hp.pos) _
    have hR : |ramSum (p ^ (k - 1) * M + 2) (p ^ k) * ramSum 2 M| ≤ (p : ℤ) ^ k - (p : ℤ) ^ (k - 1) := by
      rw [abs_mul]
      have hnn : (0 : ℤ) ≤ (p : ℤ) ^ k - (p : ℤ) ^ (k - 1) := by
        have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
        nlinarith
      calc |ramSum (p ^ (k - 1) * M + 2) (p ^ k)| * |ramSum 2 M|
          ≤ ((p : ℤ) ^ k - (p : ℤ) ^ (k - 1)) * 1 := mul_le_mul hpk hμ (abs_nonneg _) hnn
        _ = (p : ℤ) ^ k - (p : ℤ) ^ (k - 1) := mul_one _
    have hL : (p : ℤ) ^ k ≤ |-((p ^ (k - 1) : ℕ) : ℤ) * (Nat.totient M : ℤ)| := by
      rw [abs_mul, abs_neg]
      push_cast
      rw [abs_of_pos hpos, abs_of_nonneg (by positivity), hpk']
      have hφ' : (p : ℤ) ≤ (Nat.totient M : ℤ) := by exact_mod_cast hφM
      nlinarith
    rw [heq] at hL
    linarith

/-- **5e.** N ∉ {1, 4} ∪ 素数 なら E_1 ∉ ⟨D_u, E_N⟩（証拠は δ_1 − δ_{−1} と z = 1 + N/minFac(N)）。 -/
theorem convL_geps_one_not_mem_oneEAlg {N : ℕ} [NeZero N] (h1 : N ≠ 1) (h4 : N ≠ 4) (hpr : ¬ N.Prime) :
    PAG.Part15.convL (geps N 1) ∉ oneEAlg N N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hp := Nat.minFac_prime h1
  have hq0 : 0 < N / N.minFac := Nat.div_pos (Nat.minFac_le hN) hp.pos
  have hqle : 2 * (N / N.minFac) ≤ N :=
    le_trans (Nat.mul_le_mul_left 2 (Nat.div_le_div_left hp.two_le two_pos)) (Nat.mul_div_le N 2)
  have hN6 : 6 ≤ N := by
    by_contra hlt
    have : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 := by omega
    rcases this with h | h | h | h | h | h
    · exact NeZero.ne N h
    · exact h1 h
    · exact hpr (by rw [h]; exact Nat.prime_two)
    · exact hpr (by rw [h]; exact Nat.prime_three)
    · exact h4 h
    · exact hpr (by rw [h]; exact Nat.prime_five)
  generalize hq : N / N.minFac = q at hq0 hqle
  have hz1 : ((1 + q : ℕ) : ZMod N) ≠ 1 := by
    intro h
    have h0 : ((q : ℕ) : ZMod N) = 0 := by
      push_cast at h
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd hq0 h0) (by omega)
  have hz2 : ((1 + q : ℕ) : ZMod N) ≠ -1 := by
    intro h
    have h0 : ((q + 2 : ℕ) : ZMod N) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)
  have hf : testFn N ((1 + q : ℕ) : ZMod N) = 0 := by
    simp only [testFn, Pi.sub_apply]
    rw [Pi.single_eq_of_ne hz1, Pi.single_eq_of_ne hz2, sub_zero]
  intro hmem
  have h0 := apply_eq_zero_of_mem_oneEAlg hmem (shellAvg_testFn N) hf
  have hv : PAG.Part15.conv (geps N 1) (testFn N) ((1 + q : ℕ) : ZMod N) =
      geps N 1 ((q : ℕ) : ZMod N) - geps N 1 ((q + 2 : ℕ) : ZMod N) := by
    rw [conv_geps_testFn_apply]
    congr 2
    · push_cast
      ring
    · push_cast
      ring
  have hzero : geps N 1 ((q : ℕ) : ZMod N) - geps N 1 ((q + 2 : ℕ) : ZMod N) = 0 := hv ▸ h0
  have h' : (N : ℂ) * geps N 1 ((q : ℕ) : ZMod N) = (N : ℂ) * geps N 1 ((q + 2 : ℕ) : ZMod N) := by
    rw [sub_eq_zero.mp hzero]
  rw [natCast_mul_geps_eq_ramSum (one_dvd N), natCast_mul_geps_eq_ramSum (one_dvd N), Nat.div_one] at h'
  apply ramSum_div_minFac_ne h1 h4 hpr
  rw [hq]
  exact_mod_cast h'

/-- **5f.** E_1 ∈ ⟨D_u, E_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数。 -/
theorem convL_geps_one_mem_oneEAlg_iff (N : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N 1) ∈ oneEAlg N N ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  constructor
  · intro h
    by_contra hN
    exact convL_geps_one_not_mem_oneEAlg (fun e => hN (Or.inl e)) (fun e => hN (Or.inr (Or.inl e)))
      (fun e => hN (Or.inr (Or.inr e))) h
  · intro hN
    rw [← (shellAlg_eq_oneEAlg_iff N).mpr hN]
    exact PAG.Part232.convL_geps_mem N 1

/-- **5g.** まとめ：s ∣ N で E_s ∈ ⟨D_u, E_N⟩ ⇔ (s ≠ 1 かつ φ(N/s) = 1) または (s = 1 かつ N ∈ {1, 4} ∪ 素数)。 -/
theorem convL_geps_mem_oneEAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∣ N) :
    PAG.Part15.convL (geps N s) ∈ oneEAlg N N ↔
      (s ≠ 1 ∧ Nat.totient (N / s) = 1) ∨ (s = 1 ∧ (N = 1 ∨ N = 4 ∨ N.Prime)) := by
  by_cases h1 : s = 1
  · subst h1
    rw [convL_geps_one_mem_oneEAlg_iff]
    constructor
    · intro h
      exact Or.inr ⟨rfl, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd rfl h
      · exact h
  · rw [convL_geps_mem_oneEAlg_iff hs h1]
    constructor
    · intro h
      exact Or.inl ⟨h1, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h h1

/-- **5h.** フーリエ双対：D_1 ∈ ⟨E_u, D_N⟩ ⇔ N = 1 ∨ N = 4 ∨ N は素数。 -/
theorem mulLeft_dind_one_mem_dualOneEAlg_iff (N : ℕ) [NeZero N] :
    LinearMap.mulLeft ℂ (dind N 1) ∈ dualOneEAlg N ↔ N = 1 ∨ N = 4 ∨ N.Prime := by
  rw [← convL_geps_one_mem_oneEAlg_iff, ← map_fourierConj_oneEAlg, ← fourierConj_convL_geps]
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := Subalgebra.mem_map.mp h
    have hxe : x = PAG.Part15.convL (geps N 1) := (fourierConj N).injective hfx
    rw [← hxe]
    exact hx
  · intro h
    exact Subalgebra.mem_map.mpr ⟨_, h, rfl⟩

end PAG.Part247

#print axioms PAG.Part247.ramSum_eq_totient_iff
#print axioms PAG.Part247.sum_dind_mul_eq_zero
#print axioms PAG.Part247.radialMatOp_apply_eq_zero
#print axioms PAG.Part247.shellDev_apply_of_shellAvg_eq_zero
#print axioms PAG.Part247.exists_apply_of_mem_oneEAlg
#print axioms PAG.Part247.apply_eq_zero_of_mem_oneEAlg
#print axioms PAG.Part247.mulLeft_dind_mul_shellAvg
#print axioms PAG.Part247.mem_oneEAlg_iff
#print axioms PAG.Part247.testFn
#print axioms PAG.Part247.sum_mul_single
#print axioms PAG.Part247.shellAvg_testFn
#print axioms PAG.Part247.conv_single_apply
#print axioms PAG.Part247.conv_geps_testFn_apply
#print axioms PAG.Part247.three_le_div
#print axioms PAG.Part247.conv_geps_testFn_ne_zero
#print axioms PAG.Part247.testFn_apply_eq_zero
#print axioms PAG.Part247.convL_geps_not_mem_oneEAlg
#print axioms PAG.Part247.convL_geps_mem_oneEAlg_iff
#print axioms PAG.Part247.convL_geps_mem_oneEAlg_iff_eq
#print axioms PAG.Part247.mulLeft_dind_mem_dualOneEAlg_iff
#print axioms PAG.Part247.abs_ramSum_primePow_le
#print axioms PAG.Part247.ramSum_mul_eq
#print axioms PAG.Part247.ramSum_mul_add_two
#print axioms PAG.Part247.ramSum_div_minFac_ne
#print axioms PAG.Part247.convL_geps_one_not_mem_oneEAlg
#print axioms PAG.Part247.convL_geps_one_mem_oneEAlg_iff
#print axioms PAG.Part247.convL_geps_mem_oneEAlg_iff_all
#print axioms PAG.Part247.mulLeft_dind_one_mem_dualOneEAlg_iff
