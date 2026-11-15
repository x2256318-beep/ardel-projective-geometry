/-
  PAG 2.0 Part 240（2026-11-05）— 中心のべき等元 P = Σ_s P_{s,s} と、E_s 1 つで足りる条件（ラマヌジャン和が 0 にならない条件）
  Part 239 で数値だけだった主張を Lean にする。
  1. 単数倍の軌道の数え上げ：Σ_{a 単数} F(a·x) = #Stab(x)·Σ_{y ∈ D_{gcd(N,x)}} F(y)（sum_units_mul）、
     #Stab(x)·φ(N/gcd(N, x)) = φ(N)（card_stab_mul_totient）。P = Σ_{s ∣ N} P_{s,s}（shellAvg）は
     単数倍の平均 (1/φ(N))·Σ_a U_a（unitAvg）に等しい（shellAvg_eq_unitAvg）
  2. P は A_N の中心のべき等元（shellAvg_mem_center・shellAvg_mul_self）。T ∈ A_N なら P T = T P = Σ_{s,t} [T](s, t)·P_{s,t}
     （shellAvg_mul_eq：角の代数 P A_N P は Part 239 の行列単位の代数 ≅ M_{d(N)}(ℂ)）、radialHom T = 0 ⇔ P T = 0。
     P f は動径関数で、動径関数 f では P f = f
  3. ラマヌジャン和 c_q(n) = (μ * (d ↦ d·[d ∣ n]))(q)（ramSum）は q について乗法的（isMultiplicative_ramSum）。
     N·ε_t(u) = c_{N/t}(u)（Part 239 の C(u, t)）、c_{p^k}(n) = p^k[p^k ∣ n] − p^{k−1}[p^{k−1} ∣ n]、c_q(1) = μ(q)、
     c_q(n) ≠ 0 ⇔ q のどの素因数 p でも p^{v_p(q)−1} ∣ n（ramSum_ne_zero_iff）
  4. D_u と E_s（s ∣ N）だけで動径関数の空間の上の全行列環が出る ⇔ N/s が平方因子をもたない（radialHom_oneE_surjective_iff）。
     平方因子をもたないときは [E_s] の成分がどれも 0 でなく、X_{u,t} = [E_s](u, t)⁻¹·D_u E_s D_t が行列単位（oneETrans）。
     平方因子をもつときは c_{N/s}(1) = μ(N/s) = 0 なので、⟨D_u, E_s⟩ の元の行列の (1, t) 成分（t ≠ 1）はすべて 0
-/
import PAG243

namespace PAG.Part244

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 単数倍の軌道の数え上げと、単数倍の平均 -/

/-- **1a.** gcd(N, y) = gcd(N, x) なら、a·x = y となる単数 a の個数は a·x = x となる個数と同じ。 -/
theorem card_fiber_eq {N : ℕ} [NeZero N] (x y : ZMod N) (h : Nat.gcd N y.val = Nat.gcd N x.val) :
    (Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = y)).card =
      (Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card := by
  obtain ⟨b, hb⟩ : ∃ b : (ZMod N)ˣ, (b : ZMod N) * x = y := by
    obtain ⟨c, hc⟩ := exists_unit_mul_gcd N y
    obtain ⟨d, hd⟩ := exists_unit_mul_gcd N x
    rw [h] at hc
    generalize ((Nat.gcd N x.val : ℕ) : ZMod N) = g at hc hd
    refine ⟨c * d⁻¹, ?_⟩
    rw [← hc, ← hd, Units.val_mul, mul_assoc, ← mul_assoc ((d⁻¹ : (ZMod N)ˣ) : ZMod N), Units.inv_mul, one_mul]
  refine Finset.card_nbij' (fun a => b⁻¹ * a) (fun a => b * a) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [Units.val_mul, mul_assoc, ha, ← hb, ← mul_assoc, Units.inv_mul, one_mul]
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [Units.val_mul, mul_assoc, ha, hb]
  · intro a _
    simp only [mul_inv_cancel_left]
  · intro a _
    simp only [inv_mul_cancel_left]

/-- **1b.** Σ_{a 単数} F(a·x) = #{a : a·x = x}·Σ_{y ∈ D_{gcd(N, x)}} F(y)。 -/
theorem sum_units_mul {N : ℕ} [NeZero N] (F : ZMod N → ℂ) (x : ZMod N) :
    ∑ a : (ZMod N)ˣ, F ((a : ZMod N) * x) =
      ((Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card : ℂ) *
        ∑ y, dind N (Nat.gcd N x.val) y * F y := by
  have h1 : ∀ a : (ZMod N)ˣ, F ((a : ZMod N) * x) = ∑ y, if (a : ZMod N) * x = y then F y else 0 := by
    intro a
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  by_cases hy : Nat.gcd N y.val = Nat.gcd N x.val
  · rw [card_fiber_eq x y hy]
    have hd : dind N (Nat.gcd N x.val) y = 1 := by
      show (if Nat.gcd N y.val = Nat.gcd N x.val then (1 : ℂ) else 0) = 1
      exact ite_eq_left hy
    rw [hd, one_mul]
  · have h0 : (Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = y)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a _ ha
      apply hy
      rw [← ha]
      exact gcd_val_unit_mul N a x
    have hd : dind N (Nat.gcd N x.val) y = 0 := by
      show (if Nat.gcd N y.val = Nat.gcd N x.val then (1 : ℂ) else 0) = 0
      exact ite_eq_right hy
    rw [h0, hd]
    simp

/-- **1c.** #{a : a·x = x}·φ(N/gcd(N, x)) = φ(N)（軌道と固定群の個数）。 -/
theorem card_stab_mul_totient {N : ℕ} [NeZero N] (x : ZMod N) :
    ((Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card : ℂ) *
      (Nat.totient (N / Nat.gcd N x.val) : ℂ) = Nat.totient N := by
  have h := sum_units_mul (fun _ => (1 : ℂ)) x
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul, mul_one] at h
  have hs : ∑ y, dind N (Nat.gcd N x.val) y = (Nat.totient (N / Nat.gcd N x.val) : ℂ) := by
    simp only [dind]
    rw [Finset.sum_boole, card_dsh N _ (Nat.gcd_dvd_left N x.val)]
  rw [← hs, ← h]

/-- 単数倍の平均 (1/φ(N))·Σ_a U_a。 -/
noncomputable def unitAvg (N : ℕ) [NeZero N] : Module.End ℂ (ZMod N → ℂ) :=
  ((Nat.totient N : ℂ))⁻¹ • ∑ a : (ZMod N)ˣ, dil a

/-- **1d.** (単数倍の平均 f)(x) = D_{gcd(N, x)} の上の f の平均。 -/
theorem unitAvg_apply {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (x : ZMod N) :
    unitAvg N f x = (∑ y, dind N (Nat.gcd N x.val) y * f y) / (Nat.totient (N / Nat.gcd N x.val) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hφN : (Nat.totient N : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hN).ne'
  have hφg : (Nat.totient (N / Nat.gcd N x.val) : ℂ) ≠ 0 := by
    have h0 : 0 < N / Nat.gcd N x.val :=
      Nat.div_pos (Nat.gcd_le_left _ hN) (Nat.gcd_pos_of_pos_left _ hN)
    exact_mod_cast (Nat.totient_pos.mpr h0).ne'
  have hc := card_stab_mul_totient x
  rw [unitAvg, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply]
  simp only [dil_apply, smul_eq_mul]
  rw [sum_units_mul f x, eq_div_iff hφg]
  calc ((Nat.totient N : ℂ))⁻¹ * (((Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card : ℂ) *
        ∑ y, dind N (Nat.gcd N x.val) y * f y) * (Nat.totient (N / Nat.gcd N x.val) : ℂ)
      = ((Nat.totient N : ℂ))⁻¹ * (((Finset.univ.filter (fun a : (ZMod N)ˣ => (a : ZMod N) * x = x)).card : ℂ) *
        (Nat.totient (N / Nat.gcd N x.val) : ℂ)) * ∑ y, dind N (Nat.gcd N x.val) y * f y := by ring
    _ = _ := by rw [hc, inv_mul_cancel₀ hφN, one_mul]

/-- 殻ごとの平均 P = Σ_{s ∣ N} P_{s,s}（Part 239 の殻の移し替え）。 -/
noncomputable def shellAvg (N : ℕ) [NeZero N] : Module.End ℂ (ZMod N → ℂ) := ∑ s ∈ N.divisors, shellTrans N s s

/-- **1e.** (P f)(x) = D_{gcd(N, x)} の上の f の平均。 -/
theorem shellAvg_apply {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (x : ZMod N) :
    shellAvg N f x = (∑ y, dind N (Nat.gcd N x.val) y * f y) / (Nat.totient (N / Nat.gcd N x.val) : ℂ) := by
  rw [shellAvg, LinearMap.sum_apply, Finset.sum_apply]
  simp only [shellTrans_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (Nat.gcd N x.val)]
  · have hd : dind N (Nat.gcd N x.val) x = 1 := by
      show (if Nat.gcd N x.val = Nat.gcd N x.val then (1 : ℂ) else 0) = 1
      exact ite_eq_left rfl
    rw [hd, mul_one]
  · intro s _ hs
    have hd : dind N s x = 0 := by
      show (if Nat.gcd N x.val = s then (1 : ℂ) else 0) = 0
      exact ite_eq_right (fun h => hs h.symm)
    rw [hd, mul_zero]
  · intro h
    exact absurd (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left N x.val, NeZero.ne N⟩) h

/-- **1f.** Σ_{s ∣ N} P_{s,s} = (1/φ(N))·Σ_a U_a。 -/
theorem shellAvg_eq_unitAvg (N : ℕ) [NeZero N] : shellAvg N = unitAvg N := by
  apply LinearMap.ext
  intro f
  funext x
  rw [shellAvg_apply, unitAvg_apply]

/-! ### 2. 中心のべき等元 P = Σ_s P_{s,s} と、角の代数 P A P -/

/-- **2a.** P ∈ A_N。 -/
theorem shellAvg_mem (N : ℕ) [NeZero N] : shellAvg N ∈ shellAlg N :=
  Subalgebra.sum_mem _ (fun s _ => shellTrans_mem N s s)

/-- **2b.** P = Σ_{s,t} δ_{st}·P_{s,t}（単位行列の行き先）。 -/
theorem radialMatOp_one_eq (N : ℕ) [NeZero N] : radialMatOp N 1 = shellAvg N := by
  rw [radialMatOp_one, shellAvg]
  exact Finset.sum_coe_sort N.divisors (fun s => shellTrans N s s)

/-- **2c.** P² = P。 -/
theorem shellAvg_mul_self (N : ℕ) [NeZero N] : shellAvg N * shellAvg N = shellAvg N := by
  rw [← radialMatOp_one_eq, ← radialMatOp_mul, one_mul]

/-- **2d.** A_N の元は動径関数を動径関数に写す。 -/
theorem radial_apply_of_mem {N : ℕ} [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N)
    {f : ZMod N → ℂ} (hf : Radial f) : Radial (T f) :=
  (radial_iff_dil _).mpr (fun a => by rw [← shellAlg_comm_dil N hT a f, (radial_iff_dil f).mp hf a])

/-- **2e.** P は A_N のすべての元と可換（A_N の元は U_a と可換なので、単数倍の平均とも可換）。 -/
theorem commute_shellAvg (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N) :
    T * shellAvg N = shellAvg N * T := by
  rw [shellAvg_eq_unitAvg]
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, Module.End.mul_apply, unitAvg, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp only [shellAlg_comm_dil N hT]

/-- **2f.** P は A_N の中心の元。 -/
theorem shellAvg_mem_center (N : ℕ) [NeZero N] :
    (⟨shellAvg N, shellAvg_mem N⟩ : shellAlg N) ∈ Subalgebra.center ℂ (shellAlg N) := by
  rw [Subalgebra.mem_center_iff]
  intro T
  exact Subtype.ext (commute_shellAvg N T.2)

/-- **2g.** 角の代数：T ∈ A_N なら P T = Σ_{s,t} [T](s, t)·P_{s,t}（[T] は動径関数の上の行列）。 -/
theorem shellAvg_mul_eq (N : ℕ) [NeZero N] (T : shellAlg N) :
    shellAvg N * T = radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N T)) := by
  apply LinearMap.ext
  intro f
  have hexp : ∀ t : ℕ, (T : Module.End ℂ (ZMod N → ℂ)) (dind N t) =
      ∑ s ∈ N.divisors, (T : Module.End ℂ (ZMod N → ℂ)) (dind N t) (s : ZMod N) • dind N s :=
    fun t => radial_eq_sum (radial_apply_of_mem T.2 (dind_radial N t))
  have lhs : (shellAvg N * T) f = ∑ t ∈ N.divisors, ∑ s ∈ N.divisors,
      ((∑ y, dind N t y * f y) / (Nat.totient (N / t) : ℂ) *
        (T : Module.End ℂ (ZMod N → ℂ)) (dind N t) (s : ZMod N)) • dind N s := by
    rw [← commute_shellAvg N T.2, Module.End.mul_apply, shellAvg, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [shellTrans_apply, map_smul]
    conv_lhs => rw [hexp t]
    rw [Finset.smul_sum]
    simp only [smul_smul]
  have rhs : radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N T)) f =
      ∑ s ∈ N.divisors, ∑ t ∈ N.divisors,
        ((∑ y, dind N t y * f y) / (Nat.totient (N / t) : ℂ) *
          (T : Module.End ℂ (ZMod N → ℂ)) (dind N t) (s : ZMod N)) • dind N s := by
    rw [radialMatOp, LinearMap.sum_apply, ← Finset.sum_coe_sort N.divisors]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [LinearMap.sum_apply, ← Finset.sum_coe_sort N.divisors]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [LinearMap.smul_apply, toMatrix_radialHom, shellTrans_apply, smul_smul]
    congr 1
    ring
  rw [lhs, rhs, Finset.sum_comm]

/-- **2h.** T P = P T = Σ_{s,t} [T](s, t)·P_{s,t}。 -/
theorem mul_shellAvg_eq (N : ℕ) [NeZero N] (T : shellAlg N) :
    (T : Module.End ℂ (ZMod N → ℂ)) * shellAvg N =
      radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N T)) := by
  rw [commute_shellAvg N T.2, shellAvg_mul_eq]

/-- **2i.** P·Σ M_{st}P_{s,t} = Σ M_{st}P_{s,t}（P は行列単位の代数の単位元）。 -/
theorem shellAvg_mul_radialMatOp (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    shellAvg N * radialMatOp N M = radialMatOp N M := by
  rw [← radialMatOp_one_eq, ← radialMatOp_mul, one_mul]

/-- **2j.** radialHom T = 0 ⇔ P T = 0。 -/
theorem radialHom_eq_zero_iff (N : ℕ) [NeZero N] (T : shellAlg N) :
    radialHom N T = 0 ↔ shellAvg N * T = 0 := by
  have h0 : radialMatOp N 0 = 0 := by
    simp only [radialMatOp, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
  rw [shellAvg_mul_eq]
  constructor
  · intro h
    rw [h, map_zero, h0]
  · intro h
    have hM := radialMatOp_injective N (h.trans h0.symm)
    exact (LinearMap.toMatrix (radialBasis N) (radialBasis N)).injective (hM.trans (map_zero _).symm)

/-- **2k.** P f は動径関数。 -/
theorem radial_shellAvg_apply {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : Radial (shellAvg N f) := by
  intro a x
  rw [shellAvg_apply, shellAvg_apply, gcd_val_unit_mul]

/-- **2l.** 動径関数 f では P f = f（P は動径関数の空間への射影）。 -/
theorem shellAvg_apply_of_radial {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) : shellAvg N f = f := by
  rw [shellAvg, LinearMap.sum_apply]
  exact sum_shellTrans_self_radial hf

/-! ### 3. ラマヌジャン和の乗法性と、0 にならない条件 -/

/-- d ↦ d·[d ∣ n]。 -/
noncomputable def dvdWeight (n : ℕ) : ArithmeticFunction ℤ := ⟨fun d => if d ∣ n then (d : ℤ) else 0, by simp⟩

/-- **3a.** dvdWeight n d = d·[d ∣ n]。 -/
theorem dvdWeight_apply (n d : ℕ) : dvdWeight n d = if d ∣ n then (d : ℤ) else 0 := rfl

/-- **3b.** d ↦ d·[d ∣ n] は乗法的。 -/
theorem isMultiplicative_dvdWeight (n : ℕ) : (dvdWeight n).IsMultiplicative := by
  refine ⟨by simp [dvdWeight_apply], fun {a b} hab => ?_⟩
  simp only [dvdWeight_apply]
  by_cases ha : a ∣ n
  · by_cases hb : b ∣ n
    · rw [ite_eq_left (Nat.Coprime.mul_dvd_of_dvd_of_dvd hab ha hb), ite_eq_left ha, ite_eq_left hb]
      exact Nat.cast_mul a b
    · rw [ite_eq_right (fun h => hb (dvd_trans (dvd_mul_left b a) h)), ite_eq_right hb, mul_zero]
  · rw [ite_eq_right (fun h => ha (dvd_trans (dvd_mul_right a b) h)), ite_eq_right ha, zero_mul]

/-- ラマヌジャン和 c_q(n) = (μ * (d ↦ d·[d ∣ n]))(q)。 -/
noncomputable def ramSum (n : ℕ) : ArithmeticFunction ℤ := ArithmeticFunction.moebius * dvdWeight n

/-- **3c.** c_q(n) = Σ_{e ∣ q} μ(e)·(q/e)·[q/e ∣ n]。 -/
theorem ramSum_apply (n q : ℕ) :
    ramSum n q = ∑ e ∈ q.divisors,
      ArithmeticFunction.moebius e * (if q / e ∣ n then ((q / e : ℕ) : ℤ) else 0) := by
  rw [ramSum, ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun x y => ArithmeticFunction.moebius x * dvdWeight n y)

/-- **3d.** q ↦ c_q(n) は乗法的。 -/
theorem isMultiplicative_ramSum (n : ℕ) : (ramSum n).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.mul (isMultiplicative_dvdWeight n)

/-- **3e.** N·ε_t(u) = c_{N/t}(u)（t ∣ N）。 -/
theorem natCast_mul_geps_eq_ramSum {N t : ℕ} [NeZero N] (ht : t ∣ N) (u : ℕ) :
    (N : ℂ) * geps N t (u : ZMod N) = (ramSum u (N / t) : ℂ) := by
  rw [natCast_mul_geps ht u, ramSum_apply]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_natCast, Int.cast_zero]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Nat.div_div_eq_div_mul]
  split_ifs <;> ring

/-- **3f.** ラマヌジャンの行列 C(u, t) = c_{N/t}(u)。 -/
theorem ramMat_eq_ramSum (N : ℕ) [NeZero N] (u t : N.divisors) :
    ramMat N u t = (ramSum u (N / t) : ℂ) := by
  rw [ramMat, Matrix.of_apply]
  exact natCast_mul_geps_eq_ramSum (Nat.dvd_of_mem_divisors t.2) u

/-- **3g.** Σ_{e ∣ q^n} μ(e)·g(e) = g(1) − g(q)（整数値、q は素数、n ≥ 1）。 -/
theorem sum_divisors_primePow_moebius_int {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℤ) :
    ∑ e ∈ (q ^ n).divisors, ArithmeticFunction.moebius e * g e = g 1 - g q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.divisors_prime_pow hq, Finset.sum_map, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_eq_zero (fun x _ => ?_)]
  · simp only [Function.Embedding.coeFn_mk, zero_add, pow_zero, pow_one, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hq]
    ring
  · simp only [Function.Embedding.coeFn_mk]
    rw [ArithmeticFunction.moebius_apply_prime_pow hq (by omega), ite_eq_right (by omega), zero_mul]

/-- **3h.** 素冪：c_{p^k}(n) = p^k·[p^k ∣ n] − p^{k−1}·[p^{k−1} ∣ n]（k ≥ 1）。 -/
theorem ramSum_primePow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ramSum n (p ^ k) = (if p ^ k ∣ n then ((p ^ k : ℕ) : ℤ) else 0) -
      (if p ^ (k - 1) ∣ n then ((p ^ (k - 1) : ℕ) : ℤ) else 0) := by
  have hpk : p ^ k / p = p ^ (k - 1) :=
    Nat.div_eq_of_eq_mul_left hp.pos (by rw [← pow_succ, Nat.sub_add_cancel hk])
  rw [ramSum_apply]
  refine (sum_divisors_primePow_moebius_int hp hk
    (fun e => if p ^ k / e ∣ n then ((p ^ k / e : ℕ) : ℤ) else 0)).trans ?_
  simp only [Nat.div_one, hpk]

/-- **3i.** c_q(1) = μ(q)。 -/
theorem ramSum_one (q : ℕ) : ramSum 1 q = ArithmeticFunction.moebius q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  rw [ramSum_apply, Finset.sum_eq_single q]
  · rw [Nat.div_self hq, ite_eq_left (dvd_refl 1), Nat.cast_one, mul_one]
  · intro e he heq
    have hne : ¬ q / e ∣ 1 := by
      intro h
      exact heq (Nat.eq_of_dvd_of_div_eq_one (Nat.dvd_of_mem_divisors he) (Nat.dvd_one.mp h))
    rw [ite_eq_right hne, mul_zero]
  · intro h
    exact absurd (Nat.mem_divisors_self q hq.ne') h

/-- **3j.** p^{k−1} ∣ n なら c_{p^k}(n) ≠ 0（k ≥ 1）。 -/
theorem ramSum_primePow_ne_zero {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) {n : ℕ} (h : p ^ (k - 1) ∣ n) :
    ramSum n (p ^ k) ≠ 0 := by
  rw [ramSum_primePow hp hk, ite_eq_left h]
  have hlt : ((p ^ (k - 1) : ℕ) : ℤ) < ((p ^ k : ℕ) : ℤ) := by
    exact_mod_cast Nat.pow_lt_pow_right hp.one_lt (by omega)
  by_cases hk' : p ^ k ∣ n
  · rw [ite_eq_left hk']
    exact sub_ne_zero.mpr (ne_of_gt hlt)
  · rw [ite_eq_right hk', zero_sub, neg_ne_zero]
    exact_mod_cast (pow_pos hp.pos _).ne'

/-- **3k.** q ≠ 0 で、q のどの素因数 p でも p^{v_p(q) − 1} ∣ n なら c_q(n) ≠ 0。 -/
theorem ramSum_ne_zero {q n : ℕ} (hq : q ≠ 0) (h : ∀ p ∈ q.primeFactors, p ^ (q.factorization p - 1) ∣ n) :
    ramSum n q ≠ 0 := by
  rw [(isMultiplicative_ramSum n).multiplicative_factorization (ramSum n) hq, Finsupp.prod,
    Finset.prod_ne_zero_iff]
  intro p hp
  rw [Nat.support_factorization] at hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact ramSum_primePow_ne_zero hpp (hpp.factorization_pos_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)) (h p hp)

/-- **3l.** c_q(n) ≠ 0 ⇔ q のどの素因数 p でも p^{v_p(q) − 1} ∣ n（q ≠ 0）。 -/
theorem ramSum_ne_zero_iff {q n : ℕ} (hq : q ≠ 0) :
    ramSum n q ≠ 0 ↔ ∀ p ∈ q.primeFactors, p ^ (q.factorization p - 1) ∣ n := by
  refine ⟨fun h p hp => ?_, ramSum_ne_zero hq⟩
  rw [(isMultiplicative_ramSum n).multiplicative_factorization (ramSum n) hq, Finsupp.prod,
    Finset.prod_ne_zero_iff] at h
  have hp' := hp
  rw [← Nat.support_factorization] at hp'
  have hf := h p hp'
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hk : 1 ≤ q.factorization p := hpp.factorization_pos_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)
  by_contra hnd
  apply hf
  rw [ramSum_primePow hpp hk, ite_eq_right hnd]
  have hnk : ¬ p ^ q.factorization p ∣ n :=
    fun h' => hnd (dvd_trans (Nat.pow_dvd_pow p (Nat.sub_le _ 1)) h')
  rw [ite_eq_right hnk, sub_zero]

/-! ### 4. E_s 1 つと D_u で全行列環が出る条件：N/s が平方因子をもたない -/

/-- **4a.** q が平方因子をもたなければ c_q(u) ≠ 0（すべての u）。 -/
theorem ramSum_ne_zero_of_squarefree {q : ℕ} (hq : Squarefree q) (u : ℕ) : ramSum u q ≠ 0 := by
  apply ramSum_ne_zero (Squarefree.ne_zero hq)
  intro p _
  have h1 : q.factorization p ≤ 1 := hq.natFactorization_le_one p
  rw [show q.factorization p - 1 = 0 by omega, pow_zero]
  exact one_dvd u

/-- **4b.** N/s が平方因子をもたなければ c_{N/t}(s) ≠ 0（s, t ∣ N）。 -/
theorem ramSum_div_ne_zero {N s t : ℕ} (hN : N ≠ 0) (hs : s ∣ N) (ht : t ∣ N) (hsq : Squarefree (N / s)) :
    ramSum s (N / t) ≠ 0 := by
  have hNt : N / t ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ht)
    (Nat.pos_of_dvd_of_pos ht (Nat.pos_of_ne_zero hN))).ne'
  apply ramSum_ne_zero hNt
  intro p _
  have h1 : (N / s).factorization p ≤ 1 := hsq.natFactorization_le_one p
  rw [Nat.factorization_div hs, Finsupp.tsub_apply] at h1
  rw [Nat.factorization_div ht, Finsupp.tsub_apply]
  have hle : N.factorization p - t.factorization p - 1 ≤ s.factorization p := by omega
  exact dvd_trans (Nat.pow_dvd_pow p hle) (Nat.ordProj_dvd s p)

/-- **4c.** N/s が平方因子をもたなければ [E_s] のどの成分も 0 でない。 -/
theorem toMatrix_E_ne_zero (N : ℕ) [NeZero N] (s : N.divisors) (hsq : Squarefree (N / s)) (u t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N s), PAG.Part232.convL_geps_mem N s⟩) u t ≠ 0 := by
  rw [toMatrix_E_eq_ramMat, ramMat_eq_ramSum, ramMat_eq_ramSum]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (ramSum s (N / t) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr
    (ramSum_div_ne_zero (NeZero.ne N) (Nat.dvd_of_mem_divisors s.2) (Nat.dvd_of_mem_divisors t.2) hsq)
  have h2 : (ramSum u (N / s) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (ramSum_ne_zero_of_squarefree hsq u)
  exact div_ne_zero (mul_ne_zero h1 h2) hN

/-- D_u（u ∈ ℕ）と E_s だけが生成する部分代数。 -/
noncomputable def oneEAlg (N s : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : ℕ => LinearMap.mulLeft ℂ (dind N u)) ∪ {PAG.Part15.convL (geps N s)})

/-- **4d.** ⟨D_u, E_s⟩ ⊆ A_N。 -/
theorem oneEAlg_le (N s : ℕ) [NeZero N] : oneEAlg N s ≤ shellAlg N :=
  Algebra.adjoin_le (Set.union_subset (Set.range_subset_iff.mpr (fun u => PAG.Part232.mulLeft_dind_mem N u))
    (Set.singleton_subset_iff.mpr (PAG.Part232.convL_geps_mem N s)))

/-- E_s から作る行列単位 X_{u,t} = [E_s](u, t)⁻¹·D_u E_s D_t。 -/
noncomputable def oneETrans (N s u t : ℕ) [NeZero N] : Module.End ℂ (ZMod N → ℂ) :=
  ((N : ℂ) * geps N t (s : ZMod N) * geps N s (u : ZMod N))⁻¹ •
    (LinearMap.mulLeft ℂ (dind N u) * PAG.Part15.convL (geps N s) * LinearMap.mulLeft ℂ (dind N t))

/-- **4e.** X_{u,t} ∈ ⟨D_u, E_s⟩。 -/
theorem oneETrans_mem (N s u t : ℕ) [NeZero N] : oneETrans N s u t ∈ oneEAlg N s :=
  Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)) (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))))
    (Algebra.subset_adjoin (Or.inl ⟨t, rfl⟩))) _

/-- **4f.** [E_s](u, t) ≠ 0 なら X_{u,t} 1_{D_r} = [t = r]·1_{D_u}。 -/
theorem oneETrans_dind (N s u t r : ℕ) [NeZero N]
    (hne : (N : ℂ) * geps N t (s : ZMod N) * geps N s (u : ZMod N) ≠ 0) :
    oneETrans N s u t (dind N r) = if t = r then dind N u else 0 := by
  show ((N : ℂ) * geps N t (s : ZMod N) * geps N s (u : ZMod N))⁻¹ •
    (dind N u * PAG.Part15.conv (geps N s) (dind N t * dind N r)) = _
  rw [dind_mul]
  by_cases htr : t = r
  · rw [ite_eq_left htr, ite_eq_left htr, conv_geps_dind]
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    by_cases hx : Nat.gcd N x.val = u
    · have hd : dind N u x = 1 := by
        show (if Nat.gcd N x.val = u then (1 : ℂ) else 0) = 1
        exact ite_eq_left hx
      have hg : geps N s x = geps N s (u : ZMod N) := by
        rw [radial_apply_eq (geps_radial N s) x, hx]
      rw [hd, hg, one_mul, inv_mul_cancel₀ hne]
    · have hd : dind N u x = 0 := by
        show (if Nat.gcd N x.val = u then (1 : ℂ) else 0) = 0
        exact ite_eq_right hx
      rw [hd, zero_mul, mul_zero]
  · rw [ite_eq_right htr, ite_eq_right htr]
    have h0 : PAG.Part15.conv (geps N s) (0 : ZMod N → ℂ) = 0 := by
      funext x
      simp [PAG.Part15.conv]
    rw [h0, mul_zero, smul_zero]

/-- **4g.** [E_s](u, t) ≠ 0 なら X_{u,t} の行列は行列単位 E_{ut}。 -/
theorem toMatrix_oneETrans (N : ℕ) [NeZero N] (s u t : N.divisors)
    (hne : (N : ℂ) * geps N t (s : ZMod N) * geps N s (u : ZMod N) ≠ 0) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨oneETrans N s u t, oneEAlg_le N s (oneETrans_mem N s u t)⟩) = Matrix.single u t 1 := by
  ext v r
  rw [toMatrix_radialHom]
  show oneETrans N s u t (dind N r) ((v : ℕ) : ZMod N) = _
  rw [oneETrans_dind N s u t r hne, Matrix.single, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors v.2), ite_eq_left (Subtype.ext_iff.mp h2.1).symm]
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors v.2)]
    exact ite_eq_right (fun hvu => h2 ⟨Subtype.ext hvu.symm, Subtype.ext h1⟩)
  · exact absurd (Subtype.ext_iff.mp h2.2) h1
  · rfl

/-- **4h.** N/s が平方因子をもたなければ、D_u と E_s だけで動径関数の上の全行列環が出る。 -/
theorem radialHom_oneE_surjective (N : ℕ) [NeZero N] (s : N.divisors) (hsq : Squarefree (N / s))
    (S : Module.End ℂ (refLayer N (baseIdx N))) :
    ∃ T : shellAlg N, (T : Module.End ℂ (ZMod N → ℂ)) ∈ oneEAlg N s ∧ radialHom N T = S := by
  have hne : ∀ u t : N.divisors, (N : ℂ) * geps N t (s : ZMod N) * geps N s (u : ZMod N) ≠ 0 := by
    intro u t
    have h := toMatrix_E_ne_zero N s hsq u t
    rwa [toMatrix_E] at h
  have hX : ∀ u t : N.divisors, LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨oneETrans N s u t, oneEAlg_le N s (oneETrans_mem N s u t)⟩) = Matrix.single u t 1 :=
    fun u t => toMatrix_oneETrans N s u t (hne u t)
  refine ⟨∑ u : N.divisors, ∑ t : N.divisors, LinearMap.toMatrix (radialBasis N) (radialBasis N) S u t •
    ⟨oneETrans N s u t, oneEAlg_le N s (oneETrans_mem N s u t)⟩, ?_, ?_⟩
  · rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ (fun u _ => ?_)
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Subalgebra.sum_mem _ (fun t _ => ?_)
    rw [Subalgebra.coe_smul]
    exact Subalgebra.smul_mem _ (oneETrans_mem N s u t) _
  · apply (LinearMap.toMatrix (radialBasis N) (radialBasis N)).injective
    simp only [map_sum, map_smul, hX, Matrix.smul_single, smul_eq_mul, mul_one]
    exact (Matrix.matrix_eq_sum_single _).symm

/-- **4i.** N/s が平方因子をもつなら、⟨D_u, E_s⟩ のどの元 T でも (T 1_{D_t})(1) = 0（t ≠ 1）。 -/
theorem oneEAlg_apply_one_eq_zero (N : ℕ) [NeZero N] (s : ℕ) (hs : s ∣ N) (hsq : ¬ Squarefree (N / s))
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ oneEAlg N s) (t : ℕ) (ht : t ≠ 1) :
    T (dind N t) ((1 : ℕ) : ZMod N) = 0 := by
  have hgs : geps N s ((1 : ℕ) : ZMod N) = 0 := by
    have h := natCast_mul_geps_eq_ramSum hs 1
    rw [ramSum_one, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr (NeZero.ne N))
  unfold oneEAlg at hT
  induction hT using Algebra.adjoin_induction generalizing t with
  | mem x hx =>
    rcases hx with ⟨u, rfl⟩ | hx
    · show (dind N u * dind N t) ((1 : ℕ) : ZMod N) = 0
      rw [Pi.mul_apply, dind_natCast t (one_dvd N), ite_eq_right (Ne.symm ht), mul_zero]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      show PAG.Part15.conv (geps N s) (dind N t) ((1 : ℕ) : ZMod N) = 0
      rw [conv_geps_dind, Pi.smul_apply, hgs, smul_zero]
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, Pi.smul_apply, dind_natCast t (one_dvd N), ite_eq_right (Ne.symm ht),
      smul_zero]
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply, Pi.add_apply, hx t ht, hy t ht, add_zero]
  | mul x y _ hy' hx hy =>
    have hyR : Radial (y (dind N t)) := radial_apply_of_mem (oneEAlg_le N s hy') (dind_radial N t)
    rw [Module.End.mul_apply, radial_eq_sum hyR, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = 1
    · subst hr
      rw [hy t ht, zero_mul]
    · rw [hx r hr, mul_zero]

/-- **4j.** N/s が平方因子をもつなら、D_u と E_s では動径関数の上の全行列環は出ない。 -/
theorem not_radialHom_oneE_surjective (N : ℕ) [NeZero N] (s : N.divisors) (hsq : ¬ Squarefree (N / s)) :
    ¬ ∀ S : Module.End ℂ (refLayer N (baseIdx N)),
      ∃ T : shellAlg N, (T : Module.End ℂ (ZMod N → ℂ)) ∈ oneEAlg N s ∧ radialHom N T = S := by
  intro hall
  have hN1 : N ≠ 1 := by
    intro hN
    apply hsq
    have hs1 : (s : ℕ) = 1 := Nat.dvd_one.mp (hN ▸ Nat.dvd_of_mem_divisors s.2)
    rw [hs1, hN]
    exact squarefree_one
  have h1 : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.mpr (NeZero.ne N)
  have hNN : N ∈ N.divisors := Nat.mem_divisors_self N (NeZero.ne N)
  obtain ⟨T, hT, hS⟩ := hall ((LinearMap.toMatrix (radialBasis N) (radialBasis N)).symm
    (Matrix.single ⟨1, h1⟩ ⟨N, hNN⟩ 1))
  have key := congrArg (fun S => LinearMap.toMatrix (radialBasis N) (radialBasis N) S ⟨1, h1⟩ ⟨N, hNN⟩) hS
  simp only [LinearEquiv.apply_symm_apply, Matrix.single_apply_same, toMatrix_radialHom] at key
  rw [oneEAlg_apply_one_eq_zero N s (Nat.dvd_of_mem_divisors s.2) hsq hT N hN1] at key
  exact zero_ne_one key

/-- **4k. E_s 1 つの判定**：D_u（u ∈ ℕ）と E_s が動径関数の上の全行列環を生成する ⇔ N/s が平方因子をもたない。 -/
theorem radialHom_oneE_surjective_iff (N : ℕ) [NeZero N] (s : N.divisors) :
    (∀ S : Module.End ℂ (refLayer N (baseIdx N)),
      ∃ T : shellAlg N, (T : Module.End ℂ (ZMod N → ℂ)) ∈ oneEAlg N s ∧ radialHom N T = S) ↔
      Squarefree (N / s) := by
  constructor
  · intro h
    by_contra hsq
    exact not_radialHom_oneE_surjective N s hsq h
  · intro hsq S
    exact radialHom_oneE_surjective N s hsq S

end PAG.Part244

#print axioms PAG.Part244.card_fiber_eq
#print axioms PAG.Part244.sum_units_mul
#print axioms PAG.Part244.card_stab_mul_totient
#print axioms PAG.Part244.unitAvg
#print axioms PAG.Part244.unitAvg_apply
#print axioms PAG.Part244.shellAvg
#print axioms PAG.Part244.shellAvg_apply
#print axioms PAG.Part244.shellAvg_eq_unitAvg
#print axioms PAG.Part244.shellAvg_mem
#print axioms PAG.Part244.radialMatOp_one_eq
#print axioms PAG.Part244.shellAvg_mul_self
#print axioms PAG.Part244.radial_apply_of_mem
#print axioms PAG.Part244.commute_shellAvg
#print axioms PAG.Part244.shellAvg_mem_center
#print axioms PAG.Part244.shellAvg_mul_eq
#print axioms PAG.Part244.mul_shellAvg_eq
#print axioms PAG.Part244.shellAvg_mul_radialMatOp
#print axioms PAG.Part244.radialHom_eq_zero_iff
#print axioms PAG.Part244.radial_shellAvg_apply
#print axioms PAG.Part244.shellAvg_apply_of_radial
#print axioms PAG.Part244.dvdWeight
#print axioms PAG.Part244.dvdWeight_apply
#print axioms PAG.Part244.isMultiplicative_dvdWeight
#print axioms PAG.Part244.ramSum
#print axioms PAG.Part244.ramSum_apply
#print axioms PAG.Part244.isMultiplicative_ramSum
#print axioms PAG.Part244.natCast_mul_geps_eq_ramSum
#print axioms PAG.Part244.ramMat_eq_ramSum
#print axioms PAG.Part244.sum_divisors_primePow_moebius_int
#print axioms PAG.Part244.ramSum_primePow
#print axioms PAG.Part244.ramSum_one
#print axioms PAG.Part244.ramSum_primePow_ne_zero
#print axioms PAG.Part244.ramSum_ne_zero
#print axioms PAG.Part244.ramSum_ne_zero_iff
#print axioms PAG.Part244.ramSum_ne_zero_of_squarefree
#print axioms PAG.Part244.ramSum_div_ne_zero
#print axioms PAG.Part244.toMatrix_E_ne_zero
#print axioms PAG.Part244.oneEAlg
#print axioms PAG.Part244.oneEAlg_le
#print axioms PAG.Part244.oneETrans
#print axioms PAG.Part244.oneETrans_mem
#print axioms PAG.Part244.oneETrans_dind
#print axioms PAG.Part244.toMatrix_oneETrans
#print axioms PAG.Part244.radialHom_oneE_surjective
#print axioms PAG.Part244.oneEAlg_apply_one_eq_zero
#print axioms PAG.Part244.not_radialHom_oneE_surjective
#print axioms PAG.Part244.radialHom_oneE_surjective_iff
