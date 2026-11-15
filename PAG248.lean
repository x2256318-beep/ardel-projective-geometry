/-
  PAG 2.0 Part 244（2026-11-05）— ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ = Φ(M_d(ℂ)) + ℂ·(1 − P) ≅ M_{d(N)}(ℂ) × ℂ（N ≥ 3）
  ⟨D_u, E_N⟩（Part 240 の oneEAlg N N。Part 241 で Ψ(M, b) = Φ(M) + Σ_{t ∈ S′} b_t·Q_t の形）と、そのフーリエ双対
  ⟨E_u, D_N⟩（Part 242 の dualOneEAlg）の共通部分。P は殻の平均、1 − P は殻の平均が 0 の関数への射影。
  1. 𝓕 と P は可換：𝓕(P f) = P(𝓕 f)（Part 214 の 𝓕 U_a = U_{a⁻¹} 𝓕 と P = (1/φ(N))·Σ_a U_a）、𝓕P𝓕⁻¹ = P（fourierConj_shellAvg）
  2. 双対側の判定：X ∈ ⟨E_u, D_N⟩ なら、P f = 0 の f に X f = Σ_{t ∈ S′} c_t·E_t f（exists_apply_of_mem_dualOneEAlg）。
     とくに P h = 0 の h に X(E_1 h) = c·E_1 h（c は h によらない、exists_apply_convL_geps_one）
  3. 証拠：t ∈ S′ なら h_t = δ_t − δ_{−t} は P h_t = 0 で、(E_1 h_t)(t) = (φ(N) − c_N(2t))/N ≠ 0（N ∤ 2t）。
     共通部分の元 X = Ψ(M, b) では、点 t で b_t·(E_1 h_t)(t) = c·(E_1 h_t)(t) なので、すべての t ∈ S′ で b_t = c
  4. 主定理：X ∈ ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ ⇔ X = Φ(M) + c(1 − P)（mem_inf_iff）⇔ X = Φ(M) + c·1（mem_inf_iff_one）。
     N ≥ 3 では (M, c) ↦ Φ(M) + c(1 − P) が代数の同型 M_{d(N)}(ℂ) × ℂ ≃ 共通部分（interAlgEquiv）で、次元は d(N)² + 1。
     N ≤ 2 では共通部分 = ⟨D_u, E_N⟩（次元 d(N)²）。まとめて dim = d(N)² + [N ≥ 3]（finrank_inf_eq）
  5. 和の次元：N ≥ 3 で dim(⟨D_u, E_N⟩ + ⟨E_u, D_N⟩) + 1 = d(N)² + 2|S′|（finrank_sup_add_one）。
     共通部分はフーリエ変換で不変：𝓕(共通部分)𝓕⁻¹ = 共通部分（map_fourierConj_inf）
-/
import PAG247

namespace PAG.Part248

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246 PAG.Part247
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. フーリエ変換と殻の平均 P は可換 -/

/-- **1a.** 共役の値：(𝓕 T 𝓕⁻¹) h = 𝓕 (T (𝓕⁻¹ h))。 -/
theorem fourierConj_apply {N : ℕ} [NeZero N] (T : Module.End ℂ (ZMod N → ℂ)) (h : ZMod N → ℂ) :
    fourierConj N T h = 𝓕 (T (ZMod.dft.symm h)) := by
  rw [fourierConj, LinearEquiv.conjAlgEquiv_apply]
  rfl

/-- **1b.** 𝓕(P f) = P(𝓕 f)（P は単数倍の平均 (1/φ(N))·Σ_a U_a、Part 214 の 𝓕 U_a = U_{a⁻¹} 𝓕）。 -/
theorem dft_shellAvg {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : 𝓕 (shellAvg N f) = shellAvg N (𝓕 f) := by
  rw [shellAvg_eq_unitAvg, unitAvg, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  simp only [dft_dil]
  exact Fintype.sum_equiv (Equiv.inv (ZMod N)ˣ) _ _ (fun a => rfl)

/-- **1c.** 𝓕⁻¹(P f) = P(𝓕⁻¹ f)。 -/
theorem dft_symm_shellAvg {N : ℕ} [NeZero N] (f : ZMod N → ℂ) :
    ZMod.dft.symm (shellAvg N f) = shellAvg N (ZMod.dft.symm f) := by
  apply (ZMod.dft : (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod N → ℂ)).injective
  rw [LinearEquiv.apply_symm_apply, dft_shellAvg, LinearEquiv.apply_symm_apply]

/-- **1d.** 𝓕 P 𝓕⁻¹ = P。 -/
theorem fourierConj_shellAvg (N : ℕ) [NeZero N] : fourierConj N (shellAvg N) = shellAvg N := by
  apply LinearMap.ext
  intro h
  rw [fourierConj_apply, dft_shellAvg, LinearEquiv.apply_symm_apply]

/-- **1e.** P h = 0 なら P(𝓕⁻¹ h) = 0（𝓕⁻¹ は殻の平均が 0 の関数の空間を保つ）。 -/
theorem shellAvg_dft_symm_eq_zero {N : ℕ} [NeZero N] {h : ZMod N → ℂ} (hh : shellAvg N h = 0) :
    shellAvg N (ZMod.dft.symm h) = 0 := by
  rw [← dft_symm_shellAvg, hh, map_zero]

/-! ### 2. D_t・E_s は P と可換（関数の水準） -/

/-- **2a.** P(1_{D_t}·g) = 1_{D_t}·P g。 -/
theorem shellAvg_dind_mul {N : ℕ} [NeZero N] (t : ℕ) (g : ZMod N → ℂ) :
    shellAvg N (dind N t * g) = dind N t * shellAvg N g := by
  have h := congrArg (fun T => T g) (commute_shellAvg N (PAG.Part232.mulLeft_dind_mem N t))
  simp only [Module.End.mul_apply, LinearMap.mulLeft_apply] at h
  exact h.symm

/-- **2b.** P(E_s h) = E_s(P h)。 -/
theorem shellAvg_convL_geps {N : ℕ} [NeZero N] (s : ℕ) (h : ZMod N → ℂ) :
    shellAvg N (PAG.Part15.convL (geps N s) h) = PAG.Part15.convL (geps N s) (shellAvg N h) := by
  have e := congrArg (fun T => T h) (commute_shellAvg N (PAG.Part232.convL_geps_mem N s))
  simp only [Module.End.mul_apply] at e
  exact e.symm

/-! ### 3. ⟨E_u, D_N⟩ の元は、E_1 の像（殻の平均が 0 の部分）に定数として働く -/

/-- **3a.** X ∈ ⟨E_u, D_N⟩ なら、ある c があって、P h = 0 のどの h にも X(E_1 h) = c·E_1 h。 -/
theorem exists_apply_convL_geps_one {N : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)}
    (hX : X ∈ dualOneEAlg N) : ∃ c : ℂ, ∀ h : ZMod N → ℂ, shellAvg N h = 0 →
      X (PAG.Part15.convL (geps N 1) h) = c • PAG.Part15.convL (geps N 1) h := by
  rw [← map_fourierConj_oneEAlg] at hX
  obtain ⟨Y, hY, hYX⟩ := Subalgebra.mem_map.mp hX
  have hYX' : fourierConj N Y = X := hYX
  obtain ⟨b, hb⟩ := exists_apply_of_mem_oneEAlg hY
  refine ⟨∑ t : devSet N, if (t : ℕ) = 1 then b t else 0, fun h hh => ?_⟩
  have hE : ∀ g : ZMod N → ℂ, PAG.Part15.convL (geps N 1) g = 𝓕 (dind N 1 * ZMod.dft.symm g) := by
    intro g
    rw [← fourierConj_mulLeft_dind, fourierConj_apply, LinearMap.mulLeft_apply]
  have hg : shellAvg N (dind N 1 * ZMod.dft.symm h) = 0 := by
    rw [shellAvg_dind_mul, shellAvg_dft_symm_eq_zero hh, mul_zero]
  have key : ∑ t : devSet N, b t • (dind N (t : ℕ) * (dind N 1 * ZMod.dft.symm h)) =
      (∑ t : devSet N, if (t : ℕ) = 1 then b t else 0) • (dind N 1 * ZMod.dft.symm h) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← mul_assoc, dind_mul]
    by_cases ht : (t : ℕ) = 1
    · rw [ite_eq_left ht, ite_eq_left ht, ht]
    · rw [ite_eq_right ht, ite_eq_right ht, zero_mul, smul_zero, zero_smul]
  rw [← hYX', fourierConj_apply, hE h, LinearEquiv.symm_apply_apply, hb _ hg, key, map_smul]

/-- **3b.** X ∈ ⟨E_u, D_N⟩ なら、ある c : S′ → ℂ で、P f = 0 のどの f にも X f = Σ_{t ∈ S′} c_t·E_t f
（Part 243 の exists_apply_of_mem_oneEAlg のフーリエ双対）。 -/
theorem exists_apply_of_mem_dualOneEAlg {N : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)}
    (hX : X ∈ dualOneEAlg N) : ∃ c : devSet N → ℂ, ∀ f : ZMod N → ℂ, shellAvg N f = 0 →
      X f = ∑ t : devSet N, c t • PAG.Part15.convL (geps N t) f := by
  rw [← map_fourierConj_oneEAlg] at hX
  obtain ⟨Y, hY, hYX⟩ := Subalgebra.mem_map.mp hX
  have hYX' : fourierConj N Y = X := hYX
  obtain ⟨b, hb⟩ := exists_apply_of_mem_oneEAlg hY
  refine ⟨b, fun f hf => ?_⟩
  rw [← hYX', fourierConj_apply, hb _ (shellAvg_dft_symm_eq_zero hf), map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [map_smul, ← fourierConj_mulLeft_dind, fourierConj_apply, LinearMap.mulLeft_apply]

/-! ### 4. 証拠の関数 h_a = δ_a − δ_{−a} -/

/-- 試しの関数 h_a = δ_a − δ_{−a}（Part 243 の testFn は a = 1）。 -/
noncomputable def pairFn (N : ℕ) (a : ZMod N) : ZMod N → ℂ := Pi.single a (1 : ℂ) - Pi.single (-a) (1 : ℂ)

/-- **4a.** P(δ_a − δ_{−a}) = 0（a と −a は同じ殻）。 -/
theorem shellAvg_pairFn (N : ℕ) [NeZero N] (a : ZMod N) : shellAvg N (pairFn N a) = 0 := by
  funext x
  rw [shellAvg_apply, Pi.zero_apply]
  have h : ∑ y, dind N (Nat.gcd N x.val) y * pairFn N a y = 0 := by
    simp only [pairFn, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sum_mul_single]
    have hr := dind_radial N (Nat.gcd N x.val) (-1 : (ZMod N)ˣ) a
    simp only [Units.val_neg, Units.val_one, neg_mul, one_mul] at hr
    rw [hr, sub_self]
  rw [h, zero_div]

/-- **4b.** (E_s h_a)(a) = ε_s(0) − ε_s(a + a)。 -/
theorem convL_geps_pairFn_apply (N s : ℕ) [NeZero N] (a : ZMod N) :
    PAG.Part15.convL (geps N s) (pairFn N a) a = geps N s 0 - geps N s (a + a) := by
  have h : PAG.Part15.convL (geps N s) (pairFn N a) =
      PAG.Part15.conv (geps N s) (Pi.single a (1 : ℂ)) - PAG.Part15.conv (geps N s) (Pi.single (-a) (1 : ℂ)) := by
    show PAG.Part15.convL (geps N s) (pairFn N a) =
      PAG.Part15.convL (geps N s) (Pi.single a (1 : ℂ)) - PAG.Part15.convL (geps N s) (Pi.single (-a) (1 : ℂ))
    rw [pairFn, map_sub]
  rw [h, Pi.sub_apply, conv_single_apply, conv_single_apply, sub_self, sub_neg_eq_add]

/-- **4c.** t ∣ N、φ(N/t) ≠ 1 なら N ∤ 2t（とくに −t ≢ t（法 N））。 -/
theorem not_dvd_two_mul {N t : ℕ} [NeZero N] (ht : t ∣ N) (hφ : Nat.totient (N / t) ≠ 1) : ¬ N ∣ 2 * t := by
  intro hd
  have hq3 := three_le_div ht hφ
  obtain ⟨q, hq⟩ := ht
  have ht0 : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hq; exact NeZero.ne N hq)
  rw [hq, Nat.mul_div_cancel_left q ht0] at hq3
  rw [hq, mul_comm 2 t] at hd
  have h2 : q ∣ 2 := Nat.dvd_of_mul_dvd_mul_left ht0 hd
  have := Nat.le_of_dvd two_pos h2
  omega

/-- **4d.** t ∣ N、φ(N/t) ≠ 1 なら (E_1 h_t)(t) ≠ 0（値は (φ(N) − c_N(2t))/N）。 -/
theorem convL_geps_one_pairFn_ne_zero {N t : ℕ} [NeZero N] (ht : t ∣ N) (hφ : Nat.totient (N / t) ≠ 1) :
    PAG.Part15.convL (geps N 1) (pairFn N (t : ZMod N)) (t : ZMod N) ≠ 0 := by
  rw [convL_geps_pairFn_apply]
  intro h
  have h' : (N : ℂ) * geps N 1 ((0 : ℕ) : ZMod N) = (N : ℂ) * geps N 1 ((2 * t : ℕ) : ZMod N) := by
    have e1 : ((0 : ℕ) : ZMod N) = 0 := Nat.cast_zero
    have e2 : ((2 * t : ℕ) : ZMod N) = (t : ZMod N) + (t : ZMod N) := by
      push_cast
      ring
    rw [e1, e2, sub_eq_zero.mp h]
  rw [natCast_mul_geps_eq_ramSum (one_dvd N), natCast_mul_geps_eq_ramSum (one_dvd N), Nat.div_one,
    ramSum_of_dvd (dvd_zero N)] at h'
  have h2 : ramSum (2 * t) N = (Nat.totient N : ℤ) := by exact_mod_cast h'.symm
  exact not_dvd_two_mul ht hφ ((ramSum_eq_totient_iff (NeZero.ne N) (2 * t)).mp h2)

/-! ### 5. 共通部分 ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ = {Φ(M) + c(1 − P)} -/

/-- **5a.** Φ(M)·P = Φ(M)。 -/
theorem radialMatOp_mul_shellAvg (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M * shellAvg N = radialMatOp N M := by
  rw [← radialMatOp_one_eq, ← radialMatOp_mul, mul_one]

/-- **5b.** P ∈ ⟨E_u, D_N⟩。 -/
theorem shellAvg_mem_dualOneEAlg (N : ℕ) [NeZero N] : shellAvg N ∈ dualOneEAlg N := by
  rw [← map_fourierConj_oneEAlg]
  refine Subalgebra.mem_map.mpr ⟨shellAvg N, ?_, fourierConj_shellAvg N⟩
  rw [← radialMatOp_one_eq]
  exact radialMatOp_mem_oneEAlg N 1

/-- **5c.** Φ(M) ∈ ⟨E_u, D_N⟩（𝓕⁻¹Φ(M)𝓕 は A_N の元で、右から P を掛けても変わらないので Φ の形）。 -/
theorem radialMatOp_mem_dualOneEAlg (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M ∈ dualOneEAlg N := by
  have hA : radialMatOp N M ∈ shellAlg N := oneEAlg_le N N (radialMatOp_mem_oneEAlg N M)
  rw [← map_fourierConj_shellAlg] at hA
  obtain ⟨T, hT, hTM⟩ := Subalgebra.mem_map.mp hA
  have hTM' : fourierConj N T = radialMatOp N M := hTM
  have hTP : T * shellAvg N = T := by
    apply (fourierConj N).injective
    rw [map_mul, fourierConj_shellAvg, hTM', radialMatOp_mul_shellAvg]
  have hT' : T ∈ oneEAlg N N := by
    have e : T * shellAvg N =
        radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N ⟨T, hT⟩)) :=
      mul_shellAvg_eq N ⟨T, hT⟩
    rw [← hTP, e]
    exact radialMatOp_mem_oneEAlg N _
  rw [← map_fourierConj_oneEAlg]
  exact Subalgebra.mem_map.mpr ⟨T, hT', hTM⟩

/-- **5d.** Φ(M) + c(1 − P) ∈ ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩。 -/
theorem radialMatOp_add_smul_mem_inf (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) (c : ℂ) :
    radialMatOp N M + c • (1 - shellAvg N) ∈ oneEAlg N N ⊓ dualOneEAlg N := by
  have hP1 : shellAvg N ∈ oneEAlg N N := by
    rw [← radialMatOp_one_eq]
    exact radialMatOp_mem_oneEAlg N 1
  refine Algebra.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subalgebra.add_mem _ (radialMatOp_mem_oneEAlg N M)
      (Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hP1) c)
  · exact Subalgebra.add_mem _ (radialMatOp_mem_dualOneEAlg N M)
      (Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _) (shellAvg_mem_dualOneEAlg N)) c)

/-- **5e.** Σ_{s ∈ S′} c·Q_s = c(1 − P)。 -/
theorem sum_smul_shellDev (N : ℕ) [NeZero N] (c : ℂ) :
    ∑ s : devSet N, c • shellDev N s = c • (1 - shellAvg N) := by
  rw [← Finset.smul_sum, ← shellAvg_add_sum_shellDev N, add_sub_cancel_left]

/-- **5f.** 主定理：X ∈ ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ ⇔ ある M、c で X = Φ(M) + c(1 − P)。 -/
theorem mem_inf_iff {N : ℕ} [NeZero N] (X : Module.End ℂ (ZMod N → ℂ)) :
    X ∈ oneEAlg N N ⊓ dualOneEAlg N ↔
      ∃ (M : Matrix N.divisors N.divisors ℂ) (c : ℂ), X = radialMatOp N M + c • (1 - shellAvg N) := by
  constructor
  · intro hX
    obtain ⟨h1, h2⟩ := Algebra.mem_inf.mp hX
    obtain ⟨c, hc⟩ := exists_apply_convL_geps_one h2
    rw [← range_wholeHom] at h1
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp h1
    refine ⟨p.1, c, ?_⟩
    have hb : ∀ t : devSet N, p.2 t = c := by
      intro t
      have ht := dvd_of_mem_devSet t
      have hφ : Nat.totient (N / t) ≠ 1 := by
        have h2 : (t : ℕ) ∈ N.divisors.filter (fun s => Nat.totient (N / s) ≠ 1) := t.2
        exact (Finset.mem_filter.mp h2).2
      have hPh := shellAvg_pairFn N ((t : ℕ) : ZMod N)
      have hPg : shellAvg N (PAG.Part15.convL (geps N 1) (pairFn N ((t : ℕ) : ZMod N))) = 0 := by
        rw [shellAvg_convL_geps, hPh, map_zero]
      have e1 : wholeHom N p (PAG.Part15.convL (geps N 1) (pairFn N ((t : ℕ) : ZMod N))) =
          ∑ s : devSet N, p.2 s • (dind N s * PAG.Part15.convL (geps N 1) (pairFn N ((t : ℕ) : ZMod N))) := by
        rw [wholeHom_apply, wholeMap_apply, LinearMap.add_apply, radialMatOp_apply_eq_zero p.1 hPg, zero_add,
          LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [LinearMap.smul_apply, shellDev_apply_of_shellAvg_eq_zero (dvd_of_mem_devSet s) hPg]
      have e2 := congrFun (e1.symm.trans (hc _ hPh)) ((t : ℕ) : ZMod N)
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e2
      rw [Finset.sum_eq_single t] at e2
      · rw [dind_self N t ht, one_mul] at e2
        exact mul_right_cancel₀ (convL_geps_one_pairFn_ne_zero ht hφ) e2
      · intro s _ hs
        have hne : (s : ℕ) ≠ (t : ℕ) := fun e => hs (Subtype.ext e)
        have hd : dind N (s : ℕ) ((t : ℕ) : ZMod N) = 0 := by
          show (if Nat.gcd N ((t : ℕ) : ZMod N).val = (s : ℕ) then (1 : ℂ) else 0) = 0
          rw [gcd_natCast_self N t ht]
          exact ite_eq_right (fun e => hne e.symm)
        rw [hd, zero_mul, mul_zero]
      · intro hnot
        exact absurd (Finset.mem_univ t) hnot
    rw [wholeHom_apply, wholeMap_apply, ← sum_smul_shellDev]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => by rw [hb s])
  · rintro ⟨M, c, rfl⟩
    exact radialMatOp_add_smul_mem_inf N M c

/-- **5f′.** 言い換え：X ∈ ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ ⇔ ある M、c で X = Φ(M) + c·1（共通部分 = Φ(M_d(ℂ)) + ℂ·1）。 -/
theorem mem_inf_iff_one {N : ℕ} [NeZero N] (X : Module.End ℂ (ZMod N → ℂ)) :
    X ∈ oneEAlg N N ⊓ dualOneEAlg N ↔
      ∃ (M : Matrix N.divisors N.divisors ℂ) (c : ℂ), X = radialMatOp N M + c • 1 := by
  rw [mem_inf_iff]
  constructor
  · rintro ⟨M, c, rfl⟩
    refine ⟨M - c • 1, c, ?_⟩
    have h : radialMatOp N M = radialMatOp N (M - c • 1) + c • shellAvg N := by
      rw [← radialMatOp_one_eq, ← radialMatOp_smul, ← radialMatOp_add, sub_add_cancel]
    rw [h, smul_sub]
    abel
  · rintro ⟨M, c, rfl⟩
    refine ⟨M + c • 1, c, ?_⟩
    rw [radialMatOp_add, radialMatOp_smul, radialMatOp_one_eq, smul_sub]
    abel

/-- **5g.** N ≥ 3 なら 1 ∈ S′。 -/
theorem one_mem_devSet {N : ℕ} [NeZero N] (hN : 3 ≤ N) : 1 ∈ devSet N := by
  rw [devSet, Finset.mem_filter, Nat.div_one]
  refine ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), ?_⟩
  rw [Ne, Nat.totient_eq_one_iff]
  omega

/-- (M, c) ↦ (M, (c, …, c)) ↦ Φ(M) + c(1 − P)（Part 241 の wholeHom を対角の部分に制限）。 -/
noncomputable def interHom (N : ℕ) [NeZero N] :
    (Matrix N.divisors N.divisors ℂ × ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  (wholeHom N).comp ((AlgHom.id ℂ (Matrix N.divisors N.divisors ℂ)).prodMap (Algebra.ofId ℂ (devSet N → ℂ)))

/-- **5h.** interHom (M, c) = Φ(M) + c(1 − P)。 -/
theorem interHom_apply (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) (c : ℂ) :
    interHom N (M, c) = radialMatOp N M + c • (1 - shellAvg N) := by
  show wholeMap N (M, algebraMap ℂ (devSet N → ℂ) c) = _
  rw [wholeMap_apply, ← sum_smul_shellDev]
  rfl

/-- **5i.** interHom の像は共通部分。 -/
theorem range_interHom (N : ℕ) [NeZero N] : (interHom N).range = oneEAlg N N ⊓ dualOneEAlg N := by
  ext X
  rw [AlgHom.mem_range, mem_inf_iff]
  constructor
  · rintro ⟨⟨M, c⟩, rfl⟩
    exact ⟨M, c, interHom_apply N M c⟩
  · rintro ⟨M, c, rfl⟩
    exact ⟨(M, c), interHom_apply N M c⟩

/-- **5j.** N ≥ 3 なら interHom は単射。 -/
theorem interHom_injective {N : ℕ} [NeZero N] (hN : 3 ≤ N) : Function.Injective (interHom N) := by
  intro x y hxy
  have h : ((x.1, algebraMap ℂ (devSet N → ℂ) x.2) : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) =
      (y.1, algebraMap ℂ (devSet N → ℂ) y.2) := wholeMap_injective N hxy
  have h1 := congrArg Prod.fst h
  have h2 := congrFun (congrArg Prod.snd h) ⟨1, one_mem_devSet hN⟩
  have h1' : x.1 = y.1 := h1
  have h2' : x.2 = y.2 := h2
  exact Prod.ext h1' h2'

/-- 共通部分 ≅ M_{d(N)}(ℂ) × ℂ（N ≥ 3）。 -/
noncomputable def interAlgEquiv {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (Matrix N.divisors N.divisors ℂ × ℂ) ≃ₐ[ℂ] ↥(oneEAlg N N ⊓ dualOneEAlg N) :=
  (AlgEquiv.ofInjective (interHom N) (interHom_injective hN)).trans (Subalgebra.equivOfEq _ _ (range_interHom N))

/-- **5k.** interAlgEquiv (M, c) = Φ(M) + c(1 − P)。 -/
theorem interAlgEquiv_apply {N : ℕ} [NeZero N] (hN : 3 ≤ N) (M : Matrix N.divisors N.divisors ℂ) (c : ℂ) :
    (interAlgEquiv hN (M, c) : Module.End ℂ (ZMod N → ℂ)) = radialMatOp N M + c • (1 - shellAvg N) :=
  interHom_apply N M c

/-- **5l.** dim(⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩) = d(N)² + 1（N ≥ 3）。 -/
theorem finrank_inf {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    Module.finrank ℂ ↥(oneEAlg N N ⊓ dualOneEAlg N) = N.divisors.card ^ 2 + 1 := by
  rw [← (interAlgEquiv hN).toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_coe]
  ring

/-- **5m.** N ≤ 2 なら、どの約数 s でも φ(N/s) = 1（S′ は空）。 -/
theorem totient_div_eq_one_of_le_two {N s : ℕ} [NeZero N] (hN : N ≤ 2) (hs : s ∣ N) :
    Nat.totient (N / s) = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hpos : 0 < N / s := Nat.div_pos (Nat.le_of_dvd hN0 hs) (Nat.pos_of_dvd_of_pos hs hN0)
  have hle : N / s ≤ 2 := le_trans (Nat.div_le_self N s) hN
  rw [Nat.totient_eq_one_iff]
  omega

/-- **5n.** N ≤ 2 なら ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ = ⟨D_u, E_N⟩（Q_s の項がない）。 -/
theorem inf_eq_oneEAlg_of_le_two {N : ℕ} [NeZero N] (hN : N ≤ 2) :
    oneEAlg N N ⊓ dualOneEAlg N = oneEAlg N N := by
  apply le_antisymm inf_le_left
  intro X hX
  refine Algebra.mem_inf.mpr ⟨hX, ?_⟩
  rw [← range_wholeHom] at hX
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hX
  have hs : ∑ s : devSet N, p.2 s • shellDev N s = 0 := by
    refine Finset.sum_eq_zero (fun s _ => ?_)
    have h2 : (s : ℕ) ∈ N.divisors.filter (fun s => Nat.totient (N / s) ≠ 1) := s.2
    obtain ⟨hs1, hs2⟩ := Finset.mem_filter.mp h2
    exact absurd (totient_div_eq_one_of_le_two hN (Nat.dvd_of_mem_divisors hs1)) hs2
  rw [wholeHom_apply, wholeMap_apply, hs, add_zero]
  exact radialMatOp_mem_dualOneEAlg N p.1

/-- **5o.** dim(⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩) = d(N)² + [N ≥ 3]（すべての N）。 -/
theorem finrank_inf_eq (N : ℕ) [NeZero N] :
    Module.finrank ℂ ↥(oneEAlg N N ⊓ dualOneEAlg N) = N.divisors.card ^ 2 + (if 3 ≤ N then 1 else 0) := by
  by_cases hN : 3 ≤ N
  · rw [finrank_inf hN, ite_eq_left hN]
  · have hN2 : N ≤ 2 := by omega
    have hcard : (devSet N).card = 0 := by
      rw [Finset.card_eq_zero]
      show N.divisors.filter (fun s => Nat.totient (N / s) ≠ 1) = ∅
      rw [Finset.filter_eq_empty_iff]
      intro s hs
      exact not_not.mpr (totient_div_eq_one_of_le_two hN2 (Nat.dvd_of_mem_divisors hs))
    rw [inf_eq_oneEAlg_of_le_two hN2, finrank_oneEAlg_self, ite_eq_right hN, hcard]

/-! ### 6. 和の次元とフーリエ変換での不変性 -/

/-- **6a.** 部分代数の共通部分の部分空間は、部分空間の共通部分。 -/
theorem toSubmodule_inf {N : ℕ} (S T : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ))) :
    Subalgebra.toSubmodule (S ⊓ T) = Subalgebra.toSubmodule S ⊓ Subalgebra.toSubmodule T := by
  ext X
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_inf, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
    Subalgebra.mem_toSubmodule]

/-- **6b.** dim(⟨D_u, E_N⟩ + ⟨E_u, D_N⟩) + dim(⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩) = 2·dim ⟨D_u, E_N⟩。 -/
theorem finrank_sup_add_finrank_inf (N : ℕ) [NeZero N] :
    Module.finrank ℂ ↥(Subalgebra.toSubmodule (oneEAlg N N) ⊔ Subalgebra.toSubmodule (dualOneEAlg N)) +
      Module.finrank ℂ ↥(oneEAlg N N ⊓ dualOneEAlg N) = 2 * Module.finrank ℂ ↥(oneEAlg N N) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (Subalgebra.toSubmodule (oneEAlg N N))
    (Subalgebra.toSubmodule (dualOneEAlg N))
  rw [← toSubmodule_inf] at h
  have e1 : Module.finrank ℂ ↥(Subalgebra.toSubmodule (oneEAlg N N ⊓ dualOneEAlg N)) =
      Module.finrank ℂ ↥(oneEAlg N N ⊓ dualOneEAlg N) := rfl
  have e2 : Module.finrank ℂ ↥(Subalgebra.toSubmodule (oneEAlg N N)) = Module.finrank ℂ ↥(oneEAlg N N) := rfl
  have e3 : Module.finrank ℂ ↥(Subalgebra.toSubmodule (dualOneEAlg N)) = Module.finrank ℂ ↥(dualOneEAlg N) := rfl
  rw [e1, e2, e3, finrank_dualOneEAlg] at h
  rw [h]
  ring

/-- **6c.** N ≥ 3 なら dim(⟨D_u, E_N⟩ + ⟨E_u, D_N⟩) + 1 = d(N)² + 2|S′|。 -/
theorem finrank_sup_add_one {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    Module.finrank ℂ ↥(Subalgebra.toSubmodule (oneEAlg N N) ⊔ Subalgebra.toSubmodule (dualOneEAlg N)) + 1 =
      N.divisors.card ^ 2 + 2 * (devSet N).card := by
  have h := finrank_sup_add_finrank_inf N
  rw [finrank_inf hN, finrank_oneEAlg_self] at h
  generalize N.divisors.card ^ 2 = D at h ⊢
  omega

/-- **6d.** 𝓕 Φ(M) 𝓕⁻¹ は ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩ に入る。 -/
theorem fourierConj_radialMatOp_mem_inf (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    fourierConj N (radialMatOp N M) ∈ oneEAlg N N ⊓ dualOneEAlg N := by
  have hA : fourierConj N (radialMatOp N M) ∈ shellAlg N := by
    rw [← map_fourierConj_shellAlg]
    exact Subalgebra.mem_map.mpr ⟨radialMatOp N M, oneEAlg_le N N (radialMatOp_mem_oneEAlg N M), rfl⟩
  have hTP : fourierConj N (radialMatOp N M) * shellAvg N = fourierConj N (radialMatOp N M) := by
    rw [← fourierConj_shellAvg, ← map_mul, radialMatOp_mul_shellAvg]
  refine Algebra.mem_inf.mpr ⟨?_, ?_⟩
  · have e : fourierConj N (radialMatOp N M) * shellAvg N =
        radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N ⟨_, hA⟩)) :=
      mul_shellAvg_eq N ⟨_, hA⟩
    rw [← hTP, e]
    exact radialMatOp_mem_oneEAlg N _
  · rw [← map_fourierConj_oneEAlg]
    exact Subalgebra.mem_map.mpr ⟨radialMatOp N M, radialMatOp_mem_oneEAlg N M, rfl⟩

/-- **6e.** 𝓕 (⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩) 𝓕⁻¹ = ⟨D_u, E_N⟩ ∩ ⟨E_u, D_N⟩。 -/
theorem map_fourierConj_inf (N : ℕ) [NeZero N] :
    (oneEAlg N N ⊓ dualOneEAlg N).map (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) =
      oneEAlg N N ⊓ dualOneEAlg N := by
  have hle : (oneEAlg N N ⊓ dualOneEAlg N).map
      (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ≤ oneEAlg N N ⊓ dualOneEAlg N := by
    intro Y hY
    obtain ⟨X, hX, hXY⟩ := Subalgebra.mem_map.mp hY
    have hXY' : fourierConj N X = Y := hXY
    obtain ⟨M, c, rfl⟩ := (mem_inf_iff X).mp hX
    rw [← hXY', map_add, map_smul, map_sub, map_one, fourierConj_shellAvg]
    have hP1 : (1 : Module.End ℂ (ZMod N → ℂ)) - shellAvg N ∈ oneEAlg N N ⊓ dualOneEAlg N := by
      have e := radialMatOp_add_smul_mem_inf N 0 1
      have h0 : radialMatOp N 0 = 0 := by
        simp only [radialMatOp, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]
      rw [h0, zero_add, one_smul] at e
      exact e
    exact Subalgebra.add_mem _ (fourierConj_radialMatOp_mem_inf N M) (Subalgebra.smul_mem _ hP1 c)
  apply Subalgebra.toSubmodule_injective
  apply Submodule.eq_of_le_of_finrank_eq (Subalgebra.toSubmodule.monotone hle)
  exact ((fourierConj N).subalgebraMap (oneEAlg N N ⊓ dualOneEAlg N)).toLinearEquiv.finrank_eq.symm

end PAG.Part248

#print axioms PAG.Part248.fourierConj_apply
#print axioms PAG.Part248.dft_shellAvg
#print axioms PAG.Part248.dft_symm_shellAvg
#print axioms PAG.Part248.fourierConj_shellAvg
#print axioms PAG.Part248.shellAvg_dft_symm_eq_zero
#print axioms PAG.Part248.shellAvg_dind_mul
#print axioms PAG.Part248.shellAvg_convL_geps
#print axioms PAG.Part248.exists_apply_convL_geps_one
#print axioms PAG.Part248.exists_apply_of_mem_dualOneEAlg
#print axioms PAG.Part248.pairFn
#print axioms PAG.Part248.shellAvg_pairFn
#print axioms PAG.Part248.convL_geps_pairFn_apply
#print axioms PAG.Part248.not_dvd_two_mul
#print axioms PAG.Part248.convL_geps_one_pairFn_ne_zero
#print axioms PAG.Part248.radialMatOp_mul_shellAvg
#print axioms PAG.Part248.shellAvg_mem_dualOneEAlg
#print axioms PAG.Part248.radialMatOp_mem_dualOneEAlg
#print axioms PAG.Part248.radialMatOp_add_smul_mem_inf
#print axioms PAG.Part248.sum_smul_shellDev
#print axioms PAG.Part248.mem_inf_iff
#print axioms PAG.Part248.mem_inf_iff_one
#print axioms PAG.Part248.one_mem_devSet
#print axioms PAG.Part248.interHom
#print axioms PAG.Part248.interHom_apply
#print axioms PAG.Part248.range_interHom
#print axioms PAG.Part248.interHom_injective
#print axioms PAG.Part248.interAlgEquiv
#print axioms PAG.Part248.interAlgEquiv_apply
#print axioms PAG.Part248.finrank_inf
#print axioms PAG.Part248.totient_div_eq_one_of_le_two
#print axioms PAG.Part248.inf_eq_oneEAlg_of_le_two
#print axioms PAG.Part248.finrank_inf_eq
#print axioms PAG.Part248.toSubmodule_inf
#print axioms PAG.Part248.finrank_sup_add_finrank_inf
#print axioms PAG.Part248.finrank_sup_add_one
#print axioms PAG.Part248.fourierConj_radialMatOp_mem_inf
#print axioms PAG.Part248.map_fourierConj_inf
