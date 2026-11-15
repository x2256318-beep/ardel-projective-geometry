/-
  PAG 2.0 Part 239（2026-11-05）— 動径関数の空間の上の A の具体的な形：E_s・D_s・𝓕 の行列と、A の中の行列単位
  Part 238 で、A_N は動径関数の空間 W_{p₀}（dim d(N)）に全行列環として作用することを示した（radialHom_surjective）。
  ここでは殻の指示関数の基底 (1_{D_t})_{t ∣ N} で作用を具体的な行列に書き、全行列環が出ることを直接示す。
  1. 基底（radialBasis、座標は値 f(t)：radialCoord）。radialHom T の行列の成分は (T 1_{D_t})(u)（toMatrix_radialHom）
  2. D_s の行列は行列単位 E_{ss}（toMatrix_D）、E_s の行列は N·ε_t(s)·ε_s(u)（列と行の積、toMatrix_E）、
     E_N は定数への射影で、行列の成分は φ(N/t)/N（どれも 0 でない、toMatrix_E_self）
  3. 殻の移し替え P_{s,t} = (N/φ(N/t))·D_s E_N D_t ∈ A_N（shellTrans）：P_{s,t} f = (D_t の上の f の平均)·1_{D_s}、
     P_{s,t} P_{t′,r} = [t = t′]·P_{s,r}（A_N の中の行列単位）。M ↦ Σ M_{st} P_{s,t} は単射な非単位的代数準同型
     M_{d(N)}(ℂ) → A_N（radialMatHom）で、radialHom との合成は行列 ↦ End の同型。明示的な原像（radialSection）。
     D_s と E_N だけで、動径関数の上の全行列環が出る（radialHom_diagAvg_surjective）
  4. 𝓕 の行列はラマヌジャンの行列 C(u, t) = N·ε_t(u) = Σ_{e ∣ N/t} μ(e)·(N/(te))·[N/(te) ∣ u]
     （toMatrix_radialDFT・ramMat_apply）。C² = N·1（ramMat_mul_self）、C·[E_s] = [D_s]·C、[E_s](u, t) = C(s, t)·C(u, s)/N
  5. 素冪：C(q^i, q^j) = 1（j = k）、q^{k−j}·[k−j ≤ i] − q^{k−j−1}·[k−j−1 ≤ i]（j < k）（ramMat_primePow）。
     互いに素な a, b で C_{ab}(u_a u_b, t_a t_b) = C_a(u_a, t_a)·C_b(u_b, t_b)（クロネッカー積、ramMat_mul_coprime）
-/
import PAG242

namespace PAG.Part243

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 動径関数の座標と、殻の指示関数の基底 -/

/-- **1a.** u ∣ N なら gcd(N, (u : ℤ/N).val) = u（u は殻 D_u の点）。 -/
theorem gcd_val_natCast_of_dvd {N u : ℕ} (hu : u ∣ N) : Nat.gcd N (u : ZMod N).val = u := by
  rw [ZMod.val_natCast, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_eq_right hu]

/-- **1b.** u ∣ N なら 1_{D_t}(u) = [u = t]。 -/
theorem dind_natCast {N u : ℕ} (t : ℕ) (hu : u ∣ N) : dind N t (u : ZMod N) = if u = t then 1 else 0 := by
  show (if Nat.gcd N (u : ZMod N).val = t then (1 : ℂ) else 0) = _
  rw [gcd_val_natCast_of_dvd hu]

/-- **1c.** 動径関数は殻ごとに一定：f(ξ) = f(gcd(N, ξ))。 -/
theorem radial_apply_eq {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) (ξ : ZMod N) :
    f ξ = f ((Nat.gcd N ξ.val : ℕ) : ZMod N) := by
  obtain ⟨a, ha⟩ := exists_unit_mul_gcd N ξ
  conv_lhs => rw [← ha]
  exact hf a _

/-- **1d.** 動径関数は殻の指示関数の一次結合：f = Σ_{t ∣ N} f(t)·1_{D_t}。 -/
theorem radial_eq_sum {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) :
    f = ∑ t ∈ N.divisors, f (t : ZMod N) • dind N t := by
  funext ξ
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, dind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left N ξ.val, NeZero.ne N⟩)]
  exact radial_apply_eq hf ξ

/-- **1e.** 1_{D_t} は動径関数の空間 W_{p₀}（Part 238）の元。 -/
theorem dind_mem_base (N : ℕ) [NeZero N] (t : ℕ) : dind N t ∈ refLayer N (baseIdx N) :=
  (mem_refLayer_base_iff N _).mpr (dind_radial N t)

/-- 動径関数の座標：W_{p₀} ≅ ℂ^{約数}、f ↦ (f(t))_{t ∣ N}。逆は c ↦ Σ_t c_t·1_{D_t}。 -/
noncomputable def radialCoord (N : ℕ) [NeZero N] : refLayer N (baseIdx N) ≃ₗ[ℂ] (N.divisors → ℂ) where
  toFun f t := (f : ZMod N → ℂ) ((t : ℕ) : ZMod N)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun c := ⟨∑ t : N.divisors, c t • dind N t,
    Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (dind_mem_base N t))⟩
  left_inv f := by
    apply Subtype.ext
    show ∑ t : N.divisors, (f : ZMod N → ℂ) ((t : ℕ) : ZMod N) • dind N t = f
    rw [Finset.sum_coe_sort N.divisors (fun t => (f : ZMod N → ℂ) (t : ZMod N) • dind N t)]
    exact (radial_eq_sum ((mem_refLayer_base_iff N _).mp f.2)).symm
  right_inv c := by
    funext u
    show (∑ t : N.divisors, c t • dind N t) ((u : ℕ) : ZMod N) = c u
    rw [Finset.sum_apply, Finset.sum_eq_single u]
    · rw [Pi.smul_apply, dind_natCast _ (Nat.dvd_of_mem_divisors u.2), ite_eq_left rfl, smul_eq_mul, mul_one]
    · intro t _ htu
      rw [Pi.smul_apply, dind_natCast _ (Nat.dvd_of_mem_divisors u.2),
        ite_eq_right (fun h => htu (Subtype.ext h.symm)), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ u) h

/-- 殻の指示関数の基底 (1_{D_t})_{t ∣ N}（動径関数の空間 W_{p₀}、dim = d(N)）。 -/
noncomputable def radialBasis (N : ℕ) [NeZero N] : Module.Basis N.divisors ℂ (refLayer N (baseIdx N)) :=
  Module.Basis.ofEquivFun (radialCoord N)

/-- **1f.** 基底の元は 1_{D_t}。 -/
theorem radialBasis_apply (N : ℕ) [NeZero N] (t : N.divisors) :
    (radialBasis N t : ZMod N → ℂ) = dind N t := by
  rw [radialBasis, Module.Basis.coe_ofEquivFun]
  show ∑ t' : N.divisors, (Pi.single t (1 : ℂ) : N.divisors → ℂ) t' • dind N t' = dind N t
  rw [Finset.sum_eq_single t]
  · rw [Pi.single_eq_same, one_smul]
  · intro t' _ ht'
    rw [Pi.single_eq_of_ne ht', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ t) h

/-- **1g.** 基底での座標は値：(radialBasis N).repr f t = f(t)。 -/
theorem radialBasis_repr (N : ℕ) [NeZero N] (f : refLayer N (baseIdx N)) (t : N.divisors) :
    (radialBasis N).repr f t = (f : ZMod N → ℂ) ((t : ℕ) : ZMod N) :=
  Module.Basis.ofEquivFun_repr_apply _ _ _

/-- **1h.** radialHom T（Part 238、A_N → End(動径関数)）の行列の成分は (T 1_{D_t})(u)（u, t ∣ N）。 -/
theorem toMatrix_radialHom (N : ℕ) [NeZero N] (T : shellAlg N) (u t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N T) u t =
      (T : Module.End ℂ (ZMod N → ℂ)) (dind N t) ((u : ℕ) : ZMod N) := by
  rw [LinearMap.toMatrix_apply, radialBasis_repr, radialHom_apply, radialBasis_apply]

/-! ### 2. 殻の射影 D_s・E_s の行列 -/

/-- **2a.** ε_t(−ξ) = ε_t(ξ)。 -/
theorem geps_neg (N t : ℕ) [NeZero N] (ξ : ZMod N) : geps N t (-ξ) = geps N t ξ := by
  have h := geps_radial N t (-1) ξ
  rwa [Units.val_neg, Units.val_one, neg_one_mul] at h

/-- **2b.** 𝓕(1_{D_t}) = N·ε_t。 -/
theorem dft_dind (N t : ℕ) [NeZero N] : 𝓕 (dind N t) = (N : ℂ) • geps N t := by
  rw [← dft_geps N t, ZMod.dft_dft]
  funext j
  show (N : ℂ) • geps N t (-j) = ((N : ℂ) • geps N t) j
  rw [Pi.smul_apply, geps_neg]

/-- **2c.** E_s 1_{D_t} = N·ε_t(s)·ε_s（ε_s ⋆ 1_{D_t}）。 -/
theorem conv_geps_dind (N s t : ℕ) [NeZero N] :
    PAG.Part15.conv (geps N s) (dind N t) = ((N : ℂ) * geps N t (s : ZMod N)) • geps N s := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  rw [PAG.Part16.dft_conv, dft_geps, dft_dind, map_smul, dft_geps]
  funext ξ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : Nat.gcd N ξ.val = s
  · rw [radial_apply_eq (geps_radial N t) ξ, h]
    ring
  · have h0 : dind N s ξ = 0 := by
      show (if Nat.gcd N ξ.val = s then (1 : ℂ) else 0) = 0
      exact ite_eq_right h
    rw [h0]
    ring

/-- **2d.** D_s の行列は行列単位 E_{ss}（s ∣ N）。 -/
theorem toMatrix_D (N : ℕ) [NeZero N] (s : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨LinearMap.mulLeft ℂ (dind N s), PAG.Part232.mulLeft_dind_mem N s⟩) =
      Matrix.single s s 1 := by
  ext u t
  rw [toMatrix_radialHom]
  show (dind N s * dind N t) ((u : ℕ) : ZMod N) = _
  rw [dind_mul, Matrix.single, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors u.2), ite_eq_left (Subtype.ext_iff.mp h2.1).symm]
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors u.2)]
    exact ite_eq_right (fun hus => h2 ⟨Subtype.ext hus.symm, Subtype.ext h1⟩)
  · exact absurd (Subtype.ext_iff.mp h2.2) h1
  · rfl

/-- **2e.** E_s の行列：(E_s 1_{D_t})(u) = N·ε_t(s)·ε_s(u)（階数 1）。 -/
theorem toMatrix_E (N : ℕ) [NeZero N] (s u t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N s), PAG.Part232.convL_geps_mem N s⟩) u t =
      (N : ℂ) * geps N t ((s : ℕ) : ZMod N) * geps N s ((u : ℕ) : ZMod N) := by
  rw [toMatrix_radialHom]
  show PAG.Part15.conv (geps N s) (dind N t) ((u : ℕ) : ZMod N) = _
  rw [conv_geps_dind, Pi.smul_apply, smul_eq_mul]

/-- **2f.** ε_N = 1/N（双対殻 D_N = {0}）。 -/
theorem geps_self (N : ℕ) [NeZero N] (x : ZMod N) : geps N N x = (N : ℂ)⁻¹ := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [PAG.Part232.geps_apply_eq_sum N N dvd_rfl x, Nat.div_self hN, Nat.divisors_one, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one, mul_one, Nat.div_self hN]
  simp

/-- **2g.** E_N g = (1/N)·Σ_y g(y)（定数関数への射影）。 -/
theorem conv_geps_self (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    PAG.Part15.conv (geps N N) g = fun _ => (N : ℂ)⁻¹ * ∑ y, g y := by
  funext x
  show ∑ y, geps N N y * g (x - y) = (N : ℂ)⁻¹ * ∑ y, g y
  simp only [geps_self, ← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun _ => rfl)

/-- **2h.** E_N の行列：(E_N 1_{D_t})(u) = φ(N/t)/N（どの成分も 0 でない）。 -/
theorem toMatrix_E_self (N : ℕ) [NeZero N] (u t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N N), PAG.Part232.convL_geps_mem N N⟩) u t =
      (Nat.totient (N / t) : ℂ) / N := by
  rw [toMatrix_radialHom]
  show PAG.Part15.conv (geps N N) (dind N t) ((u : ℕ) : ZMod N) = _
  rw [conv_geps_self]
  show (N : ℂ)⁻¹ * ∑ y, dind N t y = _
  simp only [dind]
  rw [Finset.sum_boole, card_dsh N t (Nat.dvd_of_mem_divisors t.2), inv_mul_eq_div]

/-! ### 3. 殻の移し替え P_{s,t}：A の中の行列単位 -/

/-- 殻の移し替え P_{s,t} = (N/φ(N/t))·D_s E_N D_t。 -/
noncomputable def shellTrans (N s t : ℕ) [NeZero N] : Module.End ℂ (ZMod N → ℂ) :=
  ((N : ℂ) / (Nat.totient (N / t) : ℂ)) •
    (LinearMap.mulLeft ℂ (dind N s) * PAG.Part15.convL (geps N N) * LinearMap.mulLeft ℂ (dind N t))

/-- **3a.** P_{s,t} ∈ A_N。 -/
theorem shellTrans_mem (N s t : ℕ) [NeZero N] : shellTrans N s t ∈ shellAlg N :=
  Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (PAG.Part232.mulLeft_dind_mem N s)
    (PAG.Part232.convL_geps_mem N N)) (PAG.Part232.mulLeft_dind_mem N t)) _

/-- **3b.** P_{s,t} f = (D_t の上の f の平均)·1_{D_s} = (Σ_y 1_{D_t}(y) f(y) / φ(N/t))·1_{D_s}。 -/
theorem shellTrans_apply (N s t : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    shellTrans N s t f = ((∑ y, dind N t y * f y) / (Nat.totient (N / t) : ℂ)) • dind N s := by
  have hN : (N : ℂ) * (N : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  show ((N : ℂ) / (Nat.totient (N / t) : ℂ)) •
    (dind N s * PAG.Part15.conv (geps N N) (dind N t * f)) = _
  rw [conv_geps_self]
  funext x
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  linear_combination (dind N s x * (∑ y, dind N t y * f y) / (Nat.totient (N / t) : ℂ)) * hN

/-- **3c.** Σ_y 1_{D_t}(y)·1_{D_r}(y) = [t = r]·φ(N/t)（t ∣ N）。 -/
theorem sum_dind_mul_dind (N t r : ℕ) [NeZero N] (ht : t ∣ N) :
    ∑ y, dind N t y * dind N r y = if t = r then (Nat.totient (N / t) : ℂ) else 0 := by
  have h := congrArg (fun F => ∑ y, F y) (dind_mul N t r)
  simp only [Pi.mul_apply] at h
  rw [h]
  by_cases htr : t = r
  · rw [ite_eq_left htr, ite_eq_left htr]
    simp only [dind]
    rw [Finset.sum_boole, card_dsh N t ht]
  · rw [ite_eq_right htr, ite_eq_right htr]
    simp

/-- **3d.** P_{s,t} 1_{D_r} = [t = r]·1_{D_s}（t ∣ N）。 -/
theorem shellTrans_dind (N s t r : ℕ) [NeZero N] (ht : t ∣ N) :
    shellTrans N s t (dind N r) = if t = r then dind N s else 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hφ : (Nat.totient (N / t) : ℂ) ≠ 0 := by
    have h0 : 0 < N / t := Nat.div_pos (Nat.le_of_dvd hN ht) (Nat.pos_of_dvd_of_pos ht hN)
    exact_mod_cast (Nat.totient_pos.mpr h0).ne'
  rw [shellTrans_apply, sum_dind_mul_dind N t r ht]
  by_cases htr : t = r
  · rw [ite_eq_left htr, ite_eq_left htr, div_self hφ, one_smul]
  · rw [ite_eq_right htr, ite_eq_right htr, zero_div, zero_smul]

/-- **3e.** 行列単位の積：P_{s,t} P_{t',r} = [t = t']·P_{s,r}（t ∣ N）。 -/
theorem shellTrans_mul (N s t t' r : ℕ) [NeZero N] (ht : t ∣ N) :
    shellTrans N s t * shellTrans N t' r = if t = t' then shellTrans N s r else 0 := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, shellTrans_apply N t' r f, map_smul, shellTrans_dind N s t t' ht]
  by_cases htt : t = t'
  · rw [ite_eq_left htt, ite_eq_left htt, shellTrans_apply]
  · rw [ite_eq_right htt, ite_eq_right htt, smul_zero, LinearMap.zero_apply]

/-- **3f.** P_{s,t} の行列は行列単位 E_{st}（s, t ∣ N）。 -/
theorem toMatrix_shellTrans (N : ℕ) [NeZero N] (s t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialHom N ⟨shellTrans N s t, shellTrans_mem N s t⟩) =
      Matrix.single s t 1 := by
  ext u r
  rw [toMatrix_radialHom]
  show shellTrans N s t (dind N r) ((u : ℕ) : ZMod N) = _
  rw [shellTrans_dind N s t r (Nat.dvd_of_mem_divisors t.2), Matrix.single, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors u.2), ite_eq_left (Subtype.ext_iff.mp h2.1).symm]
  · rw [dind_natCast _ (Nat.dvd_of_mem_divisors u.2)]
    exact ite_eq_right (fun hus => h2 ⟨Subtype.ext hus.symm, Subtype.ext h1⟩)
  · exact absurd (Subtype.ext_iff.mp h2.2) h1
  · rfl

/-- **3g.** 約数を番号にした形：P_{s,t} P_{t',r} = [t = t']·P_{s,r}。 -/
theorem shellTrans_mul_div (N : ℕ) [NeZero N] (s t t' r : N.divisors) :
    shellTrans N s t * shellTrans N t' r = if t = t' then shellTrans N s r else 0 := by
  rw [shellTrans_mul N s t t' r (Nat.dvd_of_mem_divisors t.2)]
  by_cases h : t = t'
  · rw [ite_eq_left h, ite_eq_left (Subtype.ext_iff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun e => h (Subtype.ext e))]

/-- 行列 M ↦ Σ_{s,t} M_{st}·P_{s,t}（作用素）。 -/
noncomputable def radialMatOp (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    Module.End ℂ (ZMod N → ℂ) :=
  ∑ s : N.divisors, ∑ t : N.divisors, M s t • shellTrans N s t

/-- **3h.** Σ_{s,t} M_{st}·P_{s,t} ∈ A_N。 -/
theorem radialMatOp_mem (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M ∈ shellAlg N :=
  Subalgebra.sum_mem _ (fun s _ => Subalgebra.sum_mem _ (fun t _ => Subalgebra.smul_mem _ (shellTrans_mem N s t) _))

/-- **3i.** 積を保つ：Σ (MM′)_{sr} P_{s,r} = (Σ M_{st} P_{s,t})(Σ M′_{t′r} P_{t′,r})。 -/
theorem radialMatOp_mul (N : ℕ) [NeZero N] (M M' : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N (M * M') = radialMatOp N M * radialMatOp N M' := by
  simp only [radialMatOp, Fintype.sum_mul_sum, smul_mul_smul_comm, shellTrans_mul_div, smul_ite, smul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Matrix.mul_apply,
    Finset.sum_smul]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_comm)

/-- **3j.** 単位行列の行き先は Σ_{s ∣ N} P_{s,s}。 -/
theorem radialMatOp_one (N : ℕ) [NeZero N] : radialMatOp N 1 = ∑ s : N.divisors, shellTrans N s s := by
  simp only [radialMatOp, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]

/-- **3k.** radialHom(Σ M_{st} P_{s,t}) の行列は M。 -/
theorem toMatrix_radialHom_radialMatOp (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨radialMatOp N M, radialMatOp_mem N M⟩) = M := by
  have h : (⟨radialMatOp N M, radialMatOp_mem N M⟩ : shellAlg N) =
      ∑ s : N.divisors, ∑ t : N.divisors, M s t • ⟨shellTrans N s t, shellTrans_mem N s t⟩ := by
    apply Subtype.ext
    simp only [radialMatOp, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul]
  rw [h]
  simp only [map_sum, map_smul, toMatrix_shellTrans, Matrix.smul_single, smul_eq_mul, mul_one]
  exact (Matrix.matrix_eq_sum_single _).symm

/-- **3l.** M ↦ Σ M_{st} P_{s,t} は単射。 -/
theorem radialMatOp_injective (N : ℕ) [NeZero N] : Function.Injective (radialMatOp N) := by
  intro M M' h
  have e : (⟨radialMatOp N M, radialMatOp_mem N M⟩ : shellAlg N) = ⟨radialMatOp N M', radialMatOp_mem N M'⟩ :=
    Subtype.ext h
  rw [← toMatrix_radialHom_radialMatOp N M, ← toMatrix_radialHom_radialMatOp N M', e]

/-- 非単位的な代数準同型 M_{d(N)}(ℂ) → A_N、M ↦ Σ_{s,t} M_{st}·P_{s,t}（行列単位 P_{s,t}）。 -/
noncomputable def radialMatHom (N : ℕ) [NeZero N] : Matrix N.divisors N.divisors ℂ →ₙₐ[ℂ] shellAlg N where
  toFun M := ⟨radialMatOp N M, radialMatOp_mem N M⟩
  map_smul' c M := Subtype.ext (show radialMatOp N (c • M) = c • radialMatOp N M by
    simp only [radialMatOp, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum])
  map_zero' := Subtype.ext (show radialMatOp N 0 = 0 by
    simp only [radialMatOp, Matrix.zero_apply, zero_smul, Finset.sum_const_zero])
  map_add' M M' := Subtype.ext (show radialMatOp N (M + M') = radialMatOp N M + radialMatOp N M' by
    simp only [radialMatOp, Matrix.add_apply, add_smul, Finset.sum_add_distrib])
  map_mul' M M' := Subtype.ext (radialMatOp_mul N M M')

/-- **3m.** radialMatHom は単射（A_N の中に M_{d(N)}(ℂ) の写しがあり、その単位元は Σ_s P_{s,s}）。 -/
theorem radialMatHom_injective (N : ℕ) [NeZero N] : Function.Injective (radialMatHom N) :=
  fun _ _ h => radialMatOp_injective N (congrArg Subtype.val h)

/-- 明示的な原像：S ∈ End(W_{p₀}) ↦ Σ_{s,t} S_{st}·P_{s,t} ∈ A_N。 -/
noncomputable def radialSection (N : ℕ) [NeZero N] (S : Module.End ℂ (refLayer N (baseIdx N))) : shellAlg N :=
  radialMatHom N (LinearMap.toMatrix (radialBasis N) (radialBasis N) S)

/-- **3n.** radialHom (radialSection S) = S（Part 238 の全射を、P_{s,t} で直接示したもの）。 -/
theorem radialHom_radialSection (N : ℕ) [NeZero N] (S : Module.End ℂ (refLayer N (baseIdx N))) :
    radialHom N (radialSection N S) = S :=
  (LinearMap.toMatrix (radialBasis N) (radialBasis N)).injective (toMatrix_radialHom_radialMatOp N _)

/-- D_s（s ∈ ℕ）と E_N だけが生成する部分代数。 -/
noncomputable def diagAvgAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)) ∪ {PAG.Part15.convL (geps N N)})

/-- **3o.** ⟨D_s, E_N⟩ ⊆ A_N。 -/
theorem diagAvgAlg_le (N : ℕ) [NeZero N] : diagAvgAlg N ≤ shellAlg N :=
  Algebra.adjoin_le (Set.union_subset (Set.range_subset_iff.mpr (fun s => PAG.Part232.mulLeft_dind_mem N s))
    (Set.singleton_subset_iff.mpr (PAG.Part232.convL_geps_mem N N)))

/-- **3p.** Σ_{s,t} M_{st}·P_{s,t} ∈ ⟨D_s, E_N⟩。 -/
theorem radialMatOp_mem_diagAvg (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M ∈ diagAvgAlg N :=
  Subalgebra.sum_mem _ (fun s _ => Subalgebra.sum_mem _ (fun t _ => Subalgebra.smul_mem _
    (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
      (Algebra.subset_adjoin (Or.inl ⟨(s : ℕ), rfl⟩)) (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))))
      (Algebra.subset_adjoin (Or.inl ⟨(t : ℕ), rfl⟩))) _) _))

/-- **3q.** D_s と E_N（定数への射影）だけで、動径関数の空間の上の全行列環が出る。 -/
theorem radialHom_diagAvg_surjective (N : ℕ) [NeZero N] (S : Module.End ℂ (refLayer N (baseIdx N))) :
    ∃ T : shellAlg N, (T : Module.End ℂ (ZMod N → ℂ)) ∈ diagAvgAlg N ∧ radialHom N T = S :=
  ⟨radialSection N S, radialMatOp_mem_diagAvg N _, radialHom_radialSection N S⟩

/-- **3r.** 動径関数 f では Σ_y 1_{D_s}(y) f(y) = φ(N/s)·f(s)（s ∣ N）。 -/
theorem sum_dind_mul_radial {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) (s : ℕ) (hs : s ∣ N) :
    ∑ y, dind N s y * f y = (Nat.totient (N / s) : ℂ) * f (s : ZMod N) := by
  have key : ∀ y, dind N s y * f y = dind N s y * f (s : ZMod N) := by
    intro y
    by_cases h : Nat.gcd N y.val = s
    · rw [radial_apply_eq hf y, h]
    · have h0 : dind N s y = 0 := by
        show (if Nat.gcd N y.val = s then (1 : ℂ) else 0) = 0
        exact ite_eq_right h
      rw [h0, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun y _ => key y), ← Finset.sum_mul]
  simp only [dind]
  rw [Finset.sum_boole, card_dsh N s hs]

/-- **3s.** 動径関数 f では P_{s,s} f = f(s)·1_{D_s}（s ∣ N）。 -/
theorem shellTrans_self_radial {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) (s : ℕ) (hs : s ∣ N) :
    shellTrans N s s f = f (s : ZMod N) • dind N s := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hφ : (Nat.totient (N / s) : ℂ) ≠ 0 := by
    have h0 : 0 < N / s := Nat.div_pos (Nat.le_of_dvd hN hs) (Nat.pos_of_dvd_of_pos hs hN)
    exact_mod_cast (Nat.totient_pos.mpr h0).ne'
  rw [shellTrans_apply, sum_dind_mul_radial hf s hs, mul_div_cancel_left₀ _ hφ]

/-- **3t.** 動径関数 f では Σ_{s ∣ N} P_{s,s} f = f（Σ_s P_{s,s} は動径関数の上で恒等）。 -/
theorem sum_shellTrans_self_radial {N : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : Radial f) :
    ∑ s ∈ N.divisors, shellTrans N s s f = f := by
  rw [Finset.sum_congr rfl (fun s hs => shellTrans_self_radial hf s (Nat.dvd_of_mem_divisors hs))]
  exact (radial_eq_sum hf).symm

/-! ### 4. 𝓕 の行列：ラマヌジャン和の行列 C -/

/-- ラマヌジャンの行列 C(u, t) = N·ε_t(u)（= 𝓕(1_{D_t})(u) = c_{N/t}(u)、u, t ∣ N）。 -/
noncomputable def ramMat (N : ℕ) [NeZero N] : Matrix N.divisors N.divisors ℂ :=
  Matrix.of fun u t => (N : ℂ) * geps N t ((u : ℕ) : ZMod N)

/-- **4a.** N·ε_t(u) = Σ_{e ∣ N/t} μ(e)·(N/(te))·[N/(te) ∣ u]（t ∣ N、u は任意の自然数。ラマヌジャン和の式）。 -/
theorem natCast_mul_geps {N t : ℕ} [NeZero N] (ht : t ∣ N) (u : ℕ) :
    (N : ℂ) * geps N t (u : ZMod N) = ∑ e ∈ (N / t).divisors,
      (ArithmeticFunction.moebius e : ℂ) * ((N / (t * e) : ℕ) : ℂ) * (if N / (t * e) ∣ u then 1 else 0) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [PAG.Part232.geps_apply_eq_sum N t ht, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hte : t * e ∣ N := Nat.mul_dvd_of_dvd_div ht (Nat.dvd_of_mem_divisors he)
  have hte0 : ((t * e : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos hte hN).ne'
  simp only [ZMod.val_natCast, Nat.dvd_mod_iff (Nat.div_dvd_of_dvd hte)]
  rw [Nat.cast_div hte hte0]
  ring

/-- **4b.** C(u, t) = Σ_{e ∣ N/t} μ(e)·(N/(te))·[N/(te) ∣ u]。 -/
theorem ramMat_apply (N : ℕ) [NeZero N] (u t : N.divisors) :
    ramMat N u t = ∑ e ∈ (N / t).divisors,
      (ArithmeticFunction.moebius e : ℂ) * ((N / (t * e) : ℕ) : ℂ) * (if N / (t * e) ∣ (u : ℕ) then 1 else 0) := by
  rw [ramMat, Matrix.of_apply]
  exact natCast_mul_geps (Nat.dvd_of_mem_divisors t.2) u

/-- 𝓕 は動径関数の空間を保つ（Part 203 の dft_radial）。その制限。 -/
noncomputable def radialDFT (N : ℕ) [NeZero N] : Module.End ℂ (refLayer N (baseIdx N)) :=
  (ZMod.dft (N := N) (E := ℂ)).toLinearMap.restrict (fun f hf =>
    (mem_refLayer_base_iff N _).mpr (dft_radial f ((mem_refLayer_base_iff N f).mp hf)))

/-- **4c.** 𝓕|_{W_{p₀}} の行列は C。 -/
theorem toMatrix_radialDFT (N : ℕ) [NeZero N] :
    LinearMap.toMatrix (radialBasis N) (radialBasis N) (radialDFT N) = ramMat N := by
  ext u t
  rw [LinearMap.toMatrix_apply, radialBasis_repr]
  show 𝓕 ((radialBasis N t : ZMod N → ℂ)) ((u : ℕ) : ZMod N) = _
  rw [radialBasis_apply, dft_dind, ramMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]

/-- **4d.** 動径関数の上で 𝓕𝓕 = N。 -/
theorem radialDFT_mul_self (N : ℕ) [NeZero N] : radialDFT N * radialDFT N = (N : ℂ) • 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  show 𝓕 (𝓕 (f : ZMod N → ℂ)) = (N : ℂ) • (f : ZMod N → ℂ)
  rw [ZMod.dft_dft]
  funext j
  have h := (mem_refLayer_base_iff N _).mp f.2 (-1) j
  rw [Units.val_neg, Units.val_one, neg_one_mul] at h
  show (N : ℂ) • (f : ZMod N → ℂ) (-j) = (N : ℂ) • (f : ZMod N → ℂ) j
  rw [h]

/-- **4e.** C² = N·1（ラマヌジャン和の直交関係 Σ_r C(u, r) C(r, t) = N·[u = t]）。 -/
theorem ramMat_mul_self (N : ℕ) [NeZero N] : ramMat N * ramMat N = (N : ℂ) • 1 := by
  rw [← toMatrix_radialDFT, ← LinearMap.toMatrix_mul, radialDFT_mul_self, map_smul, LinearMap.toMatrix_one]

/-- **4f.** 𝓕 E_s = D_s 𝓕（E_s = 𝓕⁻¹ D_s 𝓕）。 -/
theorem dft_conv_geps (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    𝓕 (PAG.Part15.conv (geps N s) f) = dind N s * 𝓕 f := by
  rw [PAG.Part16.dft_conv, dft_geps]

/-- **4g.** 行列の形：C·[E_s] = [D_s]·C（s ∣ N）。 -/
theorem ramMat_mul_toMatrix_E (N : ℕ) [NeZero N] (s : N.divisors) :
    ramMat N * LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N s), PAG.Part232.convL_geps_mem N s⟩) =
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨LinearMap.mulLeft ℂ (dind N s), PAG.Part232.mulLeft_dind_mem N s⟩) * ramMat N := by
  rw [← toMatrix_radialDFT, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
  congr 1
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  show 𝓕 (PAG.Part15.conv (geps N s) (f : ZMod N → ℂ)) = dind N s * 𝓕 (f : ZMod N → ℂ)
  exact dft_conv_geps N s f

/-- **4h.** [E_s] の成分をラマヌジャンの行列で：[E_s](u, t) = C(s, t)·C(u, s)/N（列 C(·, s) と行 C(s, ·) の積、階数 1）。 -/
theorem toMatrix_E_eq_ramMat (N : ℕ) [NeZero N] (s u t : N.divisors) :
    LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N s), PAG.Part232.convL_geps_mem N s⟩) u t =
      ramMat N s t * ramMat N u s / N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [toMatrix_E, ramMat, Matrix.of_apply, Matrix.of_apply, eq_div_iff hN]
  ring

/-- **4i.** C(u, N) = 1（c_1 = 1）。 -/
theorem ramMat_apply_col_self (N : ℕ) [NeZero N] (u : N.divisors) :
    ramMat N u ⟨N, Nat.mem_divisors_self N (NeZero.ne N)⟩ = 1 := by
  rw [ramMat, Matrix.of_apply]
  show (N : ℂ) * geps N N ((u : ℕ) : ZMod N) = 1
  rw [geps_self, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne N))]

/-- **4j.** C(N, t) = φ(N/t)（c_{N/t}(0) = φ(N/t)、点 N は 0）。 -/
theorem ramMat_apply_row_self (N : ℕ) [NeZero N] (t : N.divisors) :
    ramMat N ⟨N, Nat.mem_divisors_self N (NeZero.ne N)⟩ t = Nat.totient (N / t) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [ramMat, Matrix.of_apply]
  show (N : ℂ) * geps N t ((N : ℕ) : ZMod N) = _
  rw [ZMod.natCast_self, geps_apply_zero N t (Nat.dvd_of_mem_divisors t.2), mul_div_assoc',
    mul_div_cancel_left₀ _ hN]

/-! ### 5. 素冪の場合の C と、互いに素な積（クロネッカー積） -/

/-- **5a.** Σ_{e ∣ q^n} μ(e)·g(e) = g(1) − g(q)（q は素数、n ≥ 1）。 -/
theorem sum_divisors_primePow_moebius {q : ℕ} (hq : q.Prime) {n : ℕ} (hn : 1 ≤ n) (g : ℕ → ℂ) :
    ∑ e ∈ (q ^ n).divisors, (ArithmeticFunction.moebius e : ℂ) * g e = g 1 - g q := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.divisors_prime_pow hq, Finset.sum_map, Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_eq_zero (fun x _ => ?_)]
  · simp only [Function.Embedding.coeFn_mk, zero_add, pow_zero, pow_one, ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime hq]
    push_cast
    ring
  · simp only [Function.Embedding.coeFn_mk]
    rw [ArithmeticFunction.moebius_apply_prime_pow hq (by omega), ite_eq_right (by omega)]
    simp

/-- **5b.** N = q^k、u = q^i、t = q^j（i, j ≤ k）のラマヌジャンの行列：C(q^i, q^j) = 1（j = k）、
  q^{k−j}·[k − j ≤ i] − q^{k−j−1}·[k − j − 1 ≤ i]（j < k）。 -/
theorem ramMat_primePow {q : ℕ} (hq : q.Prime) {k i j : ℕ} [NeZero (q ^ k)] (hj : j ≤ k) :
    ((q ^ k : ℕ) : ℂ) * geps (q ^ k) (q ^ j) ((q ^ i : ℕ) : ZMod (q ^ k)) =
      if j = k then 1 else
        (if k - j ≤ i then ((q ^ (k - j) : ℕ) : ℂ) else 0) -
          (if k - j - 1 ≤ i then ((q ^ (k - j - 1) : ℕ) : ℂ) else 0) := by
  rw [natCast_mul_geps (pow_dvd_pow q hj), Nat.pow_div hj hq.pos]
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, Nat.sub_self, pow_zero, Nat.divisors_one, Finset.sum_singleton,
      ArithmeticFunction.moebius_apply_one, mul_one, Nat.div_self (pow_pos hq.pos _)]
    simp
  · rw [ite_eq_right hjk]
    have hj1 : j + 1 ≤ k := by omega
    simp only [mul_assoc]
    refine (sum_divisors_primePow_moebius hq (by omega)
      (fun e => ((q ^ k / (q ^ j * e) : ℕ) : ℂ) * (if q ^ k / (q ^ j * e) ∣ q ^ i then 1 else 0))).trans ?_
    simp only [mul_one, ← pow_succ, Nat.pow_div hj hq.pos, Nat.pow_div hj1 hq.pos,
      Nat.pow_dvd_pow_iff_le_right hq.one_lt, Nat.sub_sub, mul_ite, mul_zero]

/-- **5c.** 互いに素な a, b：C_{ab}(u_a u_b, t_a t_b) = C_a(u_a, t_a)·C_b(u_b, t_b)（クロネッカー積。
  Part 228 の geps_crt と、単数倍での不変性から）。 -/
theorem ramMat_mul_coprime {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ua ta ub tb : ℕ}
    (hua : ua ∣ a) (hta : ta ∣ a) (hub : ub ∣ b) (htb : tb ∣ b) :
    ((a * b : ℕ) : ℂ) * geps (a * b) (ta * tb) ((ua * ub : ℕ) : ZMod (a * b)) =
      ((a : ℂ) * geps a ta (ua : ZMod a)) * ((b : ℂ) * geps b tb (ub : ZMod b)) := by
  have hcb : Nat.Coprime ub a := Nat.Coprime.coprime_dvd_left hub hab.symm
  have hca : Nat.Coprime ua b := Nat.Coprime.coprime_dvd_left hua hab
  rw [PAG.Part232.geps_crt hab hta htb, map_natCast (ZMod.chineseRemainder hab) (ua * ub),
    Prod.fst_natCast, Prod.snd_natCast]
  have ea : geps a ta ((ua * ub : ℕ) : ZMod a) = geps a ta (ua : ZMod a) := by
    rw [Nat.cast_mul, mul_comm, ← ZMod.coe_unitOfCoprime ub hcb]
    exact geps_radial a ta _ _
  have eb : geps b tb ((ua * ub : ℕ) : ZMod b) = geps b tb (ub : ZMod b) := by
    rw [Nat.cast_mul, ← ZMod.coe_unitOfCoprime ua hca]
    exact geps_radial b tb _ _
  rw [ea, eb]
  push_cast
  ring

end PAG.Part243

#print axioms PAG.Part243.gcd_val_natCast_of_dvd
#print axioms PAG.Part243.dind_natCast
#print axioms PAG.Part243.radial_apply_eq
#print axioms PAG.Part243.radial_eq_sum
#print axioms PAG.Part243.dind_mem_base
#print axioms PAG.Part243.radialCoord
#print axioms PAG.Part243.radialBasis
#print axioms PAG.Part243.radialBasis_apply
#print axioms PAG.Part243.radialBasis_repr
#print axioms PAG.Part243.toMatrix_radialHom
#print axioms PAG.Part243.geps_neg
#print axioms PAG.Part243.dft_dind
#print axioms PAG.Part243.conv_geps_dind
#print axioms PAG.Part243.toMatrix_D
#print axioms PAG.Part243.toMatrix_E
#print axioms PAG.Part243.geps_self
#print axioms PAG.Part243.conv_geps_self
#print axioms PAG.Part243.toMatrix_E_self
#print axioms PAG.Part243.shellTrans
#print axioms PAG.Part243.shellTrans_mem
#print axioms PAG.Part243.shellTrans_apply
#print axioms PAG.Part243.sum_dind_mul_dind
#print axioms PAG.Part243.shellTrans_dind
#print axioms PAG.Part243.shellTrans_mul
#print axioms PAG.Part243.toMatrix_shellTrans
#print axioms PAG.Part243.shellTrans_mul_div
#print axioms PAG.Part243.radialMatOp
#print axioms PAG.Part243.radialMatOp_mem
#print axioms PAG.Part243.radialMatOp_mul
#print axioms PAG.Part243.radialMatOp_one
#print axioms PAG.Part243.toMatrix_radialHom_radialMatOp
#print axioms PAG.Part243.radialMatOp_injective
#print axioms PAG.Part243.radialMatHom
#print axioms PAG.Part243.radialMatHom_injective
#print axioms PAG.Part243.radialSection
#print axioms PAG.Part243.radialHom_radialSection
#print axioms PAG.Part243.diagAvgAlg
#print axioms PAG.Part243.diagAvgAlg_le
#print axioms PAG.Part243.radialMatOp_mem_diagAvg
#print axioms PAG.Part243.radialHom_diagAvg_surjective
#print axioms PAG.Part243.sum_dind_mul_radial
#print axioms PAG.Part243.shellTrans_self_radial
#print axioms PAG.Part243.sum_shellTrans_self_radial
#print axioms PAG.Part243.ramMat
#print axioms PAG.Part243.natCast_mul_geps
#print axioms PAG.Part243.ramMat_apply
#print axioms PAG.Part243.radialDFT
#print axioms PAG.Part243.toMatrix_radialDFT
#print axioms PAG.Part243.radialDFT_mul_self
#print axioms PAG.Part243.ramMat_mul_self
#print axioms PAG.Part243.dft_conv_geps
#print axioms PAG.Part243.ramMat_mul_toMatrix_E
#print axioms PAG.Part243.toMatrix_E_eq_ramMat
#print axioms PAG.Part243.ramMat_apply_col_self
#print axioms PAG.Part243.ramMat_apply_row_self
#print axioms PAG.Part243.sum_divisors_primePow_moebius
#print axioms PAG.Part243.ramMat_primePow
#print axioms PAG.Part243.ramMat_mul_coprime
