/-
  PAG 2.0 Part 198（2026-10-24）— ℤ/N のケットのフーリエ双対性とスペクトル
  𝓕f(k) = Σ_x e(−xk/N) f(x)（Mathlib の ZMod.dft）。uM = N、c ∣ M、χ は法 c の原始指標。
  1. dft_push_memb：𝓕_N(ι_{u,*} g)(k) = 𝓕_M g(k mod M)（Part 14 の dft_push の一般化）
     dft_pull：𝓕_M(f ∘ π_c) = (M/c)·ι_{M/c,*}(𝓕_c f)（引き戻しのフーリエ変換は押し出し）
  2. dft_gket（フーリエ双対性）：𝓕|u, χ⟩_N = √(φ(uc)/φ(M))·(M/c)·χ̄(−1)τ(χ)·|M/c, χ̄⟩_N
     （双対の殻 M/c = N/(uc)、指標 χ̄。Part 113 の双対殻 a = K − c − w の一般化）
     dft_gket_unitary：u と M の素因数が c を割るなら (1/√N)𝓕|u, χ⟩ = χ̄(−1)·z(χ)·|M/c, χ̄⟩（z = τ/√c）
  3. スペクトル（畳み込みの作用素 f ↦ |u, χ⟩ ⋆ f の固有値は 𝓕|u, χ⟩ の値）：
     normSq_dft_gket：0 でない固有値の絶対値の 2 乗は (M/c)²c/φ(M)（条件のもとで N/φ(uc)）
     pow_const_iff：固有値の m 乗が台の上で一定 ⇔ χ^m = 1（Part 100 (5) の大域版、Part 107・108 の lcm を含む）
  4. gket_unif：固有値は 𝓕k(t₀)·μ_{ord χ} に一様に分布する（Part 118 の Unif の大域版。冪和の消滅から、
     `fiber_of_power_sums`）。gket_charpoly：Π_{t ∈ T}(X − 𝓕k(t)) = (X^o − 𝓕k(t₀)^o)^(|T|/o)
-/
import PAG201

namespace PAG.Part202

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part201
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. 押し出しと引き戻しのフーリエ変換 -/

/-- 押し出しの値：ι_{u,*} g (x) = [u ∣ x] g(x/u)。 -/
theorem push_memb_apply (u M N : ℕ) [NeZero N] [NeZero M] (h : u * M = N) (g : ZMod M → ℂ) (x : ZMod N) :
    PAG.Part17.push (memb u M N h) g x = if u ∣ x.val then g ((x.val / u : ℕ) : ZMod M) else 0 := by
  by_cases hx : u ∣ x.val
  · obtain ⟨k, hk⟩ := hx
    have hkM : k < M := by
      have hxv := ZMod.val_lt x
      rw [hk, ← h] at hxv
      exact Nat.lt_of_mul_lt_mul_left hxv
    have hx' : memb u M N h (k : ZMod M) = x := by
      apply ZMod.val_injective N
      rw [memb_val, ZMod.val_natCast_of_lt hkM, hk]
    have hdiv : x.val / u = k := by rw [hk, Nat.mul_div_cancel_left k (pos_of_mul h)]
    rw [ite_eq_left ⟨k, hk⟩, hdiv, ← hx', PAG.Part17.push, (memb_injective u M N h).extend_apply]
  · rw [ite_eq_right hx, PAG.Part17.push, Function.extend_apply' _ _ _
      (fun hy => hx ((exists_memb_iff u M N h x).mp hy)), Pi.zero_apply]

/-- **1a. 押し出しのフーリエ変換は引き戻し**：𝓕_N(ι_{u,*} g)(k) = 𝓕_M g(k mod M)。 -/
theorem dft_push_memb (u M N : ℕ) [NeZero N] [NeZero M] (h : u * M = N) (g : ZMod M → ℂ) (k : ZMod N) :
    𝓕 (PAG.Part17.push (memb u M N h) g) k = 𝓕 g (ZMod.castHom (Dvd.intro_left u h) (ZMod M) k) := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp_rw [smul_eq_mul]
  rw [show (∑ z, stdAddChar (-(z * k)) * PAG.Part17.push (memb u M N h) g z)
      = ∑ z, PAG.Part17.push (memb u M N h) g z * stdAddChar (-(z * k)) from
      sum_congr rfl (fun _ _ => mul_comm _ _), PAG.Part17.sum_push_mul _ (memb_injective u M N h)]
  refine sum_congr rfl (fun y _ => ?_)
  rw [mul_comm]
  congr 1
  have e1 : -(memb u M N h y * k) = (u : ZMod N) * (-((y.val : ZMod N) * k)) := by
    rw [memb_apply]; push_cast; ring
  rw [e1, PAG.Part117.stdAddChar_mul_cast (Dvd.intro_left u h) u (by rw [← h, mul_comm]) _]
  congr 1
  rw [map_neg, map_mul, map_natCast, ZMod.natCast_zmod_val]

/-- **1b. 引き戻しのフーリエ変換は押し出し**：𝓕_M(f ∘ π_c) = (M/c)·ι_{M/c,*}(𝓕_c f)。 -/
theorem dft_pull (M c : ℕ) [NeZero M] [NeZero c] (hc : c ∣ M) (f : ZMod c → ℂ) :
    𝓕 (fun x => f (ZMod.castHom hc (ZMod c) x))
      = ((M / c : ℕ) : ℂ) • PAG.Part17.push (memb (M / c) c M (Nat.div_mul_cancel hc)) (𝓕 f) := by
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  funext k
  rw [Pi.smul_apply, smul_eq_mul, push_memb_apply]
  by_cases hk : (M / c) ∣ k.val
  · obtain ⟨j, hj⟩ := hk
    rw [ite_eq_left ⟨j, hj⟩]
    have hk' : k = ((M / c : ℕ) : ZMod M) * ((j : ℕ) : ZMod M) := by
      rw [← Nat.cast_mul, ← hj, ZMod.natCast_zmod_val]
    rw [hk', PAG.Part117.dft_pullback_mul hc (M / c) (Nat.mul_div_cancel' hc).symm f, map_natCast]
    congr 2
    have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
    rw [← hk', hj, Nat.mul_div_cancel_left j hMc]
  · rw [ite_eq_right hk, mul_zero]
    apply PAG.Part17.dft_pullback_eq_zero hc f k
    intro h0
    apply hk
    have e : ((c * k.val : ℕ) : ZMod M) = 0 := by rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact h0
    rw [ZMod.natCast_eq_zero_iff] at e
    have e' : c * (M / c) ∣ c * k.val := by rwa [Nat.mul_div_cancel' hc]
    exact Nat.dvd_of_mul_dvd_mul_left hc0 e'

/-! ### 2. フーリエ双対性 -/

/-- 双対の殻の等式 (M/c)·(uc) = N。 -/
theorem dual_eq {u M N c : ℕ} (h : u * M = N) (hc : c ∣ M) : M / c * (u * c) = N := by
  rw [← h, show M / c * (u * c) = u * (M / c * c) by ring, Nat.div_mul_cancel hc]

/-- **2. フーリエ双対性**：𝓕|u, χ⟩_N = √(φ(uc)/φ(M))·(M/c)·χ̄(−1)τ(χ)·|M/c, χ̄⟩_N（χ 原始的）。 -/
theorem dft_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    𝓕 (gket u M N h c hc χ)
      = (((Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient M) : ℝ) : ℂ) * ((M / c : ℕ) : ℂ)
          * χ⁻¹ (-1) * gaussSum χ stdAddChar) •
        gket (M / c) (u * c) N (dual_eq h hc) c (dvd_mul_left c u) (χ⁻¹ : DirichletCharacter ℂ c) := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hMcZ : NeZero (M / c) := ⟨hMc.ne'⟩
  have hu : 0 < u := pos_of_mul h
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  have huc0 : u * c ≠ 0 := mul_ne_zero hu.ne' hc0.ne'
  have hφuc : (0 : ℝ) < Real.sqrt (Nat.totient (u * c)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero huc0))
  funext k
  have eL : 𝓕 (gket u M N h c hc χ) k
      = (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) *
        (((M / c : ℕ) : ℂ) * PAG.Part17.push (memb (M / c) c M (Nat.div_mul_cancel hc)) (𝓕 χ)
          (ZMod.castHom (Dvd.intro_left u h) (ZMod M) k)) := by
    unfold gket
    rw [ZMod.dft_const_smul, Pi.smul_apply, smul_eq_mul, dft_push_memb]
    congr 1
    have := congrFun (dft_pull M c hc χ) (ZMod.castHom (Dvd.intro_left u h) (ZMod M) k)
    rw [Pi.smul_apply, smul_eq_mul] at this
    exact this
  rw [eL, push_memb_apply, Pi.smul_apply, smul_eq_mul, gket_apply]
  have hv : (ZMod.castHom (Dvd.intro_left u h) (ZMod M) k).val = k.val % M := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [hv]
  have hdvd : M / c ∣ k.val % M ↔ M / c ∣ k.val := Nat.dvd_mod_iff (Nat.div_dvd_of_dvd hc)
  by_cases hk : M / c ∣ k.val
  · obtain ⟨q, hq⟩ := hk
    have e1 : k.val % M = M / c * (q % c) := by
      have hMeq : M / c * c = M := Nat.div_mul_cancel hc
      calc k.val % M = M / c * q % (M / c * c) := by rw [hq, hMeq]
        _ = M / c * (q % c) := Nat.mul_mod_mul_left _ _ _
    rw [ite_eq_left (hdvd.mpr ⟨q, hq⟩), ite_eq_left ⟨q, hq⟩, e1, Nat.mul_div_cancel_left _ hMc, hq,
      Nat.mul_div_cancel_left _ hMc, ZMod.natCast_mod, hχ.fourierTransform_eq_inv_mul_gaussSum,
      show -((q : ℕ) : ZMod c) = (-1) * ((q : ℕ) : ZMod c) by ring, map_mul]
    have a1 : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
    have a2 : ((Real.sqrt (Nat.totient (u * c)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφuc.ne'
    push_cast
    field_simp
  · rw [ite_eq_right (fun hd => hk (hdvd.mp hd)), ite_eq_right hk, mul_zero, mul_zero, mul_zero]

/-- **2'. ユニタリな正規化**：u と M の素因数がすべて c を割るなら
(1/√N)·𝓕|u, χ⟩_N = χ̄(−1)·(τ(χ)/√c)·|M/c, χ̄⟩_N。 -/
theorem dft_gket_unitary (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (hu : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) (hM : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) :
    (((Real.sqrt N)⁻¹ : ℝ) : ℂ) • 𝓕 (gket u M N h c hc χ)
      = (χ⁻¹ (-1) * (gaussSum χ stdAddChar / ((Real.sqrt c : ℝ) : ℂ))) •
        gket (M / c) (u * c) N (dual_eq h hc) c (dvd_mul_left c u) (χ⁻¹ : DirichletCharacter ℂ c) := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu0 : 0 < u := pos_of_mul h
  have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  rw [dft_gket u M N h c hc χ hχ, smul_smul]
  congr 1
  -- φ(uc) = φ(c)·u、φ(M) = φ(c)·(M/c)
  have e1 : Nat.totient (u * c) = Nat.totient c * u := by
    rw [mul_comm u c]; exact totient_mul_of_primes c u hu
  have e2 : Nat.totient M = Nat.totient c * (M / c) := by
    have := totient_mul_of_primes c (M / c) (fun q hq hqt => hM q hq (hqt.trans (Nat.div_dvd_of_dvd hc)))
    rwa [Nat.mul_div_cancel' hc] at this
  have hN : (N : ℝ) = (u : ℝ) * ((M / c : ℕ) : ℝ) * c := by
    rw [← h]; push_cast
    rw [mul_assoc, ← Nat.cast_mul (M / c) c, Nat.div_mul_cancel hc]
  have hφc : (0 : ℝ) < Nat.totient c := by exact_mod_cast Nat.totient_pos.mpr hc0
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu0
  have hMc' : (0 : ℝ) < ((M / c : ℕ) : ℝ) := by exact_mod_cast hMc
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc0
  have key : (Real.sqrt N)⁻¹ * (Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient M))
      * ((M / c : ℕ) : ℝ) = (Real.sqrt c)⁻¹ := by
    have p1 : (0 : ℝ) < Real.sqrt (Nat.totient c) := Real.sqrt_pos.mpr hφc
    have p2 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hu'
    have p3 : (0 : ℝ) < Real.sqrt ((M / c : ℕ) : ℝ) := Real.sqrt_pos.mpr hMc'
    have p4 : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc'
    have s1 : Real.sqrt ((M / c : ℕ) : ℝ) * Real.sqrt ((M / c : ℕ) : ℝ) = ((M / c : ℕ) : ℝ) :=
      Real.mul_self_sqrt hMc'.le
    rw [e1, e2, hN, Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    field_simp
    rw [sq, s1]
  calc (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * ((((Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient M) : ℝ) : ℂ)
        * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar))
      = ((((Real.sqrt N)⁻¹ * (Real.sqrt (Nat.totient (u * c)) / Real.sqrt (Nat.totient M))
          * ((M / c : ℕ) : ℝ) : ℝ)) : ℂ) * (χ⁻¹ (-1) * gaussSum χ stdAddChar) := by
        push_cast; ring
    _ = χ⁻¹ (-1) * (gaussSum χ stdAddChar / ((Real.sqrt c : ℝ) : ℂ)) := by
        rw [key]; push_cast; ring

/-! ### 3. スペクトル -/

/-- 単数での指標の値は絶対値 1。 -/
theorem normSq_chi_unit {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (a : (ZMod d)ˣ) :
    Complex.normSq (Ψ a) = 1 := by
  have h := PAG.Part193.chi_unit_root Ψ a
  rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one h (orderOf_pos _).ne', one_pow]

/-- **3a. 固有値の値**：𝓕|u, χ⟩_N (k) = [M/c ∣ k]·B·χ̄(k/(M/c))、B = φ(M)^(−1/2)(M/c)χ̄(−1)τ(χ)。 -/
theorem dft_gket_apply (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (k : ZMod N) :
    𝓕 (gket u M N h c hc χ) k =
      if M / c ∣ k.val then
        ((((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar)
          * χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c)
      else 0 := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu : 0 < u := pos_of_mul h
  have huc0 : u * c ≠ 0 := mul_ne_zero hu.ne' hc0.ne'
  have hφuc : (0 : ℝ) < Real.sqrt (Nat.totient (u * c)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero huc0))
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  rw [dft_gket u M N h c hc χ hχ, Pi.smul_apply, smul_eq_mul, gket_apply]
  by_cases hk : M / c ∣ k.val
  · rw [ite_eq_left hk, ite_eq_left hk]
    have a1 : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
    have a2 : ((Real.sqrt (Nat.totient (u * c)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφuc.ne'
    push_cast
    field_simp
  · rw [ite_eq_right hk, ite_eq_right hk, mul_zero]

/-- **3b. 固有値の絶対値**：0 でない固有値では |𝓕|u, χ⟩(k)|² = (M/c)²·c/φ(M)。 -/
theorem normSq_dft_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (k : ZMod N)
    (hk : 𝓕 (gket u M N h c hc χ) k ≠ 0) :
    Complex.normSq (𝓕 (gket u M N h c hc χ) k) = ((M / c : ℕ) : ℝ) ^ 2 * c / Nat.totient M := by
  have hMZ := neZero_of_mul h
  have hφM : (0 : ℝ) < Nat.totient M := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  rw [dft_gket_apply u M N h c hc χ hχ k] at hk ⊢
  by_cases hd : M / c ∣ k.val
  · rw [ite_eq_left hd] at hk ⊢
    have hne : χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c) ≠ 0 := fun h0 => hk (by rw [h0, mul_zero])
    have hunit : IsUnit ((k.val / (M / c) : ℕ) : ZMod c) := by
      by_contra hn
      exact hne (MulChar.map_nonunit _ hn)
    obtain ⟨a, ha⟩ := hunit
    have hm1 : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
    rw [← ha, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
      normSq_chi_unit χ⁻¹ a, ← hm1, normSq_chi_unit χ⁻¹ (-1), PAG.Part16.normSq_gaussSum hχ,
      Complex.normSq_ofReal, Complex.normSq_natCast]
    have hs : Real.sqrt (Nat.totient M) * Real.sqrt (Nat.totient M) = Nat.totient M :=
      Real.mul_self_sqrt (Nat.cast_nonneg _)
    rw [← mul_inv, hs]
    field_simp
  · rw [ite_eq_right hd] at hk
    exact absurd rfl hk

/-- **3b'.** u と M の素因数がすべて c を割るなら、0 でない固有値の絶対値の 2 乗は N/φ(uc)。 -/
theorem normSq_dft_gket' (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (hu : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) (hM : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) (k : ZMod N)
    (hk : 𝓕 (gket u M N h c hc χ) k ≠ 0) :
    Complex.normSq (𝓕 (gket u M N h c hc χ) k) = (N : ℝ) / Nat.totient (u * c) := by
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu0 : 0 < u := pos_of_mul h
  have hMZ := neZero_of_mul h
  have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  rw [normSq_dft_gket u M N h c hc χ hχ k hk]
  have e1 : Nat.totient (u * c) = Nat.totient c * u := by
    rw [mul_comm u c]; exact totient_mul_of_primes c u hu
  have e2 : Nat.totient M = Nat.totient c * (M / c) := by
    have := totient_mul_of_primes c (M / c) (fun q hq hqt => hM q hq (hqt.trans (Nat.div_dvd_of_dvd hc)))
    rwa [Nat.mul_div_cancel' hc] at this
  have hN : (N : ℝ) = (u : ℝ) * ((M / c : ℕ) : ℝ) * c := by
    rw [← h]; push_cast
    rw [mul_assoc, ← Nat.cast_mul (M / c) c, Nat.div_mul_cancel hc]
  have hφc : (0 : ℝ) < Nat.totient c := by exact_mod_cast Nat.totient_pos.mpr hc0
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu0
  have hMc' : (0 : ℝ) < ((M / c : ℕ) : ℝ) := by exact_mod_cast hMc
  rw [e1, e2, hN]
  push_cast
  field_simp

/-- **3c. 固有値の冪の一定性**：固有値の m 乗が台の上で一定 ⇔ χ^m = 1（Part 100 (5) の大域版）。 -/
theorem pow_const_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (m : ℕ) :
    (∀ k k' : ZMod N, 𝓕 (gket u M N h c hc χ) k ≠ 0 → 𝓕 (gket u M N h c hc χ) k' ≠ 0 →
      (𝓕 (gket u M N h c hc χ) k) ^ m = (𝓕 (gket u M N h c hc χ) k') ^ m) ↔ χ ^ m = 1 := by
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hMle : M ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Dvd.intro_left u h)
  set B : ℂ := (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) *
    gaussSum χ stdAddChar with hB
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  have hB0 : B ≠ 0 := by
    have hm1 : χ⁻¹ (-1) ≠ 0 := by
      have : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
      rw [← this]; exact ((-1 : (ZMod c)ˣ).isUnit.map χ⁻¹).ne_zero
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hm1) (PAG.Part16.gaussSum_ne_zero hχ)
    · exact_mod_cast (inv_pos.mpr hφM).ne'
    · exact_mod_cast hMc.ne'
  -- 単数 a ∈ (ZMod c)ˣ に対応する点 k_a = (M/c)·a
  have hka : ∀ a : (ZMod c)ˣ, 𝓕 (gket u M N h c hc χ) (((M / c * (a : ZMod c).val : ℕ) : ZMod N))
      = B * χ⁻¹ a := by
    intro a
    have hlt : M / c * (a : ZMod c).val < N := by
      have h1 : (a : ZMod c).val < c := ZMod.val_lt _
      have h2 : M / c * c = M := Nat.div_mul_cancel hc
      calc M / c * (a : ZMod c).val < M / c * c := Nat.mul_lt_mul_of_pos_left h1 hMc
        _ = M := h2
        _ ≤ N := hMle
    rw [dft_gket_apply u M N h c hc χ hχ, ZMod.val_natCast_of_lt hlt, ite_eq_left (Dvd.intro _ rfl),
      Nat.mul_div_cancel_left _ hMc, ZMod.natCast_zmod_val]
  constructor
  · intro H
    apply MulChar.ext
    intro a
    have e1 := H (((M / c * ((a : ZMod c)).val : ℕ) : ZMod N)) (((M / c * ((1 : (ZMod c)ˣ) : ZMod c).val : ℕ) : ZMod N))
      (by rw [hka]; exact mul_ne_zero hB0 ((a.isUnit.map χ⁻¹).ne_zero))
      (by rw [hka]; exact mul_ne_zero hB0 (((1 : (ZMod c)ˣ).isUnit.map χ⁻¹).ne_zero))
    rw [hka, hka, Units.val_one, map_one, mul_one, mul_pow] at e1
    have e2 : (χ⁻¹ a) ^ m = 1 := by
      have := mul_left_cancel₀ (pow_ne_zero m hB0) (e1.trans (mul_one _).symm)
      exact this
    rw [MulChar.one_apply_coe, MulChar.pow_apply_coe]
    have e3 : χ⁻¹ a * χ a = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply_coe]
    have e4 : (χ a) ^ m = ((χ⁻¹ a) ^ m)⁻¹ := by
      rw [← inv_pow, eq_inv_of_mul_eq_one_left e3, inv_inv]
    rw [e4, e2, inv_one]
  · intro hm k k' hk hk'
    rw [dft_gket_apply u M N h c hc χ hχ k] at hk ⊢
    rw [dft_gket_apply u M N h c hc χ hχ k'] at hk' ⊢
    by_cases hd : M / c ∣ k.val
    · by_cases hd' : M / c ∣ k'.val
      · rw [ite_eq_left hd] at hk ⊢
        rw [ite_eq_left hd'] at hk' ⊢
        have pw : ∀ y : ZMod c, χ⁻¹ y ≠ 0 → (χ⁻¹ y) ^ m = 1 := by
          intro y hy
          have hun : IsUnit y := by
            by_contra hn; exact hy (MulChar.map_nonunit _ hn)
          obtain ⟨a, rfl⟩ := hun
          have : (χ⁻¹ a) ^ m = (χ ^ m)⁻¹ a := by
            rw [← MulChar.pow_apply_coe, inv_pow]
          rw [this, hm, inv_one, MulChar.one_apply_coe]
        have h1 := pw (((k.val / (M / c) : ℕ) : ZMod c)) (fun h0 => hk (by rw [h0, mul_zero]))
        have h2 := pw (((k'.val / (M / c) : ℕ) : ZMod c)) (fun h0 => hk' (by rw [h0, mul_zero]))
        simp only [mul_pow, h1, h2, mul_one]
      · rw [ite_eq_right hd'] at hk'; exact absurd rfl hk'
    · rw [ite_eq_right hd] at hk; exact absurd rfl hk

/-! ### 4. 固有値の一様分布と特性多項式 -/

/-- 冪和が消えれば、値は F(t₀)·μ_o に一様に分布する（Part 99 の方法を抽象化）。 -/
theorem fiber_of_power_sums {α : Type*} [DecidableEq α] (T : Finset α) (F : α → ℂ) (t₀ : α) (o : ℕ)
    (ho : 0 < o) (hF0 : F t₀ ≠ 0) (hpow : ∀ t ∈ T, (F t / F t₀) ^ o = 1)
    (hsum : ∀ j : ℕ, 0 < j → j < o → ∑ t ∈ T, (F t / F t₀) ^ j = 0) (ξ : ℂ) (hξ : ξ ^ o = 1) :
    o * (T.filter (fun t => F t = F t₀ * ξ)).card = T.card := by
  classical
  have hξ0 : ξ ≠ 0 := by intro h0; rw [h0, zero_pow ho.ne'] at hξ; exact zero_ne_one hξ
  set c := F t₀ * ξ with hc
  have hc0 : c ≠ 0 := mul_ne_zero hF0 hξ0
  have hy : ∀ t ∈ T, (F t / c) ^ o = 1 := by
    intro t ht
    rw [hc, div_mul_eq_div_div, div_pow, hpow t ht, hξ, div_one]
  have h1 : ((o * (T.filter (fun t => F t = c)).card : ℕ) : ℂ)
      = ∑ t ∈ T, ∑ j ∈ Finset.range o, (F t / c) ^ j := by
    rw [Nat.cast_mul, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [PAG.Part103.geom_indicator o _ (hy t ht)]
    by_cases hFt : F t = c
    · rw [ite_eq_left hFt, ite_eq_left (by rw [hFt, div_self hc0])]; simp
    · rw [ite_eq_right hFt, ite_eq_right (fun e => hFt (by rwa [div_eq_one_iff_eq hc0] at e))]; simp
  have h2 : ∑ t ∈ T, ∑ j ∈ Finset.range o, (F t / c) ^ j
      = ∑ j ∈ Finset.range o, (ξ⁻¹) ^ j * ∑ t ∈ T, (F t / F t₀) ^ j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hc, div_mul_eq_div_div, div_pow, div_eq_mul_inv ((F t / F t₀) ^ j), ← inv_pow, mul_comm]
  have h3 : ∑ j ∈ Finset.range o, (ξ⁻¹) ^ j * ∑ t ∈ T, (F t / F t₀) ^ j = (T.card : ℂ) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j hj hj0
      rw [hsum j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj), mul_zero]
    · intro h0; exact absurd (Finset.mem_range.mpr ho) h0
  have h4 : ((o * (T.filter (fun t => F t = c)).card : ℕ) : ℂ) = ((T.card : ℕ) : ℂ) := by
    rw [h1, h2, h3]
  exact_mod_cast h4

/-- 固有値の比の冪和：0 < j < ord χ なら Σ_k [M/c ∣ k]·χ̄(k/(M/c))^j = 0。 -/
theorem sum_pow_chi_eq_zero (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (j : ℕ) (hj0 : 0 < j) (hjo : j < orderOf χ) :
    ∑ k : ZMod N, (if M / c ∣ k.val then (χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c)) ^ j else 0) = 0 := by
  classical
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hu : 0 < u := pos_of_mul h
  have hucZ : NeZero (u * c) := ⟨mul_ne_zero hu.ne' hc0.ne'⟩
  set ψ : DirichletCharacter ℂ c := χ⁻¹ ^ j with hψ
  have hψ1 : ψ ≠ 1 := by
    intro h1
    have : χ ^ j = 1 := by
      have e : (χ ^ j)⁻¹ = 1 := by rw [← inv_pow]; exact h1
      exact inv_eq_one.mp e
    exact pow_ne_one_of_lt_orderOf hj0.ne' hjo this
  have hval : ∀ x : ZMod c, (χ⁻¹ x) ^ j = ψ x := fun x => (MulChar.pow_apply' χ⁻¹ hj0.ne' x).symm
  -- 押し出しとして書く
  have e1 : ∀ k : ZMod N, (if M / c ∣ k.val then (χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c)) ^ j else 0)
      = PAG.Part17.push (memb (M / c) (u * c) N (dual_eq h hc))
          (fun y => ψ (ZMod.castHom (dvd_mul_left c u) (ZMod c) y)) k := by
    intro k
    rw [push_memb_apply, map_natCast (ZMod.castHom (dvd_mul_left c u) (ZMod c)), hval]
  rw [Finset.sum_congr rfl (fun k _ => e1 k)]
  have e2 := PAG.Part17.sum_push_mul (memb (M / c) (u * c) N (dual_eq h hc))
    (memb_injective _ _ _ (dual_eq h hc)) (fun y => ψ (ZMod.castHom (dvd_mul_left c u) (ZMod c) y))
    (fun _ => (1 : ℂ))
  simp only [mul_one] at e2
  rw [e2]
  have e3 := PAG.Part17.sum_comp_surj (ZMod.castHom (dvd_mul_left c u) (ZMod c)).toAddMonoidHom
    (ZMod.ringHom_surjective _) (fun x => ψ x)
  rw [show (∑ y : ZMod (u * c), ψ (ZMod.castHom (dvd_mul_left c u) (ZMod c) y))
      = ∑ y : ZMod (u * c), (fun x => ψ x) ((ZMod.castHom (dvd_mul_left c u) (ZMod c)).toAddMonoidHom y)
      from rfl, e3, MulChar.sum_eq_zero_of_ne_one hψ1, mul_zero]

/-- **4. 固有値の一様分布**（Part 118 の Unif の大域版）：台 T 上で 𝓕|u, χ⟩ は 𝓕|u, χ⟩(t₀)·μ_{ord χ} に
一様に分布する（t₀ = M/c）。 -/
theorem gket_unif (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    PAG.Part122.Unif (Finset.univ.filter (fun k : ZMod N => 𝓕 (gket u M N h c hc χ) k ≠ 0))
      (fun k => 𝓕 (gket u M N h c hc χ) k)
      (((M / c * ((1 : (ZMod c)ˣ) : ZMod c).val : ℕ) : ZMod N)) (orderOf χ) := by
  classical
  have hMZ := neZero_of_mul h
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hMc : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc) hc0
  have hMle : M ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Dvd.intro_left u h)
  set B : ℂ := (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) *
    gaussSum χ stdAddChar with hB
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  have hB0 : B ≠ 0 := by
    have hm1 : χ⁻¹ (-1) ≠ 0 := by
      have : ((-1 : (ZMod c)ˣ) : ZMod c) = -1 := by simp
      rw [← this]; exact ((-1 : (ZMod c)ˣ).isUnit.map χ⁻¹).ne_zero
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) hm1) (PAG.Part16.gaussSum_ne_zero hχ)
    · exact_mod_cast (inv_pos.mpr hφM).ne'
    · exact_mod_cast hMc.ne'
  have hFk : ∀ k : ZMod N, 𝓕 (gket u M N h c hc χ) k = if M / c ∣ k.val then B * χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c) else 0 :=
    fun k => dft_gket_apply u M N h c hc χ hχ k
  set t₀ : ZMod N := ((M / c * ((1 : (ZMod c)ˣ) : ZMod c).val : ℕ) : ZMod N) with ht₀
  have hFt₀ : 𝓕 (gket u M N h c hc χ) t₀ = B := by
    have hlt : M / c * ((1 : (ZMod c)ˣ) : ZMod c).val < N := by
      have h1 : ((1 : (ZMod c)ˣ) : ZMod c).val < c := ZMod.val_lt _
      calc M / c * ((1 : (ZMod c)ˣ) : ZMod c).val < M / c * c := Nat.mul_lt_mul_of_pos_left h1 hMc
        _ = M := Nat.div_mul_cancel hc
        _ ≤ N := hMle
    rw [hFk, ht₀, ZMod.val_natCast_of_lt hlt, ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ hMc,
      ZMod.natCast_zmod_val, Units.val_one, map_one, mul_one]
  have hratio : ∀ k : ZMod N, 𝓕 (gket u M N h c hc χ) k / 𝓕 (gket u M N h c hc χ) t₀ = if M / c ∣ k.val then χ⁻¹ ((k.val / (M / c) : ℕ) : ZMod c) else 0 := by
    intro k
    rw [hFt₀, hFk]
    split_ifs
    · field_simp
    · rw [zero_div]
  have ho : 0 < orderOf χ := orderOf_pos χ
  have hχo : χ ^ orderOf χ = 1 := pow_orderOf_eq_one χ
  refine ⟨?_, ho, ?_, ?_, ?_⟩
  · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by rw [hFt₀]; exact hB0⟩
  · show 𝓕 (gket u M N h c hc χ) t₀ ≠ 0; rw [hFt₀]; exact hB0
  · intro t ht
    have htF : 𝓕 (gket u M N h c hc χ) t ≠ 0 := (Finset.mem_filter.mp ht).2
    show (𝓕 (gket u M N h c hc χ) t / 𝓕 (gket u M N h c hc χ) t₀) ^ orderOf χ = 1
    rw [hratio]
    by_cases hd : M / c ∣ t.val
    · rw [ite_eq_left hd]
      have hne : χ⁻¹ ((t.val / (M / c) : ℕ) : ZMod c) ≠ 0 := by
        intro h0; apply htF; rw [hFk, ite_eq_left hd, h0, mul_zero]
      have hun : IsUnit ((t.val / (M / c) : ℕ) : ZMod c) := by
        by_contra hn; exact hne (MulChar.map_nonunit _ hn)
      obtain ⟨a, ha⟩ := hun
      rw [← ha, ← MulChar.pow_apply_coe, inv_pow, hχo, inv_one, MulChar.one_apply_coe]
    · exact absurd (by rw [hFk, ite_eq_right hd]) htF
  · intro ξ hξ
    apply fiber_of_power_sums _ (fun k => 𝓕 (gket u M N h c hc χ) k) t₀ _ ho (by rw [hFt₀]; exact hB0) _ _ ξ hξ
    · intro t ht
      have htF : 𝓕 (gket u M N h c hc χ) t ≠ 0 := (Finset.mem_filter.mp ht).2
      rw [hratio]
      by_cases hd : M / c ∣ t.val
      · rw [ite_eq_left hd]
        have hne : χ⁻¹ ((t.val / (M / c) : ℕ) : ZMod c) ≠ 0 := by
          intro h0; apply htF; rw [hFk, ite_eq_left hd, h0, mul_zero]
        have hun : IsUnit ((t.val / (M / c) : ℕ) : ZMod c) := by
          by_contra hn; exact hne (MulChar.map_nonunit _ hn)
        obtain ⟨a, ha⟩ := hun
        rw [← ha, ← MulChar.pow_apply_coe, inv_pow, hχo, inv_one, MulChar.one_apply_coe]
      · exact absurd (by rw [hFk, ite_eq_right hd]) htF
    · intro j hj0 hjo
      have e := sum_pow_chi_eq_zero u M N h c hc χ j hj0 hjo
      have hG : ∀ t ∈ Finset.univ.filter (fun k : ZMod N => 𝓕 (gket u M N h c hc χ) k ≠ 0),
          (𝓕 (gket u M N h c hc χ) t / 𝓕 (gket u M N h c hc χ) t₀) ^ j
            = (if M / c ∣ t.val then (χ⁻¹ ((t.val / (M / c) : ℕ) : ZMod c)) ^ j else 0) := by
        intro t _
        rw [hratio]
        split_ifs <;> simp [zero_pow hj0.ne']
      show ∑ t ∈ Finset.univ.filter (fun k : ZMod N => 𝓕 (gket u M N h c hc χ) k ≠ 0),
          (𝓕 (gket u M N h c hc χ) t / 𝓕 (gket u M N h c hc χ) t₀) ^ j = 0
      rw [Finset.sum_congr rfl hG, Finset.sum_subset (Finset.subset_univ _) ?_]
      · exact e
      · intro t _ ht
        have hFt : 𝓕 (gket u M N h c hc χ) t = 0 := by
          by_contra hne; exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        by_cases hd : M / c ∣ t.val
        · rw [ite_eq_left hd]
          rw [hFk, ite_eq_left hd] at hFt
          rw [(mul_eq_zero.mp hFt).resolve_left hB0, zero_pow hj0.ne']
        · rw [ite_eq_right hd]

/-- **4'. 特性多項式の閉じた形**（Part 118 の大域版）：
Π_{t ∈ T}(X − 𝓕|u, χ⟩(t)) = (X^o − 𝓕|u, χ⟩(t₀)^o)^(|T|/o)、o = ord χ。 -/
theorem gket_charpoly (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    ∏ t ∈ Finset.univ.filter (fun k : ZMod N => 𝓕 (gket u M N h c hc χ) k ≠ 0),
        (Polynomial.X - Polynomial.C (𝓕 (gket u M N h c hc χ) t))
      = (Polynomial.X ^ orderOf χ - Polynomial.C ((𝓕 (gket u M N h c hc χ)
          (((M / c * ((1 : (ZMod c)ˣ) : ZMod c).val : ℕ) : ZMod N))) ^ orderOf χ)) ^
        ((Finset.univ.filter (fun k : ZMod N => 𝓕 (gket u M N h c hc χ) k ≠ 0)).card / orderOf χ) :=
  PAG.Part122.closed_of_unif (gket_unif u M N h c hc χ hχ)

end PAG.Part202

#print axioms PAG.Part202.push_memb_apply
#print axioms PAG.Part202.dft_push_memb
#print axioms PAG.Part202.dft_pull
#print axioms PAG.Part202.dual_eq
#print axioms PAG.Part202.dft_gket
#print axioms PAG.Part202.dft_gket_unitary
#print axioms PAG.Part202.normSq_chi_unit
#print axioms PAG.Part202.dft_gket_apply
#print axioms PAG.Part202.normSq_dft_gket
#print axioms PAG.Part202.normSq_dft_gket'
#print axioms PAG.Part202.pow_const_iff
#print axioms PAG.Part202.fiber_of_power_sums
#print axioms PAG.Part202.sum_pow_chi_eq_zero
#print axioms PAG.Part202.gket_unif
#print axioms PAG.Part202.gket_charpoly
