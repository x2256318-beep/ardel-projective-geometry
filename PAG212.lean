/-
  PAG 2.0 Part 208（2026-10-24）— ケット基底の双対基底（座標の式）とブロック直交性
  ケット k = |u, χ⟩_N（χ は法 c の原始指標、M = N/u、s₀ = M/c）、B = kcoef(M, c, χ)。
  g_{s,ψ} は Part 204 の基底ベクトル、χ̄′ = liftc χ⁻¹ n は χ⁻¹ を法 n へ持ち上げたもの。
  1. 内積：s·n = N なら ⟨g_{s,ψ}, k⟩ = [s₀ ∣ s, s/s₀ ∣ u]·B·χ̄(s/s₀)·[ψ = χ̄′]·φ(n)/N
  2. 双対ベクトル k^∨ = Σ_{e ∣ s₀} conj(B⁻¹μ(e)χ̄(e)·N/φ(N/(s₀/e)))·g_{s₀/e, χ̄′}：
     ⟨k^∨_{(u,c,χ)}, |u′, χ′⟩⟩ = [(u, c, χ) = (u′, c′, χ′)]
     （(c, χ) が違えば指標の持ち上げが違うので 0、同じならメビウス関数の和 Σ_{e ∣ r} μ(e) = [r = 1]）
  3. 座標：ケット基底での f の座標は ⟨k^∨, f⟩ = B⁻¹ Σ_{e ∣ s₀} μ(e)χ̄(e)·(N/φ(N/(s₀/e)))·⟨g_{s₀/e, χ̄′}, f⟩、
     B⁻¹ = τ(χ̄)√φ(M)/M。f = Σ_i ⟨k_i^∨, f⟩·k_i
  4. ブロック直交性：(c, χ) が違うケットは直交する
-/
import PAG211

namespace PAG.Part212

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** 内積の第 2 引数の線形性：⟨v, Σ_j b_j·w_j⟩ = Σ_j b_j·⟨v, w_j⟩。 -/
theorem inner_sum_smul_right {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (v : ZMod N → ℂ) (b : ι → ℂ)
    (w : ι → ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (v x) * (∑ j ∈ S, b j • w j) x =
      ∑ j ∈ S, b j * ∑ x, starRingEnd ℂ (v x) * w j x := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun x _ => by ring))

/-- **0b.** 内積の第 1 引数：⟨Σ_s a_s·v_s, f⟩ = Σ_s conj(a_s)·⟨v_s, f⟩。 -/
theorem inner_sum_smul_left {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (a : ι → ℂ) (v : ι → ZMod N → ℂ)
    (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ ((∑ s ∈ S, a s • v s) x) * f x =
      ∑ s ∈ S, starRingEnd ℂ (a s) * ∑ x, starRingEnd ℂ (v s x) * f x := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun x _ => by ring))

/-- **0c.** B⁻¹ = τ(χ̄)·√φ(M)/M（χ 原始的、c ∣ M、M ≠ 0）。 -/
theorem kcoef_inv (M c : ℕ) [NeZero c] (hM : M ≠ 0) (hc : c ∣ M) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (kcoef M c χ)⁻¹ = gaussSum χ⁻¹ stdAddChar * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) / (M : ℂ) := by
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM))
  have hsq0 : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hm : χ⁻¹ (-1) * χ (-1) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_one.neg]
  have hMc : ((M / c : ℕ) : ℂ) * (c : ℂ) = (M : ℂ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hc]
  apply inv_eq_of_mul_eq_one_right
  unfold kcoef
  rw [Complex.ofReal_inv]
  calc ((Real.sqrt (Nat.totient M) : ℝ) : ℂ)⁻¹ * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar *
        (gaussSum χ⁻¹ stdAddChar * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) / (M : ℂ))
      = (((Real.sqrt (Nat.totient M) : ℝ) : ℂ)⁻¹ * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ)) *
          ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * (gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar) / (M : ℂ) := by
        ring
    _ = 1 := by
        rw [inv_mul_cancel₀ hsq0, PAG.Part16.gauss_mul_gauss_inv_eq hχ, div_eq_one_iff_eq hMC, ← hMc]
        linear_combination ((M / c : ℕ) : ℂ) * (c : ℂ) * hm

/-- **0d.** s·r ≠ 0 なら e ∣ s·r について (s ∣ s·r/e ⇔ e ∣ r)（s > 0）。 -/
theorem dvd_div_iff_dvd (s r e : ℕ) (hs : 0 < s) (he : e ∣ s * r) : s ∣ s * r / e ↔ e ∣ r := by
  constructor
  · rintro ⟨m, hm⟩
    have h1 : s * r = s * (m * e) := by
      rw [← mul_assoc, ← hm, Nat.div_mul_cancel he]
    exact Dvd.intro_left m (Nat.eq_of_mul_eq_mul_left hs h1).symm
  · intro her
    exact ⟨r / e, Nat.mul_div_assoc s her⟩

/-- **0e.** e ∣ r なら s·r/e/s = r/e（s > 0）。 -/
theorem mul_div_div_cancel (s r e : ℕ) (hs : 0 < s) (her : e ∣ r) : s * r / e / s = r / e := by
  rw [Nat.mul_div_assoc s her, Nat.mul_div_cancel_left _ hs]

/-- **0f.** Σ_{e ∣ s·r} [e ∣ r]·μ(e) = [r = 1]（s·r ≠ 0）。 -/
theorem sum_moebius_dvd_filter (s r : ℕ) (h0 : s * r ≠ 0) :
    ∑ e ∈ (s * r).divisors, (if e ∣ r then (ArithmeticFunction.moebius e : ℂ) else 0) =
      if r = 1 then 1 else 0 := by
  have hr0 : r ≠ 0 := right_ne_zero_of_mul h0
  have e : (s * r).divisors.filter (fun e => e ∣ r) = r.divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, her⟩
      exact ⟨her, hr0⟩
    · rintro ⟨her, _⟩
      exact ⟨⟨dvd_mul_of_dvd_right her s, h0⟩, her⟩
  rw [← Finset.sum_filter, e, sum_moebius_divisors]

/-- **0g.** 双対殻の分解：e ∣ N/u/c（u ∣ N、c ∣ N/u）なら (N/u/c/e)·(u·e·c) = N。 -/
theorem kdual_shell_eq (N u c e : ℕ) (hu : u ∣ N) (hcu : c ∣ N / u) (he : e ∣ N / u / c) :
    N / u / c / e * (u * e * c) = N := by
  rw [show N / u / c / e * (u * e * c) = u * ((N / u / c / e * e) * c) by ring, Nat.div_mul_cancel he,
    Nat.div_mul_cancel hcu, Nat.mul_div_cancel' hu]

/-- **0h.** 持ち上げの比較：c, c′ ∣ n で、原始指標 χ, χ′ の持ち上げ χ̄′, χ̄′′ が等しければ c = c′。 -/
theorem conductor_eq_of_liftc_eq (n : ℕ) [NeZero n] {c c' : ℕ} (hcn : c ∣ n) (hc'n : c' ∣ n)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (e : liftc χ⁻¹ n = liftc χ'⁻¹ n) : c = c' := by
  rw [liftc_of_dvd χ⁻¹ hcn, liftc_of_dvd χ'⁻¹ hc'n] at e
  have h := congrArg DirichletCharacter.conductor e
  rwa [conductor_changeLevel_inv n c hcn χ hχ, conductor_changeLevel_inv n c' hc'n χ' hχ'] at h

/-- **0i.** 同じ c ∣ n で χ̄′ = χ̄′′ なら χ = χ′。 -/
theorem eq_of_liftc_eq (n : ℕ) [NeZero n] {c : ℕ} (hcn : c ∣ n) (χ χ' : DirichletCharacter ℂ c)
    (e : liftc χ⁻¹ n = liftc χ'⁻¹ n) : χ = χ' := by
  rw [liftc_of_dvd χ⁻¹ hcn, liftc_of_dvd χ'⁻¹ hcn] at e
  exact changeLevel_inv_injective n c hcn χ χ' e

/-! ### 1. 基底ベクトルとケットの内積 -/

open Classical in
/-- **1. 内積**：s·n = N のとき ⟨g_{s,ψ}, |u, χ⟩⟩ = [s₀ ∣ s, s/s₀ ∣ u]·B·χ̄(s/s₀)·[ψ = χ̄′]·φ(n)/N
（s₀ = M/c、χ̄′ = liftc χ⁻¹ n）。 -/
theorem inner_gbas_gket (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n)
    (u M : ℕ) (hM : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    ∑ j, starRingEnd ℂ (gbas s n N ψ j) * gket u M N hM c hc χ j =
      if M / c ∣ s ∧ s / (M / c) ∣ u then
        kcoef M c χ * χ⁻¹ ((s / (M / c) : ℕ) : ZMod c) *
          (if ψ = liftc χ⁻¹ n then (Nat.totient n : ℂ) / N else 0)
      else 0 := by
  have hn : n = N / s := (Nat.div_eq_of_eq_mul_right (pos_of_mul h) h.symm).symm
  subst hn
  have hMZ := neZero_of_mul hM
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  rw [← inner_gbas_geps_conv s (N / s) N h ψ]
  by_cases hcond : M / c ∣ s ∧ s / (M / c) ∣ u
  · rw [ite_eq_left hcond, geps_conv_gket_canon u M N hM c hc χ hχ s hcond.1 hcond.2]
    simp only [Pi.smul_apply, smul_eq_mul]
    have e : ∑ j, starRingEnd ℂ (gbas s (N / s) N ψ j) *
        (kcoef M c χ * χ⁻¹ ((s / (M / c) : ℕ) : ZMod c) * gbas s (N / s) N (liftc χ⁻¹ (N / s)) j) =
        kcoef M c χ * χ⁻¹ ((s / (M / c) : ℕ) : ZMod c) *
          ∑ j, starRingEnd ℂ (gbas s (N / s) N ψ j) * gbas s (N / s) N (liftc χ⁻¹ (N / s)) j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [e, inner_gbas s (N / s) N h ψ (liftc χ⁻¹ (N / s))]
  · rw [ite_eq_right hcond, geps_conv_gket_eq_zero u M N hM c hc χ hχ s
      (fun t ht _ hst => hcond ⟨⟨t, hst⟩, by rw [hst, Nat.mul_div_cancel_left t hs0]; exact ht⟩)]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-! ### 2. 双対ベクトル -/

/-- 双対ベクトル：k^∨ = Σ_{e ∣ s₀} conj(B⁻¹μ(e)χ̄(e)·N/φ(N/(s₀/e)))·g_{s₀/e, χ̄′}（M = N/u、s₀ = M/c）。 -/
noncomputable def kdual (N u c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) : ZMod N → ℂ :=
  ∑ e ∈ (N / u / c).divisors,
    starRingEnd ℂ ((kcoef (N / u) c χ)⁻¹ * ((ArithmeticFunction.moebius e : ℂ) * χ⁻¹ (e : ZMod c)) *
        ((N : ℂ) / (Nat.totient (N / (N / u / c / e)) : ℂ))) •
      gbas (N / u / c / e) (N / (N / u / c / e)) N (liftc χ⁻¹ (N / (N / u / c / e)))

/-- **2a.** ⟨k^∨, f⟩ = B⁻¹ Σ_{e ∣ s₀} μ(e)χ̄(e)·(N/φ(N/(s₀/e)))·⟨g_{s₀/e, χ̄′}, f⟩。 -/
theorem inner_kdual (N u c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * f x =
      ∑ e ∈ (N / u / c).divisors,
        (kcoef (N / u) c χ)⁻¹ * ((ArithmeticFunction.moebius e : ℂ) * χ⁻¹ (e : ZMod c)) *
          ((N : ℂ) / (Nat.totient (N / (N / u / c / e)) : ℂ)) *
          ∑ x, starRingEnd ℂ (gbas (N / u / c / e) (N / (N / u / c / e)) N
            (liftc χ⁻¹ (N / (N / u / c / e))) x) * f x := by
  unfold kdual
  rw [inner_sum_smul_left]
  simp only [Complex.conj_conj]

/-- **2b. 同じ (c, χ)**：⟨k^∨_{(u,c,χ)}, |u′, χ⟩⟩ = [u = u′]。 -/
theorem inner_kdual_gket_same (N u c : ℕ) [NeZero N] [NeZero c] (hu : u ∣ N) (hcu : c ∣ N / u)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (hc' : c ∣ M') :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * gket u' M' N h' c hc' χ x = if u = u' then 1 else 0 := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hM'Z := neZero_of_mul h'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hu0 : 0 < u := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr ⟨hu, hN0⟩)
  have hNu : u * (N / u) = N := Nat.mul_div_cancel' hu
  have hNuc : N / u / c * c = N / u := Nat.div_mul_cancel hcu
  have hM'c : M' / c * c = M' := Nat.div_mul_cancel hc'
  have hNu0 : N / u ≠ 0 := fun h0 => hN0 (by rw [← hNu, h0, mul_zero])
  have hs₀pos : 0 < N / u / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hNu0) hcu) hc0
  have hs₀'pos : 0 < M' / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M')) hc') hc0
  have hkey : u * (N / u / c) = u' * (M' / c) :=
    Nat.eq_of_mul_eq_mul_right hc0 (by rw [mul_assoc, hNuc, hNu, mul_assoc, hM'c, h'])
  -- 各項の内積の形（s = N/u/c/e）
  have hsh : ∀ e ∈ (N / u / c).divisors, N / u / c / e * (N / (N / u / c / e)) = N := by
    intro e he
    have h1 := kdual_shell_eq N u c e hu hcu (Nat.dvd_of_mem_divisors he)
    have hpos : 0 < N / u / c / e :=
      Nat.div_pos (Nat.le_of_dvd hs₀pos (Nat.dvd_of_mem_divisors he)) (Nat.pos_of_mem_divisors he)
    rw [Nat.div_eq_of_eq_mul_right hpos h1.symm, h1]
  rw [inner_kdual]
  by_cases hdiv : M' / c ∣ N / u / c
  · obtain ⟨r, hr⟩ := hdiv
    have hr0 : M' / c * r ≠ 0 := by rw [← hr]; exact hs₀pos.ne'
    have hur : u * r = u' := by
      have h2 : M' / c * (u * r) = M' / c * u' := by
        rw [mul_comm (M' / c) u', ← hkey, hr]
        ring
      exact Nat.eq_of_mul_eq_mul_left hs₀'pos h2
    have hterm : ∀ e ∈ (N / u / c).divisors,
        (kcoef (N / u) c χ)⁻¹ * ((ArithmeticFunction.moebius e : ℂ) * χ⁻¹ (e : ZMod c)) *
            ((N : ℂ) / (Nat.totient (N / (N / u / c / e)) : ℂ)) *
            ∑ x, starRingEnd ℂ (gbas (N / u / c / e) (N / (N / u / c / e)) N
              (liftc χ⁻¹ (N / (N / u / c / e))) x) * gket u' M' N h' c hc' χ x =
          if e ∣ r then
            ((kcoef (N / u) c χ)⁻¹ * kcoef M' c χ * χ⁻¹ (r : ZMod c)) * (ArithmeticFunction.moebius e : ℂ)
          else 0 := by
      intro e he
      have hn0 : N / (N / u / c / e) ≠ 0 := by
        intro h0
        have := hsh e he
        rw [h0, mul_zero] at this
        exact hN0 this.symm
      have hφ : (Nat.totient (N / (N / u / c / e)) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)).ne'
      have he' : e ∣ M' / c * r := by rw [← hr]; exact Nat.dvd_of_mem_divisors he
      rw [inner_gbas_gket (N / u / c / e) (N / (N / u / c / e)) N (hsh e he) _ u' M' h' c hc' χ hχ, hr]
      by_cases her : e ∣ r
      · have hd1 : M' / c ∣ M' / c * r / e := (dvd_div_iff_dvd _ _ _ hs₀'pos he').mpr her
        have hq : M' / c * r / e / (M' / c) = r / e := mul_div_div_cancel _ _ _ hs₀'pos her
        have hd2 : M' / c * r / e / (M' / c) ∣ u' := by
          rw [hq, ← hur]
          exact dvd_mul_of_dvd_right (Nat.div_dvd_of_dvd her) u
        have hχr : χ⁻¹ (e : ZMod c) * χ⁻¹ ((r / e : ℕ) : ZMod c) = χ⁻¹ (r : ZMod c) := by
          rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' her]
        have hcancel : (N : ℂ) / (Nat.totient (N / (M' / c * r / e)) : ℂ) *
            ((Nat.totient (N / (M' / c * r / e)) : ℂ) / N) = 1 := by
          rw [← hr]
          field_simp
        rw [ite_eq_left ⟨hd1, hd2⟩, ite_eq_left rfl, ite_eq_left her, hq, ← hχr]
        linear_combination ((kcoef (N / u) c χ)⁻¹ * kcoef M' c χ *
          (χ⁻¹ (e : ZMod c) * χ⁻¹ ((r / e : ℕ) : ZMod c)) * (ArithmeticFunction.moebius e : ℂ)) * hcancel
      · have hd1 : ¬ M' / c ∣ M' / c * r / e := fun hh => her ((dvd_div_iff_dvd _ _ _ hs₀'pos he').mp hh)
        rw [ite_eq_right (fun hh => hd1 hh.1), ite_eq_right her, mul_zero]
    rw [Finset.sum_congr rfl hterm, hr]
    have hfac : ∑ e ∈ (M' / c * r).divisors, (if e ∣ r then
          ((kcoef (N / u) c χ)⁻¹ * kcoef M' c χ * χ⁻¹ (r : ZMod c)) * (ArithmeticFunction.moebius e : ℂ)
          else 0) =
        ((kcoef (N / u) c χ)⁻¹ * kcoef M' c χ * χ⁻¹ (r : ZMod c)) *
          ∑ e ∈ (M' / c * r).divisors, (if e ∣ r then (ArithmeticFunction.moebius e : ℂ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      split_ifs <;> simp
    rw [hfac, sum_moebius_dvd_filter (M' / c) r hr0]
    by_cases hr1 : r = 1
    · subst hr1
      have huu : u = u' := by rw [← hur, mul_one]
      have hM : N / u = M' := by rw [← hNuc, hr, mul_one, hM'c]
      rw [ite_eq_left rfl, ite_eq_left huu, mul_one, Nat.cast_one, map_one, mul_one, hM,
        inv_mul_cancel₀ (kcoef_ne_zero M' c (NeZero.ne M') hc' χ hχ)]
    · rw [ite_eq_right hr1, mul_zero, ite_eq_right]
      intro huu
      apply hr1
      exact Nat.eq_of_mul_eq_mul_left hu0 (by rw [hur, mul_one, huu])
  · rw [Finset.sum_eq_zero (fun e he => by
      rw [inner_gbas_gket (N / u / c / e) (N / (N / u / c / e)) N (hsh e he) _ u' M' h' c hc' χ hχ,
        ite_eq_right (fun hh => hdiv (dvd_trans hh.1 (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)))),
        mul_zero]), ite_eq_right]
    intro huu
    apply hdiv
    subst huu
    exact ⟨1, by rw [mul_one, Nat.eq_of_mul_eq_mul_left hu0 hkey]⟩

/-- **2c. 導手が違う**：c ≠ c′ なら ⟨k^∨_{(u,c,χ)}, |u′, χ′⟩⟩ = 0。 -/
theorem inner_kdual_gket_of_ne_conductor (N u c : ℕ) [NeZero N] [NeZero c] (hu : u ∣ N) (hcu : c ∣ N / u)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (c' : ℕ) [NeZero c']
    (hc' : c' ∣ M') (χ' : DirichletCharacter ℂ c') (hχ' : χ'.IsPrimitive) (hne : c ≠ c') :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * gket u' M' N h' c' hc' χ' x = 0 := by
  rw [inner_kdual]
  refine Finset.sum_eq_zero (fun e he => ?_)
  have he' : e ∣ N / u / c := Nat.dvd_of_mem_divisors he
  have h1 := kdual_shell_eq N u c e hu hcu he'
  have hs₀pos : 0 < N / u / c := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, Nat.zero_div, zero_mul] at h1; exact NeZero.ne N h1.symm)
  have hpos : 0 < N / u / c / e := Nat.div_pos (Nat.le_of_dvd hs₀pos he') (Nat.pos_of_mem_divisors he)
  have hn : N / (N / u / c / e) = u * e * c := Nat.div_eq_of_eq_mul_right hpos h1.symm
  have hsh : N / u / c / e * (N / (N / u / c / e)) = N := by rw [hn, h1]
  have hnZ : NeZero (N / (N / u / c / e)) := neZero_of_mul hsh
  have hcn : c ∣ N / (N / u / c / e) := by rw [hn]; exact dvd_mul_left c _
  rw [inner_gbas_gket (N / u / c / e) (N / (N / u / c / e)) N hsh _ u' M' h' c' hc' χ' hχ']
  split_ifs with hcond hψ
  · exfalso
    have hc'n : c' ∣ N / (N / u / c / e) := by
      rw [(shell_quot h' hc' hcond.1 hcond.2).2]; exact dvd_mul_left c' _
    exact hne (conductor_eq_of_liftc_eq _ hcn hc'n χ χ' hχ hχ' hψ)
  · simp
  · simp

/-- **2d. 同じ導手で指標が違う**：χ ≠ χ′ なら ⟨k^∨_{(u,c,χ)}, |u′, χ′⟩⟩ = 0（χ の原始性は要らない）。 -/
theorem inner_kdual_gket_of_ne (N u c : ℕ) [NeZero N] [NeZero c] (hu : u ∣ N) (hcu : c ∣ N / u)
    (χ : DirichletCharacter ℂ c) (u' M' : ℕ) (h' : u' * M' = N) (hc' : c ∣ M')
    (χ' : DirichletCharacter ℂ c) (hχ' : χ'.IsPrimitive) (hne : χ ≠ χ') :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * gket u' M' N h' c hc' χ' x = 0 := by
  rw [inner_kdual]
  refine Finset.sum_eq_zero (fun e he => ?_)
  have he' : e ∣ N / u / c := Nat.dvd_of_mem_divisors he
  have h1 := kdual_shell_eq N u c e hu hcu he'
  have hs₀pos : 0 < N / u / c := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, Nat.zero_div, zero_mul] at h1; exact NeZero.ne N h1.symm)
  have hpos : 0 < N / u / c / e := Nat.div_pos (Nat.le_of_dvd hs₀pos he') (Nat.pos_of_mem_divisors he)
  have hn : N / (N / u / c / e) = u * e * c := Nat.div_eq_of_eq_mul_right hpos h1.symm
  have hsh : N / u / c / e * (N / (N / u / c / e)) = N := by rw [hn, h1]
  have hnZ : NeZero (N / (N / u / c / e)) := neZero_of_mul hsh
  have hcn : c ∣ N / (N / u / c / e) := by rw [hn]; exact dvd_mul_left c _
  rw [inner_gbas_gket (N / u / c / e) (N / (N / u / c / e)) N hsh _ u' M' h' c hc' χ' hχ']
  split_ifs with hcond hψ
  · exact absurd (eq_of_liftc_eq _ hcn χ χ' hψ) hne
  · simp
  · simp

/-! ### 3. ケット基底での座標 -/

/-- 番号 i = (u, c, χ) の双対ベクトル。 -/
noncomputable def kdualI (N : ℕ) [NeZero N] (i : KetIdx N) : ZMod N → ℂ :=
  @kdual N i.1 i.2.1 _ ⟨(Nat.pos_of_mem_divisors i.2.1.2).ne'⟩ i.2.2.1

open Classical in
/-- **3a. 双直交性**：⟨k_i^∨, k_j⟩ = [i = j]。 -/
theorem inner_kdualI_ketFam (N : ℕ) [NeZero N] (i j : KetIdx N) :
    ∑ x, starRingEnd ℂ (kdualI N i x) * ketFam N j x = if i = j then 1 else 0 := by
  obtain ⟨⟨u, hu⟩, ⟨c, hc⟩, ⟨χ, hχ⟩⟩ := i
  obtain ⟨⟨u', hu'⟩, ⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := j
  have : NeZero c := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  have : NeZero c' := ⟨(Nat.pos_of_mem_divisors hc').ne'⟩
  have hu1 : u ∣ N := Nat.dvd_of_mem_divisors hu
  have hc1 : c ∣ N / u := Nat.dvd_of_mem_divisors hc
  show ∑ x, starRingEnd ℂ (kdual N u c χ x) *
      gket u' (N / u') N (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hu')) c' (Nat.dvd_of_mem_divisors hc') χ' x = _
  by_cases hcc : c = c'
  · subst hcc
    by_cases hχχ : χ = χ'
    · subst hχχ
      rw [inner_kdual_gket_same N u c hu1 hc1 χ hχ u' (N / u') _ _]
      by_cases huu : u = u'
      · subst huu
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right huu, ite_eq_right]
        intro e
        cases e
        exact huu rfl
    · rw [inner_kdual_gket_of_ne N u c hu1 hc1 χ u' (N / u') _ _ χ' hχ' hχχ, ite_eq_right]
      intro e
      cases e
      exact hχχ rfl
  · rw [inner_kdual_gket_of_ne_conductor N u c hu1 hc1 χ hχ u' (N / u') _ c' _ χ' hχ' hcc, ite_eq_right]
    intro e
    cases e
    exact hcc rfl

/-- **3b. 座標の式**：ケット基底での f の i 番目の座標は ⟨k_i^∨, f⟩。 -/
theorem ketBasis_repr (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (i : KetIdx N) :
    (ketBasis N).repr f i = ∑ x, starRingEnd ℂ (kdualI N i x) * f x := by
  classical
  let _ := Fintype.ofFinite (KetIdx N)
  conv_rhs => rw [← (ketBasis N).sum_repr f]
  rw [inner_sum_smul_right]
  simp only [ketBasis_apply, inner_kdualI_ketFam, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **3c. 展開**：f = Σ_i ⟨k_i^∨, f⟩·k_i（番号の集合の Fintype はどれでもよい）。 -/
theorem eq_sum_kdualI (N : ℕ) [NeZero N] [Fintype (KetIdx N)] (f : ZMod N → ℂ) :
    f = ∑ i, (∑ x, starRingEnd ℂ (kdualI N i x) * f x) • ketFam N i := by
  conv_lhs => rw [← (ketBasis N).sum_repr f]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ketBasis_repr, ketBasis_apply]

/-- **3d. 座標の式（係数を書き出した形）**：u ∣ N、c ∣ N/u、χ 原始的なら
⟨k^∨, f⟩ = (τ(χ̄)√φ(M)/M)·Σ_{e ∣ s₀} μ(e)χ̄(e)·(N/φ(N/(s₀/e)))·⟨g_{s₀/e, χ̄′}, f⟩（M = N/u）。 -/
theorem inner_kdual_explicit (N u c : ℕ) [NeZero N] [NeZero c] (hu : u ∣ N) (hcu : c ∣ N / u)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * f x =
      gaussSum χ⁻¹ stdAddChar * ((Real.sqrt (Nat.totient (N / u)) : ℝ) : ℂ) / ((N / u : ℕ) : ℂ) *
        ∑ e ∈ (N / u / c).divisors,
          (ArithmeticFunction.moebius e : ℂ) * χ⁻¹ (e : ZMod c) *
            ((N : ℂ) / (Nat.totient (N / (N / u / c / e)) : ℂ)) *
            ∑ x, starRingEnd ℂ (gbas (N / u / c / e) (N / (N / u / c / e)) N
              (liftc χ⁻¹ (N / (N / u / c / e))) x) * f x := by
  have hNu0 : N / u ≠ 0 := by
    intro h0
    have := Nat.mul_div_cancel' hu
    rw [h0, mul_zero] at this
    exact NeZero.ne N this.symm
  rw [inner_kdual, ← kcoef_inv (N / u) c hNu0 hcu χ hχ, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => by ring)

/-! ### 4. ブロック直交性 -/

/-- **4a.** 導手が違うケットは直交する：c ≠ c′ なら ⟨|u, χ⟩, |u′, χ′⟩⟩ = 0。 -/
theorem inner_gket_of_ne_conductor (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (c' : ℕ) [NeZero c']
    (hc' : c' ∣ M') (χ' : DirichletCharacter ℂ c') (hχ' : χ'.IsPrimitive) (hne : c ≠ c') :
    ∑ x, starRingEnd ℂ (gket u M N h c hc χ x) * gket u' M' N h' c' hc' χ' x = 0 := by
  rw [gket_eq_sum_gbas u M N h c hc χ hχ, inner_sum_smul_left]
  refine Finset.sum_eq_zero (fun t ht => ?_)
  have htu : t ∣ u := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1
  have hst := shell_eq h hc htu
  have hnZ : NeZero (u / t * c) := neZero_of_mul hst
  rw [inner_gbas_gket (M / c * t) (u / t * c) N hst _ u' M' h' c' hc' χ' hχ']
  split_ifs with hcond hψ
  · exfalso
    have hNs : N / (M / c * t) = u / t * c := Nat.div_eq_of_eq_mul_right (pos_of_mul hst) hst.symm
    have hc'n : c' ∣ u / t * c := by
      rw [← hNs, (shell_quot h' hc' hcond.1 hcond.2).2]; exact dvd_mul_left c' _
    rw [← liftc_of_dvd χ⁻¹ (dvd_mul_left c (u / t))] at hψ
    exact hne (conductor_eq_of_liftc_eq _ (dvd_mul_left c (u / t)) hc'n χ χ' hχ hχ' hψ)
  · simp
  · simp

/-- **4b.** 同じ導手で指標が違うケットは直交する：χ ≠ χ′ なら ⟨|u, χ⟩, |u′, χ′⟩⟩ = 0。 -/
theorem inner_gket_of_ne (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (u' M' : ℕ) (h' : u' * M' = N) (hc' : c ∣ M')
    (χ' : DirichletCharacter ℂ c) (hχ' : χ'.IsPrimitive) (hne : χ ≠ χ') :
    ∑ x, starRingEnd ℂ (gket u M N h c hc χ x) * gket u' M' N h' c hc' χ' x = 0 := by
  rw [gket_eq_sum_gbas u M N h c hc χ hχ, inner_sum_smul_left]
  refine Finset.sum_eq_zero (fun t ht => ?_)
  have htu : t ∣ u := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1
  have hst := shell_eq h hc htu
  have hnZ : NeZero (u / t * c) := neZero_of_mul hst
  rw [inner_gbas_gket (M / c * t) (u / t * c) N hst _ u' M' h' c hc' χ' hχ']
  split_ifs with hcond hψ
  · rw [← liftc_of_dvd χ⁻¹ (dvd_mul_left c (u / t))] at hψ
    exact absurd (eq_of_liftc_eq _ (dvd_mul_left c (u / t)) χ χ' hψ) hne
  · simp
  · simp

/-- ケットの番号のブロック (c, χ)。 -/
def ketClass {N : ℕ} (i : KetIdx N) : Σ c : ℕ, DirichletCharacter ℂ c := ⟨i.2.1, i.2.2.1⟩

/-- **4c. ブロック直交性**：(c, χ) が違うケットは直交する。 -/
theorem inner_ketFam_of_ketClass_ne (N : ℕ) [NeZero N] (i j : KetIdx N) (hne : ketClass i ≠ ketClass j) :
    ∑ x, starRingEnd ℂ (ketFam N i x) * ketFam N j x = 0 := by
  obtain ⟨⟨u, hu⟩, ⟨c, hc⟩, ⟨χ, hχ⟩⟩ := i
  obtain ⟨⟨u', hu'⟩, ⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := j
  have : NeZero c := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  have : NeZero c' := ⟨(Nat.pos_of_mem_divisors hc').ne'⟩
  by_cases hcc : c = c'
  · subst hcc
    have hχχ : χ ≠ χ' := fun e => hne (by subst e; rfl)
    exact inner_gket_of_ne u _ N _ c _ χ hχ u' _ _ _ χ' hχ' hχχ
  · exact inner_gket_of_ne_conductor u _ N _ c _ χ hχ u' _ _ c' _ χ' hχ' hcc

end PAG.Part212

#print axioms PAG.Part212.inner_sum_smul_right
#print axioms PAG.Part212.inner_sum_smul_left
#print axioms PAG.Part212.kcoef_inv
#print axioms PAG.Part212.dvd_div_iff_dvd
#print axioms PAG.Part212.mul_div_div_cancel
#print axioms PAG.Part212.sum_moebius_dvd_filter
#print axioms PAG.Part212.kdual_shell_eq
#print axioms PAG.Part212.conductor_eq_of_liftc_eq
#print axioms PAG.Part212.eq_of_liftc_eq
#print axioms PAG.Part212.inner_gbas_gket
#print axioms PAG.Part212.kdual
#print axioms PAG.Part212.inner_kdual
#print axioms PAG.Part212.inner_kdual_gket_same
#print axioms PAG.Part212.inner_kdual_gket_of_ne_conductor
#print axioms PAG.Part212.inner_kdual_gket_of_ne
#print axioms PAG.Part212.kdualI
#print axioms PAG.Part212.inner_kdualI_ketFam
#print axioms PAG.Part212.ketBasis_repr
#print axioms PAG.Part212.eq_sum_kdualI
#print axioms PAG.Part212.inner_kdual_explicit
#print axioms PAG.Part212.inner_gket_of_ne_conductor
#print axioms PAG.Part212.inner_gket_of_ne
#print axioms PAG.Part212.ketClass
#print axioms PAG.Part212.inner_ketFam_of_ketClass_ne
