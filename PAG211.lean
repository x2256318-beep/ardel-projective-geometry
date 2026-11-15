/-
  PAG 2.0 Part 207（2026-10-24）— 基底の取り替え（g_{s,ψ} をケットで書く）とケット基底
  s·n = N、ψ は法 n の指標、Ψ はその原始部分（法 d、ψ = Ψ′ は Ψ を法 n へ持ち上げたもの）。
  rk(v, d, Ψ)(x) = [v ∣ x]·Ψ(x/v)（PAG203。v·W = N、d ∣ W なら rk = √φ(W)·|v, Ψ⟩_N）
  1. フーリエ側：𝓕g_{s,ψ} = rk(s, n, ψ) = Σ_{e ∣ n, (e,d)=1} μ(e)Ψ(e)·rk(se, d, Ψ)（メビウス分解）
  2. rk の双対：wd ∣ N、Ψ 原始的なら 𝓕⁻¹ rk(w, d, Ψ) = (τ(Ψ)/(wd))·rk(N/(wd), d, Ψ̄)
  3. 基底の取り替え：g_{s,ψ} = Σ_{e ∣ n, (e,d)=1} (τ(Ψ)μ(e)Ψ(e)/(sed))·rk(N/(sed), d, Ψ̄)
  4. 特別な場合：ψ 原始的（d = n）なら g_{s,ψ} = (τ(ψ)/N)·rk(1, n, ψ̄) = (τ(ψ)√φ(N)/N)·|1, ψ̄⟩_N。
     単位指標（d = 1）では Part 201 の式 ε_s = Σ_{e ∣ n} (μ(e)/(se))·rk(N/(se), 1, 1) が別の道で出る
  5. 各点の式：g_{s,ψ}(x) = N⁻¹ Σ_{b mod n} ψ(b)e(bx/n)。系として、原始的でない指標のガウス和の公式
     Σ_b ψ(b)e(bx/n) = τ(Ψ)·Σ_e μ(e)Ψ(e)(n/(ed))·rk_n(n/(ed), d, Ψ̄)(x) と、
     ラマヌジャン和の公式 c_n(x) = Σ_{e ∣ n} μ(e)(n/e)·[n/e ∣ x]
  6. ケット基底：ケット |u, χ⟩_N（u ∣ N、c ∣ N/u、χ は法 c の原始指標）は N 個で、ℂ^{ℤ/N} の基底
     （直交ではない。3 で g_{s,ψ} がケットの一次結合になることと、個数 Σ_{u ∣ N} φ(N/u) = N から）
-/
import PAG210
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.FiniteType

namespace PAG.Part211

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** d ∣ n のとき、Ψ を法 n へ持ち上げたもの Ψ′ について Ψ′(m) = [(m, n) = 1]·Ψ(m)。 -/
theorem changeLevel_natCast_eq {d n : ℕ} (hdn : d ∣ n) (Ψ : DirichletCharacter ℂ d) (m : ℕ) :
    Ψ.changeLevel hdn (m : ZMod n) = if m.Coprime n then Ψ (m : ZMod d) else 0 := by
  by_cases hm : m.Coprime n
  · rw [ite_eq_left hm, changeLevel_natCast hdn Ψ m hm]
  · rw [ite_eq_right hm]
    exact MulChar.map_nonunit _ (fun hu => hm ((ZMod.isUnit_iff_coprime m n).mp hu))

/-- **0b.** s·n = N、d ∣ n、e ∣ n、(e, d) = 1 なら sed ∣ N。 -/
theorem sed_dvd (s n N : ℕ) (h : s * n = N) {d e : ℕ} (hdn : d ∣ n)
    (he : e ∈ n.divisors.filter (fun e => e.Coprime d)) : s * e * d ∣ N := by
  rw [Finset.mem_filter, Nat.mem_divisors] at he
  rw [mul_assoc, ← h]
  exact Nat.mul_dvd_mul_left s (Nat.Coprime.mul_dvd_of_dvd_of_dvd he.2 he.1.1 hdn)

/-! ### 1. フーリエ側のメビウス分解 -/

/-- **1a.** 𝓕g_{s,ψ} = rk(s, n, ψ)（押し出した指標 ι_{s,*}ψ は rk そのもの）。 -/
theorem dft_gbas_eq_rk (s n N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ n) :
    𝓕 (gbas s n N ψ) = rk (N := N) s n ψ := by
  funext ξ
  rw [dft_gbas_apply]
  rfl

/-- **1b.** g_{s,ψ} = 𝓕⁻¹ rk(s, n, ψ)。 -/
theorem gbas_eq_invDFT_rk (s n N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ n) :
    gbas s n N ψ = 𝓕⁻ (rk (N := N) s n ψ) := by
  rw [← dft_gbas_eq_rk, LinearEquiv.symm_apply_apply]

/-- **1c. メビウス分解**：s ≠ 0、d ∣ n なら rk(s, n, Ψ′) = Σ_{e ∣ n, (e,d)=1} μ(e)Ψ(e)·rk(se, d, Ψ)
（Ψ′ は Ψ を法 n へ持ち上げたもの。PAG203 の mobius_identity を各点で使う）。 -/
theorem rk_changeLevel (s n N : ℕ) [NeZero n] (hs : s ≠ 0) (d : ℕ) (hdn : d ∣ n)
    (Ψ : DirichletCharacter ℂ d) :
    rk (N := N) s n (Ψ.changeLevel hdn) =
      ∑ e ∈ n.divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ (e : ZMod d)) • rk (N := N) (s * e) d Ψ := by
  have : NeZero d := NeZero.of_pos (Nat.pos_of_dvd_of_pos hdn (Nat.pos_of_ne_zero (NeZero.ne n)))
  have hs0 : 0 < s := Nat.pos_of_ne_zero hs
  funext ξ
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, rk]
  by_cases hsξ : s ∣ ξ.val
  · rw [ite_eq_left hsξ]
    obtain ⟨t, ht⟩ := hsξ
    rw [ht, Nat.mul_div_cancel_left t hs0, changeLevel_natCast_eq hdn Ψ t, ← mobius_identity n d hdn Ψ t]
    refine sum_congr rfl (fun e _ => ?_)
    by_cases het : e ∣ t
    · rw [ite_eq_left het, ite_eq_left (Nat.mul_dvd_mul_left s het), Nat.mul_div_mul_left t e hs0, mul_assoc]
    · rw [ite_eq_right het, ite_eq_right (fun h' => het (Nat.dvd_of_mul_dvd_mul_left hs0 h')), mul_zero]
  · rw [ite_eq_right hsξ]
    symm
    refine sum_eq_zero (fun e _ => ?_)
    rw [ite_eq_right (fun h' => hsξ (dvd_trans (dvd_mul_right s e) h')), mul_zero]

/-- **1d.** 𝓕g_{s,Ψ′} = Σ_{e ∣ n, (e,d)=1} μ(e)Ψ(e)·rk(se, d, Ψ)。 -/
theorem dft_gbas_eq_sum_rk (s n N : ℕ) [NeZero N] (h : s * n = N) (d : ℕ) (hdn : d ∣ n)
    (Ψ : DirichletCharacter ℂ d) :
    𝓕 (gbas s n N (Ψ.changeLevel hdn)) =
      ∑ e ∈ n.divisors.filter (fun e => e.Coprime d),
        ((ArithmeticFunction.moebius e : ℂ) * Ψ (e : ZMod d)) • rk (N := N) (s * e) d Ψ := by
  have : NeZero n := neZero_of_mul h
  rw [dft_gbas_eq_rk, rk_changeLevel s n N (pos_of_mul h).ne' d hdn Ψ]

/-! ### 2. rk のフーリエ双対 -/

/-- **2a.** PAG203 の dft_rk のベクトルの形：v·W = N、d ∣ W、Ψ 原始的なら
𝓕 rk(v, d, Ψ) = ((W/d)·Ψ̄(−1)·τ(Ψ))·rk(W/d, d, Ψ̄)。 -/
theorem dft_rk_eq_smul (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) [NeZero d] (hd : d ∣ W)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) :
    𝓕 (rk (N := N) v d Ψ) =
      (((W / d : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar) •
        rk (N := N) (W / d) d (Ψ⁻¹ : DirichletCharacter ℂ d) := by
  funext ξ
  rw [dft_rk v W N h d hd Ψ hΨ ξ, Pi.smul_apply, smul_eq_mul]
  simp only [rk]
  by_cases hξ : W / d ∣ ξ.val
  · rw [ite_eq_left hξ, ite_eq_left hξ]
  · rw [ite_eq_right hξ, ite_eq_right hξ, mul_zero]

/-- **2b. rk の逆変換**：wd ∣ N、Ψ 原始的なら rk(w, d, Ψ) = (τ(Ψ)/(wd))·𝓕 rk(N/(wd), d, Ψ̄)
（τ(Ψ)τ(Ψ̄) = Ψ(−1)·d を使う）。 -/
theorem rk_eq_smul_dft (w d N : ℕ) [NeZero N] [NeZero d] (hwd : w * d ∣ N) (Ψ : DirichletCharacter ℂ d)
    (hΨ : Ψ.IsPrimitive) :
    rk (N := N) w d Ψ = (gaussSum Ψ stdAddChar / ((w * d : ℕ) : ℂ)) •
      𝓕 (rk (N := N) (N / (w * d)) d (Ψ⁻¹ : DirichletCharacter ℂ d)) := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hwd
    exact NeZero.ne N hwd
  have hN : N / (w * d) * (w * d) = N := Nat.div_mul_cancel hwd
  have hw : w * d / d = w := Nat.mul_div_cancel w (Nat.pos_of_ne_zero (NeZero.ne d))
  have hg := PAG.Part16.gauss_mul_gauss_inv_eq hΨ
  have h1 : Ψ (-1) * Ψ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw0
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have key : gaussSum Ψ stdAddChar / ((w * d : ℕ) : ℂ) * ((w : ℂ) * Ψ (-1) * gaussSum Ψ⁻¹ stdAddChar) = 1 := by
    rw [Nat.cast_mul, div_mul_eq_mul_div, div_eq_one_iff_eq (mul_ne_zero hwC hdC)]
    linear_combination (w : ℂ) * Ψ (-1) * hg + (w : ℂ) * (d : ℂ) * h1
  rw [dft_rk_eq_smul (N / (w * d)) (w * d) N hN d (dvd_mul_left d w) Ψ⁻¹ (PAG.Part16.isPrimitive_inv hΨ),
    hw, inv_inv, smul_smul, key, one_smul]

/-- **2c.** 𝓕⁻¹ rk(w, d, Ψ) = (τ(Ψ)/(wd))·rk(N/(wd), d, Ψ̄)（wd ∣ N、Ψ 原始的）。 -/
theorem invDFT_rk (w d N : ℕ) [NeZero N] [NeZero d] (hwd : w * d ∣ N) (Ψ : DirichletCharacter ℂ d)
    (hΨ : Ψ.IsPrimitive) :
    𝓕⁻ (rk (N := N) w d Ψ) = (gaussSum Ψ stdAddChar / ((w * d : ℕ) : ℂ)) •
      rk (N := N) (N / (w * d)) d (Ψ⁻¹ : DirichletCharacter ℂ d) := by
  rw [rk_eq_smul_dft w d N hwd Ψ hΨ, map_smul, LinearEquiv.symm_apply_apply]

/-! ### 3. 基底の取り替え -/

/-- **3. 基底の取り替え**：s·n = N、d ∣ n、Ψ が法 d の原始指標なら
g_{s,Ψ′} = Σ_{e ∣ n, (e,d)=1} (τ(Ψ)μ(e)Ψ(e)/(sed))·rk(N/(sed), d, Ψ̄)
（rk(N/(sed), d, Ψ̄) = √φ(sed)·|N/(sed), Ψ̄⟩_N なので、右辺はケットの一次結合）。 -/
theorem gbas_eq_sum_rk (s n N : ℕ) [NeZero N] (h : s * n = N) (d : ℕ) [NeZero d] (hdn : d ∣ n)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) :
    gbas s n N (Ψ.changeLevel hdn) =
      ∑ e ∈ n.divisors.filter (fun e => e.Coprime d),
        (gaussSum Ψ stdAddChar * ((ArithmeticFunction.moebius e : ℂ) * Ψ (e : ZMod d)) /
            ((s * e * d : ℕ) : ℂ)) •
          rk (N := N) (N / (s * e * d)) d (Ψ⁻¹ : DirichletCharacter ℂ d) := by
  have : NeZero n := neZero_of_mul h
  rw [gbas_eq_invDFT_rk, rk_changeLevel s n N (pos_of_mul h).ne' d hdn Ψ, map_sum]
  refine sum_congr rfl (fun e he => ?_)
  rw [map_smul, invDFT_rk (s * e) d N (sed_dvd s n N h hdn he) Ψ hΨ, smul_smul]
  congr 1
  ring

/-! ### 4. 特別な場合 -/

/-- **4a. 原始的な場合**：ψ が法 n の原始指標なら g_{s,ψ} = (τ(ψ)/N)·rk(1, n, ψ̄)。 -/
theorem gbas_of_isPrimitive (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N) (ψ : DirichletCharacter ℂ n)
    (hψ : ψ.IsPrimitive) :
    gbas s n N ψ = (gaussSum ψ stdAddChar / (N : ℂ)) • rk (N := N) 1 n (ψ⁻¹ : DirichletCharacter ℂ n) := by
  have hsn : s * n ∣ N := ⟨1, by rw [mul_one, h]⟩
  rw [gbas_eq_invDFT_rk, invDFT_rk s n N hsn ψ hψ, h, Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne N))]

/-- **4b.** ケットで書くと g_{s,ψ} = (τ(ψ)√φ(N)/N)·|1, ψ̄⟩_N（ψ 原始的）。 -/
theorem gbas_of_isPrimitive_gket (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N)
    (ψ : DirichletCharacter ℂ n) (hψ : ψ.IsPrimitive) :
    gbas s n N ψ = (gaussSum ψ stdAddChar * ((Real.sqrt (Nat.totient N) : ℝ) : ℂ) / (N : ℂ)) •
      gket 1 N N (one_mul N) n (Dvd.intro_left s h) (ψ⁻¹ : DirichletCharacter ℂ n) := by
  rw [gbas_of_isPrimitive s n N h ψ hψ, rk_eq_gket 1 N N (one_mul N) n (Dvd.intro_left s h), smul_smul]
  congr 1
  ring

/-- **4c.** 各点で g_{s,ψ}(x) = (τ(ψ)/N)·ψ̄(x mod n)（ψ 原始的）。 -/
theorem gbas_of_isPrimitive_apply (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N)
    (ψ : DirichletCharacter ℂ n) (hψ : ψ.IsPrimitive) (x : ZMod N) :
    gbas s n N ψ x = gaussSum ψ stdAddChar / (N : ℂ) * ψ⁻¹ (x.val : ZMod n) := by
  rw [gbas_of_isPrimitive s n N h ψ hψ, Pi.smul_apply, smul_eq_mul]
  simp only [rk, Nat.div_one]
  rw [ite_eq_left (one_dvd _)]

/-- **4d. 単位指標**（d = 1）：基底の取り替えから Part 201 の式（PAG205.geps_eq_balls と同じ主張）が
別の道で出る：ε_s = Σ_{e ∣ N/s} (μ(e)/(se))·rk(N/(se), 1, 1)。 -/
theorem geps_eq_balls_of_gbas (N s : ℕ) [NeZero N] (hs : s ∣ N) :
    geps N s = ∑ e ∈ (N / s).divisors,
      ((ArithmeticFunction.moebius e : ℂ) / ((s * e : ℕ) : ℂ)) • rk (N := N) (N / (s * e)) 1 (fun _ => 1) := by
  have h : s * (N / s) = N := Nat.mul_div_cancel' hs
  have key := gbas_eq_sum_rk s (N / s) N h 1 (one_dvd _) 1 DirichletCharacter.isPrimitive_one_level_one
  rw [map_one, gbas_one s (N / s) N h, gaussSum_level_one,
    Finset.filter_true_of_mem (fun e _ => Nat.coprime_one_right e)] at key
  rw [key]
  refine sum_congr rfl (fun e _ => ?_)
  have h1 : (⇑((1 : DirichletCharacter ℂ 1)⁻¹) : ZMod 1 → ℂ) = fun _ => 1 := funext (chi_level_one _)
  rw [h1]
  simp only [chi_level_one, mul_one, one_mul]

/-! ### 5. 各点の式（ガウス・ラマヌジャン和） -/

/-- **5a.** g_{s,ψ}(x) = N⁻¹ Σ_{b mod n} ψ(b)·e(b·x/n)（x/n は x を法 n に落としたもの）。 -/
theorem gbas_apply (s n N : ℕ) [NeZero N] [NeZero n] (h : s * n = N) (ψ : DirichletCharacter ℂ n)
    (x : ZMod N) :
    gbas s n N ψ x = (N : ℂ)⁻¹ * ∑ b : ZMod n, ψ b * stdAddChar (b * (x.val : ZMod n)) := by
  have hg : gbas s n N ψ = 𝓕⁻ (PAG.Part17.push (memb s n N h) ψ) := by
    rw [← dft_gbas s n N h ψ, LinearEquiv.symm_apply_apply]
  rw [hg, ZMod.invDFT_apply', smul_eq_mul, dft_push_memb s n N h, ZMod.dft_apply,
    map_neg (ZMod.castHom (Dvd.intro_left s h) (ZMod n))]
  congr 1
  refine sum_congr rfl (fun b _ => ?_)
  rw [smul_eq_mul, mul_neg, neg_neg, mul_comm, ZMod.castHom_apply, ZMod.cast_eq_val]

/-- **5b. 原始的でない指標のガウス和**：d ∣ n、Ψ が法 d の原始指標、x ∈ ℤ/n なら
Σ_{b mod n} Ψ′(b)·e(bx/n) = τ(Ψ)·Σ_{e ∣ n, (e,d)=1} μ(e)Ψ(e)·(n/(ed))·rk_n(n/(ed), d, Ψ̄)(x)
（3 と 5a を N = n、s = 1 で比べる）。 -/
theorem gaussSum_changeLevel_apply (n : ℕ) [NeZero n] (d : ℕ) [NeZero d] (hdn : d ∣ n)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) (x : ZMod n) :
    ∑ b : ZMod n, Ψ.changeLevel hdn b * stdAddChar (b * x) =
      gaussSum Ψ stdAddChar * ∑ e ∈ n.divisors.filter (fun e => e.Coprime d),
        (ArithmeticFunction.moebius e : ℂ) * Ψ (e : ZMod d) * ((n : ℂ) / ((e * d : ℕ) : ℂ)) *
          rk (N := n) (n / (e * d)) d (Ψ⁻¹ : DirichletCharacter ℂ d) x := by
  have h1 : 1 * n = n := one_mul n
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have key := congrFun (gbas_eq_sum_rk 1 n n h1 d hdn Ψ hΨ) x
  rw [gbas_apply 1 n n h1 _ x, ZMod.natCast_zmod_val, Finset.sum_apply] at key
  simp only [Pi.smul_apply, smul_eq_mul, one_mul] at key
  rw [inv_mul_eq_iff_eq_mul₀ hn] at key
  rw [key, Finset.mul_sum, Finset.mul_sum]
  refine sum_congr rfl (fun e _ => ?_)
  ring

/-- **5c. ラマヌジャン和**：c_n(x) = Σ_{b mod n} 1(b)·e(bx/n) = Σ_{e ∣ n} μ(e)·(n/e)·[n/e ∣ x]
（1 は法 n の単位指標で、1(b) = [b は単数]。5b の d = 1）。 -/
theorem ramanujan_sum (n : ℕ) [NeZero n] (x : ZMod n) :
    ∑ b : ZMod n, (1 : DirichletCharacter ℂ n) b * stdAddChar (b * x) =
      ∑ e ∈ n.divisors,
        (ArithmeticFunction.moebius e : ℂ) * ((n / e : ℕ) : ℂ) * (if n / e ∣ x.val then 1 else 0) := by
  have key := gaussSum_changeLevel_apply n 1 (one_dvd n) 1 DirichletCharacter.isPrimitive_one_level_one x
  rw [map_one, gaussSum_level_one, one_mul,
    Finset.filter_true_of_mem (fun e _ => Nat.coprime_one_right e)] at key
  rw [key]
  refine sum_congr rfl (fun e he => ?_)
  have hen : e ∣ n := Nat.dvd_of_mem_divisors he
  have he0 : (e : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
  simp only [rk, chi_level_one, mul_one]
  rw [Nat.cast_div hen he0]

/-! ### 6. ケット基底 -/

/-- ケットの番号：u ∣ N、c ∣ N/u、χ は法 c の原始指標。 -/
abbrev KetIdx (N : ℕ) : Type :=
  Σ u : N.divisors, Σ c : (N / (u : ℕ)).divisors, {χ : DirichletCharacter ℂ c // χ.IsPrimitive}

/-- ケットの族：番号 (u, c, χ) に |u, χ⟩_N を対応させる。 -/
noncomputable def ketFam (N : ℕ) [NeZero N] (i : KetIdx N) : ZMod N → ℂ :=
  gket i.1 (N / i.1) N (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors i.1.2)) i.2.1
    (Nat.dvd_of_mem_divisors i.2.1.2) i.2.2.1

/-- **6a.** M = M′ ならケットも等しい（証明の項の付け替え）。 -/
theorem gket_congr (u N : ℕ) [NeZero N] {M M' : ℕ} (e : M = M') (h : u * M = N) (h' : u * M' = N)
    (c : ℕ) (hc : c ∣ M) (hc' : c ∣ M') (χ : ZMod c → ℂ) :
    gket u M N h c hc χ = gket u M' N h' c hc' χ := by
  subst e
  rfl

/-- **6b.** v·W = N、d ∣ W、Φ が法 d の原始指標なら rk(v, d, Φ) はケットの族の張る空間に入る。 -/
theorem rk_mem_span_ketFam (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) (hd : d ∣ W)
    (Φ : DirichletCharacter ℂ d) (hΦ : Φ.IsPrimitive) :
    rk (N := N) v d Φ ∈ Submodule.span ℂ (Set.range (ketFam N)) := by
  have hW : NeZero W := neZero_of_mul h
  have hNv : N / v = W := Nat.div_eq_of_eq_mul_right (pos_of_mul h) h.symm
  have hvN : v ∈ N.divisors := Nat.mem_divisors.mpr ⟨Dvd.intro W h, NeZero.ne N⟩
  have hdN : d ∈ (N / v).divisors := by
    rw [hNv]
    exact Nat.mem_divisors.mpr ⟨hd, NeZero.ne W⟩
  rw [rk_eq_gket v W N h d hd Φ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨v, hvN⟩, ⟨d, hdN⟩, ⟨Φ, hΦ⟩⟩, ?_⟩)
  exact gket_congr v N hNv _ h d _ hd Φ

/-- **6c.** Part 204 の基底ベクトル g_{s,ψ} はケットの族の張る空間に入る（3 による）。 -/
theorem gbas_mem_span_ketFam (s n N : ℕ) [NeZero N] (h : s * n = N) (ψ : DirichletCharacter ℂ n) :
    gbas s n N ψ ∈ Submodule.span ℂ (Set.range (ketFam N)) := by
  have : NeZero n := neZero_of_mul h
  have : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have key := gbas_eq_sum_rk s n N h ψ.conductor ψ.conductor_dvd_level ψ.primitiveCharacter
    ψ.primitiveCharacter_isPrimitive
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at key
  rw [key]
  refine Submodule.sum_mem _ (fun e he => Submodule.smul_mem _ _ ?_)
  have hsed := sed_dvd s n N h ψ.conductor_dvd_level he
  exact rk_mem_span_ketFam (N / (s * e * ψ.conductor)) (s * e * ψ.conductor) N (Nat.div_mul_cancel hsed)
    ψ.conductor (dvd_mul_left _ _) _ (PAG.Part16.isPrimitive_inv ψ.primitiveCharacter_isPrimitive)

/-- **6d. ケットは全体を張る**：span{|u, χ⟩_N} = ℂ^{ℤ/N}。 -/
theorem span_ketFam (N : ℕ) [NeZero N] : ⊤ ≤ Submodule.span ℂ (Set.range (ketFam N)) := by
  intro f _
  rw [eq_sum_sum_gbas N f]
  refine Submodule.sum_mem _ (fun s hs => Submodule.sum_mem _ (fun ψ _ => Submodule.smul_mem _ _ ?_))
  exact gbas_mem_span_ketFam s (N / s) N (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs)) ψ

/-- **6e. ケットの個数**：Σ_{u ∣ N} Σ_{c ∣ N/u} #{法 c の原始指標} = N。 -/
theorem card_ketIdx (N : ℕ) [NeZero N] : Nat.card (KetIdx N) = N := by
  conv_rhs => rw [← sum_totient_div N, ← Finset.sum_coe_sort N.divisors]
  rw [Nat.card_sigma]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have : NeZero (N / (u : ℕ)) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.dvd_of_mem_divisors u.2))
      (Nat.pos_of_mem_divisors u.2)).ne'⟩
  rw [Nat.card_sigma, ← sum_card_primitive (N / (u : ℕ)), ← Finset.sum_coe_sort (N / (u : ℕ)).divisors]

/-- **6f. ケットは一次独立**（全体を張り、個数が次元 N に等しい）。 -/
theorem ketFam_linearIndependent (N : ℕ) [NeZero N] : LinearIndependent ℂ (ketFam N) := by
  let _ := Fintype.ofFinite (KetIdx N)
  refine linearIndependent_of_top_le_span_of_card_eq_finrank (span_ketFam N) ?_
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card, ← Nat.card_eq_fintype_card, card_ketIdx]

/-- **6g. ケット基底**：ケット |u, χ⟩_N（u ∣ N、c ∣ N/u、χ は法 c の原始指標）は ℂ^{ℤ/N} の基底。 -/
noncomputable def ketBasis (N : ℕ) [NeZero N] : Module.Basis (KetIdx N) ℂ (ZMod N → ℂ) :=
  Module.Basis.mk (ketFam_linearIndependent N) (span_ketFam N)

/-- **6h.** ケット基底の元は対応するケット。 -/
theorem ketBasis_apply (N : ℕ) [NeZero N] (i : KetIdx N) : ketBasis N i = ketFam N i :=
  Module.Basis.mk_apply _ _ _

/-- **6i.** 番号が違えばケットも違う。 -/
theorem ketFam_injective (N : ℕ) [NeZero N] : Function.Injective (ketFam N) :=
  (ketFam_linearIndependent N).injective

end PAG.Part211

#print axioms PAG.Part211.changeLevel_natCast_eq
#print axioms PAG.Part211.sed_dvd
#print axioms PAG.Part211.dft_gbas_eq_rk
#print axioms PAG.Part211.gbas_eq_invDFT_rk
#print axioms PAG.Part211.rk_changeLevel
#print axioms PAG.Part211.dft_gbas_eq_sum_rk
#print axioms PAG.Part211.dft_rk_eq_smul
#print axioms PAG.Part211.rk_eq_smul_dft
#print axioms PAG.Part211.invDFT_rk
#print axioms PAG.Part211.gbas_eq_sum_rk
#print axioms PAG.Part211.gbas_of_isPrimitive
#print axioms PAG.Part211.gbas_of_isPrimitive_gket
#print axioms PAG.Part211.gbas_of_isPrimitive_apply
#print axioms PAG.Part211.geps_eq_balls_of_gbas
#print axioms PAG.Part211.gbas_apply
#print axioms PAG.Part211.gaussSum_changeLevel_apply
#print axioms PAG.Part211.ramanujan_sum
#print axioms PAG.Part211.gket_congr
#print axioms PAG.Part211.rk_mem_span_ketFam
#print axioms PAG.Part211.gbas_mem_span_ketFam
#print axioms PAG.Part211.span_ketFam
#print axioms PAG.Part211.card_ketIdx
#print axioms PAG.Part211.ketFam_linearIndependent
#print axioms PAG.Part211.ketFam
#print axioms PAG.Part211.ketBasis
#print axioms PAG.Part211.ketBasis_apply
#print axioms PAG.Part211.ketFam_injective
