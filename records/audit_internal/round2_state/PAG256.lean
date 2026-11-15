/-
  PAG 2.0 Part 252（2026-11-12）— 離散 Hartley 変換と反転 J の合成 J∘H_N/√N の、単数の上での原始指標についての式
  （読み：公理 A1 の境界ユニタリの原始指標の部分）
  問いの出所：著者の判断（2026-11-12 17:14「判断 3：Lean 化してください」）。重なりの読みは「ねじれた貼り合わせ（U）」
  （同日の著者の回答）。構築者が再構成したモノグラフ §1.3 の主張 (2)（A1 のもとで U = J∘H_N/√N）の、各レベル N の
  原始指標の部分と読める恒等式を Lean にする（読み。U と A1 は Lean の文に出てこない。照合ノート §5 の 6、着手前の文書の
  Q1。盲検の問いテストの S1）。
  記号：e = stdAddChar（e(t) = exp(2πi t.val/N)）、τ(χ) = gaussSum χ e、(H_N f)(y) = Σ_x f(x) cas(2π xy/N)、
  cas = cos + sin（離散 Hartley 変換）、(J g)(u) = g(u⁻¹)（単数の上）、W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。
  1. Hartley の核：cas(2π t/N) = ((1 − i)e(t) + (1 + i)e(−t))/2
  2. 原始指標 χ について H_N χ = ε(χ)·τ(χ)·χ⁻¹。ε(χ) = ((1 − i) + (1 + i)χ(−1))/2 は偶で 1、奇で −i
  3. 単数でないところで H_N χ = 0（原始指標の部分は、単数の上の関数の空間に留まる）
  4. 単数 u で (J H_N χ)(u)/√N = W(χ)·χ(u)。|W(χ)| = 1
  5. 非空虚性の証人（法 3 の奇の原始指標、法 5 の偶で自明でない原始指標）と、除去テストの反例（原始性を外すと 3 と |W| = 1 が破れる）
  6.（独立照合の指摘で追加）単数の上の式 4 は原始性なしで成り立つ（`JH_eq_rootNum_mul_any`）。原始性が効くのは 3 と |W| = 1 だけ。
     除去テストの反例は、法 2（原始指標がないことは Lean の外）と、原始指標のある法 4（Lean の文に含めた）の両方で置いた
  どれも既知の事実の書き直し（再導出）：原始指標のガウス和はフーリエ係数（Mathlib の `gaussSum_mulShift_of_isPrimitive`）。
  Hartley の形で書いた文献は、盲検の問いテストでは見つからなかった（書き直しであって新しい内容ではない）。
  公理 A1 は Lean の公理にしていない。ここでの文は W（`rootNum`。原始指標ではルート数）についての恒等式である（読み：A1 は原始指標の
  位相をこの値に選ぶ公準）。

内部照合（2026-11-14、`pag2_internal_audit_249_256.md`）：前の鎖と同じ文・同じ値の定義（A。Lean で確認）は、
`inv_apply_neg_one`・`neg_one_mul_self`（Part 5・21・25・77）、`isPrimitive_of_prime_of_ne_one`（Part 167）、`casKer`（付録 A の
Part 3 の `casK` と同じ値）。前の宣言から直ちに出るもの（B。Lean で確認）は、`rootNum`（Part 192 の `zN` ÷ Part 194 の `gs` と同じ値）、
`inv_apply_units_inv`・`sum_mul_stdAddChar_neg`（付録 A の Part 3）。照合者の判定で数行で出るもの（C）は、`hartley_one`・`casKer_eq`
（付録 A の Part 3 の命題 2.8 `hartley_char`、`casK_even_part`・`casK_odd_part` から。この 2 件は Lean で確認）、`hartley_eq_of_isPrimitive`・
`hartley_eq_zero_of_not_isUnit`・`hartley_units_inv`・`JH_eq_rootNum_mul`・`JH_eq_rootNum_mul_any`（`hartley_char` などから。5 件とも
確信度 低、Lean では未確認）、`normSq_rootNum`（Part 12 の `normSq_gaussSum` から。Lean で確認）、`exists_primitive_odd_three`
（Part 115・163・167 から。Lean で確認）・`exists_primitive_even_five`、`parFac`・`rootNum_eq`（Part 194 の `gs`、付録 A の Part 2 の
`parity_weight`）。前の鎖に見つからなかったもの（網羅ではない）は、変換としての定義（`hartley`・`JH`）と、反例（`removal_counterexample` など）。
-/
import PAG255
import PAG16
import PAG144
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace PAG.Part256

open ZMod Complex Finset

variable {N : ℕ} [NeZero N]

/-! ### 1. Hartley の核と離散 Hartley 変換 -/

/-- Hartley の核 cas(2π t/N) = cos(2π t/N) + sin(2π t/N)（t の代表は t.val）。
内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `casK` と同じ値（式の書き方は違う。Lean で値の一致を確認）。 -/
noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

/-- 離散 Hartley 変換 (H_N f)(y) = Σ_x f(x)·cas(2π xy/N)。 -/
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

/-- **Hartley の核と標準の加法的指標**：cas(2π t/N) = ((1 − i)e(t) + (1 + i)e(−t))/2。 -/
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2 := by
  set θ : ℝ := 2 * Real.pi * t.val / N with hθ
  have h1 : (stdAddChar t : ℂ) = Complex.exp ((θ : ℂ) * I) := by
    rw [stdAddChar_apply, toCircle_apply, hθ]
    congr 1
    push_cast
    ring
  have h2 : (stdAddChar (-t) : ℂ) = Complex.exp (-((θ : ℂ) * I)) := by
    rw [AddChar.map_neg_eq_inv, h1, Complex.exp_neg]
  rw [h1, h2, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  unfold casKer
  rw [← hθ]
  push_cast
  linear_combination (Complex.sin (θ : ℂ)) * Complex.I_sq

/-! ### 2. 原始指標の Hartley 変換 -/

/-- パリティ因子 ε(χ) = ((1 − i) + (1 + i)χ(−1))/2。 -/
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1 := by
  unfold parFac
  rw [show χ (-1) = 1 from h]
  ring

omit [NeZero N] in
theorem parFac_of_odd {χ : DirichletCharacter ℂ N} (h : χ.Odd) : parFac χ = -I := by
  unfold parFac
  rw [show χ (-1) = -1 from h]
  ring

omit [NeZero N] in
/-- χ⁻¹(−1) = χ(−1)（χ(−1) = ±1）。
内部照合（2026-11-14）：Part 5（PAG9）の `inv_apply_neg_one`、Part 21（PAG25）の `chi_inv_neg_one`、Part 77（PAG81）の `inv_neg_one` と同じ文（Lean で両向きに確認）。 -/
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  rcases χ.even_or_odd with h | h
  · rw [show χ (-1) = 1 from h, inv_one]
  · rw [show χ (-1) = -1 from h, inv_neg, inv_one]

/-- Σ_x χ(x) e(xy) をガウス和の形に。 -/
theorem sum_mul_stdAddChar (χ : DirichletCharacter ℂ N) (y : ZMod N) :
    ∑ x : ZMod N, χ x * stdAddChar (x * y) = gaussSum χ (stdAddChar.mulShift y) := by
  unfold gaussSum
  congr 1 with x
  rw [AddChar.mulShift_apply, mul_comm y x]

/-- **原始指標の Hartley 変換**：H_N χ = ε(χ)·τ(χ)·χ⁻¹（ℤ/N のすべての点で）。 -/
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y := by
  have hA : ∑ x : ZMod N, χ x * stdAddChar (x * y) = χ⁻¹ y * gaussSum χ stdAddChar := by
    rw [sum_mul_stdAddChar, gaussSum_mulShift_of_isPrimitive _ hχ]
  have hB : ∑ x : ZMod N, χ x * stdAddChar (-(x * y)) = χ⁻¹ (-y) * gaussSum χ stdAddChar := by
    rw [← gaussSum_mulShift_of_isPrimitive _ hχ, ← sum_mul_stdAddChar]
    congr 1 with x
    rw [mul_neg]
  have hneg : χ⁻¹ (-y) = χ (-1) * χ⁻¹ y := by
    rw [neg_eq_neg_one_mul, map_mul, inv_apply_neg_one]
  have hsplit : ∀ x : ZMod N, χ x * casKer (x * y) =
      (1 - I) / 2 * (χ x * stdAddChar (x * y)) + (1 + I) / 2 * (χ x * stdAddChar (-(x * y))) := by
    intro x
    rw [casKer_eq]
    ring
  unfold hartley
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, hA, hB, hneg]
  unfold parFac
  ring

/-- **単数でないところで H_N χ = 0**（χ 原始的）。 -/
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0 := by
  rw [hartley_eq_of_isPrimitive hχ, MulChar.map_nonunit _ hy, mul_zero]

/-! ### 3. ルート数と、J と Hartley 変換の合成 -/

open Classical in
/-- W(χ) = τ(χ)/(i^a √N)（a = 0 は偶、a = 1 は奇）。χ が原始ならルート数（関数等式との一致は Lean の外）。原始的でない
χ ではルート数ではなく、0 にもなる（法 4 の自明な指標）。
内部照合（2026-11-14）：Part 192（PAG196）の `zN` を Part 194（PAG198）の `gs` で割ったものと同じ値（Lean で確認）。 -/
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

/-- W(χ) = ε(χ)·τ(χ)/√N。 -/
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ) := by
  unfold rootNum
  rcases χ.even_or_odd with h | h
  · simp only [h, ↓reduceIte]
    rw [parFac_of_even h]
    ring
  · have hne : ¬χ.Even := by
      intro he
      have e1 : χ (-1) = 1 := he
      have e2 : χ (-1) = -1 := h
      rw [e1] at e2
      norm_num at e2
    simp only [hne, ↓reduceIte]
    rw [parFac_of_odd h, div_eq_mul_inv, div_eq_mul_inv, mul_inv, Complex.inv_I]
    ring

/-- 単数の上の関数への J∘H_N/√N：(J H_N f)(u)/√N = (H_N f)(u⁻¹)/√N。 -/
noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)

omit [NeZero N] in
/-- χ⁻¹(u⁻¹) = χ(u)（u は単数）。
内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `apply_inv_eq_inv_apply` から 1 行で出る（Lean で確認）。 -/
theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u := by
  have h1 : χ (u : ZMod N) * χ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [MulChar.inv_apply_eq_inv', eq_inv_of_mul_eq_one_right h1, inv_inv]

/-- χ が原始的なら、すべての単数 u で (H_N χ)(u⁻¹)/√N = W(χ)·χ(u)。式そのものは原始性なしで成り立つ
（`JH_eq_rootNum_mul_any`）。構築者が再構成したモノグラフ §1.3 の主張 (2) の原始指標の部分と読む（解釈。本文と未照合。
U と A1 は文に出てこない）。JH は ℤ/N の上の関数を単数の上の関数に送る写像で、同じ空間の上の固有値方程式ではない。 -/
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u := by
  unfold JH
  rw [hartley_eq_of_isPrimitive hχ, rootNum_eq, inv_apply_units_inv]
  ring

/-- |W(χ)|² = 1（χ 原始的。Part 12（PAG16）の |τ(χ)|² = N から）。 -/
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpar : Complex.normSq (parFac χ) = 1 := by
    rcases χ.even_or_odd with h | h
    · rw [parFac_of_even h, map_one]
    · rw [parFac_of_odd h, Complex.normSq_neg, Complex.normSq_I]
  have hsq : Complex.normSq (Real.sqrt N : ℂ) = N := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [rootNum_eq, map_div₀, map_mul, hpar, PAG.Part16.normSq_gaussSum hχ, hsq, one_mul,
    div_self hN]

/-! ### 3b. 単数の上の式は原始性なしで成り立つ（独立照合の指摘を受けて追加）

原始性が効くのは、単数でないところで 0（`hartley_eq_zero_of_not_isUnit`）と |W| = 1（`normSq_rootNum`）だけ。
単数の上の固有値の式 `JH_eq_rootNum_mul_any` は、すべての指標で成り立つ（原始的でない指標では、固有値 ε(χ)τ(χ)/√N は
誘導元の原始指標のルート数と一致せず、絶対値は 1 未満になりうる）。 -/

/-- 単数 u で H_N χ (u⁻¹) = χ(u)·H_N χ (1)（x ↦ u·x の置換。原始性は要らない）。 -/
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1 := by
  unfold hartley
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Units.mulLeft u) _ _ (fun x => ?_)).symm
  rw [Units.mulLeft_apply, map_mul, mul_one]
  have : (u : ZMod N) * x * ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = x := by
    rw [mul_comm (u : ZMod N) x, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  ring

omit [NeZero N] in
/-- χ(−1)·χ(−1) = 1。
内部照合（2026-11-14）：Part 5（PAG9）の `chi_neg_one_sq`、Part 25（PAG29）の `chi_neg_one_sq'` と同じ文（Lean で両向きに確認）。 -/
theorem neg_one_mul_self (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- Σ_x χ(x)e(−x) = χ(−1)·τ(χ)（x ↦ −x の置換。原始性は要らない）。
内部照合（2026-11-14）：付録 A の Part 3（PAG3.lean）の `sum_neg_twist` の x = 1 の場合（Lean で確認）。 -/
theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar := by
  unfold gaussSum
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.neg (ZMod N)) _ _ (fun x => ?_)
  have hx : χ (-x) = χ (-1) * χ x := by rw [← map_mul, neg_one_mul]
  rw [Equiv.neg_apply, hx]
  linear_combination (-(χ x * stdAddChar (-x))) * neg_one_mul_self χ

/-- H_N χ (1) = ε(χ)·τ(χ)（原始性は要らない）。 -/
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar := by
  have hsplit : ∀ x : ZMod N, χ x * casKer (x * 1) =
      (1 - I) / 2 * (χ x * stdAddChar x) + (1 + I) / 2 * (χ x * stdAddChar (-x)) := by
    intro x
    rw [mul_one, casKer_eq]
    ring
  unfold hartley
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, sum_mul_stdAddChar_neg]
  unfold parFac gaussSum
  ring

/-- **単数の上の固有値の式（すべての指標）**：(J H_N χ)(u)/√N = W(χ)·χ(u)。W(χ) = rootNum χ = ε(χ)τ(χ)/√N。
原始指標では W(χ) はルート数で |W(χ)| = 1（`normSq_rootNum`）。 -/
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u := by
  unfold JH
  rw [hartley_units_inv, hartley_one, rootNum_eq]
  ring

/-! ### 4. 非空虚性の証人と、除去テストの反例 -/

/-- 素数の法では、自明でない指標は原始的。
内部照合（2026-11-14）：Part 167（PAG171）の `primitive_of_ne_one` と同じ文（Lean で両向きに確認）。 -/
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [DirichletCharacter.isPrimitive_def]
  rcases hp.out.eq_one_or_self_of_dvd _ χ.conductor_dvd_level with h1 | h1
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1) h
  · exact h1

/-- 証人（奇）：法 3 の奇の原始指標がある。 -/
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd := by
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (show (-1 : ZMod 3) ≠ 1 by decide)
  have hodd : χ.Odd := by
    rcases χ.even_or_odd with h | h
    · exact absurd h hχ
    · exact h
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply (isUnit_neg_one))
  exact ⟨χ, isPrimitive_of_prime_of_ne_one hne, hodd⟩

/-- 証人（偶）：法 5 の偶で自明でない原始指標がある（奇の χ をとった場合は χ² を使う）。 -/
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1 := by
  have h21 : (2 : ZMod 5) ≠ 1 := by decide
  have hm1 : (-1 : ZMod 5) = 2 * 2 := by decide
  have hu2 : IsUnit (2 : ZMod 5) := ⟨⟨2, 3, by decide, by decide⟩, rfl⟩
  have hp5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h21
  rcases χ.even_or_odd with he | ho
  · have hne : χ ≠ 1 := by
      rintro rfl
      exact hχ (MulChar.one_apply hu2)
    exact ⟨χ, isPrimitive_of_prime_of_ne_one hne, he, hne⟩
  · -- χ(2)² = χ(−1) = −1 なので χ² は偶で、χ²(2) = −1 ≠ 1
    have h22 : χ 2 * χ 2 = -1 := by
      rw [← map_mul, ← hm1]
      exact ho
    have heven : (χ * χ).Even := by
      show (χ * χ) (-1) = 1
      rw [MulChar.mul_apply, show χ (-1) = -1 from ho]
      ring
    have hne : χ * χ ≠ 1 := by
      intro h1
      have := congrArg (fun ψ : DirichletCharacter ℂ 5 => ψ 2) h1
      simp only [MulChar.mul_apply, MulChar.one_apply hu2] at this
      rw [h22] at this
      norm_num at this
    exact ⟨χ * χ, isPrimitive_of_prime_of_ne_one hne, heven, hne⟩

/-- 除去テストの反例：原始性を外すと「単数でないところで 0」が破れる（法 2 の自明な指標、y = 0）。 -/
theorem removal_counterexample :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      hartley ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1 := by
  refine ⟨?_, not_isUnit_zero, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
    norm_num
  · have key : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
    unfold hartley casKer
    simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, zero_div, Real.cos_zero, Real.sin_zero,
      add_zero, Complex.ofReal_one, mul_one]
    rw [Finset.sum_eq_single (1 : ZMod 2)]
    · exact map_one _
    · intro b _ hb
      rw [key b hb]
      exact MulChar.map_nonunit _ not_isUnit_zero
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- 法 2 の自明な指標で |rootNum|² = 1/2。原始的でないことは `removal_counterexample` の第 1 成分で、2 つを合わせて
|W| = 1 の除去テストの反例になる。 -/
theorem removal_counterexample_normSq :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ 2)) = 1 / 2 := by
  have key : ∀ b : ZMod 2, b ≠ 1 → b = 0 := by decide
  have he1 : (stdAddChar (1 : ZMod 2) : ℂ) = -1 := by
    rw [stdAddChar_apply, toCircle_apply, ZMod.val_one]
    push_cast
    rw [show 2 * (Real.pi : ℂ) * I * 1 / 2 = Real.pi * I by ring, Complex.exp_pi_mul_I]
  have hg : gaussSum (1 : DirichletCharacter ℂ 2) stdAddChar = -1 := by
    unfold gaussSum
    rw [Finset.sum_eq_single (1 : ZMod 2)]
    · rw [map_one, one_mul, he1]
    · intro b _ hb
      rw [key b hb, MulChar.map_nonunit _ not_isUnit_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have heven : (1 : DirichletCharacter ℂ 2).Even := MulChar.one_apply isUnit_neg_one
  rw [rootNum_eq, parFac_of_even heven, hg, map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- 除去テストの反例（原始指標がある法 4 で。独立照合 B の指摘を受けて追加）：法 4 には原始指標があるが
（Part 140 の `exists_primitive`）、自明な指標（原始的でない）では、単数でない 2 で H_N χ (2) = −2 ≠ 0、
|W|² = 0（τ = i − i = 0）。法 2 の反例と違い、原始指標のある法でも原始性を外すと 2 つの文が破れることを示す。 -/
theorem removal_counterexample_four :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      hartley ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (rootNum (1 : DirichletCharacter ℂ 4)) = 0 := by
  have hu3 : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have hn2 : ¬IsUnit (2 : ZMod 4) := by
    rintro ⟨u, hu⟩
    have key : ∀ a : ZMod 4, 2 * a ≠ 1 := by decide
    exact key ((u⁻¹ : (ZMod 4)ˣ) : ZMod 4) (by rw [← hu, Units.mul_inv])
  have hn0 : ¬IsUnit (0 : ZMod 4) := by
    rintro ⟨u, hu⟩
    have key : ∀ a : ZMod 4, 0 * a ≠ 1 := by decide
    exact key ((u⁻¹ : (ZMod 4)ˣ) : ZMod 4) (by rw [← hu, Units.mul_inv])
  have key02 : ∀ y : ZMod 4, y ≠ 1 ∧ y ≠ 3 → y = 0 ∨ y = 2 := by decide
  have h13 : (1 : ZMod 4) ≠ 3 := by decide
  refine ⟨PAG.Part144.exists_primitive 2 le_rfl, ?_, hn2, ?_, ?_⟩
  · rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
    norm_num
  · unfold hartley
    rw [Fintype.sum_eq_add (1 : ZMod 4) (3 : ZMod 4) h13]
    · have h12 : (1 : ZMod 4) * 2 = 2 := by decide
      have h32 : (3 : ZMod 4) * 2 = 2 := by decide
      have hθ : 2 * Real.pi * ((2 : ZMod 4).val : ℝ) / ((4 : ℕ) : ℝ) = Real.pi := by
        rw [show (2 : ZMod 4).val = 2 from rfl]
        push_cast
        ring
      have hc : casKer (2 : ZMod 4) = -1 := by
        unfold casKer
        rw [hθ, Real.cos_pi, Real.sin_pi]
        push_cast
        ring
      rw [h12, h32, hc, MulChar.one_apply isUnit_one, MulChar.one_apply hu3]
      ring
    · intro x hx
      rcases key02 x hx with rfl | rfl
      · rw [MulChar.map_nonunit _ hn0, zero_mul]
      · rw [MulChar.map_nonunit _ hn2, zero_mul]
  · have he1 : (stdAddChar (1 : ZMod 4) : ℂ) = I := by
      rw [stdAddChar_apply, toCircle_apply, show (1 : ZMod 4).val = 1 from rfl]
      push_cast
      rw [show 2 * (Real.pi : ℂ) * I * 1 / 4 = Real.pi / 2 * I by ring, Complex.exp_pi_div_two_mul_I]
    have he3 : (stdAddChar (3 : ZMod 4) : ℂ) = -I := by
      rw [show (3 : ZMod 4) = -1 by decide, AddChar.map_neg_eq_inv, he1, Complex.inv_I]
    have hg : gaussSum (1 : DirichletCharacter ℂ 4) stdAddChar = 0 := by
      unfold gaussSum
      rw [Fintype.sum_eq_add (1 : ZMod 4) (3 : ZMod 4) h13]
      · rw [MulChar.one_apply isUnit_one, MulChar.one_apply hu3, he1, he3]
        ring
      · intro x hx
        rcases key02 x hx with rfl | rfl
        · rw [MulChar.map_nonunit _ hn0, zero_mul]
        · rw [MulChar.map_nonunit _ hn2, zero_mul]
    rw [rootNum_eq, hg, mul_zero, zero_div, map_zero]

end PAG.Part256

#print axioms PAG.Part256.casKer
#print axioms PAG.Part256.hartley
#print axioms PAG.Part256.casKer_eq
#print axioms PAG.Part256.parFac
#print axioms PAG.Part256.parFac_of_even
#print axioms PAG.Part256.parFac_of_odd
#print axioms PAG.Part256.inv_apply_neg_one
#print axioms PAG.Part256.sum_mul_stdAddChar
#print axioms PAG.Part256.hartley_eq_of_isPrimitive
#print axioms PAG.Part256.hartley_eq_zero_of_not_isUnit
#print axioms PAG.Part256.rootNum
#print axioms PAG.Part256.rootNum_eq
#print axioms PAG.Part256.JH
#print axioms PAG.Part256.inv_apply_units_inv
#print axioms PAG.Part256.JH_eq_rootNum_mul
#print axioms PAG.Part256.normSq_rootNum
#print axioms PAG.Part256.isPrimitive_of_prime_of_ne_one
#print axioms PAG.Part256.exists_primitive_odd_three
#print axioms PAG.Part256.exists_primitive_even_five
#print axioms PAG.Part256.removal_counterexample
#print axioms PAG.Part256.hartley_units_inv
#print axioms PAG.Part256.neg_one_mul_self
#print axioms PAG.Part256.sum_mul_stdAddChar_neg
#print axioms PAG.Part256.hartley_one
#print axioms PAG.Part256.JH_eq_rootNum_mul_any
#print axioms PAG.Part256.removal_counterexample_normSq
#print axioms PAG.Part256.removal_counterexample_four
