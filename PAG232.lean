/-
  PAG 2.0 Part 228（2026-10-30）— 中国剰余定理による A_{ab} ≅ A_a ⊗ A_b（gcd(a, b) = 1）
  A_N = ⟨E_s, D_s⟩（Part 214 の shellAlg）、E_s = ε_s の畳み込み、D_s = 1_{D_s} の掛け算（Part 201 の geps・dind）、
  ε_s の球の交代和（Part 201 の geps_eq_balls）、dim A_{ab} = dim A_a·dim A_b（Part 226 の finrank_shellAlg_mul）
  0. 中国剰余定理 ℤ/ab ≅ ℤ/a × ℤ/b（Mathlib の ZMod.chineseRemainder）の成分は x mod a と x mod b。
     gcd(ab, x) = gcd(a, x mod a)·gcd(b, x mod b)。g_a g_b = s_a s_b ⇔ g_a = s_a かつ g_b = s_b（g_a, s_a ∣ a、g_b, s_b ∣ b）
  1. 関数の分解（s_a ∣ a、s_b ∣ b）：1_{D_{s_a s_b}}(x) = 1_{D_{s_a}}(x mod a)·1_{D_{s_b}}(x mod b)、
     ε_{s_a s_b}(x) = ε_{s_a}(x mod a)·ε_{s_b}(x mod b)（約数の和の分解とメビウス関数の乗法性から）
  2. 作用素の分解：ℂ^{ℤ/ab} ≅ ℂ^{ℤ/a × ℤ/b}（def crtLin）による共役 C（def crtConj、代数同型）で
     C(E_{s_a s_b}) = L(E_{s_a})·R(E_{s_b})、C(D_{s_a s_b}) = L(D_{s_a})·R(D_{s_b})。
     L(S)（def leftOp）は第 1 座標に、R(T)（def rightOp）は第 2 座標に作用する。L(S) と R(T) は可換、L と R は単射
  3. 部分代数：C(A_{ab}) = L(A_a) ⊔ R(A_b)、dim (L(A_a) ⊔ R(A_b)) = dim A_a·dim A_b
  4. テンソル積：S ⊗ T ↦ L(S)R(T)（def tensLift）の像は L(A_a) ⊔ R(A_b)、次元が等しいので単射。
     A_a ⊗ A_b ≅ A_{ab}（def shellAlgTensorEquiv、代数同型）、E_{s_a} ⊗ E_{s_b} ↦ E_{s_a s_b}、D_{s_a} ⊗ D_{s_b} ↦ D_{s_a s_b}
-/
import PAG231

namespace PAG.Part232

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 中国剰余定理の座標 -/

/-- **0a.** 中国剰余定理 ℤ/ab ≅ ℤ/a × ℤ/b の第 1 成分は x mod a。 -/
theorem crt_fst_val {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (x : ZMod (a * b)) :
    (ZMod.chineseRemainder hab x).1.val = x.val % a := by
  show ((ZMod.castHom (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)) (ZMod a × ZMod b)) x).1.val = x.val % a
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, Prod.fst_natCast, ZMod.val_natCast]

/-- **0b.** 第 2 成分は x mod b。 -/
theorem crt_snd_val {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (x : ZMod (a * b)) :
    (ZMod.chineseRemainder hab x).2.val = x.val % b := by
  show ((ZMod.castHom (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)) (ZMod a × ZMod b)) x).2.val = x.val % b
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, Prod.snd_natCast, ZMod.val_natCast]

/-- **0c.** gcd(ab, x) = gcd(a, x mod a)·gcd(b, x mod b)。 -/
theorem gcd_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (x : ZMod (a * b)) :
    Nat.gcd (a * b) x.val =
      Nat.gcd a (ZMod.chineseRemainder hab x).1.val * Nat.gcd b (ZMod.chineseRemainder hab x).2.val := by
  rw [crt_fst_val, crt_snd_val, Nat.gcd_comm (a * b), Nat.Coprime.gcd_mul x.val hab, Nat.gcd_comm x.val a,
    Nat.gcd_comm x.val b, Nat.gcd_rec a x.val, Nat.gcd_rec b x.val, Nat.gcd_comm (x.val % a),
    Nat.gcd_comm (x.val % b)]

/-- **0d.** gcd(a, b) = 1、g_a, s_a ∣ a、g_b, s_b ∣ b なら g_a g_b = s_a s_b ⇔ g_a = s_a かつ g_b = s_b。 -/
theorem mul_eq_mul_iff_of_coprime {a b ga gb sa sb : ℕ} (hab : Nat.Coprime a b) (hga : ga ∣ a) (hgb : gb ∣ b)
    (hsa : sa ∣ a) (hsb : sb ∣ b) : ga * gb = sa * sb ↔ ga = sa ∧ gb = sb := by
  constructor
  · intro h
    have h1 : Nat.gcd (ga * gb) a = ga := by
      rw [Nat.Coprime.gcd_mul_right_cancel ga (Nat.Coprime.coprime_dvd_left hgb hab.symm), Nat.gcd_eq_left hga]
    have h2 : Nat.gcd (sa * sb) a = sa := by
      rw [Nat.Coprime.gcd_mul_right_cancel sa (Nat.Coprime.coprime_dvd_left hsb hab.symm), Nat.gcd_eq_left hsa]
    have h3 : Nat.gcd (gb * ga) b = gb := by
      rw [Nat.Coprime.gcd_mul_right_cancel gb (Nat.Coprime.coprime_dvd_left hga hab), Nat.gcd_eq_left hgb]
    have h4 : Nat.gcd (sb * sa) b = sb := by
      rw [Nat.Coprime.gcd_mul_right_cancel sb (Nat.Coprime.coprime_dvd_left hsa hab), Nat.gcd_eq_left hsb]
    refine ⟨?_, ?_⟩
    · rw [← h1, ← h2, h]
    · rw [← h3, ← h4, mul_comm gb, mul_comm sb, h]
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ### 1. 関数の分解 -/

/-- **1a.** 1_{D_{s_a s_b}}(x) = 1_{D_{s_a}}(x mod a)·1_{D_{s_b}}(x mod b)（s_a ∣ a、s_b ∣ b。双対殻は積に分かれる）。 -/
theorem dind_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ} (hsa : sa ∣ a) (hsb : sb ∣ b)
    (x : ZMod (a * b)) :
    dind (a * b) (sa * sb) x = dind a sa (ZMod.chineseRemainder hab x).1 * dind b sb (ZMod.chineseRemainder hab x).2 := by
  unfold dind
  rw [gcd_crt hab x]
  have hiff := mul_eq_mul_iff_of_coprime hab (Nat.gcd_dvd_left a (ZMod.chineseRemainder hab x).1.val)
    (Nat.gcd_dvd_left b (ZMod.chineseRemainder hab x).2.val) hsa hsb
  by_cases h1 : Nat.gcd a (ZMod.chineseRemainder hab x).1.val = sa <;>
    by_cases h2 : Nat.gcd b (ZMod.chineseRemainder hab x).2.val = sb <;> simp_all

/-- **1b.** gcd(A, B) = 1 なら Σ_{e ∣ AB} F(e) = Σ_{x ∣ A} Σ_{y ∣ B} F(xy)（e ↦ (gcd(e, A), gcd(e, B))）。 -/
theorem sum_divisors_mul_of_coprime {M : Type*} [AddCommMonoid M] {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : Nat.Coprime A B) (F : ℕ → M) :
    ∑ e ∈ (A * B).divisors, F e = ∑ x ∈ A.divisors, ∑ y ∈ B.divisors, F (x * y) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun e => (Nat.gcd e A, Nat.gcd e B)) (fun p => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · intro e _
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right e A, hA⟩, ⟨Nat.gcd_dvd_right e B, hB⟩⟩
  · intro p hp
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
    rw [Nat.mem_divisors]
    exact ⟨Nat.mul_dvd_mul hp.1.1 hp.2.1, mul_ne_zero hA hB⟩
  · intro e he
    have heAB := Nat.dvd_of_mem_divisors he
    show Nat.gcd e A * Nat.gcd e B = e
    rw [← Nat.Coprime.gcd_mul e hAB, Nat.gcd_eq_left heAB]
  · intro p hp
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
    obtain ⟨⟨hxA, -⟩, ⟨hyB, -⟩⟩ := hp
    show (Nat.gcd (p.1 * p.2) A, Nat.gcd (p.1 * p.2) B) = p
    rw [Nat.Coprime.gcd_mul_right_cancel p.1 (Nat.Coprime.coprime_dvd_left hyB hAB.symm), Nat.gcd_eq_left hxA,
      mul_comm, Nat.Coprime.gcd_mul_right_cancel p.2 (Nat.Coprime.coprime_dvd_left hxA hAB), Nat.gcd_eq_left hyB]
  · intro e he
    have heAB := Nat.dvd_of_mem_divisors he
    show F e = F (Nat.gcd e A * Nat.gcd e B)
    rw [← Nat.Coprime.gcd_mul e hAB, Nat.gcd_eq_left heAB]

/-- **1c.** ε_s(x) = Σ_{e ∣ N/s} (μ(e)/(se))·[N/(se) ∣ x]（Part 201 の球の交代和を値で書いたもの）。 -/
theorem geps_apply_eq_sum (N s : ℕ) [NeZero N] (hs : s ∣ N) (x : ZMod N) :
    geps N s x = ∑ e ∈ (N / s).divisors,
      (ArithmeticFunction.moebius e : ℂ) / ((s * e : ℕ) : ℂ) * (if N / (s * e) ∣ x.val then 1 else 0) := by
  rw [geps_eq_balls N s hs, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]
  unfold rk
  split_ifs <;> rfl

/-- **1d.** v_a ∣ a、v_b ∣ b、gcd(a, b) = 1 なら [v_a v_b ∣ n] = [v_a ∣ n mod a]·[v_b ∣ n mod b]。 -/
theorem ite_dvd_mul_of_coprime {a b va vb n : ℕ} (hab : Nat.Coprime a b) (hva : va ∣ a) (hvb : vb ∣ b) :
    (if va * vb ∣ n then (1 : ℂ) else 0) =
      (if va ∣ n % a then (1 : ℂ) else 0) * (if vb ∣ n % b then (1 : ℂ) else 0) := by
  have hcop : Nat.Coprime va vb := Nat.Coprime.coprime_dvd_right hvb (Nat.Coprime.coprime_dvd_left hva hab)
  have hiff : va * vb ∣ n ↔ va ∣ n % a ∧ vb ∣ n % b := by
    rw [Nat.dvd_mod_iff hva, Nat.dvd_mod_iff hvb]
    exact ⟨fun h => ⟨dvd_trans (Dvd.intro vb rfl) h, dvd_trans (Dvd.intro_left va rfl) h⟩,
      fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  by_cases h1 : va ∣ n % a <;> by_cases h2 : vb ∣ n % b <;> simp_all

/-- **1e.** ε_{s_a s_b}(x) = ε_{s_a}(x mod a)·ε_{s_b}(x mod b)（ラマヌジャン和の乗法性。1b・1c・1d とメビウス関数の乗法性から）。 -/
theorem geps_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ} (hsa : sa ∣ a) (hsb : sb ∣ b)
    (x : ZMod (a * b)) :
    geps (a * b) (sa * sb) x = geps a sa (ZMod.chineseRemainder hab x).1 * geps b sb (ZMod.chineseRemainder hab x).2 := by
  have ha0 : a ≠ 0 := NeZero.ne a
  have hb0 : b ≠ 0 := NeZero.ne b
  have hsa0 : sa ≠ 0 := fun h => ha0 (Nat.eq_zero_of_zero_dvd (h ▸ hsa))
  have hsb0 : sb ≠ 0 := fun h => hb0 (Nat.eq_zero_of_zero_dvd (h ▸ hsb))
  have hA0 : a / sa ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hsa) (Nat.pos_of_ne_zero hsa0)).ne'
  have hB0 : b / sb ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hsb) (Nat.pos_of_ne_zero hsb0)).ne'
  have hAB : Nat.Coprime (a / sa) (b / sb) :=
    Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hsb) (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hsa) hab)
  rw [geps_apply_eq_sum (a * b) (sa * sb) (Nat.mul_dvd_mul hsa hsb) x,
    geps_apply_eq_sum a sa hsa _, geps_apply_eq_sum b sb hsb _, crt_fst_val, crt_snd_val,
    ← Nat.div_mul_div_comm hsa hsb, sum_divisors_mul_of_coprime hA0 hB0 hAB, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun ea hea => Finset.sum_congr rfl (fun eb heb => ?_))
  have heaA : ea ∣ a / sa := Nat.dvd_of_mem_divisors hea
  have hebB : eb ∣ b / sb := Nat.dvd_of_mem_divisors heb
  have hsea : sa * ea ∣ a := Nat.mul_dvd_of_dvd_div hsa heaA
  have hseb : sb * eb ∣ b := Nat.mul_dvd_of_dvd_div hsb hebB
  have hcop_e : Nat.Coprime ea eb :=
    Nat.Coprime.coprime_dvd_right (dvd_trans (Dvd.intro_left sb rfl) hseb)
      (Nat.Coprime.coprime_dvd_left (dvd_trans (Dvd.intro_left sa rfl) hsea) hab)
  have hmu : ArithmeticFunction.moebius (ea * eb) = ArithmeticFunction.moebius ea * ArithmeticFunction.moebius eb :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_e
  have hdiv : a * b / (sa * sb * (ea * eb)) = a / (sa * ea) * (b / (sb * eb)) := by
    rw [Nat.div_mul_div_comm hsea hseb]
    congr 1
    ring
  rw [hdiv, ite_dvd_mul_of_coprime hab (Nat.div_dvd_of_dvd hsea) (Nat.div_dvd_of_dvd hseb), hmu]
  push_cast
  field_simp

/-! ### 2. 作用素の分解 -/

/-- ℂ^{ℤ/ab} ≅ ℂ^{ℤ/a × ℤ/b}（f ↦ f ∘ (中国剰余定理)⁻¹、線形同型）。 -/
noncomputable def crtLin {a b : ℕ} (hab : Nat.Coprime a b) : (ZMod (a * b) → ℂ) ≃ₗ[ℂ] (ZMod a × ZMod b → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (ZMod.chineseRemainder hab).symm.toEquiv

/-- **2a.** crtLin の値。 -/
theorem crtLin_apply {a b : ℕ} (hab : Nat.Coprime a b) (f : ZMod (a * b) → ℂ) (p : ZMod a × ZMod b) :
    crtLin hab f p = f ((ZMod.chineseRemainder hab).symm p) := rfl

/-- **2b.** 逆写像の値：F ↦ F ∘ (中国剰余定理)。 -/
theorem crtLin_symm_apply {a b : ℕ} (hab : Nat.Coprime a b) (F : ZMod a × ZMod b → ℂ) (x : ZMod (a * b)) :
    (crtLin hab).symm F x = F (ZMod.chineseRemainder hab x) := rfl

/-- 共役 C(T) = crtLin ∘ T ∘ crtLin⁻¹（End(ℂ^{ℤ/ab}) ≅ End(ℂ^{ℤ/a × ℤ/b})、代数同型）。 -/
noncomputable def crtConj {a b : ℕ} (hab : Nat.Coprime a b) :
    Module.End ℂ (ZMod (a * b) → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  (crtLin hab).conjAlgEquiv ℂ

/-- **2c.** C の値。 -/
theorem crtConj_apply {a b : ℕ} (hab : Nat.Coprime a b) (T : Module.End ℂ (ZMod (a * b) → ℂ))
    (F : ZMod a × ZMod b → ℂ) : crtConj hab T F = crtLin hab (T ((crtLin hab).symm F)) := rfl

/-- L(S)：S ∈ End(ℂ^{ℤ/a}) を第 1 座標に作用させたもの（S ⊗ 1）。 -/
noncomputable def leftOp {a : ℕ} (b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := S (fun x => F (x, p.2)) p.1
  map_add' F G := by
    funext p
    show S ((fun x => F (x, p.2)) + (fun x => G (x, p.2))) p.1 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show S (c • (fun x => F (x, p.2))) p.1 = _
    rw [map_smul]
    rfl

/-- R(T)：T ∈ End(ℂ^{ℤ/b}) を第 2 座標に作用させたもの（1 ⊗ T）。 -/
noncomputable def rightOp (a : ℕ) {b : ℕ} (T : Module.End ℂ (ZMod b → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := T (fun y => F (p.1, y)) p.2
  map_add' F G := by
    funext p
    show T ((fun y => F (p.1, y)) + (fun y => G (p.1, y))) p.2 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show T (c • (fun y => F (p.1, y))) p.2 = _
    rw [map_smul]
    rfl

/-- **2d.** L(S) の値：L(S)F(x, y) = S(F(·, y))(x)。 -/
theorem leftOp_apply {a : ℕ} (b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) (F : ZMod a × ZMod b → ℂ) (p : ZMod a × ZMod b) :
    leftOp b S F p = S (fun x => F (x, p.2)) p.1 := rfl

/-- **2e.** R(T) の値：R(T)F(x, y) = T(F(x, ·))(y)。 -/
theorem rightOp_apply (a : ℕ) {b : ℕ} (T : Module.End ℂ (ZMod b → ℂ)) (F : ZMod a × ZMod b → ℂ) (p : ZMod a × ZMod b) :
    rightOp a T F p = T (fun y => F (p.1, y)) p.2 := rfl

/-- L：End(ℂ^{ℤ/a}) → End(ℂ^{ℤ/a × ℤ/b})（代数準同型）。 -/
noncomputable def leftHom (a b : ℕ) : Module.End ℂ (ZMod a → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := leftOp b
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)

/-- R：End(ℂ^{ℤ/b}) → End(ℂ^{ℤ/a × ℤ/b})（代数準同型）。 -/
noncomputable def rightHom (a b : ℕ) : Module.End ℂ (ZMod b → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := rightOp a
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)

/-- **2f.** L の値。 -/
theorem leftHom_apply (a b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) : leftHom a b S = leftOp b S := rfl

/-- **2g.** R の値。 -/
theorem rightHom_apply (a b : ℕ) (T : Module.End ℂ (ZMod b → ℂ)) : rightHom a b T = rightOp a T := rfl

/-- **2h.** L(S) と R(T) は可換（行列の成分で書いて和の順序を入れ替える）。 -/
theorem leftOp_commute_rightOp {a b : ℕ} [NeZero a] [NeZero b] (S : Module.End ℂ (ZMod a → ℂ))
    (T : Module.End ℂ (ZMod b → ℂ)) : Commute (leftOp b S) (rightOp a T) := by
  apply LinearMap.ext
  intro F
  funext p
  show S (fun x => T (fun y => F (x, y)) p.2) p.1 = T (fun y => S (fun x => F (x, y)) p.1) p.2
  rw [PAG.Part229.apply_eq_sum_single a S _ p.1, PAG.Part229.apply_eq_sum_single b T _ p.2]
  have hL : ∀ x : ZMod a, T (fun y => F (x, y)) p.2 = ∑ y, F (x, y) * T (Pi.single y 1) p.2 :=
    fun x => PAG.Part229.apply_eq_sum_single b T _ p.2
  have hR : ∀ y : ZMod b, S (fun x => F (x, y)) p.1 = ∑ x, F (x, y) * S (Pi.single x 1) p.1 :=
    fun y => PAG.Part229.apply_eq_sum_single a S _ p.1
  simp only [hL, hR, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

/-- **2i.** L は単射（b ≠ 0）。 -/
theorem leftHom_injective (a b : ℕ) [NeZero b] : Function.Injective (leftHom a b) := by
  intro S S' h
  apply LinearMap.ext
  intro f
  funext x
  exact congrArg (fun T : Module.End ℂ (ZMod a × ZMod b → ℂ) => T (fun p => f p.1) (x, 0)) h

/-- **2j.** R は単射（a ≠ 0）。 -/
theorem rightHom_injective (a b : ℕ) [NeZero a] : Function.Injective (rightHom a b) := by
  intro T T' h
  apply LinearMap.ext
  intro f
  funext y
  exact congrArg (fun S : Module.End ℂ (ZMod a × ZMod b → ℂ) => S (fun p => f p.2) (0, y)) h

/-- **2k.** C(D_{s_a s_b}) = L(D_{s_a})·R(D_{s_b})（1a から）。 -/
theorem crtConj_dind {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ} (hsa : sa ∣ a)
    (hsb : sb ∣ b) :
    crtConj hab (LinearMap.mulLeft ℂ (dind (a * b) (sa * sb))) =
      leftOp b (LinearMap.mulLeft ℂ (dind a sa)) * rightOp a (LinearMap.mulLeft ℂ (dind b sb)) := by
  apply LinearMap.ext
  intro F
  funext p
  show dind (a * b) (sa * sb) ((ZMod.chineseRemainder hab).symm p) *
      F (ZMod.chineseRemainder hab ((ZMod.chineseRemainder hab).symm p)) = dind a sa p.1 * (dind b sb p.2 * F (p.1, p.2))
  rw [dind_crt hab hsa hsb, RingEquiv.apply_symm_apply, mul_assoc]

/-- **2l.** C(E_{s_a s_b}) = L(E_{s_a})·R(E_{s_b})（1e と、畳み込みの和を ℤ/a × ℤ/b の和に移すことから）。 -/
theorem crtConj_geps {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ} (hsa : sa ∣ a)
    (hsb : sb ∣ b) :
    crtConj hab (PAG.Part15.convL (geps (a * b) (sa * sb))) =
      leftOp b (PAG.Part15.convL (geps a sa)) * rightOp a (PAG.Part15.convL (geps b sb)) := by
  apply LinearMap.ext
  intro F
  funext p
  show (∑ w : ZMod (a * b), geps (a * b) (sa * sb) w *
      F (ZMod.chineseRemainder hab ((ZMod.chineseRemainder hab).symm p - w))) =
    ∑ wa : ZMod a, geps a sa wa * ∑ wb : ZMod b, geps b sb wb * F (p.1 - wa, p.2 - wb)
  simp only [map_sub, RingEquiv.apply_symm_apply]
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hab).toEquiv _
    (fun q => geps (a * b) (sa * sb) ((ZMod.chineseRemainder hab).symm q) * F (p - q))
    (fun w => by simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv, RingEquiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun wa _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun wb _ => ?_)
  rw [geps_crt hab hsa hsb, RingEquiv.apply_symm_apply, mul_assoc]
  rfl

/-! ### 3. 部分代数の分解 -/

/-- **3a.** s ∤ N なら 1_{D_s} = 0。 -/
theorem dind_eq_zero_of_not_dvd {N s : ℕ} [NeZero N] (hs : ¬ s ∣ N) : dind N s = 0 := by
  funext ξ
  unfold dind
  exact ite_eq_right (fun h : Nat.gcd N ξ.val = s => hs (h ▸ Nat.gcd_dvd_left N ξ.val))

/-- **3b.** s ∤ N なら ε_s = 0。 -/
theorem geps_eq_zero_of_not_dvd {N s : ℕ} [NeZero N] (hs : ¬ s ∣ N) : geps N s = 0 := by
  unfold geps
  rw [dind_eq_zero_of_not_dvd hs, map_zero]

/-- **3c.** Σ_{s ∣ N} E_s = 1。 -/
theorem sum_convL_geps (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, PAG.Part15.convL (geps N s) = 1 := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.sum_apply, Module.End.one_apply]
  exact sum_geps_conv N f

/-- **3d.** Σ_{s ∣ N} D_s = 1。 -/
theorem sum_mulLeft_dind (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, LinearMap.mulLeft ℂ (dind N s) = 1 := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.sum_apply, Module.End.one_apply]
  simp only [LinearMap.mulLeft_apply]
  rw [← Finset.sum_mul, sum_dind, one_mul]

/-- **3e.** A_N は E_s・D_s（s ∈ ℕ）で生成される（定義の書き直し）。 -/
theorem shellAlg_eq_adjoin (N : ℕ) [NeZero N] : shellAlg N = Algebra.adjoin ℂ
    (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪ Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s))) :=
  rfl

/-- **3f.** E_s ∈ A_N。 -/
theorem convL_geps_mem (N s : ℕ) [NeZero N] : PAG.Part15.convL (geps N s) ∈ shellAlg N :=
  Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)

/-- **3g.** D_s ∈ A_N。 -/
theorem mulLeft_dind_mem (N s : ℕ) [NeZero N] : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N :=
  Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)

/-- **3h.** L(A_a) ⊆ C(A_{ab})（L(E_s) = Σ_{t ∣ b} L(E_s)R(E_t) = Σ_t C(E_{st})。D_s も同じ）。 -/
theorem map_leftHom_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (shellAlg a).map (leftHom a b) ≤ (shellAlg (a * b)).map (crtConj hab).toAlgHom := by
  rw [shellAlg_eq_adjoin a, AlgHom.map_adjoin]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨T, hT, rfl⟩
  rcases hT with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · by_cases hs : s ∣ a
    · have h1 : leftHom a b (PAG.Part15.convL (geps a s)) = ∑ t ∈ b.divisors,
          leftOp b (PAG.Part15.convL (geps a s)) * rightOp a (PAG.Part15.convL (geps b t)) := by
        rw [← Finset.mul_sum]
        have h2 : ∑ t ∈ b.divisors, rightOp a (PAG.Part15.convL (geps b t)) = 1 := by
          rw [← map_one (rightHom a b), ← sum_convL_geps b, map_sum]
          rfl
        rw [h2, mul_one]
        rfl
      rw [SetLike.mem_coe, h1]
      refine Subalgebra.sum_mem _ (fun t ht => ?_)
      rw [← crtConj_geps hab hs (Nat.dvd_of_mem_divisors ht)]
      exact Subalgebra.mem_map.mpr ⟨_, Algebra.subset_adjoin (Or.inl ⟨s * t, rfl⟩), rfl⟩
    · show leftHom a b (PAG.Part15.convL (geps a s)) ∈ _
      rw [geps_eq_zero_of_not_dvd hs, map_zero, map_zero]
      exact Subalgebra.zero_mem _
  · by_cases hs : s ∣ a
    · have h1 : leftHom a b (LinearMap.mulLeft ℂ (dind a s)) = ∑ t ∈ b.divisors,
          leftOp b (LinearMap.mulLeft ℂ (dind a s)) * rightOp a (LinearMap.mulLeft ℂ (dind b t)) := by
        rw [← Finset.mul_sum]
        have h2 : ∑ t ∈ b.divisors, rightOp a (LinearMap.mulLeft ℂ (dind b t)) = 1 := by
          rw [← map_one (rightHom a b), ← sum_mulLeft_dind b, map_sum]
          rfl
        rw [h2, mul_one]
        rfl
      rw [SetLike.mem_coe, h1]
      refine Subalgebra.sum_mem _ (fun t ht => ?_)
      rw [← crtConj_dind hab hs (Nat.dvd_of_mem_divisors ht)]
      exact Subalgebra.mem_map.mpr ⟨_, Algebra.subset_adjoin (Or.inr ⟨s * t, rfl⟩), rfl⟩
    · show leftHom a b (LinearMap.mulLeft ℂ (dind a s)) ∈ _
      rw [dind_eq_zero_of_not_dvd hs, LinearMap.mulLeft_zero_eq_zero, map_zero]
      exact Subalgebra.zero_mem _

/-- **3i.** R(A_b) ⊆ C(A_{ab})。 -/
theorem map_rightHom_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (shellAlg b).map (rightHom a b) ≤ (shellAlg (a * b)).map (crtConj hab).toAlgHom := by
  rw [shellAlg_eq_adjoin b, AlgHom.map_adjoin]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨T, hT, rfl⟩
  rcases hT with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · by_cases hs : s ∣ b
    · have h1 : rightHom a b (PAG.Part15.convL (geps b s)) = ∑ t ∈ a.divisors,
          leftOp b (PAG.Part15.convL (geps a t)) * rightOp a (PAG.Part15.convL (geps b s)) := by
        rw [← Finset.sum_mul]
        have h2 : ∑ t ∈ a.divisors, leftOp b (PAG.Part15.convL (geps a t)) = 1 := by
          rw [← map_one (leftHom a b), ← sum_convL_geps a, map_sum]
          rfl
        rw [h2, one_mul]
        rfl
      rw [SetLike.mem_coe, h1]
      refine Subalgebra.sum_mem _ (fun t ht => ?_)
      rw [← crtConj_geps hab (Nat.dvd_of_mem_divisors ht) hs]
      exact Subalgebra.mem_map.mpr ⟨_, Algebra.subset_adjoin (Or.inl ⟨t * s, rfl⟩), rfl⟩
    · show rightHom a b (PAG.Part15.convL (geps b s)) ∈ _
      rw [geps_eq_zero_of_not_dvd hs, map_zero, map_zero]
      exact Subalgebra.zero_mem _
  · by_cases hs : s ∣ b
    · have h1 : rightHom a b (LinearMap.mulLeft ℂ (dind b s)) = ∑ t ∈ a.divisors,
          leftOp b (LinearMap.mulLeft ℂ (dind a t)) * rightOp a (LinearMap.mulLeft ℂ (dind b s)) := by
        rw [← Finset.sum_mul]
        have h2 : ∑ t ∈ a.divisors, leftOp b (LinearMap.mulLeft ℂ (dind a t)) = 1 := by
          rw [← map_one (leftHom a b), ← sum_mulLeft_dind a, map_sum]
          rfl
        rw [h2, one_mul]
        rfl
      rw [SetLike.mem_coe, h1]
      refine Subalgebra.sum_mem _ (fun t ht => ?_)
      rw [← crtConj_dind hab (Nat.dvd_of_mem_divisors ht) hs]
      exact Subalgebra.mem_map.mpr ⟨_, Algebra.subset_adjoin (Or.inr ⟨t * s, rfl⟩), rfl⟩
    · show rightHom a b (LinearMap.mulLeft ℂ (dind b s)) ∈ _
      rw [dind_eq_zero_of_not_dvd hs, LinearMap.mulLeft_zero_eq_zero, map_zero]
      exact Subalgebra.zero_mem _

/-- **3j.** C(A_{ab}) ⊆ L(A_a) ⊔ R(A_b)（s ∣ ab は s = gcd(s, a)·gcd(s, b)、2k・2l）。 -/
theorem map_crtConj_le {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (shellAlg (a * b)).map (crtConj hab).toAlgHom ≤ (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b) := by
  have hL : ∀ S ∈ shellAlg a, leftOp b S ∈ (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b) :=
    fun S hS => (le_sup_left : (shellAlg a).map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩)
  have hR : ∀ T ∈ shellAlg b, rightOp a T ∈ (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b) :=
    fun T hT => (le_sup_right : (shellAlg b).map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨T, hT, rfl⟩)
  rw [shellAlg_eq_adjoin (a * b), AlgHom.map_adjoin]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨T, hT, rfl⟩
  rcases hT with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · by_cases hs : s ∣ a * b
    · have hs' : s = Nat.gcd s a * Nat.gcd s b := by rw [← Nat.Coprime.gcd_mul s hab, Nat.gcd_eq_left hs]
      show crtConj hab (PAG.Part15.convL (geps (a * b) s)) ∈ _
      rw [hs', crtConj_geps hab (Nat.gcd_dvd_right s a) (Nat.gcd_dvd_right s b)]
      exact Subalgebra.mul_mem _ (hL _ (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)))
        (hR _ (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)))
    · show crtConj hab (PAG.Part15.convL (geps (a * b) s)) ∈ _
      rw [geps_eq_zero_of_not_dvd hs, map_zero, map_zero]
      exact Subalgebra.zero_mem _
  · by_cases hs : s ∣ a * b
    · have hs' : s = Nat.gcd s a * Nat.gcd s b := by rw [← Nat.Coprime.gcd_mul s hab, Nat.gcd_eq_left hs]
      show crtConj hab (LinearMap.mulLeft ℂ (dind (a * b) s)) ∈ _
      rw [hs', crtConj_dind hab (Nat.gcd_dvd_right s a) (Nat.gcd_dvd_right s b)]
      exact Subalgebra.mul_mem _ (hL _ (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)))
        (hR _ (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)))
    · show crtConj hab (LinearMap.mulLeft ℂ (dind (a * b) s)) ∈ _
      rw [dind_eq_zero_of_not_dvd hs, LinearMap.mulLeft_zero_eq_zero, map_zero]
      exact Subalgebra.zero_mem _

/-- **3k. C(A_{ab}) = L(A_a) ⊔ R(A_b)**。 -/
theorem map_crtConj_shellAlg {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (shellAlg (a * b)).map (crtConj hab).toAlgHom = (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b) :=
  le_antisymm (map_crtConj_le hab) (sup_le (map_leftHom_le hab) (map_rightHom_le hab))

/-- **3l.** T ∈ A_{ab} ⇔ C(T) ∈ L(A_a) ⊔ R(A_b)。 -/
theorem mem_shellAlg_mul_iff {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (T : Module.End ℂ (ZMod (a * b) → ℂ)) :
    T ∈ shellAlg (a * b) ↔ crtConj hab T ∈ (shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b) := by
  rw [← map_crtConj_shellAlg hab]
  constructor
  · intro h
    exact Subalgebra.mem_map.mpr ⟨T, h, rfl⟩
  · intro h
    obtain ⟨T', hT', he⟩ := Subalgebra.mem_map.mp h
    have hTT : T' = T := (crtConj hab).injective he
    rw [← hTT]
    exact hT'

/-- **3m.** dim C(A_{ab}) = dim A_{ab}。 -/
theorem finrank_map_crtConj {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ ((shellAlg (a * b)).map (crtConj hab).toAlgHom) = Module.finrank ℂ (shellAlg (a * b)) :=
  ((Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom
    (crtConj hab).injective).toLinearEquiv.finrank_eq).symm

/-- **3n.** dim (L(A_a) ⊔ R(A_b)) = dim A_a·dim A_b（3k・3m と Part 226 の finrank_shellAlg_mul）。 -/
theorem finrank_sup_leftHom_rightHom {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ ↥((shellAlg a).map (leftHom a b) ⊔ (shellAlg b).map (rightHom a b)) =
      Module.finrank ℂ (shellAlg a) * Module.finrank ℂ (shellAlg b) := by
  rw [← map_crtConj_shellAlg hab, finrank_map_crtConj hab, PAG.Part230.finrank_shellAlg_mul hab]

/-! ### 4. テンソル積 A_a ⊗ A_b ≅ A_{ab} -/

/-- A_a ⊗ A_b → End(ℂ^{ℤ/a × ℤ/b})、S ⊗ T ↦ L(S)R(T)（L(S) と R(T) は可換なので代数準同型）。 -/
noncomputable def tensLift (a b : ℕ) [NeZero a] [NeZero b] :
    TensorProduct ℂ (shellAlg a) (shellAlg b) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  Algebra.TensorProduct.lift ((leftHom a b).comp (shellAlg a).val) ((rightHom a b).comp (shellAlg b).val)
    (fun x y => leftOp_commute_rightOp (x : Module.End ℂ (ZMod a → ℂ)) (y : Module.End ℂ (ZMod b → ℂ)))

/-- **4a.** S ⊗ T ↦ L(S)·R(T)。 -/
theorem tensLift_tmul (a b : ℕ) [NeZero a] [NeZero b] (S : shellAlg a) (T : shellAlg b) :
    tensLift a b (S ⊗ₜ[ℂ] T) = leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) :=
  Algebra.TensorProduct.lift_tmul _ _ _ S T

/-- **4b.** 像 = C(A_{ab})（= L(A_a) ⊔ R(A_b)）。 -/
theorem range_tensLift {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    (tensLift a b).range = (shellAlg (a * b)).map (crtConj hab).toAlgHom := by
  rw [map_crtConj_shellAlg hab]
  apply le_antisymm
  · intro y hmem
    obtain ⟨z, rfl⟩ := (AlgHom.mem_range _).mp hmem
    clear hmem
    induction z using TensorProduct.inductionOn with
    | tmul S T =>
      rw [tensLift_tmul]
      exact Subalgebra.mul_mem _
        ((le_sup_left : (shellAlg a).map (leftHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨S.1, S.2, rfl⟩))
        ((le_sup_right : (shellAlg b).map (rightHom a b) ≤ _) (Subalgebra.mem_map.mpr ⟨T.1, T.2, rfl⟩))
    | add x y hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  · refine sup_le ?_ ?_
    · intro y hmem
      obtain ⟨S, hS, rfl⟩ := Subalgebra.mem_map.mp hmem
      refine (AlgHom.mem_range _).mpr ⟨⟨S, hS⟩ ⊗ₜ[ℂ] 1, ?_⟩
      rw [tensLift_tmul]
      show leftOp b S * rightHom a b 1 = leftHom a b S
      rw [map_one, mul_one]
      rfl
    · intro y hmem
      obtain ⟨T, hT, rfl⟩ := Subalgebra.mem_map.mp hmem
      refine (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ[ℂ] ⟨T, hT⟩, ?_⟩
      rw [tensLift_tmul]
      show leftHom a b 1 * rightOp a T = rightHom a b T
      rw [map_one, one_mul]
      rfl

/-- **4c.** dim A_a ⊗ A_b = dim A_{ab}（Part 226 の finrank_shellAlg_mul）。 -/
theorem finrank_tensor_shellAlg {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Module.finrank ℂ (TensorProduct ℂ (shellAlg a) (shellAlg b)) = Module.finrank ℂ (shellAlg (a * b)) := by
  have h1 : @Module.Free ℂ ↥(shellAlg a) _ (AddSubmonoidClass.toAddCommMonoid (shellAlg a)) Algebra.toModule :=
    Module.Free.of_divisionRing ℂ ↥(shellAlg a)
  have h2 : @Module.Free ℂ ↥(shellAlg b) _ (AddSubmonoidClass.toAddCommMonoid (shellAlg b)) Algebra.toModule :=
    Module.Free.of_divisionRing ℂ ↥(shellAlg b)
  rw [Module.finrank_tensorProduct, PAG.Part230.finrank_shellAlg_mul hab]

/-- **4d.** S ⊗ T ↦ L(S)R(T) は単射（像の次元 = 定義域の次元）。 -/
theorem tensLift_injective {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    Function.Injective (tensLift a b) := by
  let _ : AddCommGroup (TensorProduct ℂ (shellAlg a) (shellAlg b)) := Module.addCommMonoidToAddCommGroup ℂ
  have hfd : FiniteDimensional ℂ (TensorProduct ℂ (shellAlg a) (shellAlg b)) := inferInstance
  have hsurj : Function.Surjective (tensLift a b).rangeRestrict := AlgHom.rangeRestrict_surjective _
  have hfin : Module.finrank ℂ (TensorProduct ℂ (shellAlg a) (shellAlg b)) =
      Module.finrank ℂ (tensLift a b).range := by
    rw [finrank_tensor_shellAlg hab, range_tensLift hab, finrank_map_crtConj hab]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℂ)
    (V := TensorProduct ℂ (shellAlg a) (shellAlg b)) (V₂ := (tensLift a b).range) hfin
    (f := (tensLift a b).rangeRestrict.toLinearMap)).mpr hsurj
  intro x y h
  exact hinj (Subtype.ext h)

/-- **代数同型** A_a ⊗ A_b ≅ A_{ab}（gcd(a, b) = 1）。 -/
noncomputable def shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (shellAlg a) (shellAlg b) ≃ₐ[ℂ] shellAlg (a * b) :=
  ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))).trans
    (Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective).symm

/-- **4e.** C(Θ(z)) = tensLift(z)（Θ = shellAlgTensorEquiv）。 -/
theorem crtConj_shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (z : TensorProduct ℂ (shellAlg a) (shellAlg b)) :
    crtConj hab (shellAlgTensorEquiv hab z : Module.End ℂ (ZMod (a * b) → ℂ)) = tensLift a b z := by
  set e := Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective
  set w := ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))) z
  have h1 : ((e (e.symm w)) : Module.End ℂ (ZMod a × ZMod b → ℂ)) = (crtConj hab).toAlgHom (e.symm w : Module.End ℂ (ZMod (a * b) → ℂ)) :=
    Subalgebra.coe_equivMapOfInjective_apply _ _ _ _
  rw [AlgEquiv.apply_symm_apply] at h1
  have h2 : (w : Module.End ℂ (ZMod a × ZMod b → ℂ)) = tensLift a b z := by
    simp only [w, AlgEquiv.trans_apply, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]
  show crtConj hab ((e.symm w : shellAlg (a * b)) : Module.End ℂ (ZMod (a * b) → ℂ)) = tensLift a b z
  rw [← h2, h1]
  rfl

/-- **4f.** C(Θ(S ⊗ T)) = L(S)·R(T)。 -/
theorem crtConj_shellAlgTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (S : shellAlg a) (T : shellAlg b) :
    crtConj hab (shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ)) := by
  rw [crtConj_shellAlgTensorEquiv, tensLift_tmul]

/-- **4g.** Θ(E_{s_a} ⊗ E_{s_b}) = E_{s_a s_b}（s_a ∣ a、s_b ∣ b）。 -/
theorem shellAlgTensorEquiv_geps {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ}
    (hsa : sa ∣ a) (hsb : sb ∣ b) :
    (shellAlgTensorEquiv hab (⟨_, convL_geps_mem a sa⟩ ⊗ₜ[ℂ] ⟨_, convL_geps_mem b sb⟩) :
      Module.End ℂ (ZMod (a * b) → ℂ)) = PAG.Part15.convL (geps (a * b) (sa * sb)) := by
  apply (crtConj hab).injective
  rw [crtConj_shellAlgTensorEquiv_tmul, crtConj_geps hab hsa hsb]

/-- **4h.** Θ(D_{s_a} ⊗ D_{s_b}) = D_{s_a s_b}。 -/
theorem shellAlgTensorEquiv_dind {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ}
    (hsa : sa ∣ a) (hsb : sb ∣ b) :
    (shellAlgTensorEquiv hab (⟨_, mulLeft_dind_mem a sa⟩ ⊗ₜ[ℂ] ⟨_, mulLeft_dind_mem b sb⟩) :
      Module.End ℂ (ZMod (a * b) → ℂ)) = LinearMap.mulLeft ℂ (dind (a * b) (sa * sb)) := by
  apply (crtConj hab).injective
  rw [crtConj_shellAlgTensorEquiv_tmul, crtConj_dind hab hsa hsb]

end PAG.Part232

#print axioms PAG.Part232.crt_fst_val
#print axioms PAG.Part232.crt_snd_val
#print axioms PAG.Part232.gcd_crt
#print axioms PAG.Part232.mul_eq_mul_iff_of_coprime
#print axioms PAG.Part232.dind_crt
#print axioms PAG.Part232.sum_divisors_mul_of_coprime
#print axioms PAG.Part232.geps_apply_eq_sum
#print axioms PAG.Part232.ite_dvd_mul_of_coprime
#print axioms PAG.Part232.geps_crt
#print axioms PAG.Part232.crtLin
#print axioms PAG.Part232.crtLin_apply
#print axioms PAG.Part232.crtLin_symm_apply
#print axioms PAG.Part232.crtConj
#print axioms PAG.Part232.crtConj_apply
#print axioms PAG.Part232.leftOp
#print axioms PAG.Part232.rightOp
#print axioms PAG.Part232.leftOp_apply
#print axioms PAG.Part232.rightOp_apply
#print axioms PAG.Part232.leftHom
#print axioms PAG.Part232.rightHom
#print axioms PAG.Part232.leftHom_apply
#print axioms PAG.Part232.rightHom_apply
#print axioms PAG.Part232.leftOp_commute_rightOp
#print axioms PAG.Part232.leftHom_injective
#print axioms PAG.Part232.rightHom_injective
#print axioms PAG.Part232.crtConj_dind
#print axioms PAG.Part232.crtConj_geps
#print axioms PAG.Part232.dind_eq_zero_of_not_dvd
#print axioms PAG.Part232.geps_eq_zero_of_not_dvd
#print axioms PAG.Part232.sum_convL_geps
#print axioms PAG.Part232.sum_mulLeft_dind
#print axioms PAG.Part232.shellAlg_eq_adjoin
#print axioms PAG.Part232.convL_geps_mem
#print axioms PAG.Part232.mulLeft_dind_mem
#print axioms PAG.Part232.map_leftHom_le
#print axioms PAG.Part232.map_rightHom_le
#print axioms PAG.Part232.map_crtConj_le
#print axioms PAG.Part232.map_crtConj_shellAlg
#print axioms PAG.Part232.mem_shellAlg_mul_iff
#print axioms PAG.Part232.finrank_map_crtConj
#print axioms PAG.Part232.finrank_sup_leftHom_rightHom
#print axioms PAG.Part232.tensLift
#print axioms PAG.Part232.tensLift_tmul
#print axioms PAG.Part232.range_tensLift
#print axioms PAG.Part232.finrank_tensor_shellAlg
#print axioms PAG.Part232.tensLift_injective
#print axioms PAG.Part232.shellAlgTensorEquiv
#print axioms PAG.Part232.crtConj_shellAlgTensorEquiv
#print axioms PAG.Part232.crtConj_shellAlgTensorEquiv_tmul
#print axioms PAG.Part232.shellAlgTensorEquiv_geps
#print axioms PAG.Part232.shellAlgTensorEquiv_dind
