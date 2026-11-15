/-
アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、法を上げた組み立て（Part 252 の残る問い）

問いの出所：著者の指示（2026-11-13 06:43「Part 252, Part 254 を解決してください」）を、Part 254 で Part 252 の
「残る問い」2 つを解く、と読んだ。
1. 法 N の境界ユニタリ全体（原始的でない指標を含む）を、J∘H_q（q ∣ N）の新しい部分の直和として書く文
   （Part 253 の着手前の候補 K2。盲検の問いテスト T2：既知の結果の短い帰結）。
2. 法を上げた組み立て（引き戻しと両立し、1 つの作用素にまとまること。着手前の盲検 T3 の注意：Ẑ に移るのは
   引き戻しと両立する作用素だけ）。

記号：G_N = (ℤ/N)ˣ、単数の上の関数、⟨f, g⟩ = Σ_u conj(f u)·g u（Part 253 の `ip`）、T = Part 253 の `TopL`。
χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）。
- `phaseA1 χ` = W(χ*)（Part 252 の `rootNum`）。A1 の位相を、原始的でない指標には誘導元から入れたもの。
- `UA1` = Σ_χ phaseA1(χ)·P_χ（P_χ f = (⟨χ, f⟩/φ(N))·χ）。法 N の A1 の境界ユニタリ U_N。
- `pullL hNM`（N ∣ M）：単数の上の関数の引き戻し f ↦ f ∘ (ℤ/M)ˣ → (ℤ/N)ˣ。

内容：
1. 位相：原始指標では phaseA1 χ = W(χ)（`phaseA1_of_isPrimitive`）、|phaseA1|² = 1（`normSq_phaseA1`）、
   法を上げても変わらない（`phaseA1_changeLevel`）、自明な指標では 1（`phaseA1_one`）。型の違う法の間の受け渡しは
   `rootNum_congr`（法が等しく、整数での値が等しい指標は同じ W を持つ）。
2. U_N：すべての指標で U_N χ = phaseA1(χ)·χ（`UA1_charU`）。U_N は ⟨·,·⟩ を保つ（`ip_UA1`、全体でユニタリ）。
   原始部分では U_N = T（`UA1_eq_TopL_of_mem_Vprim`）。
3. 指標ごとの式（残る問い 1）：すべての χ で U_N χ = π_{q→N}(T_q χ*)（`UA1_charU_eq_pull_TopL`。位相の定義の
   言い換え）。U_N はこの性質で一意に決まる（`UA1_unique`。基底の上の値による）。直和の部品は 10（1 つの定理にはしていない）。
4. 組み立て（残る問い 2）：法を上げる引き戻しと両立する：U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。
   T は両立しない（`TopL_not_compat`：法 1 → 2、`TopL_not_compat_prime`：法 1 → p）。
5. 原始的でない部分では U_N ≠ T：素数 p では自明な指標は V_imprim に入り、U_p(1) ≠ T_p(1)（`UA1_ne_TopL_prime`）。
   値（U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p）は `phaseA1_one`・`UA1_charU` と Part 253 の `TopL_charU`・
   `normSq_rootNum_one_prime` から。
   W(1 mod p) = −1/√p（`rootNum_one_prime`）。素数の法 p では、T の極分解のユニタリ因子のこの指標での固有値は
   −1 なので、U_p（固有値 1）はそのユニタリ因子でもない（極分解そのものは Lean にしていない）。法によっては一致する
   （法 1・6。独立照合 B の反例、数値 step277 の (20)）。
   U_N は V_prim・V_imprim を保ち（`UA1_mem_Vprim`・`UA1_mem_Vimprim`）、T と可換（`UA1_comp_TopL`）。
6. 実数性：τ(χ⁻¹) = χ(−1)·conj τ(χ)（`gaussSum_inv`）、W(χ⁻¹) = conj W(χ)（`rootNum_inv`）、
   phaseA1(χ⁻¹) = conj phaseA1(χ)（`phaseA1_inv`）、U_N は複素共役と可換（`UA1_star`：核は実数値、KUK = U）。
7. 両立する族の一意性：各法で原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけ
   （`UA1_family_unique`）。原始的でない指標の上の位相は、両立から決まる。
8. 極限：法の集合（正の整数を割り算の順で並べたもの、`Lvl`）の上の帰納系（引き戻し `pullSys`）と、その帰納極限
   `Lim`（Mathlib の `Module.DirectLimit`）。極限への写像は単射（`ofL_injective`）。U_N の族は極限の上の
   作用素 U_∞ を与え（`Uinf`、`Uinf_ofL`）、それは一意（`Uinf_unique`）で全単射（`Uinf_bijective`）。各法の原始部分の
   像は極限を張り（`span_ofL_Vprim`）、U_∞ はその上で T_q（`Uinf_ofL_of_mem_Vprim`）。U_∞ はこの性質でも一意
   （`Uinf_unique_TopL`）。
9. 極限の上の内積：引き戻しの和 φ(N)·Σ F(πu) = φ(M)·Σ F（`sum_units_unitsMap`）から、正規化した内積
   ⟨f, g⟩/φ(N) は引き戻しで変わらない（`ip_pullL`・`ipn_pullSys`）。代表によらない（`ipn_eq_of_ofL_eq`）ので
   極限の上の内積 `ipLim` が決まり、右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、
   正値（`ipLim_self_nonneg`）と定値性（`eq_zero_of_ipLim_self`：⟨z, z⟩ = 0 なら z = 0）。U_∞ はこれを保つ（`ipLim_Uinf`）。

10. 有限レベルの直和（独立照合 B の指摘で追加）：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q))
   に等しく（`condPart_eq_map`、q ∣ M）、導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、
   独立（`iSupIndep_condPart`）。添字は q ∈ ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない。合わせると
   ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になるが、1 つの定理にはしていない。U_M は各部分を保ち（`UA1_mem_condPart`）、
   原始部分の引き戻しの上で π∘T_q（`UA1_pullL_of_mem_Vprim`：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
   極限では、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`。前ヒルベルト空間での直交。Mathlib の内積の構造にはしていない。極限での独立性と、
   U_∞ が各部分を保つことは文にしていない）。

A1 との関係：U_N は A1 の位相を「定義として」入れた作用素で、3・4 は A1 の位相の選び方（誘導元から取る）の
帰結。7 は、原始的でない指標の位相が（原始部分の A1 と両立から）一通りに決まることを言う。A1 は公準のまま
（導いていない）。

Lean にしていないこと：U_N の明示の核（導手とメビウスの式。数値は step277 の (8)）。帰納極限 `Lim` と Ẑ^× の上の
局所定数関数の空間との同一視、`ipLim` による完備化（L²(Ẑ^×)）と、その上へのユニタリの延長（どちらも標準の事実）。
4 の `TopL_not_compat_prime`、5 の 2 文目以降、6〜9 は独立照合 A・C の後に、10 は独立照合 B の後に足した
（ノートの §7）。一般の N ∣ M（N < M）での T の非両立と、N ≥ 2 一般での U_N ≠ T（τ(1 mod N) = μ(N)）は Lean に
していない。10 について：q ∤ M の部分が 0 であること、直和を 1 つの文（DirectSum.IsInternal）にすること、極限での
独立性、U_∞ が各部分を保つことは Lean にしていない。
-/
import PAG257
import Mathlib.Algebra.Colimit.Module

namespace PAG.Part258

open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- 導手は 0 でない。 -/
instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

/-! ### 1. A1 の位相（誘導元の原始指標のルート数の式） -/

/-- A1 の位相 phaseA1(χ) = W(χ*)（χ* は χ を誘導する原始指標）。 -/
noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter

omit [NeZero N] in
/-- 法が等しく、整数での値が等しい 2 つの指標は、同じ W を持つ（型の違う法の間の受け渡し）。 -/
theorem rootNum_congr {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (h : d₁ = d₂)
    (χ₁ : DirichletCharacter ℂ d₁) (χ₂ : DirichletCharacter ℂ d₂)
    (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) : rootNum χ₁ = rootNum χ₂ := by
  subst h
  have : χ₁ = χ₂ := by
    refine MulChar.ext (fun u => ?_)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
    rw [← ha]
    exact hχ a
  rw [this]

/-- 原始指標では phaseA1 χ = W(χ)。 -/
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ := by
  have hc : χ.conductor = N := (isPrimitive_def χ).mp hχ
  unfold phaseA1
  refine rootNum_congr hc _ _ (fun a => ?_)
  by_cases ha : IsCoprime a N
  · exact primitiveCharacter_apply_of_isCoprime χ ha
  · have ha' : ¬IsCoprime a χ.conductor := by rwa [hc]
    rw [(apply_eq_zero_iff χ.primitiveCharacter a).mpr ha', (apply_eq_zero_iff χ a).mpr ha]

/-- |phaseA1 χ|² = 1（χ* は原始的）。 -/
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1 :=
  normSq_rootNum (primitiveCharacter_isPrimitive χ)

/-- 法を上げても位相は変わらない：phaseA1(changeLevel χ) = phaseA1(χ)。 -/
theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ := by
  unfold phaseA1
  exact rootNum_congr (conductor_changeLevel χ hNM) _ _ (primitiveCharacter_changeLevel_apply hNM χ)

omit [NeZero N] in
/-- 法 1 の自明な指標の W は 1。 -/
theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1 := by
  subst hd
  have heven : (1 : DirichletCharacter ℂ 1).Even := MulChar.one_apply isUnit_neg_one
  have hg : gaussSum (1 : DirichletCharacter ℂ 1) (stdAddChar (N := 1)) = 1 := by
    unfold gaussSum
    rw [Finset.univ_unique, Finset.sum_singleton,
      MulChar.one_apply (isUnit_of_subsingleton _), one_mul]
    have h0 : ∀ x : ZMod 1, (stdAddChar (N := 1)) x = 1 := fun x => by
      rw [Subsingleton.elim x 0, AddChar.map_zero_eq_one]
    exact h0 _
  rw [rootNum_eq, parFac_of_even heven, hg]
  simp

/-- 自明な指標の位相は 1。 -/
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1 := by
  unfold phaseA1
  rw [primitiveCharacter_one]
  exact rootNum_one_of_eq_one (conductor_one (R := ℂ) (n := N))

/-! ### 2. 法 N の境界ユニタリ U_N -/

/-- 内積の右側の加法性。 -/
theorem ip_add_right (f g h : (ZMod N)ˣ → ℂ) : ip f (g + h) = ip f g + ip f h := by
  unfold ip
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun u _ => by rw [Pi.add_apply, mul_add])

/-- 内積の右側のスカラー倍。 -/
theorem ip_smul_right (f g : (ZMod N)ˣ → ℂ) (c : ℂ) : ip f (c • g) = c * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)

/-- 法 N の A1 の境界ユニタリ U_N = Σ_χ phaseA1(χ)·P_χ。 -/
noncomputable def UA1 : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := ∑ χ : DirichletCharacter ℂ N,
    (phaseA1 χ * ip (charU χ) f / (Nat.totient N : ℂ)) • charU χ
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_add_right, mul_add, add_div, add_smul]
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [ip_smul_right, smul_smul]
    congr 1
    ring

/-- すべての指標で U_N χ = phaseA1(χ)·χ。 -/
theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ := by
  classical
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  show ∑ ψ : DirichletCharacter ℂ N,
    (phaseA1 ψ * ip (charU ψ) (charU χ) / (Nat.totient N : ℂ)) • charU ψ = phaseA1 χ • charU χ
  rw [Finset.sum_eq_single χ]
  · rw [ip_charU]
    simp only [↓reduceIte]
    congr 1
    field_simp
  · intro ψ _ hψ
    rw [ip_charU]
    simp only [hψ, ↓reduceIte, mul_zero, zero_div, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ χ) h

/-- U_N は ⟨·,·⟩ を保つ（単数の上の関数の空間全体でユニタリ）。 -/
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g := by
  classical
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  have hg : g ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  simp only [map_sum, _root_.map_smul, UA1_charU, smul_smul]
  rw [ip_sum_sum, ip_sum_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ip_charU]
  by_cases h : i = j
  · subst h
    simp only [↓reduceIte]
    have hp : (starRingEnd ℂ) (phaseA1 i) * phaseA1 i = 1 := by
      rw [mul_comm, Complex.mul_conj, normSq_phaseA1, Complex.ofReal_one]
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) (a i) * b i * (Nat.totient N : ℂ)) * hp
  · simp [h]

/-- 原始部分では U_N = T（Part 253 の `TopL_eq_of_A1`）。 -/
theorem UA1_eq_TopL_of_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f = TopL f :=
  TopL_eq_of_A1 UA1 (fun χ hχ => by rw [UA1_charU, phaseA1_of_isPrimitive hχ]) hf

/-! ### 3. 指標ごとの式（Part 252 の残る問い 1。直和そのものは §8） -/

/-- 単数の上の関数の引き戻し π_{N→M}（N ∣ M）。 -/
noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero N] in
/-- 指標の引き戻しは、法を上げた指標。 -/
theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ) := by
  funext u
  show χ ((ZMod.unitsMap hNM u : (ZMod N)ˣ) : ZMod N) = (changeLevel hNM χ) (u : ZMod M)
  rw [changeLevel_eq_cast_of_dvd χ hNM u, ZMod.unitsMap_val]

/-- **指標ごとの式**（直和の文の指標ごとの形。直和の部品は冒頭の説明の 10）：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（q = cond χ、χ* は誘導元の原始指標）。 -/
theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
    UA1 (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter)) := by
  rw [UA1_charU, TopL_charU, _root_.map_smul, pullL_charU, changeLevel_primitiveCharacter]
  rfl

/-- U_N は指標ごとの式で一意に決まる（基底の上の値による）：すべての指標で U χ = π_{q→N}(T_q χ*) となる線形写像 U は U_N。 -/
theorem UA1_unique (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N,
      U (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))) :
    U = UA1 :=
  LinearMap.ext_on_range span_charU_eq_top (fun χ => by rw [hU, UA1_charU_eq_pull_TopL])

/-! ### 4. 法を上げた組み立て（Part 252 の残る問い 2） -/

/-- 引き戻しとの両立：U_M ∘ π = π ∘ U_N。 -/
theorem UA1_comp_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℂ) :
    UA1 (pullL hNM f) = pullL hNM (UA1 f) := by
  have h : (UA1 (N := M)).comp (pullL hNM) = (pullL hNM).comp (UA1 (N := N)) := by
    refine LinearMap.ext_on_range (span_charU_eq_top (N := N)) (fun χ => ?_)
    simp only [LinearMap.comp_apply]
    rw [pullL_charU, UA1_charU, UA1_charU, _root_.map_smul, pullL_charU, phaseA1_changeLevel]
  exact LinearMap.congr_fun h f

/-- T は引き戻しと両立しない（法 1 → 2 の自明な指標：W(1 mod 2) の |·|² は 1/2、W(1 mod 1) = 1）。 -/
theorem TopL_not_compat :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd 2) f) ≠ pullL (one_dvd 2) (TopL f) := by
  refine ⟨charU (1 : DirichletCharacter ℂ 1), ?_⟩
  rw [pullL_charU, changeLevel_one, TopL_charU, TopL_charU, _root_.map_smul, pullL_charU,
    changeLevel_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [removal_counterexample_normSq, normSq_rootNum isPrimitive_one_level_one] at h2
  norm_num at h2

/-! ### 5. 原始的でない部分では U_N ≠ T -/

/-- 素数 p では、自明な指標は V_imprim に入り、U(1) = 1 だが T(1) = W(1)·1（|W(1)|² = 1/p）なので U ≠ T。 -/
theorem UA1_ne_TopL_prime (p : ℕ) [hp : Fact p.Prime] :
    charU (1 : DirichletCharacter ℂ p) ∈ Vimprim p ∧
      UA1 (charU (1 : DirichletCharacter ℂ p)) ≠ TopL (charU (1 : DirichletCharacter ℂ p)) := by
  refine ⟨charU_one_mem_Vimprim hp.out.two_le, ?_⟩
  rw [UA1_charU, TopL_charU, phaseA1_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [Complex.normSq_one, normSq_rootNum_one_prime] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp at h2
  linarith

/-! ### 5b. 独立照合 A の指摘で追加：不変性・可換性・T の位相・両立の族の一意性 -/

/-- V_prim は U_N で不変。 -/
theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N := by
  have hle : Vprim N ≤ (Vprim N).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ Vprim N
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

/-- V_imprim は U_N で不変。 -/
theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N := by
  have hle : Vimprim N ≤ (Vimprim N).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ Vimprim N
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

/-- U_N と T は可換（どちらも指標で対角）。 -/
theorem UA1_comp_TopL (f : (ZMod N)ˣ → ℂ) : UA1 (TopL f) = TopL (UA1 f) := by
  have h : (UA1 (N := N)).comp TopL = TopL.comp UA1 := by
    refine LinearMap.ext_on_range (span_charU_eq_top (N := N)) (fun χ => ?_)
    simp only [LinearMap.comp_apply]
    rw [TopL_charU, _root_.map_smul, UA1_charU, _root_.map_smul, TopL_charU, smul_smul,
      smul_smul, mul_comm]
  exact LinearMap.congr_fun h f

/-- 素数 p の自明な指標の W は −1/√p（実数で負）。法 p の T の極分解のユニタリ因子なら、この指標での固有値は −1
（U_p の固有値は 1）。極分解そのものは Lean にしていない。 -/
theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
  have heven : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_neg_one
  rw [rootNum_eq, parFac_of_even heven, gaussSum_one_prime, one_mul]
  push_cast
  ring

/-- すべての素数 p で、T は法 1 → p の引き戻しと両立しない（法 1 → 2 の `TopL_not_compat` の一般化）。 -/
theorem TopL_not_compat_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd p) f) ≠ pullL (one_dvd p) (TopL f) := by
  refine ⟨charU (1 : DirichletCharacter ℂ 1), ?_⟩
  rw [pullL_charU, changeLevel_one, TopL_charU, TopL_charU, _root_.map_smul, pullL_charU,
    changeLevel_one]
  intro h
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul, charU, Units.val_one, map_one, mul_one] at h1
  have h2 := congrArg Complex.normSq h1
  rw [normSq_rootNum_one_prime, normSq_rootNum isPrimitive_one_level_one] at h2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp at h2
  linarith

/-! ### 5c. 実数性（核は実数値：複素共役と可換） -/

/-- τ(χ⁻¹) = χ(−1)·conj τ(χ)。 -/
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar) := by
  have h1 : (starRingEnd ℂ) (gaussSum χ stdAddChar) = gaussSum χ⁻¹ (stdAddChar (N := N))⁻¹ := by
    rw [starRingEnd_apply, star_gaussSum_eq]
  have h2 : gaussSum χ⁻¹ (stdAddChar (N := N))⁻¹ = χ (-1) * gaussSum χ⁻¹ (stdAddChar (N := N)) := by
    rw [AddChar.inv_mulShift]
    have := gaussSum_mulShift_eq χ⁻¹ (stdAddChar (N := N)) (-1)
    rw [Units.val_neg, Units.val_one, inv_inv] at this
    rw [this]
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [h1, h2, ← mul_assoc, hsq, one_mul]

/-- W(χ⁻¹) = conj W(χ)（すべての指標で）。 -/
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ) := by
  have hpar : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv']
    rcases χ.even_or_odd with h | h
    · rw [show χ (-1) = 1 from h, inv_one]
    · rw [show χ (-1) = -1 from h, inv_neg, inv_one]
  rw [rootNum_eq, rootNum_eq, gaussSum_inv]
  unfold parFac
  rw [hpar]
  rcases χ.even_or_odd with h | h
  · rw [show χ (-1) = 1 from h]
    simp only [map_div₀, map_add, map_sub, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_ofNat]
    ring
  · rw [show χ (-1) = -1 from h]
    simp only [map_div₀, map_add, map_sub, map_mul, map_one, map_neg, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    ring

/-- (χ⁻¹)* と (χ*)⁻¹ は整数での値が等しい（法はどちらも導手）。 -/
theorem primitiveCharacter_inv_apply (χ : DirichletCharacter ℂ N) (a : ℤ) :
    (χ⁻¹).primitiveCharacter a = (χ.primitiveCharacter)⁻¹ a := by
  by_cases ha : IsCoprime a χ.conductor
  · have key : changeLevel (dvd_of_eq (conductor_inv χ)) (χ⁻¹).primitiveCharacter =
        (χ.primitiveCharacter)⁻¹ := by
      apply changeLevel_injective χ.conductor_dvd_level
      rw [← changeLevel_trans, changeLevel_primitiveCharacter, map_inv,
        changeLevel_primitiveCharacter]
    have := congrArg (fun ψ : DirichletCharacter ℂ χ.conductor => ψ (a : ZMod χ.conductor)) key
    rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
  · have ha' : ¬IsCoprime a (χ⁻¹).conductor := by rwa [conductor_inv]
    rw [(apply_eq_zero_iff _ a).mpr ha', (apply_eq_zero_iff _ a).mpr ha]

/-- phaseA1(χ⁻¹) = conj phaseA1(χ)。 -/
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ) := by
  unfold phaseA1
  rw [rootNum_congr (conductor_inv χ) _ _ (primitiveCharacter_inv_apply χ), rootNum_inv]

/-- **実数性**：U_N は複素共役と可換（U_N の核は実数値。KUK = U）。 -/
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u) := by
  classical
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have hstar : (fun u => (starRingEnd ℂ) ((∑ χ, c χ • charU χ) u)) =
      ∑ χ, (starRingEnd ℂ) (c χ) • charU χ⁻¹ := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    congr 1
    show (starRingEnd ℂ) (χ (u : ZMod N)) = χ⁻¹ (u : ZMod N)
    rw [starRingEnd_apply, MulChar.star_apply']
  rw [hstar]
  simp only [map_sum, _root_.map_smul, UA1_charU, smul_smul]
  funext u
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl (fun χ _ => ?_)
  have hχ : (starRingEnd ℂ) (charU χ u) = charU χ⁻¹ u := by
    show (starRingEnd ℂ) (χ (u : ZMod N)) = χ⁻¹ (u : ZMod N)
    rw [starRingEnd_apply, MulChar.star_apply']
  rw [phaseA1_inv, hχ]


/-! ### 6. 極限（法を割り算の順で並べた帰納極限） -/

omit [NeZero N] in
/-- 引き戻しは単射（(ℤ/M)ˣ → (ℤ/N)ˣ は全射）。 -/
theorem pullL_injective {M : ℕ} [NeZero M] (hNM : N ∣ M) : Function.Injective (pullL hNM) := by
  intro f g h
  funext v
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective hNM v
  exact congrFun h u

/-- 引き戻しの和：φ(N)·Σ_{u ∈ (ℤ/M)ˣ} F(πu) = φ(M)·Σ_{v ∈ (ℤ/N)ˣ} F(v)。 -/
theorem sum_units_unitsMap {M : ℕ} [NeZero M] (hNM : N ∣ M) (F : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) =
      (Nat.totient M : ℂ) * ∑ v : (ZMod N)ˣ, F v := by
  classical
  set c := (Finset.univ.filter fun u : (ZMod M)ˣ => ZMod.unitsMap hNM u = 1).card with hc
  have hfib : ∀ v : (ZMod N)ˣ,
      (Finset.univ.filter fun u : (ZMod M)ˣ => ZMod.unitsMap hNM u = v).card = c := by
    intro v
    exact MonoidHom.card_fiber_eq_of_mem_range (ZMod.unitsMap hNM)
      (ZMod.unitsMap_surjective hNM v) (ZMod.unitsMap_surjective hNM 1)
  have hsum : ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) = (c : ℂ) * ∑ v : (ZMod N)ˣ, F v := by
    rw [← Finset.sum_fiberwise Finset.univ (fun u => ZMod.unitsMap hNM u)
      (fun u => F (ZMod.unitsMap hNM u)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
      Finset.sum_const, hfib, nsmul_eq_mul]
  have hcard : Nat.totient M = c * Nat.totient N := by
    rw [← ZMod.card_units_eq_totient M, ← ZMod.card_units_eq_totient N, ← Finset.card_univ,
      Finset.card_eq_sum_card_fiberwise (f := fun u => ZMod.unitsMap hNM u) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun v _ => hfib v), Finset.sum_const, smul_eq_mul, Finset.card_univ,
      mul_comm]
  rw [hsum, hcard]
  push_cast
  ring

/-- 正規化した内積の両立：φ(N)·⟨πf, πg⟩ = φ(M)·⟨f, g⟩。 -/
theorem ip_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f g : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ip (pullL hNM f) (pullL hNM g) = (Nat.totient M : ℂ) * ip f g :=
  sum_units_unitsMap hNM (fun v => (starRingEnd ℂ) (f v) * g v)

/-- U_N は全単射（ip を保ち、⟨f, f⟩ = 0 なら f = 0、有限次元）。 -/
theorem UA1_bijective : Function.Bijective (UA1 (N := N)) := by
  have hinj : Function.Injective (UA1 (N := N)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply eq_zero_of_ip_self
    rw [← ip_UA1, hf]
    simp [ip]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- 法の集合：正の整数を、割り算の順で並べたもの。 -/
structure Lvl where
  /-- 法 -/
  val : ℕ
  pos : 0 < val
deriving DecidableEq

instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩

instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

/-- 法 a の単数の上の関数の空間。 -/
abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

/-- 系の写像：a ∣ b なら引き戻し π_{a→b}。 -/
noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

/-- **両立する族の一意性**（独立照合 A の指摘で追加）：各法で原始部分の上では T と一致し、引き戻しと両立する
作用素の族は U_N だけ。原始的でない指標の上の位相は、両立から決まる（仮定に A1 の位相は原始部分にしか入らない）。 -/
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1 := by
  refine LinearMap.ext_on_range (span_charU_eq_top (N := a.val)) (fun χ => ?_)
  let q : Lvl := ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩
  have hq : q ≤ a := χ.conductor_dvd_level
  have h1 : charU χ = pullSys q a hq (charU χ.primitiveCharacter) := by
    show charU χ = pullL χ.conductor_dvd_level (charU χ.primitiveCharacter)
    rw [pullL_charU, changeLevel_primitiveCharacter]
  have hprim : charU χ.primitiveCharacter ∈ Vprim q.val :=
    Submodule.subset_span ⟨⟨χ.primitiveCharacter, primitiveCharacter_isPrimitive χ⟩, rfl⟩
  rw [UA1_charU_eq_pull_TopL, h1, hc q a hq, hT q _ hprim]
  rfl

/-- 帰納極限 lim_N (単数の上の関数)。 -/
abbrev Lim : Type := Module.DirectLimit Gsp pullSys

/-- 法 a の成分から極限への写像。 -/
noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

/-- 極限への写像は単射。 -/
theorem ofL_injective (a : Lvl) : Function.Injective (ofL a) := by
  intro f g h
  obtain ⟨b, hab, hb⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  exact pullL_injective hab hb

/-- 極限の作用素 U_∞：各法の U_N が引き戻しと両立することから。 -/
noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

/-- U_∞ は各法で U_N。 -/
theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f) :=
  Module.DirectLimit.map_apply_of _ _ _

/-- U_∞ は各法で U_N となる線形写像として一意。 -/
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf :=
  Module.DirectLimit.hom_ext (fun a => LinearMap.ext (fun f => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hV, Uinf_ofL]))

/-- U_∞ は全単射。 -/
theorem Uinf_bijective : Function.Bijective Uinf := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
    rw [Uinf_ofL] at hz
    have h1 : UA1 f = 0 := ofL_injective a (by rw [hz, map_zero])
    have h2 : f = 0 := UA1_bijective.1 (by rw [h1, map_zero])
    rw [h2, map_zero]
  · intro z
    obtain ⟨a, g, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨f, rfl⟩ := UA1_bijective.2 g
    exact ⟨ofL a f, Uinf_ofL a f⟩

/-- 原始部分の像の上では U_∞ = T_q。 -/
theorem Uinf_ofL_of_mem_Vprim (q : Lvl) {f : Gsp q} (hf : f ∈ Vprim q.val) :
    Uinf (ofL q f) = ofL q (TopL f) := by
  rw [Uinf_ofL, UA1_eq_TopL_of_mem_Vprim hf]

/-- 導手の法の成分：法 a の指標 χ の像は、導手 q の成分の χ* の像。 -/
theorem ofL_charU (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    ofL a (charU χ) =
      ofL ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩ (charU χ.primitiveCharacter) := by
  have h : charU χ = pullL χ.conductor_dvd_level (charU χ.primitiveCharacter) := by
    rw [pullL_charU, changeLevel_primitiveCharacter]
  rw [h]
  exact Module.DirectLimit.of_f (G := Gsp) (f := pullSys)
    (i := ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩) (j := a)
    (hij := χ.conductor_dvd_level) (x := charU χ.primitiveCharacter)

/-- 各法の原始部分の像は極限を張る。 -/
theorem span_ofL_Vprim : Submodule.span ℂ (⋃ q : Lvl, ofL q '' (Vprim q.val : Set (Gsp q))) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr (fun z => ?_)
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  have hf : f ∈ Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ a.val => charU χ) := by
    rw [span_charU_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  rw [map_sum]
  refine Submodule.sum_mem _ (fun χ _ => ?_)
  rw [_root_.map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [ofL_charU]
  refine Set.mem_iUnion.mpr ⟨⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩,
    charU χ.primitiveCharacter, ?_, rfl⟩
  exact Submodule.subset_span ⟨⟨χ.primitiveCharacter, primitiveCharacter_isPrimitive χ⟩, rfl⟩

/-- U_∞ は「各導手 q の原始部分の像の上で T_q」となる線形写像として一意。 -/
theorem Uinf_unique_TopL (V : Lim →ₗ[ℂ] Lim)
    (hV : ∀ q (f : Gsp q), f ∈ Vprim q.val → V (ofL q f) = ofL q (TopL f)) : V = Uinf := by
  refine LinearMap.ext_on span_ofL_Vprim (fun z hz => ?_)
  simp only [Set.mem_iUnion, Set.mem_image, SetLike.mem_coe] at hz
  obtain ⟨q, f, hf, rfl⟩ := hz
  rw [hV q f hf, Uinf_ofL_of_mem_Vprim q hf]

/-! ### 7. 極限の上の内積（法ごとに 1/φ(N) で正規化した内積をまとめたもの） -/

/-- 法 a の正規化した内積 ⟨f, g⟩/φ(a)。 -/
noncomputable def ipn {a : Lvl} (f g : Gsp a) : ℂ := ip f g / (Nat.totient a.val : ℂ)

theorem totient_ne_zero' (a : Lvl) : (Nat.totient a.val : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.totient_pos.mpr a.pos).ne'

/-- 正規化した内積は引き戻しで変わらない。 -/
theorem ipn_pullSys {a b : Lvl} (h : a ≤ b) (f g : Gsp a) :
    ipn (pullSys a b h f) (pullSys a b h g) = ipn f g := by
  unfold ipn
  have := ip_pullL (N := a.val) (M := b.val) h f g
  have ha := totient_ne_zero' a
  have hb := totient_ne_zero' b
  rw [div_eq_div_iff hb ha]
  calc ip (pullSys a b h f) (pullSys a b h g) * (Nat.totient a.val : ℂ)
      = (Nat.totient a.val : ℂ) * ip (pullL (N := a.val) (M := b.val) h f)
          (pullL (N := a.val) (M := b.val) h g) := by rw [mul_comm]; rfl
    _ = ip f g * (Nat.totient b.val : ℂ) := by rw [this, mul_comm]

/-- 代表の取り方によらない：極限で同じ元を表す組では、正規化した内積は等しい。 -/
theorem ipn_eq_of_ofL_eq {a b : Lvl} {f g : Gsp a} {f' g' : Gsp b}
    (hf : ofL a f = ofL b f') (hg : ofL a g = ofL b g') : ipn f g = ipn f' g' := by
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  have e1 : pullSys a c hac f = pullSys b c hbc f' := by
    apply ofL_injective c
    rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f]
    exact hf
  have e2 : pullSys a c hac g = pullSys b c hbc g' := by
    apply ofL_injective c
    rw [Module.DirectLimit.of_f, Module.DirectLimit.of_f]
    exact hg
  rw [← ipn_pullSys hac, e1, e2, ipn_pullSys]

/-- 極限の上の内積：共通の法の代表で ⟨f, g⟩/φ(a)。 -/
noncomputable def ipLim (z w : Lim) : ℂ :=
  ipn (Module.DirectLimit.exists_of₂ z w).choose_spec.choose
    (Module.DirectLimit.exists_of₂ z w).choose_spec.choose_spec.choose

theorem ipLim_ofL (a : Lvl) (f g : Gsp a) : ipLim (ofL a f) (ofL a g) = ipn f g := by
  unfold ipLim
  set h := Module.DirectLimit.exists_of₂ (ofL a f) (ofL a g)
  exact ipn_eq_of_ofL_eq h.choose_spec.choose_spec.choose_spec.1
    h.choose_spec.choose_spec.choose_spec.2

/-- U_∞ は極限の内積を保つ。 -/
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [Uinf_ofL, Uinf_ofL, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_UA1]

/-- 極限の内積の右側の加法性。 -/
theorem ipLim_add_right (z w w' : Lim) : ipLim z (w + w') = ipLim z w + ipLim z w' := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  obtain ⟨b, f', g', hf', rfl⟩ := Module.DirectLimit.exists_of₂ (ofL a f) w'
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  rw [← hf']
  rw [← Module.DirectLimit.of_f (hij := hbc) (x := f'), ← Module.DirectLimit.of_f (hij := hbc) (x := g'),
    ← Module.DirectLimit.of_f (hij := hac) (x := g), ← map_add, ipLim_ofL, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_add_right, add_div]

/-- 極限の内積の右側のスカラー倍。 -/
theorem ipLim_smul_right (z w : Lim) (r : ℂ) : ipLim z (r • w) = r * ipLim z w := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [← _root_.map_smul, ipLim_ofL, ipLim_ofL]
  unfold ipn
  rw [ip_smul_right, mul_div_assoc]

/-- 極限の内積のエルミート性：⟨w, z⟩ = conj ⟨z, w⟩。 -/
theorem ipLim_conj (z w : Lim) : ipLim w z = (starRingEnd ℂ) (ipLim z w) := by
  obtain ⟨a, f, g, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
  rw [ipLim_ofL, ipLim_ofL]
  unfold ipn ip
  rw [map_div₀, map_natCast, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- 極限の内積の定値性：⟨z, z⟩ = 0 なら z = 0（正値は `ipLim_self_nonneg`）。 -/
theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0 := by
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  rw [ipLim_ofL] at h
  unfold ipn at h
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · rw [eq_zero_of_ip_self f h, map_zero]
  · exact absurd h (totient_ne_zero' a)

/-- 極限の内積で ⟨z, z⟩ は 0 以上の実数（`eq_zero_of_ipLim_self` と合わせて正定値）。 -/
theorem ipLim_self_nonneg (z : Lim) : ∃ r : ℝ, 0 ≤ r ∧ ipLim z z = r := by
  obtain ⟨a, f, rfl⟩ := Module.DirectLimit.exists_of z
  refine ⟨(∑ u, Complex.normSq (f u)) / (Nat.totient a.val : ℝ), ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun u _ => Complex.normSq_nonneg _)) (Nat.cast_nonneg _)
  · rw [ipLim_ofL]
    unfold ipn ip
    push_cast
    congr 1
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [mul_comm, Complex.mul_conj]

/-! ### 8. 有限レベルの直和（独立照合 B の指摘で追加。冒頭の内容の 10） -/

/-- 新しい部分の上の U_M：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)（左辺の U は法 M、右辺の T は法 q）。 -/
theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
    (hg : g ∈ Vprim N) : UA1 (pullL hNM g) = pullL hNM (TopL g) := by
  rw [UA1_comp_pullL, UA1_eq_TopL_of_mem_Vprim hg]

/-- 導手が q の指標が張る部分（法 N）。 -/
noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)

/-- 導手が q の指標が張る部分は π_{q→M}(V_prim(q))（q ∣ M）。 -/
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM) := by
  have key : ∀ (ψ : DirichletCharacter ℂ M) (d : ℕ) [NeZero d] (hd : ψ.conductor = d)
      (hdM : d ∣ M), charU ψ ∈ (Vprim d).map (pullL hdM) := by
    intro ψ d _ hd hdM
    subst hd
    refine ⟨charU ψ.primitiveCharacter,
      Submodule.subset_span ⟨⟨ψ.primitiveCharacter, primitiveCharacter_isPrimitive ψ⟩, rfl⟩, ?_⟩
    rw [pullL_charU]
    exact congrArg charU (changeLevel_primitiveCharacter ψ)
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨ψ, rfl⟩
    exact key ψ.1 N ψ.2 hNM
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show pullL hNM (charU χ.1) ∈ condPart M N
    rw [pullL_charU]
    refine Submodule.subset_span ⟨⟨changeLevel hNM χ.1, ?_⟩, rfl⟩
    rw [conductor_changeLevel]
    exact (isPrimitive_def χ.1).mp χ.2

/-- 導手の違う部分は直交する。 -/
theorem ip_condPart {q q' : ℕ} (hqq : q ≠ q') {f g : (ZMod N)ˣ → ℂ}
    (hf : f ∈ condPart N q) (hg : g ∈ condPart N q') : ip f g = 0 := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  rw [ip_sum_sum]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  have hne : i.1 ≠ j.1 := fun h => hqq (i.2.symm.trans (h ▸ j.2))
  rw [ip_charU]
  simp [hne]

/-- 導手ごとの部分は全体を張る。 -/
theorem iSup_condPart : ⨆ q, condPart N q = ⊤ := by
  rw [eq_top_iff, ← span_charU_eq_top, Submodule.span_le]
  rintro _ ⟨χ, rfl⟩
  exact Submodule.mem_iSup_of_mem χ.conductor (Submodule.subset_span ⟨⟨χ, rfl⟩, rfl⟩)

/-- 内積の右側を線形写像として（補題）。 -/
noncomputable def ipR (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := ip f
  map_add' := ip_add_right f
  map_smul' c g := by rw [ip_smul_right, smul_eq_mul, RingHom.id_apply]

/-- 導手ごとの部分は独立（内部直和の独立性。添字は q ∈ ℕ 全体）。 -/
theorem iSupIndep_condPart : iSupIndep (condPart N) := by
  rw [iSupIndep_def]
  intro q
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ q), condPart N j) ≤ LinearMap.ker (ipR x) := by
    refine iSup₂_le (fun j hj => fun y hy => ?_)
    rw [LinearMap.mem_ker]
    exact ip_condPart (Ne.symm hj) hx hy
  have h0 : ip x x = 0 := LinearMap.mem_ker.mp (hle hx')
  exact eq_zero_of_ip_self x h0

/-- U_N は導手ごとの部分を保つ。 -/
theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q := by
  have hle : condPart N q ≤ (condPart N q).comap UA1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show UA1 (charU χ.1) ∈ condPart N q
    rw [UA1_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

/-- 極限で、導手の違う原始部分の像は直交する。 -/
theorem ipLim_ofL_Vprim {q q' : Lvl} (hqq : q.val ≠ q'.val) {f : Gsp q} {g : Gsp q'}
    (hf : f ∈ Vprim q.val) (hg : g ∈ Vprim q'.val) : ipLim (ofL q f) (ofL q' g) = 0 := by
  let c : Lvl := ⟨q.val * q'.val, Nat.mul_pos q.pos q'.pos⟩
  have hqc : q ≤ c := dvd_mul_right q.val q'.val
  have hq'c : q' ≤ c := dvd_mul_left q'.val q.val
  rw [← Module.DirectLimit.of_f (hij := hqc) (x := f), ← Module.DirectLimit.of_f (hij := hq'c) (x := g),
    ipLim_ofL]
  unfold ipn
  have h1 : pullSys q c hqc f ∈ condPart c.val q.val := by
    rw [condPart_eq_map (N := q.val) (M := c.val) hqc]
    exact ⟨f, hf, rfl⟩
  have h2 : pullSys q' c hq'c g ∈ condPart c.val q'.val := by
    rw [condPart_eq_map (N := q'.val) (M := c.val) hq'c]
    exact ⟨g, hg, rfl⟩
  rw [ip_condPart hqq h1 h2, zero_div]

end PAG.Part258

#print axioms PAG.Part258.rootNum_congr
#print axioms PAG.Part258.phaseA1_of_isPrimitive
#print axioms PAG.Part258.normSq_phaseA1
#print axioms PAG.Part258.phaseA1_changeLevel
#print axioms PAG.Part258.rootNum_one_of_eq_one
#print axioms PAG.Part258.phaseA1_one
#print axioms PAG.Part258.ip_add_right
#print axioms PAG.Part258.ip_smul_right
#print axioms PAG.Part258.UA1_charU
#print axioms PAG.Part258.ip_UA1
#print axioms PAG.Part258.UA1_eq_TopL_of_mem_Vprim
#print axioms PAG.Part258.pullL_charU
#print axioms PAG.Part258.UA1_charU_eq_pull_TopL
#print axioms PAG.Part258.UA1_unique
#print axioms PAG.Part258.UA1_comp_pullL
#print axioms PAG.Part258.TopL_not_compat
#print axioms PAG.Part258.UA1_ne_TopL_prime
#print axioms PAG.Part258.UA1_mem_Vprim
#print axioms PAG.Part258.UA1_mem_Vimprim
#print axioms PAG.Part258.UA1_comp_TopL
#print axioms PAG.Part258.rootNum_one_prime
#print axioms PAG.Part258.TopL_not_compat_prime
#print axioms PAG.Part258.gaussSum_inv
#print axioms PAG.Part258.rootNum_inv
#print axioms PAG.Part258.primitiveCharacter_inv_apply
#print axioms PAG.Part258.phaseA1_inv
#print axioms PAG.Part258.UA1_star
#print axioms PAG.Part258.pullL_injective
#print axioms PAG.Part258.sum_units_unitsMap
#print axioms PAG.Part258.ip_pullL
#print axioms PAG.Part258.UA1_bijective
#print axioms PAG.Part258.UA1_family_unique
#print axioms PAG.Part258.ofL_injective
#print axioms PAG.Part258.Uinf_ofL
#print axioms PAG.Part258.Uinf_unique
#print axioms PAG.Part258.Uinf_bijective
#print axioms PAG.Part258.Uinf_ofL_of_mem_Vprim
#print axioms PAG.Part258.ofL_charU
#print axioms PAG.Part258.span_ofL_Vprim
#print axioms PAG.Part258.Uinf_unique_TopL
#print axioms PAG.Part258.totient_ne_zero'
#print axioms PAG.Part258.ipn_pullSys
#print axioms PAG.Part258.ipn_eq_of_ofL_eq
#print axioms PAG.Part258.ipLim_ofL
#print axioms PAG.Part258.ipLim_Uinf
#print axioms PAG.Part258.ipLim_add_right
#print axioms PAG.Part258.ipLim_smul_right
#print axioms PAG.Part258.ipLim_conj
#print axioms PAG.Part258.eq_zero_of_ipLim_self
#print axioms PAG.Part258.ipLim_self_nonneg
#print axioms PAG.Part258.UA1_pullL_of_mem_Vprim
#print axioms PAG.Part258.condPart_eq_map
#print axioms PAG.Part258.ip_condPart
#print axioms PAG.Part258.iSup_condPart
#print axioms PAG.Part258.iSupIndep_condPart
#print axioms PAG.Part258.UA1_mem_condPart
#print axioms PAG.Part258.ipLim_ofL_Vprim
