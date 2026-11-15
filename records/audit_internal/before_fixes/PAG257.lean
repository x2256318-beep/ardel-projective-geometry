/-
アーデル射影幾何 — Part 253（PAG 2.0）：原始部分での貼り合わせ U の作用素としての文

問いの出所：本来の道「無限素点を含む大域対象」の有限レベルの部分。著者の決定（2026-11-12 17:14）で、
無限素点での「重なり」は切断した円筒の両端の「ねじれた貼り合わせ（U）」。著者が着手前の候補 K1 を選んだ
（2026-11-12 21:17「推薦で進めてください」）。

Part 252（PAG256）は、すべての指標 χ で単数の上の式 J∘H_N/√N χ = W(χ)χ を示した（`JH_eq_rootNum_mul_any`）。
ただし、部分空間の上の作用素としての文はなかった（Part 252 の独立照合 B の指摘）。このファイルでその文を書く。

記号：G_N = (ℤ/N)ˣ。単数の上の関数 g に (T g)(u) = (H_N g̃)(u⁻¹)/√N（g̃ は g を 0 で ℤ/N に延ばしたもの、
H_N は離散 Hartley 変換）。⟨f, g⟩ = Σ_u conj(f u)·g u。W(χ) = `rootNum χ`（原始指標ではルート数、|W| = 1）。
V_prim は原始指標が張る空間、V_imprim は原始的でない指標が張る空間。

内容：
1. T を線形写像として定める（`TopL`）。すべての指標で T χ = W(χ)χ（`TopL_charU`）。
2. 指標の直交性 ⟨χ, ψ⟩ = φ(N)·[χ = ψ]（`ip_charU`）と、内積の展開（`ip_smul_smul`、`ip_sum_sum`）。
3. V_prim は T で不変で、T(V_prim) = V_prim（`TopL_mem_Vprim`、`map_TopL_Vprim`）。
4. V_prim の上で T は等長：⟨T f, T g⟩ = ⟨f, g⟩（`ip_TopL_of_mem_Vprim`）。
5. 原始指標で U χ = W(χ)χ を満たす任意の線形写像 U は、V_prim の上で T に等しい（`TopL_eq_of_A1`）。
   公理 A1 は「原始指標の部分で U χ = W(χ)χ」と課す位相の規約なので、5 は A1 の読み替えである
   （除去テスト：A1 を外すと U の位相は自由に戻り、5 の結論は消える）。T の固有値がルート数であること（1）は A1 によらない。
6. V_imprim も T で不変で（`TopL_mem_Vimprim`）、V_prim と直交する（`ip_Vprim_Vimprim`）。
7. 指標の全体は単数の上の関数をすべて張る：V_prim ⊔ V_imprim = ⊤（`span_charU_eq_top`、`Vprim_sup_Vimprim`）。
   V_prim ⊓ V_imprim = ⊥ で、空間は V_prim と V_imprim の直交する直和（`Vprim_inf_Vimprim`、`isCompl_Vprim_Vimprim`）。
8. 証人：法 3 で V_prim ≠ ⊥（`Vprim_ne_bot_three`）。法 2 で V_imprim の上の T は等長でない（`not_isometry_Vimprim_two`）。
   法 4 で T は自明な指標を 0 に送る（`TopL_charU_one_four`）。

9. （独立照合 A・C の指摘を受けて追加）V_prim の上のユニタリを 1 つの文に（`unitary_Vprim`）。すべての素数 p で
   V_imprim の上の T は等長でない（`not_isometry_Vimprim_prime`。自明な指標のガウス和は −1：`gaussSum_one_prime`、
   |W|² = 1/p：`normSq_rootNum_one_prime`）。素数 p ≥ 3 で V_prim ≠ 0（`Vprim_ne_bot_prime`）。したがって素数 p ≥ 3 では、
   同じ法で V_prim の上はユニタリ、V_imprim の上は等長でない。

10. （独立照合 B の指摘を受けて追加）法 N ≥ 2 で自明な指標は原始的でない（`not_isPrimitive_one_of_two_le`）、
   したがって V_imprim に入る（`charU_one_mem_Vimprim`。8c の「V_imprim の上で単射でない」の根拠）。法 2 の指標は
   自明な指標だけで（`eq_one_of_two`）、V_prim = 0（`Vprim_two`）。

注意（独立照合 B）：N ≡ 2 (mod 4) では原始指標がなく V_prim = 0 で、3〜5 と 9a の V_prim についての文は自明に成り立つ。
5 の仮定（A1 の位相）を外したときに結論が消えるのは V_prim ≠ 0 の法だけ（数値の除去テストは N ≢ 2 (mod 4) の 75 個の法）。
4・9a の「ユニタリ」は、このファイルの内積 `ip` に関するもので、Mathlib の内積空間にはつないでいない。
`eq_zero_of_ip_self` は非退化（⟨f, f⟩ = 0 ⇒ f = 0）だけを述べ、⟨f, f⟩ ≥ 0 の文はない。

注意（独立照合 A）：8a の法 3 では、原始指標は奇の 2 次指標 1 つだけで W = 1、T↾V_prim は恒等写像。T↾V_prim が
恒等でない最小の法は 5（4 次の指標で W ≈ 0.85 + 0.53i）で、これは数値だけ（step276 の (12)）。
V_imprim の上のノルムの評価 ‖T↾V_imprim‖ ≤ 1/√2 は、原始的でない指標のガウス和の式（Montgomery–Vaughan
Thm 9.10。Mathlib にない）が要るので、このファイルでは扱わない（数値は step276 の (10)）。
「長さが保たれるのはちょうど V_prim の上」（Sz.-Nagy–Foiaș の標準分解のユニタリ部分）も同じ理由で数値だけ（(14)）。
-/
import PAG256

namespace PAG.Part257

open ZMod Complex Finset PAG.Part256

variable {N : ℕ} [NeZero N]

/-! ### 1. 単数の上の作用素 T -/

open Classical in
/-- 単数の上の関数を 0 で ℤ/N に延ばす線形写像。 -/
noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]

open Classical in
theorem extL_apply (g : (ZMod N)ˣ → ℂ) (x : ZMod N) :
    extL g x = if h : IsUnit x then g h.unit else 0 := rfl

/-- J∘H_N/√N（Part 252 の `JH`）を線形写像として。 -/
noncomputable def JHL : (ZMod N → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := JH f
  map_add' f g := by
    funext u
    show JH (f + g) u = JH f u + JH g u
    unfold JH hartley
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.add_apply, add_mul])
  map_smul' c f := by
    funext u
    show JH (c • f) u = c * JH f u
    unfold JH hartley
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc])

/-- 単数の上の作用素 T = (J∘H_N/√N)∘(0 での延長)。 -/
noncomputable def TopL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) := JHL.comp extL

/-- 指標を単数の上の関数とみたもの。 -/
def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

/-- 単数の上の指標を 0 で延ばすと、もとの指標（単数でないところで 0）。 -/
theorem extL_charU (χ : DirichletCharacter ℂ N) : extL (charU χ) = (χ : ZMod N → ℂ) := by
  funext x
  rw [extL_apply]
  by_cases h : IsUnit x
  · simp only [h, ↓reduceDIte, charU, IsUnit.unit_spec]
  · simp only [h, ↓reduceDIte, MulChar.map_nonunit χ h]

/-- **1.** すべての指標で T χ = W(χ)χ（Part 252 の `JH_eq_rootNum_mul_any` の作用素の形）。 -/
theorem TopL_charU (χ : DirichletCharacter ℂ N) : TopL (charU χ) = rootNum χ • charU χ := by
  funext u
  show JH (extL (charU χ)) u = rootNum χ * charU χ u
  rw [extL_charU]
  exact JH_eq_rootNum_mul_any χ u

/-! ### 2. 単数の上の内積と指標の直交性 -/

/-- 単数の上の内積 ⟨f, g⟩ = Σ_u conj(f u)·g u。 -/
noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

/-- ⟨a f, b g⟩ = conj(a)·b·⟨f, g⟩。 -/
theorem ip_smul_smul (a b : ℂ) (f g : (ZMod N)ˣ → ℂ) :
    ip (a • f) (b • g) = (starRingEnd ℂ) a * b * ip f g := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  ring

/-- 内積の展開：⟨Σ a_i v_i, Σ b_j w_j⟩ = Σ_i Σ_j conj(a_i)·b_j·⟨v_i, w_j⟩。 -/
theorem ip_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → ℂ) (v : ι → (ZMod N)ˣ → ℂ)
    (b : κ → ℂ) (w : κ → (ZMod N)ˣ → ℂ) :
    ip (N := N) (∑ i, a i • v i) (∑ j, b j • w j) =
      ∑ i, ∑ j, (starRingEnd ℂ) (a i) * b j * ip (v i) (w j) := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  -- 左辺の和の順は (u, j, i)、右辺は (i, j, u)
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun u _ => ?_)))
  ring

open Classical in
/-- **2.** 指標の直交性：⟨χ, ψ⟩ = φ(N)·[χ = ψ]（Part 218 の `sum_units_char` から）。 -/
theorem ip_charU (χ ψ : DirichletCharacter ℂ N) :
    ip (charU χ) (charU ψ) = if χ = ψ then (Nat.totient N : ℂ) else 0 := by
  have h : ∀ u : (ZMod N)ˣ, (starRingEnd ℂ) (charU χ u) * charU ψ u = (χ⁻¹ * ψ) (u : ZMod N) := by
    intro u
    rw [MulChar.mul_apply, ← MulChar.star_apply']
    rfl
  rw [show ip (charU χ) (charU ψ) = ∑ u : (ZMod N)ˣ, (χ⁻¹ * ψ) (u : ZMod N) from
    Finset.sum_congr rfl (fun u _ => h u), PAG.Part218.sum_units_char]
  by_cases hχψ : χ = ψ
  · subst hχψ
    simp
  · have hne : χ⁻¹ * ψ ≠ 1 := fun h' => hχψ (inv_mul_eq_one.mp h')
    simp [hχψ, hne]

/-! ### 3. 原始部分と原始的でない部分、不変性 -/

/-- 原始部分 V_prim：原始指標（を単数に制限したもの）が張る空間。 -/
noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)

/-- 原始的でない部分 V_imprim：原始的でない指標が張る空間。 -/
noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)

/-- **3a.** V_prim は T で不変。 -/
theorem TopL_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : TopL f ∈ Vprim N := by
  have hle : Vprim N ≤ (Vprim N).comap TopL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show TopL (charU χ.1) ∈ Vprim N
    rw [TopL_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

/-- **6a.** V_imprim は T で不変。 -/
theorem TopL_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : TopL f ∈ Vimprim N := by
  have hle : Vimprim N ≤ (Vimprim N).comap TopL := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    show TopL (charU χ.1) ∈ Vimprim N
    rw [TopL_charU]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩)
  exact hle hf

/-- 原始指標では W(χ) ≠ 0（|W| = 1 から）。 -/
theorem rootNum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : rootNum χ ≠ 0 := by
  intro h
  have h1 := normSq_rootNum hχ
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- **3b.** T(V_prim) = V_prim（V_prim の上で T は全射）。 -/
theorem map_TopL_Vprim : (Vprim N).map TopL = Vprim N := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro f hf
    exact TopL_mem_Vprim hf
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨χ, rfl⟩
    refine ⟨(rootNum χ.1)⁻¹ • charU χ.1, Submodule.smul_mem _ _ (Submodule.subset_span ⟨χ, rfl⟩), ?_⟩
    rw [_root_.map_smul, TopL_charU, smul_smul, inv_mul_cancel₀ (rootNum_ne_zero χ.2), one_smul]

/-! ### 4. V_prim の上の等長性 -/

/-- 原始指標どうしで ⟨T χ, T ψ⟩ = ⟨χ, ψ⟩。 -/
theorem ip_TopL_charU_prim {χ ψ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    ip (TopL (charU χ)) (TopL (charU ψ)) = ip (charU χ) (charU ψ) := by
  classical
  rw [TopL_charU, TopL_charU, ip_smul_smul, ip_charU]
  by_cases h : χ = ψ
  · subst h
    have hn : (starRingEnd ℂ) (rootNum χ) * rootNum χ = 1 := by
      rw [mul_comm, Complex.mul_conj, normSq_rootNum hχ, Complex.ofReal_one]
    rw [hn, one_mul]
  · simp [h]

/-- **4.** V_prim の上で T は等長：⟨T f, T g⟩ = ⟨f, g⟩（f, g ∈ V_prim）。T(V_prim) = V_prim（3b）と合わせて、
T は V_prim の上のユニタリ。 -/
theorem ip_TopL_of_mem_Vprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vprim N) :
    ip (TopL f) (TopL g) = ip f g := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  simp only [map_sum, _root_.map_smul]
  rw [ip_sum_sum, ip_sum_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [ip_TopL_charU_prim i.2]

/-! ### 5. A1 の位相との一致 -/

/-- **5.** 原始指標で U χ = W(χ)χ を満たす（A1 の位相を原始部分に課した）任意の線形写像 U は、V_prim の上で
T に等しい。A1 の読み替えで、A1 を外すと結論は消える。 -/
theorem TopL_eq_of_A1 (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive → U (charU χ) = rootNum χ • charU χ)
    {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : U f = TopL f := by
  refine LinearMap.eqOn_span ?_ hf
  rintro _ ⟨χ, rfl⟩
  rw [hU χ.1 χ.2, TopL_charU]

/-! ### 6. V_prim と V_imprim の直交 -/

/-- **6b.** ⟨V_prim, V_imprim⟩ = 0。 -/
theorem ip_Vprim_Vimprim {f g : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) (hg : g ∈ Vimprim N) :
    ip f g = 0 := by
  classical
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hg
  rw [ip_sum_sum]
  refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
  have hne : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
  rw [ip_charU]
  simp [hne]

/-! ### 7. 指標の全体は単数の上の関数をすべて張る -/

/-- 内積の右側の展開：⟨f, Σ b_j w_j⟩ = Σ_j b_j·⟨f, w_j⟩。 -/
theorem ip_sum_right {κ : Type*} [Fintype κ] (f : (ZMod N)ˣ → ℂ) (b : κ → ℂ)
    (w : κ → (ZMod N)ˣ → ℂ) : ip (N := N) f (∑ j, b j • w j) = ∑ j, b j * ip f (w j) := by
  unfold ip
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring

/-- 指標（を単数に制限したもの）は一次独立（直交性から）。 -/
theorem linearIndependent_charU :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ N => charU χ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg ψ
  have h := congrArg (ip (charU ψ)) hg
  rw [ip_sum_right] at h
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  simp only [ip_charU, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h
  have h0 : ip (charU ψ) 0 = 0 := by simp [ip]
  rw [h0] at h
  exact (mul_eq_zero.mp h).resolve_right hφ

/-- **7a.** 指標の全体は単数の上の関数の空間を張る（個数 φ(N) = 次元）。 -/
theorem span_charU_eq_top :
    Submodule.span ℂ (Set.range fun χ : DirichletCharacter ℂ N => charU χ) = ⊤ := by
  classical
  refine linearIndependent_charU.span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_fintype_fun_eq_card, ZMod.card_units_eq_totient, Fintype.card_eq_nat_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

/-- **7b.** V_prim ⊔ V_imprim = ⊤（6b と合わせて、単数の上の関数の空間は V_prim と V_imprim の直交和）。 -/
theorem Vprim_sup_Vimprim : Vprim N ⊔ Vimprim N = ⊤ := by
  rw [Vprim, Vimprim, ← Submodule.span_union, ← span_charU_eq_top]
  congr 1
  ext f
  constructor
  · rintro (⟨χ, rfl⟩ | ⟨χ, rfl⟩) <;> exact ⟨χ.1, rfl⟩
  · rintro ⟨χ, rfl⟩
    by_cases h : χ.IsPrimitive
    · exact Or.inl ⟨⟨χ, h⟩, rfl⟩
    · exact Or.inr ⟨⟨χ, h⟩, rfl⟩

/-- ⟨f, f⟩ = 0 なら f = 0（内積の正定値性）。 -/
theorem eq_zero_of_ip_self (f : (ZMod N)ˣ → ℂ) (h : ip f f = 0) : f = 0 := by
  have hsum : ip f f = ((∑ u, Complex.normSq (f u) : ℝ) : ℂ) := by
    unfold ip
    push_cast
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [mul_comm, Complex.mul_conj]
  rw [hsum] at h
  have h' : ∑ u, Complex.normSq (f u) = 0 := by exact_mod_cast h
  funext u
  have hu := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Complex.normSq_nonneg (f u))).mp h' u
    (Finset.mem_univ u)
  exact Complex.normSq_eq_zero.mp hu

/-- **7c.** V_prim ⊓ V_imprim = ⊥（6b の直交性と正定値性から）。 -/
theorem Vprim_inf_Vimprim : Vprim N ⊓ Vimprim N = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_inf] at hf
  rw [Submodule.mem_bot]
  exact eq_zero_of_ip_self f (ip_Vprim_Vimprim hf.1 hf.2)

/-- **7d.** 単数の上の関数の空間は V_prim と V_imprim の直和（6b により直交）。 -/
theorem isCompl_Vprim_Vimprim : IsCompl (Vprim N) (Vimprim N) :=
  isCompl_iff.mpr ⟨disjoint_iff.mpr Vprim_inf_Vimprim, codisjoint_iff.mpr Vprim_sup_Vimprim⟩

/-! ### 8. 証人（非空虚性と、原始的でない部分での破れ） -/

/-- **8a.** 非空虚性：法 3 で V_prim ≠ ⊥（法 3 の奇の原始指標）。 -/
theorem Vprim_ne_bot_three : Vprim 3 ≠ ⊥ := by
  obtain ⟨χ, hχ, -⟩ := exists_primitive_odd_three
  intro h
  have hmem : charU χ ∈ Vprim 3 := Submodule.subset_span ⟨⟨χ, hχ⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem 1
  simp [charU] at h1

/-- **8b.** 法 2 では、V_imprim の上で T は等長でない（自明な指標で |W|² = 1/2。Part 252 の
`removal_counterexample_normSq`）。 -/
theorem not_isometry_Vimprim_two : ∃ f ∈ Vimprim 2, ip (TopL f) (TopL f) ≠ ip f f := by
  classical
  refine ⟨charU (N := 2) 1,
    Submodule.subset_span ⟨⟨(1 : DirichletCharacter ℂ 2), removal_counterexample.1⟩, rfl⟩, ?_⟩
  rw [TopL_charU, ip_smul_smul, ip_charU]
  have hn : (starRingEnd ℂ) (rootNum (1 : DirichletCharacter ℂ 2)) *
      rootNum (1 : DirichletCharacter ℂ 2) = 1 / 2 := by
    rw [mul_comm, Complex.mul_conj, removal_counterexample_normSq]
    push_cast
    ring
  rw [hn]
  simp only [↓reduceIte]
  have h2 : (Nat.totient 2 : ℂ) = 1 := by
    rw [Nat.totient_prime Nat.prime_two]
    norm_num
  rw [h2]
  norm_num

/-- **8c.** 法 4 では、T は自明な指標を 0 に送る（τ = 0。Part 252 の `removal_counterexample_four`）。
自明な指標は 0 でないので、T は V_imprim の上で単射でもない。 -/
theorem TopL_charU_one_four :
    TopL (charU (1 : DirichletCharacter ℂ 4)) = 0 ∧ charU (1 : DirichletCharacter ℂ 4) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [TopL_charU, Complex.normSq_eq_zero.mp removal_counterexample_four.2.2.2.2, zero_smul]
  · intro h
    have h1 := congrFun h 1
    simp [charU] at h1

/-! ### 9. 独立照合の指摘を受けて追加（V_prim の上のユニタリを 1 つの文に、素数の法の証人） -/

/-- **9a.** V_prim の上で T はユニタリ：V_prim の自己線形同型 e で、値は T、内積を保つものがある
（`TopL_mem_Vprim`・`map_TopL_Vprim`・`ip_TopL_of_mem_Vprim`・`eq_zero_of_ip_self` を 1 つの文に）。 -/
theorem unitary_Vprim : ∃ e : Vprim N ≃ₗ[ℂ] Vprim N,
    (∀ f : Vprim N, ((e f : Vprim N) : (ZMod N)ˣ → ℂ) = TopL (f : (ZMod N)ˣ → ℂ)) ∧
    ∀ f g : Vprim N, ip ((e f : Vprim N) : (ZMod N)ˣ → ℂ) ((e g : Vprim N) : (ZMod N)ˣ → ℂ) =
      ip (f : (ZMod N)ˣ → ℂ) (g : (ZMod N)ˣ → ℂ) := by
  have hres : ∀ f ∈ Vprim N, TopL f ∈ Vprim N := fun f hf => TopL_mem_Vprim hf
  have hL : ∀ f : Vprim N, ((TopL.restrict hres f : Vprim N) : (ZMod N)ˣ → ℂ) =
      TopL (f : (ZMod N)ˣ → ℂ) := fun f => rfl
  have hinj : Function.Injective (TopL.restrict hres) := by
    intro f g hfg
    have hfg' := congrArg Subtype.val hfg
    rw [hL, hL] at hfg'
    have h0 : TopL ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ)) = 0 := by
      rw [map_sub, hfg', sub_self]
    have hmem : (f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ) ∈ Vprim N := Submodule.sub_mem _ f.2 g.2
    have hip : ip ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ))
        ((f : (ZMod N)ˣ → ℂ) - (g : (ZMod N)ˣ → ℂ)) = 0 := by
      rw [← ip_TopL_of_mem_Vprim hmem hmem, h0]
      simp [ip]
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_ip_self _ hip))
  have hsurj : Function.Surjective (TopL.restrict hres) := by
    intro g
    have hg : (g : (ZMod N)ˣ → ℂ) ∈ (Vprim N).map TopL := by
      rw [map_TopL_Vprim]
      exact g.2
    obtain ⟨f, hf, hfg⟩ := hg
    exact ⟨⟨f, hf⟩, Subtype.ext hfg⟩
  have hbij : Function.Bijective (TopL.restrict hres) := ⟨hinj, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (TopL.restrict hres) hbij, fun f => ?_, fun f g => ?_⟩
  · rw [LinearEquiv.ofBijective_apply, hL]
  · rw [LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hL, hL]
    exact ip_TopL_of_mem_Vprim f.2 g.2

/-- 素数の法の自明な指標のガウス和は −1。 -/
theorem gaussSum_one_prime (p : ℕ) [Fact p.Prime] :
    gaussSum (1 : DirichletCharacter ℂ p) (stdAddChar (N := p)) = -1 := by
  have hne : (stdAddChar (N := p)) ≠ 1 := by
    have h := (ZMod.isPrimitive_stdAddChar p) (one_ne_zero : (1 : ZMod p) ≠ 0)
    simpa [AddChar.mulShift_one] using h
  have hsum : ∑ x : ZMod p, (stdAddChar (N := p)) x = 0 := AddChar.sum_eq_zero_of_ne_one hne
  have h1 : ∀ x : ZMod p, (1 : DirichletCharacter ℂ p) x * stdAddChar x =
      stdAddChar x - (if x = 0 then 1 else 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [MulChar.map_nonunit _ not_isUnit_zero, zero_mul, AddChar.map_zero_eq_one]
      simp
    · rw [MulChar.one_apply (Ne.isUnit hx), one_mul]
      simp [hx]
  unfold gaussSum
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, hsum]
  simp

/-- 素数の法の自明な指標で |W|² = 1/p（原始的でない指標の |W| < 1 の例）。 -/
theorem normSq_rootNum_one_prime (p : ℕ) [hp : Fact p.Prime] :
    Complex.normSq (rootNum (1 : DirichletCharacter ℂ p)) = 1 / p := by
  have heven : (1 : DirichletCharacter ℂ p).Even := MulChar.one_apply isUnit_neg_one
  have hsq : Complex.normSq (Real.sqrt p : ℂ) = p := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg p)]
  rw [rootNum_eq, parFac_of_even heven, gaussSum_one_prime, one_mul, map_div₀, Complex.normSq_neg,
    Complex.normSq_one, hsq]

/-- 素数の法では自明な指標は原始的でない。 -/
theorem not_isPrimitive_one_prime (p : ℕ) [hp : Fact p.Prime] :
    ¬(1 : DirichletCharacter ℂ p).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
  exact fun h => hp.out.one_lt.ne h

/-- **9b.** すべての素数 p で、V_imprim の上の T は等長でない（自明な指標で |W|² = 1/p。法 2 の
`not_isometry_Vimprim_two` を一般の素数に）。 -/
theorem not_isometry_Vimprim_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f ∈ Vimprim p, ip (TopL f) (TopL f) ≠ ip f f := by
  classical
  refine ⟨charU (N := p) 1,
    Submodule.subset_span ⟨⟨(1 : DirichletCharacter ℂ p), not_isPrimitive_one_prime p⟩, rfl⟩, ?_⟩
  rw [TopL_charU, ip_smul_smul, ip_charU]
  have hn : (starRingEnd ℂ) (rootNum (1 : DirichletCharacter ℂ p)) *
      rootNum (1 : DirichletCharacter ℂ p) = 1 / (p : ℂ) := by
    rw [mul_comm, Complex.mul_conj, normSq_rootNum_one_prime]
    push_cast
    ring
  rw [hn]
  simp only [↓reduceIte]
  have hφ : (Nat.totient p : ℂ) ≠ 0 := by
    rw [Nat.totient_prime hp.out]
    exact_mod_cast (Nat.sub_pos_of_lt hp.out.one_lt).ne'
  have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast hp.out.one_lt.ne'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  intro h
  have h2 : (Nat.totient p : ℂ) * (1 / (p : ℂ) - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hφ h3
  · apply hp1
    field_simp at h3
    linear_combination -h3

/-- **9c.** 素数 p ≥ 3 では V_prim ≠ 0（自明でない指標は原始的）。9b と合わせて、同じ法で V_prim の上は
ユニタリ、V_imprim の上は等長でない。 -/
theorem Vprim_ne_bot_prime (p : ℕ) [hp : Fact p.Prime] (h3 : 3 ≤ p) : Vprim p ≠ ⊥ := by
  have : Fact (2 < p) := ⟨by omega⟩
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (ZMod.neg_one_ne_one (n := p))
  have hne : χ ≠ 1 := by
    rintro rfl
    exact hχ (MulChar.one_apply isUnit_neg_one)
  intro h
  have hmem : charU χ ∈ Vprim p :=
    Submodule.subset_span ⟨⟨χ, PAG.Part256.isPrimitive_of_prime_of_ne_one hne⟩, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  have h1 := congrFun hmem 1
  simp [charU] at h1

/-! ### 10. 独立照合 B の指摘を受けて追加（形式文のなかった主張を文にする） -/

/-- 法 N ≥ 2 では自明な指標は原始的でない（導手 1 ≠ N。素数の法の `not_isPrimitive_one_prime` の一般化）。 -/
theorem not_isPrimitive_one_of_two_le (hN : 2 ≤ N) : ¬(1 : DirichletCharacter ℂ N).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]
  omega

/-- 法 N ≥ 2 では、単数の上の自明な指標は V_imprim に入る（`TopL_charU_one_four` の「V_imprim の上で単射でない」の根拠）。 -/
theorem charU_one_mem_Vimprim (hN : 2 ≤ N) : charU (1 : DirichletCharacter ℂ N) ∈ Vimprim N :=
  Submodule.subset_span ⟨⟨1, not_isPrimitive_one_of_two_le hN⟩, rfl⟩

/-- 法 2 の指標は自明な指標だけ（(ℤ/2)ˣ は 1 元）。 -/
theorem eq_one_of_two (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  have hcard : Fintype.card (ZMod 2)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_two]
  refine MulChar.ext (fun u => ?_)
  rw [Fintype.card_le_one_iff.mp hcard u 1, Units.val_one, map_one, map_one]

/-- 法 2 では V_prim = 0（原始指標がない）。 -/
theorem Vprim_two : Vprim 2 = ⊥ := by
  rw [Vprim, Submodule.span_eq_bot]
  rintro _ ⟨⟨χ, hχ⟩, rfl⟩
  have h1 := eq_one_of_two χ
  subst h1
  exact absurd hχ (not_isPrimitive_one_prime 2)

end PAG.Part257

#print axioms PAG.Part257.extL_apply
#print axioms PAG.Part257.extL_charU
#print axioms PAG.Part257.TopL_charU
#print axioms PAG.Part257.ip_smul_smul
#print axioms PAG.Part257.ip_sum_sum
#print axioms PAG.Part257.ip_charU
#print axioms PAG.Part257.TopL_mem_Vprim
#print axioms PAG.Part257.TopL_mem_Vimprim
#print axioms PAG.Part257.rootNum_ne_zero
#print axioms PAG.Part257.map_TopL_Vprim
#print axioms PAG.Part257.ip_TopL_charU_prim
#print axioms PAG.Part257.ip_TopL_of_mem_Vprim
#print axioms PAG.Part257.TopL_eq_of_A1
#print axioms PAG.Part257.ip_Vprim_Vimprim
#print axioms PAG.Part257.ip_sum_right
#print axioms PAG.Part257.linearIndependent_charU
#print axioms PAG.Part257.span_charU_eq_top
#print axioms PAG.Part257.Vprim_sup_Vimprim
#print axioms PAG.Part257.eq_zero_of_ip_self
#print axioms PAG.Part257.Vprim_inf_Vimprim
#print axioms PAG.Part257.isCompl_Vprim_Vimprim
#print axioms PAG.Part257.Vprim_ne_bot_three
#print axioms PAG.Part257.not_isometry_Vimprim_two
#print axioms PAG.Part257.TopL_charU_one_four
#print axioms PAG.Part257.unitary_Vprim
#print axioms PAG.Part257.gaussSum_one_prime
#print axioms PAG.Part257.normSq_rootNum_one_prime
#print axioms PAG.Part257.not_isPrimitive_one_prime
#print axioms PAG.Part257.not_isometry_Vimprim_prime
#print axioms PAG.Part257.Vprim_ne_bot_prime
#print axioms PAG.Part257.not_isPrimitive_one_of_two_le
#print axioms PAG.Part257.charU_one_mem_Vimprim
#print axioms PAG.Part257.eq_one_of_two
#print axioms PAG.Part257.Vprim_two
