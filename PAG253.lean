/-
  PAG 2.0 Part 249（2026-11-07）— 有限レベルのイデール類群 C_ℚ/U_N ≅ (ℤ/N)^× × ℝ と素数イデールの類（アーデル射影幾何、本来の道 B-3）
  C_ℚ ≅ Ẑ^× × ℝ（対数座標 u = log ノルム）、U_N = ker(Ẑ^× → (ℤ/N)^×)。素数イデールの類 [π_p] = (k_p, −log p)、k_p ≡ p⁻¹ (mod N)。
  構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}（既知）は Lean にせず、有限レベルのモデル (ℤ/N)^× × ℝ の上で、すべての N について述べる。
  1. k_n = n⁻¹ ∈ (ℤ/N)^×（kUnit）：k_1 = 1、k_{ab} = k_a·k_b、レベル間の整合（ZMod.unitsMap）、素数の類が (ℤ/N)^× を生成する
     （n を素因数に分けるだけ。Dirichlet の算術級数定理は使わない）
  2. 定理 2.6 の前提：N と互いに素なすべての素数 p の平行移動 T_{k_p} と可換なら、すべての平行移動と可換。よって U は各指標に
     スカラーで働き、反転条件を固有値の形（c(χ⁻¹) = conj c(χ)、|c| = 1）で仮定すれば実指標では ±1（Part 1 の
     eigen_of_commute・real_sector_sign）。JUJ = U* とユニタリ性からその形を導く部分は §6 で足した。
     A_N の側でも、素数の単数倍 U_{k_p} と可換なら Part 220 の dilCommute に入る
  3. 稠密性：(ℤ/N)^× × ℝ の任意の点の ε 以内に、正の有理数 m/n の類 (k_m·k_n⁻¹, log n − log m)（素数イデールの積の類）がある。
     m, n は M（N ∣ M）と互いに素に取れる（有限個の素数を除いた版）
  4. 帰結：素数イデールの平行移動で不変で対数座標について連続な関数は定数。C_ℚ/U_N の指標 χ(k)·e^{iλu} は、
     Euler データ χ(k_p)·p^{−iλ}（有限個の素数を除いても）で決まる
  5. T_p = M_{k_p} ∘ S_{−log p}、W T_p W = T_p⁻¹、W S_s W = S_{−s}、T_p S_s = S_s T_p（境界は入れない）
  6. 追補（2026-11-08）：定理 2.6 (a)⇒(b) の有限レベル版の完全な形（thm26_full）。標準のエルミート形 ⟪f, g⟫ = Σ conj f·g
     について U が等長で JUJ が U の随伴（JUJ = U*）なら |c(χ)| = 1、c(χ⁻¹) = conj c(χ)、実指標で c = ±1。
     非空虚性の証人（U = T_h、固有値 χ(h)）と、仮定を外した反例（等長なし：U = 2·id、随伴なし：U = i·id）も示した。
     逆向き (b)⇒(a) は扱っていない
  7. 追補（2026-11-11、独立照合の指摘）：T_p F = F の形の仮定から M_a・S_s での不変性（7a）、可換性を外した反例
     U = M_s（N ≥ 3、7d）。2f を thm26_prime から eigenFun_of_commute_prime に改名した（中身は 2e と同じ）
-/
import PAG
import PAG252

namespace PAG.Part253

open Complex PAG.Part218 PAG.Part224

/-! ### 1. 有限レベルの素数イデールの類（単数部分） -/

/-- N と互いに素な n の類の単数部分 k_n = n⁻¹ ∈ (ℤ/N)^×。素数 p では、素数イデールの類 [π_p] = (k_p, −log p)
の Ẑ^× 成分 k_p = (p⁻¹)_{ℓ ≠ p} を (ℤ/N)^× に写したもの（C_ℚ ≅ Ẑ^× × ℝ_{>0}、Neukirch 第 VI 章）。 -/
def kUnit {N : ℕ} (n : ℕ) (h : n.Coprime N) : (ZMod N)ˣ := (ZMod.unitOfCoprime n h)⁻¹

/-- **1a.** k_n · n = 1（法 N）。 -/
theorem kUnit_mul_natCast {N : ℕ} (n : ℕ) (h : n.Coprime N) :
    ((kUnit n h : (ZMod N)ˣ) : ZMod N) * (n : ZMod N) = 1 := by
  unfold kUnit
  rw [← ZMod.coe_unitOfCoprime n h, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- **1b.** k_1 = 1。 -/
theorem kUnit_one {N : ℕ} (h : (1 : ℕ).Coprime N) : kUnit 1 h = 1 := by
  unfold kUnit
  rw [inv_eq_one]
  ext
  rw [ZMod.coe_unitOfCoprime, Units.val_one, Nat.cast_one]

/-- **1c.** k_{ab} = k_a·k_b。 -/
theorem kUnit_mul {N : ℕ} {a b : ℕ} (ha : a.Coprime N) (hb : b.Coprime N) (hab : (a * b).Coprime N) :
    kUnit (a * b) hab = kUnit a ha * kUnit b hb := by
  unfold kUnit
  rw [← mul_inv]
  congr 1
  ext
  rw [ZMod.coe_unitOfCoprime, Units.val_mul, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, Nat.cast_mul]

/-- **1d. レベル間の整合**：N ∣ M なら、(ℤ/M)^× → (ℤ/N)^× は k_n を k_n に写す（k_p は Ẑ^× = lim (ℤ/N)^× の元を定める）。 -/
theorem unitsMap_kUnit {N M : ℕ} (hNM : N ∣ M) (n : ℕ) (hM : n.Coprime M) :
    ZMod.unitsMap hNM (kUnit n hM) = kUnit n (Nat.Coprime.coprime_dvd_right hNM hM) := by
  unfold kUnit
  rw [map_inv]
  congr 1
  ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime, ZMod.cast_natCast hNM]

/-- **1e.** (ℤ/N)^× の元は、ある正の整数 n（N と互いに素）の k_n。 -/
theorem exists_kUnit_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    ∃ (n : ℕ) (h : n.Coprime N), 0 < n ∧ kUnit n h = a := by
  have hc : ((a⁻¹ : (ZMod N)ˣ) : ZMod N).val.Coprime N := ZMod.val_coe_unit_coprime a⁻¹
  refine ⟨((a⁻¹ : (ZMod N)ˣ) : ZMod N).val + N, Nat.coprime_add_self_left.mpr hc, ?_, ?_⟩
  · have := NeZero.pos N
    omega
  · unfold kUnit
    rw [inv_eq_iff_eq_inv]
    ext
    rw [ZMod.coe_unitOfCoprime, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

/-- **1f. 素数の類の生成**：(ℤ/N)^× の部分モノイド S が、N と互いに素なすべての素数 p の k_p を含めば、
N と互いに素なすべての n の k_n を含む（n を素因数に分けるだけ。Dirichlet の算術級数定理は使わない）。 -/
theorem kUnit_mem_of_prime {N : ℕ} (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) :
    ∀ (n : ℕ) (hn : n.Coprime N), kUnit n hn ∈ S := by
  intro n
  induction n using Nat.recOnMul with
  | zero =>
    intro hn
    have hN : N = 1 := (Nat.coprime_zero_left N).mp hn
    subst hN
    have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
    have h1 : kUnit 0 hn = 1 := Units.ext (Subsingleton.elim _ _)
    rw [h1]
    exact S.one_mem
  | one =>
    intro hn
    rw [kUnit_one]
    exact S.one_mem
  | prime p hp => exact hS p hp
  | mul a b iha ihb =>
    intro hab
    have ha : a.Coprime N := Nat.Coprime.coprime_mul_right hab
    have hb : b.Coprime N := Nat.Coprime.coprime_mul_left hab
    rw [kUnit_mul ha hb hab]
    exact S.mul_mem (iha ha) (ihb hb)

/-- **1g.** 同じ仮定で S = ⊤（素数の類は (ℤ/N)^× をモノイドとして生成する）。 -/
theorem eq_top_of_prime {N : ℕ} [NeZero N] (S : Submonoid (ZMod N)ˣ)
    (hS : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), kUnit p hpN ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨n, hn, -, rfl⟩ := exists_kUnit_eq a
  exact kUnit_mem_of_prime S hS n hn

/-! ### 2. 定理 2.6 の前提：素数の平行移動だけで足りる（有限レベル） -/

/-- **2a.** T_1 は恒等写像。 -/
theorem transl_one {G : Type*} [CommGroup G] : PAG.transl (1 : G) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext g
  show f (g * 1) = f g
  rw [mul_one]

/-- **2b.** T_{gh} = T_g ∘ T_h。 -/
theorem transl_mul {G : Type*} [CommGroup G] (g h : G) :
    PAG.transl (g * h) = PAG.transl g ∘ₗ PAG.transl h := by
  apply LinearMap.ext
  intro f
  funext x
  show f (x * (g * h)) = f (x * g * h)
  rw [mul_assoc]

/-- **2c.** U と可換な平行移動 T_g の g の全体は部分モノイド。 -/
def commSubmonoid {G : Type*} [CommGroup G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ)) : Submonoid G where
  carrier := {g | U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U}
  one_mem' := by
    show U ∘ₗ PAG.transl 1 = PAG.transl 1 ∘ₗ U
    rw [transl_one, LinearMap.comp_id, LinearMap.id_comp]
  mul_mem' := by
    intro g h hg hh
    have hg' : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U := hg
    have hh' : U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U := hh
    show U ∘ₗ PAG.transl (g * h) = PAG.transl (g * h) ∘ₗ U
    apply LinearMap.ext
    intro f
    have e1 := LinearMap.congr_fun hg' (PAG.transl h f)
    have e2 := LinearMap.congr_fun hh' f
    simp only [LinearMap.comp_apply] at e1 e2
    simp only [transl_mul, LinearMap.comp_apply]
    rw [e1, e2]

/-- **2d. 定理 2.6 の前提（有限レベル）**：N と互いに素なすべての素数 p について T_{k_p} と可換なら、
(ℤ/N)^× のすべての平行移動と可換。モノグラフの証明は Dirichlet の算術級数定理で {k_p} の稠密性を使ったが、
素数の類が生成することで足りる。 -/
theorem commute_transl_of_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (g : (ZMod N)ˣ) : U ∘ₗ PAG.transl g = PAG.transl g ∘ₗ U := by
  have h := eq_top_of_prime (commSubmonoid U) (fun p hp hpN => hU p hp hpN)
  have hg : g ∈ commSubmonoid U := by
    rw [h]
    exact Submonoid.mem_top g
  exact hg

/-- **2e. 定理 2.6 (a)⇒(b) の前半（有限レベル、素数の平行移動だけを仮定）**：U は各指標にスカラーで働く。 -/
theorem eigen_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (χ : (ZMod N)ˣ →* ℂˣ) : ∃ c : ℂ, U (PAG.charFun χ) = c • PAG.charFun χ :=
  PAG.eigen_of_commute U (commute_transl_of_prime U hU) χ

/-- **2f.** 指標ごとのスカラーを 1 つの関数 c にまとめた形（中身は 2e と同じ）。後半の含意「|c| = 1 と
c(χ⁻¹) = conj c(χ) なら実指標で c = ±1」は U によらず、どんな関数 c でも成り立つ（Part 1 の `real_sector_sign`）。
2026-11-11 に `thm26_prime` から改名した（独立照合で、名前が内容より強いと指摘された）。定理 2.6 (a)⇒(b) の
有限レベル版として中身のある文は §6 の `thm26_full`。 -/
theorem eigenFun_of_commute_prime {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧
      ((∀ χ, ‖c χ‖ = 1) → (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) → ∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) := by
  choose c hc using fun χ => eigen_of_commute_prime U hU χ
  exact ⟨c, hc, fun h1 h2 χ hχ => PAG.real_sector_sign c h1 h2 χ hχ⟩

/-- **2g. A_N の側**：N と互いに素なすべての素数 p について単数倍 U_{k_p} と可換な作用素は、すべての単数倍と可換
（Part 220 の `dilCommute` に入る）。 -/
theorem mem_dilCommute_of_prime {N : ℕ} [NeZero N] (T : Module.End ℂ (ZMod N → ℂ))
    (hT : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (f : ZMod N → ℂ),
      T (dil (kUnit p hpN) f) = dil (kUnit p hpN) (T f)) :
    T ∈ dilCommute N := by
  let S : Submonoid (ZMod N)ˣ :=
    { carrier := {a | ∀ f, T (dil a f) = dil a (T f)}
      one_mem' := by
        intro f
        rw [dil_one, dil_one]
      mul_mem' := by
        intro a b ha hb f
        have ha' : ∀ f, T (dil a f) = dil a (T f) := ha
        have hb' : ∀ f, T (dil b f) = dil b (T f) := hb
        rw [← dil_dil, ha', hb', dil_dil] }
  have h := eq_top_of_prime S (fun p hp hpN => hT p hp hpN)
  rw [mem_dilCommute]
  intro a f
  have ha : a ∈ S := by
    rw [h]
    exact Submonoid.mem_top a
  exact ha f

/-! ### 3. 有限レベルのイデール類群 C_ℚ/U_N ≅ (ℤ/N)^× × ℝ：素数イデールの類が生成する部分群は稠密 -/

/-- **3a. 稠密性**：(ℤ/N)^× × ℝ の任意の点 (a, t) と ε > 0 に対し、正の有理数 m/n（m, n は N と互いに素）の類
(k_m·k_n⁻¹, log n − log m)（素数イデールの積 ∏ π_p^{v_p(m/n)} の類）で、単数部分が a、対数座標が t の ε 以内のものがある。
m = 1 + Nj、n = a₀ + N⌊e^t·m/N⌋（a₀ = a の代表 + N）と取り、|n/m − e^t| < 2N/m と log の連続性を使う。 -/
theorem exists_cls_near {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime N) (hn : n.Coprime N), 0 < m ∧ 0 < n ∧
      kUnit m hm * (kUnit n hn)⁻¹ = a ∧ |Real.log n - Real.log m - t| < ε := by
  obtain ⟨δ, hδ, hlog⟩ := Metric.continuousAt_iff.mp (Real.continuousAt_log (Real.exp_pos t).ne') ε hε
  have hN0 : 0 < N := NeZero.pos N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  obtain ⟨j, hj⟩ := exists_nat_gt (2 * N / δ)
  set a₀ : ℕ := (a : ZMod N).val + N with ha₀
  set m : ℕ := 1 + N * j with hm_def
  set k : ℕ := ⌊Real.exp t * m / N⌋₊ with hk_def
  set n : ℕ := a₀ + N * k with hn_def
  have hmc : m.Coprime N := (Nat.coprime_add_mul_left_left 1 N j).mpr (Nat.coprime_one_left N)
  have hnc : n.Coprime N := by
    refine (Nat.coprime_add_mul_left_left a₀ N k).mpr ?_
    exact Nat.coprime_add_self_left.mpr (ZMod.val_coe_unit_coprime a)
  have hm0 : 0 < m := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)
  have hn0 : 0 < n := Nat.lt_of_lt_of_le hN0 (le_trans (Nat.le_add_left N _) (Nat.le_add_right _ _))
  refine ⟨m, n, hmc, hnc, hm0, hn0, ?_, ?_⟩
  · have hm1 : ZMod.unitOfCoprime m hmc = 1 := by
      ext
      rw [ZMod.coe_unitOfCoprime, Units.val_one, hm_def]
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero]
    have hna : ZMod.unitOfCoprime n hnc = a := by
      ext
      rw [ZMod.coe_unitOfCoprime, hn_def, ha₀]
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero, add_zero, ZMod.natCast_zmod_val]
    unfold kUnit
    rw [hm1, hna, inv_one, inv_inv, one_mul]
  · have hmR : (m : ℝ) = 1 + N * j := by
      rw [hm_def]
      push_cast
      ring
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm0
    have hmj : (j : ℝ) < m := by
      rw [hmR]
      nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (Nat.cast_nonneg (α := ℝ) j)]
    have hx0 : 0 ≤ Real.exp t * m / N := by positivity
    have hk1 : (k : ℝ) ≤ Real.exp t * m / N := Nat.floor_le hx0
    have hk2 : Real.exp t * m / N < k + 1 := Nat.lt_floor_add_one _
    have hk1' : N * (k : ℝ) ≤ Real.exp t * m := by
      have := (le_div_iff₀ hNpos).mp hk1
      linarith
    have hk2' : Real.exp t * m < N * (k : ℝ) + N := by
      have := (div_lt_iff₀ hNpos).mp hk2
      linarith
    have hnR : (n : ℝ) = ((a : ZMod N).val : ℝ) + N + N * k := by
      rw [hn_def, ha₀]
      push_cast
      ring
    have hval : (((a : ZMod N).val : ℕ) : ℝ) < N := by exact_mod_cast ZMod.val_lt (a : ZMod N)
    have hval0 : (0 : ℝ) ≤ (((a : ZMod N).val : ℕ) : ℝ) := Nat.cast_nonneg _
    have hdiff : |(n : ℝ) - Real.exp t * m| < 2 * N := by
      rw [abs_lt]
      constructor
      · rw [hnR]
        linarith
      · rw [hnR]
        linarith
    have hjm : 2 * (N : ℝ) / δ < m := lt_trans hj hmj
    have h2N : 2 * (N : ℝ) / m < δ := by
      rw [div_lt_iff₀ hmpos]
      have := (div_lt_iff₀ hδ).mp hjm
      linarith
    have hdist : dist ((n : ℝ) / m) (Real.exp t) < δ := by
      have e : (n : ℝ) / m - Real.exp t = ((n : ℝ) - Real.exp t * m) / m := by
        field_simp
      rw [Real.dist_eq, e, abs_div, abs_of_pos hmpos]
      calc |(n : ℝ) - Real.exp t * m| / m < 2 * N / m := div_lt_div_of_pos_right hdiff hmpos
        _ < δ := h2N
    have h1 := hlog hdist
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.log_exp, Real.dist_eq, Real.log_div hnpos.ne' hmpos.ne'] at h1
    exact h1

/-- **3b. 有限個の素数を除いた版**：N ∣ M のとき、m, n を M と互いに素に取れる（(ℤ/M)^× で 3a を使い、(ℤ/N)^× に落とす）。 -/
theorem exists_cls_near_of_dvd {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : (ZMod N)ˣ) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ) (hm : m.Coprime M) (hn : n.Coprime M), 0 < m ∧ 0 < n ∧
      kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹ = a ∧
      |Real.log n - Real.log m - t| < ε := by
  obtain ⟨a', ha'⟩ := ZMod.unitsMap_surjective hNM a
  obtain ⟨m, n, hm, hn, hm0, hn0, hcls, hlog⟩ := exists_cls_near a' t hε
  refine ⟨m, n, hm, hn, hm0, hn0, ?_, hlog⟩
  rw [← unitsMap_kUnit hNM m hm, ← unitsMap_kUnit hNM n hn, ← map_inv, ← map_mul, hcls, ha']

/-! ### 4. 帰結：素数イデールの平行移動で不変な連続関数は定数、Euler データは指標を決める -/

/-- **4a.** 素数イデールの平行移動 (T_p F)(k, u) = F(k·k_p, u − log p)（p は M と互いに素）で不変なら、
M と互いに素な正の n についても F(k·k_n, u − log n) = F(k, u)。 -/
theorem invariant_kUnit {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u) :
    ∀ (n : ℕ) (hn : n.Coprime M), 0 < n → ∀ (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit n (Nat.Coprime.coprime_dvd_right hNM hn)) (u - Real.log n) = f k u := by
  intro n
  induction n using Nat.recOnMul with
  | zero =>
    intro _ h
    exact absurd h (lt_irrefl 0)
  | one =>
    intro hn _ k u
    rw [kUnit_one, mul_one, Nat.cast_one, Real.log_one, sub_zero]
  | prime p hp =>
    intro hpM _ k u
    exact hinv p hp hpM k u
  | mul a b iha ihb =>
    intro hab hpos k u
    have ha : a.Coprime M := Nat.Coprime.coprime_mul_right hab
    have hb : b.Coprime M := Nat.Coprime.coprime_mul_left hab
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
    have haN := Nat.Coprime.coprime_dvd_right hNM ha
    have hbN := Nat.Coprime.coprime_dvd_right hNM hb
    rw [kUnit_mul haN hbN, Nat.cast_mul,
      Real.log_mul (Nat.cast_pos.mpr ha0).ne' (Nat.cast_pos.mpr hb0).ne', ← mul_assoc, mul_right_comm,
      show u - (Real.log a + Real.log b) = (u - Real.log b) - Real.log a by ring]
    rw [iha ha ha0 (k * kUnit b hbN) (u - Real.log b), ihb hb hb0 k u]

/-- **4b.** 同じ仮定で、正の有理数 m/n の類による平行移動 F(k·k_m·k_n⁻¹, u + log n − log m) = F(k, u)。 -/
theorem invariant_cls {N M : ℕ} (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    {m n : ℕ} (hm : m.Coprime M) (hn : n.Coprime M) (hm0 : 0 < m) (hn0 : 0 < n) (k : (ZMod N)ˣ) (u : ℝ) :
    f (k * (kUnit m (Nat.Coprime.coprime_dvd_right hNM hm) * (kUnit n (Nat.Coprime.coprime_dvd_right hNM hn))⁻¹))
      (u + (Real.log n - Real.log m)) = f k u := by
  have hmN := Nat.Coprime.coprime_dvd_right hNM hm
  have hnN := Nat.Coprime.coprime_dvd_right hNM hn
  have h1 := invariant_kUnit hNM f hinv m hm hm0 (k * (kUnit n hnN)⁻¹) (u + Real.log n)
  have h2 := invariant_kUnit hNM f hinv n hn hn0 (k * (kUnit n hnN)⁻¹) (u + Real.log n)
  rw [inv_mul_cancel_right, add_sub_cancel_right] at h2
  have e1 : k * (kUnit m hmN * (kUnit n hnN)⁻¹) = k * (kUnit n hnN)⁻¹ * kUnit m hmN := by
    rw [mul_comm (kUnit m hmN), mul_assoc]
  rw [e1, ← add_sub_assoc, h1, ← h2]

/-- **4c. 主定理**：N ∣ M とし、M と互いに素なすべての素数 p の素数イデールの平行移動で不変で、対数座標について連続な
関数 F : (ℤ/N)^× × ℝ → ℂ は定数（素数イデールの類は C_ℚ/U_N で稠密な部分群を生成する：3b）。 -/
theorem eq_of_prime_invariant {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℝ → ℂ)
    (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂ := by
  apply eq_of_forall_dist_le
  intro δ hδ
  obtain ⟨ε, hε, hcont⟩ := Metric.continuous_iff.mp (hf k₂) u₂ δ hδ
  obtain ⟨m, n, hm, hn, hm0, hn0, hcls, hlog⟩ := exists_cls_near_of_dvd hNM (k₁⁻¹ * k₂) (u₂ - u₁) hε
  have hinv' := invariant_cls hNM f hinv hm hn hm0 hn0 k₁ u₁
  rw [hcls, mul_inv_cancel_left] at hinv'
  have hd : dist (u₁ + (Real.log n - Real.log m)) u₂ < ε := by
    rw [Real.dist_eq, show u₁ + (Real.log n - Real.log m) - u₂ = Real.log n - Real.log m - (u₂ - u₁) by ring]
    exact hlog
  have h3 := hcont _ hd
  rw [hinv'] at h3
  exact le_of_lt h3

/-- **4d.** M = N の場合：N と互いに素なすべての素数の平行移動で不変な連続関数は定数。 -/
theorem eq_of_prime_invariant' {N : ℕ} [NeZero N] (f : (ZMod N)ˣ → ℝ → ℂ) (hf : ∀ k, Continuous (f k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (k : (ZMod N)ˣ) (u : ℝ),
      f (k * kUnit p hpN) (u - Real.log p) = f k u)
    (k₁ k₂ : (ZMod N)ˣ) (u₁ u₂ : ℝ) : f k₁ u₁ = f k₂ u₂ :=
  eq_of_prime_invariant (dvd_refl N) f hf (fun p hp hpM k u => hinv p hp hpM k u) k₁ k₂ u₁ u₂

/-- **4e. Euler データは指標を決める**：C_ℚ/U_N の指標 ψ(k, u) = χ(k)·e^{iλu} について、M（N ∣ M）と互いに素な
すべての素数 p で χ₁(k_p)·p^{−iλ₁} = χ₂(k_p)·p^{−iλ₂} なら χ₁ = χ₂ かつ λ₁ = λ₂（GL₁ の強重複度 1 の素朴な場合）。 -/
theorem eq_of_euler {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (χ₁ χ₂ : (ZMod N)ˣ →* ℂˣ) (l₁ l₂ : ℝ)
    (h : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M),
      (χ₁ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₁ * Real.log p : ℝ) : ℂ) * Complex.I) =
        (χ₂ (kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) : ℂ) *
          Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I)) :
    χ₁ = χ₂ ∧ l₁ = l₂ := by
  let F : (ZMod N)ˣ → ℝ → ℂ := fun k u =>
    (χ₁ k : ℂ) * Complex.exp (((l₁ * u : ℝ) : ℂ) * Complex.I) *
      ((χ₂ k : ℂ) * Complex.exp (((l₂ * u : ℝ) : ℂ) * Complex.I))⁻¹
  have hF : ∀ k, Continuous (F k) := by
    intro k
    have hc : ∀ l : ℝ, Continuous (fun u : ℝ => Complex.exp (((l * u : ℝ) : ℂ) * Complex.I)) := by
      intro l
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
    refine (continuous_const.mul (hc l₁)).mul ((continuous_const.mul (hc l₂)).inv₀ ?_)
    intro u
    exact mul_ne_zero (Units.ne_zero _) (Complex.exp_ne_zero _)
  have hinv : ∀ (p : ℕ), p.Prime → ∀ (hpM : p.Coprime M) (k : (ZMod N)ˣ) (u : ℝ),
      F (k * kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)) (u - Real.log p) = F k u := by
    intro p hp hpM k u
    have hp' := h p hp hpM
    set kp := kUnit p (Nat.Coprime.coprime_dvd_right hNM hpM)
    have e : ∀ l : ℝ, Complex.exp (((l * (u - Real.log p) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((l * u : ℝ) : ℂ) * Complex.I) * Complex.exp (-((l * Real.log p : ℝ) : ℂ) * Complex.I) := by
      intro l
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hB : (χ₂ kp : ℂ) * Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (Complex.exp_ne_zero _)
    simp only [F, map_mul, Units.val_mul, e]
    calc (χ₁ k : ℂ) * (χ₁ kp : ℂ) * (Complex.exp (((l₁ * u : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((l₁ * Real.log p : ℝ) : ℂ) * Complex.I)) *
          ((χ₂ k : ℂ) * (χ₂ kp : ℂ) * (Complex.exp (((l₂ * u : ℝ) : ℂ) * Complex.I) *
            Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I)))⁻¹
        = ((χ₁ k : ℂ) * Complex.exp (((l₁ * u : ℝ) : ℂ) * Complex.I) *
            ((χ₂ k : ℂ) * Complex.exp (((l₂ * u : ℝ) : ℂ) * Complex.I))⁻¹) *
          (((χ₁ kp : ℂ) * Complex.exp (-((l₁ * Real.log p : ℝ) : ℂ) * Complex.I)) *
            ((χ₂ kp : ℂ) * Complex.exp (-((l₂ * Real.log p : ℝ) : ℂ) * Complex.I))⁻¹) := by ring
      _ = (χ₁ k : ℂ) * Complex.exp (((l₁ * u : ℝ) : ℂ) * Complex.I) *
            ((χ₂ k : ℂ) * Complex.exp (((l₂ * u : ℝ) : ℂ) * Complex.I))⁻¹ := by
          rw [hp', mul_inv_cancel₀ hB, mul_one]
  have hconst := eq_of_prime_invariant hNM F hF hinv
  have hF10 : F 1 0 = 1 := by
    simp only [F, map_one, Units.val_one, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, inv_one]
  have hχ : χ₁ = χ₂ := by
    apply MonoidHom.ext
    intro k
    apply Units.ext
    have h1 := hconst k 1 0 0
    rw [hF10] at h1
    simp only [F, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h1
    exact (mul_inv_eq_one₀ (Units.ne_zero _)).mp h1
  refine ⟨hχ, ?_⟩
  by_contra hne
  have hd : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr hne
  have h1 := hconst 1 1 (Real.pi / (l₁ - l₂)) 0
  rw [hF10] at h1
  simp only [F, map_one, Units.val_one, one_mul] at h1
  have h2 := (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp h1
  have h3 : Complex.exp ((((l₁ - l₂) * (Real.pi / (l₁ - l₂)) : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [show ((((l₁ - l₂) * (Real.pi / (l₁ - l₂)) : ℝ) : ℂ) * Complex.I) =
        (((l₁ * (Real.pi / (l₁ - l₂)) : ℝ) : ℂ) * Complex.I) - (((l₂ * (Real.pi / (l₁ - l₂)) : ℝ) : ℂ) * Complex.I) by
          push_cast; ring,
      Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
  have h4 : (l₁ - l₂) * (Real.pi / (l₁ - l₂)) = Real.pi := by field_simp
  rw [h4, Complex.exp_pi_mul_I] at h3
  norm_num at h3

/-! ### 5. 有限レベルの C_ℚ 上の作用素：T_p = M_p ∘ S_{−log p} と二面体関係（境界なし） -/

/-- 素数イデールの平行移動 (T_p F)(k, u) = F(k·k_p, u − log p)（モノグラフの T_p の、境界を入れない有限レベル版）。 -/
noncomputable def primeShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * kUnit p hp) (u - Real.log p)

/-- 逆向きの平行移動 (T_p⁻¹ F)(k, u) = F(k·k_p⁻¹, u + log p)。 -/
noncomputable def primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ :=
  fun k u => F (k * (kUnit p hp)⁻¹) (u + Real.log p)

/-- 大域反転 (W F)(k, u) = F(k⁻¹, −u)。 -/
def globalInv {N : ℕ} (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k⁻¹ (-u)

/-- スケーリング（D = −i∂_u の生成する平行移動）(S_s F)(k, u) = F(k, u + s)。 -/
def scaleShift {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F k (u + s)

/-- 単数の平行移動 (M_a F)(k, u) = F(k·a, u)。 -/
def unitShift {N : ℕ} (a : (ZMod N)ˣ) (F : (ZMod N)ˣ → ℝ → ℂ) : (ZMod N)ˣ → ℝ → ℂ := fun k u => F (k * a) u

/-- **5a.** T_p = M_{k_p} ∘ S_{−log p}（単数の作用とスケーリングの合成）。 -/
theorem primeShift_eq {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp F = unitShift (kUnit p hp) (scaleShift (-Real.log p) F) := by
  funext k u
  simp only [primeShift, unitShift, scaleShift, sub_eq_add_neg]

/-- **5b.** M_a と S_s は可換。 -/
theorem unitShift_scaleShift {N : ℕ} (a : (ZMod N)ˣ) (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    unitShift a (scaleShift s F) = scaleShift s (unitShift a F) := rfl

/-- **5c.** T_p T_p⁻¹ = 1。 -/
theorem primeShift_primeShiftInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp (primeShiftInv p hp F) = F := by
  funext k u
  simp only [primeShift, primeShiftInv, mul_inv_cancel_right, sub_add_cancel]

/-- **5d.** W² = 1。 -/
theorem globalInv_globalInv {N : ℕ} (F : (ZMod N)ˣ → ℝ → ℂ) : globalInv (globalInv F) = F := by
  funext k u
  simp only [globalInv, inv_inv, neg_neg]

/-- **5e. 二面体関係** W T_p W = T_p⁻¹。 -/
theorem globalInv_primeShift_globalInv {N : ℕ} (p : ℕ) (hp : p.Coprime N) (F : (ZMod N)ˣ → ℝ → ℂ) :
    globalInv (primeShift p hp (globalInv F)) = primeShiftInv p hp F := by
  funext k u
  simp only [globalInv, primeShift, primeShiftInv, mul_inv_rev, inv_inv, neg_sub, sub_neg_eq_add]
  rw [mul_comm, add_comm]

/-- **5f. 二面体関係** W S_s W = S_{−s}（群の形の WDW = −D）。 -/
theorem globalInv_scaleShift_globalInv {N : ℕ} (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    globalInv (scaleShift s (globalInv F)) = scaleShift (-s) F := by
  funext k u
  simp only [globalInv, scaleShift, inv_inv, neg_add, neg_neg]

/-- **5g.** T_p と S_s は可換。 -/
theorem primeShift_scaleShift {N : ℕ} (p : ℕ) (hp : p.Coprime N) (s : ℝ) (F : (ZMod N)ˣ → ℝ → ℂ) :
    primeShift p hp (scaleShift s F) = scaleShift s (primeShift p hp F) := by
  funext k u
  simp only [primeShift, scaleShift]
  rw [sub_add_eq_add_sub]

/-! ### 6. 追補（2026-11-08）：定理 2.6 (a)⇒(b) の有限レベル版を完全に（JUJ = U* とユニタリ性から固有値の形を導く） -/

/-- 有限群 G 上の関数の標準のエルミート形 ⟪f, g⟫ = Σ_x conj(f x)·g x（第 1 引数について共役線形）。
モノグラフの 𝓑 = L²(Ẑ^×) の内積の有限レベル版（正規化の定数は省いた。等長と随伴の条件には影響しない）。 -/
noncomputable def ipG {G : Type*} [Fintype G] (f g : G → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x

/-- **6a.** ⟪a f, g⟫ = conj a·⟪f, g⟫。 -/
theorem ipG_smul_left {G : Type*} [Fintype G] (a : ℂ) (f g : G → ℂ) :
    ipG (a • f) g = starRingEnd ℂ a * ipG f g := by
  unfold ipG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- **6a′.** ⟪f, a g⟫ = a·⟪f, g⟫。 -/
theorem ipG_smul_right {G : Type*} [Fintype G] (a : ℂ) (f g : G → ℂ) :
    ipG f (a • g) = a * ipG f g := by
  unfold ipG
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul]
  ring

/-- **6b.** 指標 χ について ⟪χ, χ⟫ ≠ 0（x = 1 の項 |χ(1)|² = 1 だけで正）。 -/
theorem ipG_charFun_self_ne_zero {G : Type*} [CommGroup G] [Fintype G] (χ : G →* ℂˣ) :
    ipG (PAG.charFun χ) (PAG.charFun χ) ≠ 0 := by
  have h : ipG (PAG.charFun χ) (PAG.charFun χ) = ((∑ x, ‖(χ x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    unfold ipG PAG.charFun
    push_cast
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [mul_comm, Complex.mul_conj']
  rw [h, Complex.ofReal_ne_zero]
  apply ne_of_gt
  calc (0 : ℝ) < ‖((χ 1 : ℂˣ) : ℂ)‖ ^ 2 := by simp
    _ ≤ ∑ x, ‖(χ x : ℂ)‖ ^ 2 :=
      Finset.single_le_sum (f := fun x => ‖(χ x : ℂ)‖ ^ 2) (fun x _ => sq_nonneg _) (Finset.mem_univ (1 : G))

/-- **6c. ユニタリ性から |c| = 1**：U が等長（⟪U f, U g⟫ = ⟪f, g⟫）で U χ = c·χ なら |c| = 1。 -/
theorem norm_eq_one_of_isometry {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g) (χ : G →* ℂˣ) {c : ℂ}
    (hc : U (PAG.charFun χ) = c • PAG.charFun χ) : ‖c‖ = 1 := by
  have h := hiso (PAG.charFun χ) (PAG.charFun χ)
  rw [hc, ipG_smul_left, ipG_smul_right, ← mul_assoc] at h
  have h2 : starRingEnd ℂ c * c = 1 :=
    mul_right_cancel₀ (ipG_charFun_self_ne_zero χ) (h.trans (one_mul _).symm)
  have h3 : ((‖c‖ : ℝ) : ℂ) ^ 2 = 1 := by
    rw [← Complex.mul_conj', mul_comm, h2]
  have h4 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h4

/-- **6d. JUJ = U* から c(χ⁻¹) = conj c(χ)**：JUJ が U の随伴（⟪J U J f, g⟫ = ⟪f, U g⟫）で、U がすべての指標に
スカラー c で働くなら、c(χ⁻¹) = conj c(χ)。J χ = χ⁻¹（Part 3 の rev_charFun と同じ計算）を使う。 -/
theorem conj_eigen_of_adjoint {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) (c : (G →* ℂˣ) → ℂ)
    (hc : ∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) (χ : G →* ℂˣ) :
    c χ⁻¹ = starRingEnd ℂ (c χ) := by
  have hrev : ∀ ψ : G →* ℂˣ, PAG.rev (PAG.charFun ψ) = PAG.charFun ψ⁻¹ := by
    intro ψ
    funext g
    simp [PAG.rev, PAG.charFun]
  have hii : (χ⁻¹)⁻¹ = χ := by
    ext g
    simp
  have h := hadj (PAG.charFun χ) (PAG.charFun χ)
  rw [hrev, hc, map_smul, hrev, hii, hc, ipG_smul_left, ipG_smul_right] at h
  have h2 := mul_right_cancel₀ (ipG_charFun_self_ne_zero χ) h
  rw [← h2, Complex.conj_conj]

/-- **6e. 定理 2.6 (a)⇒(b)（有限可換群、すべての平行移動と可換）**：U がすべての T_h と可換で、等長で、JUJ が U の随伴なら、
各指標 χ に U χ = c(χ)·χ、|c(χ)| = 1、c(χ⁻¹) = conj c(χ)、実指標では c = ±1。 -/
theorem thm26_full_of_commute {G : Type*} [CommGroup G] [Fintype G] (U : (G → ℂ) →ₗ[ℂ] (G → ℂ))
    (hU : ∀ h, U ∘ₗ PAG.transl h = PAG.transl h ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : (G →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) := by
  choose c hc using fun χ => PAG.eigen_of_commute U hU χ
  have h1 : ∀ χ, ‖c χ‖ = 1 := fun χ => norm_eq_one_of_isometry U hiso χ (hc χ)
  have h2 : ∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ) := fun χ => conj_eigen_of_adjoint U hadj c hc χ
  exact ⟨c, hc, h1, h2, fun χ hχ => PAG.real_sector_sign c h1 h2 χ hχ⟩

/-- **6f. 定理 2.6 (a)⇒(b)（有限レベル、素数版、完全な形）**：U が N と互いに素なすべての素数 p の平行移動 T_{k_p} と
可換で、標準のエルミート形について等長（ユニタリ）で、JUJ が U の随伴（JUJ = U*）なら、各指標 χ に U χ = c(χ)·χ、
|c(χ)| = 1、c(χ⁻¹) = conj c(χ)（(ℤ/N)^× の上では χ̄ = χ⁻¹ なので α_χ̄ = −α_χ）、実指標では c = ±1。 -/
theorem thm26_full {N : ℕ} [NeZero N] (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      U ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ U)
    (hiso : ∀ f g, ipG (U f) (U g) = ipG f g)
    (hadj : ∀ f g, ipG (PAG.rev (U (PAG.rev f))) g = ipG f (U g)) :
    ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, (∀ χ, U (PAG.charFun χ) = c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) ∧
      (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) ∧ (∀ χ, χ⁻¹ = χ → c χ = 1 ∨ c χ = -1) :=
  thm26_full_of_commute U (commute_transl_of_prime U hU) hiso hadj

/-- **6g.** 平行移動 T_h は等長。 -/
theorem transl_isometry {G : Type*} [CommGroup G] [Fintype G] (h : G) (f g : G → ℂ) :
    ipG (PAG.transl h f) (PAG.transl h g) = ipG f g := by
  unfold ipG
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun x => rfl)

/-- **6g′.** J T_h J は T_h の随伴（⟪J T_h J f, g⟫ = ⟪f, T_h g⟫）。 -/
theorem transl_adjoint {G : Type*} [CommGroup G] [Fintype G] (h : G) (f g : G → ℂ) :
    ipG (PAG.rev (PAG.transl h (PAG.rev f))) g = ipG f (PAG.transl h g) := by
  unfold ipG
  symm
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun x => ?_)
  have e : ((x * h)⁻¹ * h)⁻¹ = x := by rw [mul_inv, inv_inv, mul_inv_cancel_right]
  show starRingEnd ℂ (f x) * g (x * h) = starRingEnd ℂ (f ((x * h)⁻¹ * h)⁻¹) * g (x * h)
  rw [e]

/-- **6h. 非空虚性の証人**：任意の h ∈ (ℤ/N)^× について、U = T_h は 6f の仮定をすべて満たす。 -/
theorem thm26_full_hyp_transl {N : ℕ} [NeZero N] (h : (ZMod N)ˣ) :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      PAG.transl h ∘ₗ PAG.transl (kUnit p hpN) = PAG.transl (kUnit p hpN) ∘ₗ PAG.transl h) ∧
    (∀ f g, ipG (PAG.transl h f) (PAG.transl h g) = ipG f g) ∧
    (∀ f g, ipG (PAG.rev (PAG.transl h (PAG.rev f))) g = ipG f (PAG.transl h g)) := by
  refine ⟨fun p _ hpN => ?_, transl_isometry h, transl_adjoint h⟩
  rw [← transl_mul, ← transl_mul, mul_comm]

/-- **6h′.** その固有値は c(χ) = χ(h)（複素指標では実数でない位相が実際に現れる）。 -/
theorem transl_charFun {G : Type*} [CommGroup G] (h : G) (χ : G →* ℂˣ) :
    PAG.transl h (PAG.charFun χ) = ((χ h : ℂˣ) : ℂ) • PAG.charFun χ := by
  funext g
  simp [PAG.transl, PAG.charFun, mul_comm]

/-- **6i. 仮定の除去：随伴の条件は外せない**。U = i·id は素数の平行移動と可換で等長だが、
c(χ⁻¹) = conj c(χ) を満たすスカラー c は取れない（自明な指標で c = i、i ≠ conj i）。 -/
theorem thm26_needs_adjoint {N : ℕ} [NeZero N] :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      (Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ (Complex.I • LinearMap.id)) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG ((Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) f)
        ((Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) g) = ipG f g) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ,
      (∀ χ, (Complex.I • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.charFun χ) =
        c χ • PAG.charFun χ) ∧ (∀ χ, c χ⁻¹ = starRingEnd ℂ (c χ)) := by
  refine ⟨fun p _ hpN => ?_, fun f g => ?_, ?_⟩
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply, ipG_smul_left,
      ipG_smul_right, Complex.conj_I]
    linear_combination (-(ipG f g)) * Complex.I_sq
  · rintro ⟨c, hc, hconj⟩
    have h1 := congrFun (hc 1) 1
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, PAG.charFun,
      MonoidHom.one_apply, Units.val_one, mul_one] at h1
    have hi1 : (1 : (ZMod N)ˣ →* ℂˣ)⁻¹ = 1 := by
      ext g
      simp
    have h2 := hconj 1
    rw [hi1, ← h1, Complex.conj_I] at h2
    have h3 : Complex.I = 0 := by linear_combination h2 / 2
    exact Complex.I_ne_zero h3

/-- **6j. 仮定の除去：等長の条件は外せない**。U = 2·id は素数の平行移動と可換で JUJ = U* も満たすが、
|c| = 1 を満たすスカラー c は取れない（自明な指標で c = 2）。 -/
theorem thm26_needs_isometry {N : ℕ} [NeZero N] :
    (∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      ((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ ((2 : ℂ) • LinearMap.id)) ∧
    (∀ f g : (ZMod N)ˣ → ℂ,
      ipG (PAG.rev (((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.rev f))) g =
        ipG f (((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ,
      (∀ χ, ((2 : ℂ) • LinearMap.id : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) (PAG.charFun χ) =
        c χ • PAG.charFun χ) ∧ (∀ χ, ‖c χ‖ = 1) := by
  refine ⟨fun p _ hpN => ?_, fun f g => ?_, ?_⟩
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp, LinearMap.comp_id]
  · have hrr : PAG.rev (PAG.rev f) = f := by
      funext x
      simp [PAG.rev]
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply, map_smul, hrr,
      ipG_smul_left, ipG_smul_right, map_ofNat]
  · rintro ⟨c, hc, hnorm⟩
    have h1 := congrFun (hc 1) 1
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul, PAG.charFun,
      MonoidHom.one_apply, Units.val_one, mul_one] at h1
    have h2 := hnorm 1
    rw [← h1] at h2
    norm_num at h2

/-! ### 7. 追補（2026-11-11）：独立照合で出た 2 点（作用素の言葉での不変性、可換性を外した反例） -/

/-- **7a.** T_p F = F（N と互いに素なすべての素数 p）で、対数座標について連続な F は、単数の平行移動 M_a でも
スケーリング S_s でも不変（4d を §5 の作用素の言葉で述べた系。2026-11-11 の独立照合で、4a〜4e と §5 の作用素を
つなぐ文がないと指摘された）。 -/
theorem shift_invariant_of_prime_invariant {N : ℕ} [NeZero N] (F : (ZMod N)ˣ → ℝ → ℂ)
    (hF : ∀ k, Continuous (F k))
    (hinv : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N), primeShift p hpN F = F)
    (a : (ZMod N)ˣ) (s : ℝ) : unitShift a F = F ∧ scaleShift s F = F := by
  have hpt : ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N) (k : (ZMod N)ˣ) (u : ℝ),
      F (k * kUnit p hpN) (u - Real.log p) = F k u := by
    intro p hp hpN k u
    exact congrFun (congrFun (hinv p hp hpN) k) u
  constructor
  · funext k u
    exact eq_of_prime_invariant' F hF hpt (k * a) k u u
  · funext k u
    exact eq_of_prime_invariant' F hF hpt k k (u + s) u

/-- 掛け算作用素 M_s：s は単位元で 1、ほかで −1（仮定の除去 7d の反例に使う）。 -/
noncomputable def signMul {G : Type*} [Group G] [DecidableEq G] : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := (if g = 1 then (1 : ℂ) else -1) * f g
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- M_s の値。 -/
theorem signMul_apply {G : Type*} [Group G] [DecidableEq G] (f : G → ℂ) (g : G) :
    signMul f g = (if g = 1 then (1 : ℂ) else -1) * f g := rfl

/-- **7b.** M_s は等長。 -/
theorem signMul_isometry {G : Type*} [Group G] [DecidableEq G] [Fintype G] (f g : G → ℂ) :
    ipG (signMul f) (signMul g) = ipG f g := by
  unfold ipG
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [signMul_apply, signMul_apply]
  by_cases hx : x = 1
  · simp [hx]
  · simp [hx]

/-- **7c.** J M_s J は M_s の随伴（s(x⁻¹) = s(x) による）。 -/
theorem signMul_adjoint {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G] (f g : G → ℂ) :
    ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g) := by
  unfold ipG
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have h1 : PAG.rev (signMul (PAG.rev f)) x = (if x = 1 then (1 : ℂ) else -1) * f x := by
    show signMul (PAG.rev f) x⁻¹ = _
    rw [signMul_apply]
    show (if x⁻¹ = 1 then (1 : ℂ) else -1) * f x⁻¹⁻¹ = _
    rw [inv_inv]
    by_cases hx : x = 1
    · simp [hx]
    · have hx' : ¬ x⁻¹ = 1 := fun h => hx (inv_eq_one.mp h)
      simp [hx, hx']
  rw [h1, signMul_apply]
  by_cases hx : x = 1
  · simp [hx]
  · simp [hx]

/-- **7d. 仮定の除去：素数の平行移動との可換性は外せない**（N ≥ 3）。U = M_s は等長で JUJ = U* も満たすが、
指標ごとのスカラー c は取れない（自明な指標 1 が、定数でない s に写る）。2026-11-10 の独立照合で、
6f の 3 つの仮定のうち可換性を外した例がないと指摘された。 -/
theorem thm26_needs_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (signMul f) (signMul g) = ipG f g) ∧
    (∀ f g : (ZMod N)ˣ → ℂ, ipG (PAG.rev (signMul (PAG.rev f))) g = ipG f (signMul g)) ∧
    ¬ ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, ∀ χ, signMul (PAG.charFun χ) = c χ • PAG.charFun χ := by
  refine ⟨signMul_isometry, signMul_adjoint, ?_⟩
  rintro ⟨c, hc⟩
  have hne : (-1 : (ZMod N)ˣ) ≠ 1 := by
    intro h
    have h1 : ((-1 : (ZMod N)ˣ) : ZMod N) = ((1 : (ZMod N)ˣ) : ZMod N) := by rw [h]
    rw [Units.val_neg, Units.val_one] at h1
    have h2 : ((2 : ℕ) : ZMod N) = 0 := by
      push_cast
      linear_combination (-1 : ZMod N) * h1
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have h1 := congrFun (hc 1) 1
  have h2 := congrFun (hc 1) (-1)
  simp only [signMul_apply, PAG.charFun, MonoidHom.one_apply, Units.val_one, mul_one, Pi.smul_apply,
    smul_eq_mul, ite_true] at h1
  simp only [signMul_apply, PAG.charFun, MonoidHom.one_apply, Units.val_one, mul_one, Pi.smul_apply,
    smul_eq_mul, hne, ite_false] at h2
  rw [← h1] at h2
  norm_num at h2

/-- **7e.** N ≥ 3 なら、M_s は N と互いに素な素数の平行移動のどれかと可換でない（7d と 2e から）。 -/
theorem signMul_not_commute {N : ℕ} [NeZero N] (hN : 3 ≤ N) :
    ¬ ∀ (p : ℕ), p.Prime → ∀ (hpN : p.Coprime N),
      (signMul : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ)) ∘ₗ PAG.transl (kUnit p hpN) =
        PAG.transl (kUnit p hpN) ∘ₗ signMul := by
  intro h
  obtain ⟨c, hc⟩ : ∃ c : ((ZMod N)ˣ →* ℂˣ) → ℂ, ∀ χ, signMul (PAG.charFun χ) = c χ • PAG.charFun χ := by
    choose c hc using fun χ => eigen_of_commute_prime signMul h χ
    exact ⟨c, hc⟩
  exact (thm26_needs_commute hN).2.2 ⟨c, hc⟩

end PAG.Part253

#print axioms PAG.Part253.kUnit
#print axioms PAG.Part253.kUnit_mul_natCast
#print axioms PAG.Part253.kUnit_one
#print axioms PAG.Part253.kUnit_mul
#print axioms PAG.Part253.unitsMap_kUnit
#print axioms PAG.Part253.exists_kUnit_eq
#print axioms PAG.Part253.kUnit_mem_of_prime
#print axioms PAG.Part253.eq_top_of_prime
#print axioms PAG.Part253.transl_one
#print axioms PAG.Part253.transl_mul
#print axioms PAG.Part253.commSubmonoid
#print axioms PAG.Part253.commute_transl_of_prime
#print axioms PAG.Part253.eigen_of_commute_prime
#print axioms PAG.Part253.eigenFun_of_commute_prime
#print axioms PAG.Part253.mem_dilCommute_of_prime
#print axioms PAG.Part253.exists_cls_near
#print axioms PAG.Part253.exists_cls_near_of_dvd
#print axioms PAG.Part253.invariant_kUnit
#print axioms PAG.Part253.invariant_cls
#print axioms PAG.Part253.eq_of_prime_invariant
#print axioms PAG.Part253.eq_of_prime_invariant'
#print axioms PAG.Part253.eq_of_euler
#print axioms PAG.Part253.primeShift
#print axioms PAG.Part253.primeShiftInv
#print axioms PAG.Part253.globalInv
#print axioms PAG.Part253.scaleShift
#print axioms PAG.Part253.unitShift
#print axioms PAG.Part253.primeShift_eq
#print axioms PAG.Part253.unitShift_scaleShift
#print axioms PAG.Part253.primeShift_primeShiftInv
#print axioms PAG.Part253.globalInv_globalInv
#print axioms PAG.Part253.globalInv_primeShift_globalInv
#print axioms PAG.Part253.globalInv_scaleShift_globalInv
#print axioms PAG.Part253.primeShift_scaleShift
#print axioms PAG.Part253.ipG
#print axioms PAG.Part253.ipG_smul_left
#print axioms PAG.Part253.ipG_smul_right
#print axioms PAG.Part253.ipG_charFun_self_ne_zero
#print axioms PAG.Part253.norm_eq_one_of_isometry
#print axioms PAG.Part253.conj_eigen_of_adjoint
#print axioms PAG.Part253.thm26_full_of_commute
#print axioms PAG.Part253.thm26_full
#print axioms PAG.Part253.transl_isometry
#print axioms PAG.Part253.transl_adjoint
#print axioms PAG.Part253.thm26_full_hyp_transl
#print axioms PAG.Part253.transl_charFun
#print axioms PAG.Part253.thm26_needs_adjoint
#print axioms PAG.Part253.thm26_needs_isometry
#print axioms PAG.Part253.shift_invariant_of_prime_invariant
#print axioms PAG.Part253.signMul
#print axioms PAG.Part253.signMul_apply
#print axioms PAG.Part253.signMul_isometry
#print axioms PAG.Part253.signMul_adjoint
#print axioms PAG.Part253.thm26_needs_commute
#print axioms PAG.Part253.signMul_not_commute
