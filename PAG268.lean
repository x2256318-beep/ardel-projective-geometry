/-
アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致

問いの出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。

記号：`chiPt χ`（法 N の指標 χ）は [a:b] ↦ χ(a)·χ⁻¹(b)。χ⁻¹(b) は単数 b では χ(b) の複素共役、単数でない b では 0。
`torus u` は [a:b] ↦ [u a : b]（u は単数）。`extChi χ` は、χ を誘導する原始指標 χ*（法は導手）の `chiPt` を、導手から法 N への還元で引き戻したもの。

主な定理：
1. `chiPt χ` は P¹(ℤ/N) の上で well-defined（定義）。赤道では χ（`chiPt_eqPt`）、反転 W で χ⁻¹ の関数に移り（`chiPt_Wproj`）、トーラスの作用で χ(u) 倍（`chiPt_torus`）。
2. `extChi χ` の赤道への制限は χ（`extChi_eqPt`、`resE_extChi`）。N ∣ M のとき、χ を法 M に上げた指標の `extChi` は、`extChi χ` の引き戻し（`extChi_changeLevel`、段の言葉で `pullP_extChi`）。トーラスの作用で χ(u) 倍（`extChi_torus`）。
3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない場合がある（`chiPt_not_compat`：法 2 の自明な指標と点 0 の証人 1 つ。
   崩れるかどうかは新しい素数が増えるかどうかによる：統合照合 III-a の照合者の所見で、数値は法 3 → 9（原始的でないが両立する）と法 6 の例。Lean の外）。
4. p が素数で 1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` は、法 p^c の `chiPt χ` の引き戻しの |S_0|^(−1/2) 倍（`ketS_proj_zero_eq`）。
   |S_0| = `sz p K 0` = φ(p^K)。
   読み（Lean の外）：素数冪の法では、導手が 1 でない（主指標でない）χ について、法 p^c で単数であることと導手の法で単数であることが同じなので
   `chiPt χ` = `extChi χ` が成り立ち、`extChi_changeLevel` と合わせて、殻 0 のケットは規格化の定数倍で法 p^K の `extChi` に一致する見込み
   （`extChi χ = chiPt χ` は形式化していない。統合照合 III-a の指摘で、条件を「原始指標」から「導手 > 1」に直し、この段を読みとして分けた）。

注意（独立照合の指摘）：
- 導手 1 の指標（主指標）の `extChi` は、法 1 の P¹ が 1 点で 0 も単数なので、P¹(ℤ/N) の全点（0 と ∞ を含む）で 1。導手 > 1 の指標の `extChi` は 0 と ∞ で 0。
- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、照合者の確信度：中、Lean の外）。
- 4 の 1 ≤ K は 1 ≤ c と c ≤ K から出る（`ketS_proj` の型の引数として置いた）。1 ≤ c は外せない（c = 0、p = 2、K = 1 の点 ∞ で 0 ≠ 1。照合者の手計算）。
- 4 の右辺は法 p^c の `chiPt χ` の引き戻し。`extChi` との一致は上の読み（導手 > 1 のとき、Lean の外）。主指標では一致しない（`extChi` は定数 1、ケットは法 p で 0 または ∞ に落ちる点で 0。文は統合照合 III-a の指摘、「点で 0」の言い方は統合照合 IV の極低 10 で直した）。

Lean の外（盲検の問いテスト `records/p1_lift/outputs/blind_output.md`、照合者の確信度つき）：
- 引き戻しと両立し赤道への制限が恒等な延長の族は多い（導手ごとのアフィン空間、確信度：高）。トーラスとも両立する線形の族は一意で、`extChi` で与えられる（確信度：高、照合者の手の証明と数値。「線形の」は統合照合 VI の指摘で書き足した）。
- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（N ∣ 2 を除く。点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない（赤道の上で W V W = U⁻¹ が強制される）。
- 答えは F_q[t] でも同じ形の見込み（対照群）で、ℚ に固有の算術は運ばない。

内部照合：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS` を使った。
機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回）で一致なし（網羅ではない）。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1 の場合）、Part 252（PAG256）の `inv_apply_units_inv`（`mul_inv_apply_unit` の近く）。

ラベル（2026-11-25 22:28 の著者の判断による閉鎖で確定）：1〜4 は［再導出（小さい）］。新規候補なし。
-/
import PAG267
import PAG29

namespace PAG.Part268

open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter

/-! ## 1. P¹ の上の指標の関数 χ(a)·χ̄(b) -/

section chiPt

variable {N : ℕ}

theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
  rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]

/-- P¹(ℤ/N) の上の関数 [a:b] ↦ χ(a)·χ⁻¹(b)。 -/
noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
    rw [h1, h2, map_mul, map_mul]
    calc χ v.1.1 * χ⁻¹ v.1.2
        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
          rw [mul_inv_apply_unit, one_mul]
      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)

theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := rfl

/-- 赤道では χ：χ(x)·χ⁻¹(1) = χ(x)。 -/
theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := by
  show χ (x : ZMod N) * χ⁻¹ 1 = χ x
  rw [map_one, mul_one]

/-- 反転 W で χ⁻¹ の関数に移る。 -/
theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
    chiPt χ (Wproj q) = chiPt χ⁻¹ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ v.1.2 * χ⁻¹ v.1.1 = χ⁻¹ v.1.1 * χ⁻¹⁻¹ v.1.2
    rw [inv_inv, mul_comm]

/-- トーラスの作用の代表 (a, b) ↦ (u a, b)。 -/
def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
  ⟨((u : ZMod N) * v.1.1, v.1.2), by
    obtain ⟨s, t, h⟩ := v.2
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
    linear_combination h + s * v.1.1 * hu⟩

/-- トーラスの作用 [a:b] ↦ [u a : b]。 -/
def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)

/-- トーラスは赤道の上で掛け算：u·[x:1] = [u x : 1]。 -/
theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := rfl

/-- χ(a)·χ̄(b) はトーラスの作用で χ(u) 倍。 -/
theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    chiPt χ (torus u q) = χ u * chiPt χ q := by
  induction q using Quotient.inductionOn with
  | h v =>
    show χ ((u : ZMod N) * v.1.1) * χ⁻¹ v.1.2 = χ u * (χ v.1.1 * χ⁻¹ v.1.2)
    rw [map_mul, mul_assoc]

/-- 型の違う法の間の受け渡し：法が等しく整数での値が等しい 2 つの指標の関数は、還元の後で同じ。 -/
theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := by
  subst hd
  have : χ₁ = χ₂ := by
    refine MulChar.ext (fun u => ?_)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod d₁)
    rw [← ha]
    exact hχ a
  subst this
  rfl

end chiPt

/-! ## 2. 原始指標の関数を引き戻した族 -/

section ext

variable {N : ℕ} [NeZero N]

/-- E_N(χ) = r^*(χ*(a)·χ̄*(b))（χ* は χ を誘導する原始指標、導手から法 N への還元で引き戻す）。 -/
noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)

/-- 赤道への制限は χ。 -/
theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := by
  show chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (eqPt x)) = χ x
  rw [red_eqPt, chiPt_eqPt]
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) x
  rw [changeLevel_primitiveCharacter] at this
  exact this

omit [NeZero N] in
/-- 引き戻しとの両立：E_M(χ を法 M に上げたもの) = r^* E_N(χ)。 -/
theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := by
  show chiPt (changeLevel h χ).primitiveCharacter (red (changeLevel h χ).conductor_dvd_level q) =
    chiPt χ.primitiveCharacter (red χ.conductor_dvd_level (red h q))
  rw [red_comp]
  exact chiPt_red_congr (conductor_changeLevel χ h) _ _ (primitiveCharacter_changeLevel_apply h χ)
    _ _ q

/-- トーラスとの両立：E_N(χ)(u·q) = χ(u)·E_N(χ)(q)。 -/
theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    extChi χ (torus u q) = χ u * extChi χ q := by
  have hr : red χ.conductor_dvd_level (torus u q) =
      torus (unitsMap χ.conductor_dvd_level u) (red χ.conductor_dvd_level q) := by
    induction q using Quotient.inductionOn with
    | h v =>
      show mk (redU _ (torusU u v)) = mk (torusU _ (redU _ v))
      congr 1
      apply Subtype.ext
      show (castHom _ (ZMod χ.conductor) ((u : ZMod N) * v.1.1), castHom _ (ZMod χ.conductor) v.1.2) =
        (((unitsMap χ.conductor_dvd_level u : (ZMod χ.conductor)ˣ) : ZMod χ.conductor) *
          castHom _ (ZMod χ.conductor) v.1.1, castHom _ (ZMod χ.conductor) v.1.2)
      rw [map_mul]
      rfl
  show chiPt χ.primitiveCharacter (red _ (torus u q)) = χ u * chiPt χ.primitiveCharacter (red _ q)
  rw [hr, chiPt_torus]
  congr 1
  have := congrFun (pullL_charU (N := χ.conductor) χ.conductor_dvd_level χ.primitiveCharacter) u
  rw [changeLevel_primitiveCharacter] at this
  exact this

end ext

/-- 段の帰納系の言葉で：E は引き戻し `pullP` と両立する。 -/
theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) :=
  funext (fun q => (extChi_changeLevel (N := a.val) (M := b.val) h χ q).symm)

/-- E の赤道への制限は χ（Part 257 の `charU`）。 -/
theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    resE a (extChi χ) = PAG.Part257.charU χ :=
  funext (fun x => extChi_eqPt χ x)

/-! ## 3. 法 N の式をそのまま使うと両立しない（証人） -/

/-- 法 2 の自明な指標（導手 1）では、法 2 の式 χ(a)·χ⁻¹(b) は点 0 で 0、
法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない場合がある（証人 1 つ）。 -/
theorem chiPt_not_compat :
    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := by
  have h0 : ¬ IsUnit (0 : ZMod 2) := not_isUnit_zero
  show (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) 0 *
      (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1))⁻¹ 1 ≠
    (1 : DirichletCharacter ℂ 1) (castHom (one_dvd 2) (ZMod 1) 0) *
      (1 : DirichletCharacter ℂ 1)⁻¹ (castHom (one_dvd 2) (ZMod 1) 1)
  rw [MulChar.map_nonunit _ h0, zero_mul, map_one, inv_one]
  rw [MulChar.one_apply (isUnit_of_subsingleton _), MulChar.one_apply (isUnit_of_subsingleton _)]
  norm_num

/-! ## 4. 素数冪の法では Part 25（PAG29）の殻 0 のケット -/

section ket

variable {p : ℕ} [hp : Fact p.Prime]

/-- **殻 0 のケットとの一致**：1 ≤ c ≤ K のとき、P¹(ℤ/p^K) の殻 0 の南ケット `ketS_proj K 0 c`（Part 25（PAG29））は、
法 p^c の χ(a)·χ̄(b) の引き戻しの |S_0|^(−1/2) 倍。 -/
theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ c)) :
    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := by
  apply (PAG.Part28.projFunEquiv K hK).injective
  apply Subtype.ext
  rw [PAG.Part29.projFun_ketS]
  refine Prod.ext (funext (fun x => ?_)) (funext (fun y => ?_))
  · rw [PAG.Part28.projFun_south]
    show PAG.Part21.ket K 0 c h χ x = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1))
    rw [PAG.Part24.ket0_apply, map_one, map_one, mul_one]
  · rw [PAG.Part28.projFun_north]
    show (PAG.Part23.extS (PAG.Part21.ket K 0 c h χ)).2 y = (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
      (χ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) 1) *
        χ⁻¹ (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y))
    rw [map_one, map_one, one_mul]
    unfold PAG.Part23.extS
    dsimp only
    split_ifs with hy
    · rw [PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv (by omega) χ hy]
    · have hy' : ¬ IsUnit (castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) y) := by
        intro hu
        apply hy
        rw [castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)] at hu
        rw [← ZMod.natCast_zmod_val y, ZMod.isUnit_iff_coprime,
          Nat.coprime_pow_right_iff (by omega)]
        exact hu
      rw [MulChar.map_nonunit _ hy', mul_zero]

end ket

end PAG.Part268

#print axioms PAG.Part268.mul_inv_apply_unit
#print axioms PAG.Part268.chiPt_mk
#print axioms PAG.Part268.chiPt_eqPt
#print axioms PAG.Part268.chiPt_Wproj
#print axioms PAG.Part268.torus_eqPt
#print axioms PAG.Part268.chiPt_torus
#print axioms PAG.Part268.chiPt_red_congr
#print axioms PAG.Part268.extChi_eqPt
#print axioms PAG.Part268.extChi_changeLevel
#print axioms PAG.Part268.extChi_torus
#print axioms PAG.Part268.pullP_extChi
#print axioms PAG.Part268.resE_extChi
#print axioms PAG.Part268.chiPt_not_compat
#print axioms PAG.Part268.ketS_proj_zero_eq
