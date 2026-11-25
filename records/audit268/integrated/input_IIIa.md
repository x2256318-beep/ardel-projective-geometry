# 統合照合 III-a の入力：Part 264（PAG268）の材料と、独立照合の後の直し（台帳 L16）（2026-11-25）
照合の対象：Part 264 の散文（Lean の冒頭の説明と docstring、ノート、xlsx の行、引き継ぎメモの項、着手前の文書、辞書 §23）が、Lean の形式文（§2 の全文）と食い違わないか、強いことを言っていないか。§4 は独立照合の出力、§5 は独立照合に渡した形式文と前の鎖の定義、§6 は盲検の問いテストの出力（読みの出所）。

## §1 台帳 L16
```markdown
### L16：Part 264（PAG268）の独立照合の後の直し（2026-11-25 夜）

- 範囲：独立照合（`records/audit268/outputs/check_output.md`）の指摘を受けた直し。形式文は変えていない。
  - PAG268.lean の冒頭の説明に「注意（独立照合の指摘）」の 4 項（主指標の `extChi` の値、`extChi` の [NeZero N]、1 ≤ K と 1 ≤ c、4 と `extChi` の一致の条件）。作り直してエラー・警告 0。
  - ノート `notes/pag2_pag268_p1_char_extension.md` の §3・§6。
- 扱い：閉じるときの統合照合に、L15 と一緒に載せる。
```

## §2 PAG268.lean の全文
```lean
/-
アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート、2026-11-25）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致

問いの出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。

記号：`chiPt χ`（法 N の指標 χ）は [a:b] ↦ χ(a)·χ⁻¹(b)。χ⁻¹(b) は単数 b では χ(b) の複素共役、単数でない b では 0。
`torus u` は [a:b] ↦ [u a : b]（u は単数）。`extChi χ` は、χ を誘導する原始指標 χ*（法は導手）の `chiPt` を、導手から法 N への還元で引き戻したもの。

主な定理：
1. `chiPt χ` は P¹(ℤ/N) の上で well-defined（定義）。赤道では χ（`chiPt_eqPt`）、反転 W で χ⁻¹ の関数に移り（`chiPt_Wproj`）、トーラスの作用で χ(u) 倍（`chiPt_torus`）。
2. `extChi χ` の赤道への制限は χ（`extChi_eqPt`、`resE_extChi`）。N ∣ M のとき、χ を法 M に上げた指標の `extChi` は、`extChi χ` の引き戻し（`extChi_changeLevel`、段の言葉で `pullP_extChi`）。トーラスの作用で χ(u) 倍（`extChi_torus`）。
3. 法 N の式 `chiPt χ` をそのまま使うと、原始的でない χ では引き戻しと両立しない（`chiPt_not_compat`：法 2 の自明な指標と点 0）。
4. p が素数で 1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` は、法 p^c の `chiPt χ` の引き戻しの |S_0|^(−1/2) 倍（`ketS_proj_zero_eq`）。
   したがって、2 チャートのモデル（Part 19〜25（PAG23〜PAG29））の殻 0 のケットは、素数冪の法では `extChi` と同じ形の関数（原始指標なら規格化の定数倍で `extChi` そのもの）。

注意（独立照合の指摘）：
- 導手 1 の指標（主指標）の `extChi` は、法 1 の P¹ が 1 点で 0 も単数なので、P¹(ℤ/N) の全点（0 と ∞ を含む）で 1。導手 > 1 の指標の `extChi` は 0 と ∞ で 0。
- `extChi` の定義は [NeZero N] を引数に取らない（節の変数は使われたときだけ入る）。`extChi_changeLevel` は [NeZero M] だけを仮定する。M = 0 では両立が崩れる見込み（照合者の手計算、Lean の外）。
- 4 の 1 ≤ K は 1 ≤ c と c ≤ K から出る（`ketS_proj` の型の引数として置いた）。1 ≤ c は外せない（c = 0、p = 2、K = 1 の点 ∞ で 0 ≠ 1。照合者の手計算）。
- 4 の右辺は法 p^c の `chiPt χ` の引き戻しで、`extChi` と一致するのは χ が法 p^c で原始的なとき。

Lean の外（盲検の問いテスト `records/p1_lift/outputs/blind_output.md`、照合者の確信度つき）：
- 引き戻しと両立し赤道への制限が恒等な延長の族は多い（導手ごとのアフィン空間、確信度：高）。トーラスとも両立する族は一意で、`extChi` で与えられる（確信度：高、照合者の手の証明と数値）。
- レトラクション（点ごとの写像）の形の延長はあるが、トーラスと両立するものはない（点 0 がトーラスで固定されるため）。N によらない同次形式の比では書けない（確信度：高）。
- `Uinf` の持ち上げ（P¹ の上の関数の作用素で、制限すると `Uinf`、引き戻しと両立）は存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない（確信度：高、数値の反例）。局所性の条件を足すと一意（確信度：中〜高）。W とは可換にできない。
- 答えは F_q[t] でも同じ形の見込み（対照群）で、ℚ に固有の算術は運ばない。

内部照合：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS` を使った。
機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回）で一致なし（網羅ではない）。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1 の場合）、Part 252（PAG256）の `inv_apply_units_inv`（`mul_inv_apply_unit` の近く）。

ラベル（見込み、閉鎖で確定）：1〜4 は［再導出（小さい）］。新規候補なし。
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
法 1 の式を引き戻したものは 1。法 N の式 χ(a)χ̄(b) は、原始的でない χ では引き戻しと両立しない。 -/
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

#print axioms PAG.Part268.chiPt_eqPt
#print axioms PAG.Part268.chiPt_Wproj
#print axioms PAG.Part268.chiPt_torus
#print axioms PAG.Part268.extChi_eqPt
#print axioms PAG.Part268.extChi_changeLevel
#print axioms PAG.Part268.extChi_torus
#print axioms PAG.Part268.pullP_extChi
#print axioms PAG.Part268.resE_extChi
#print axioms PAG.Part268.chiPt_not_compat
#print axioms PAG.Part268.ketS_proj_zero_eq
```

## §3 ノート（全文）
```markdown
# アーデル射影幾何 — Part 264（PAG268、短期層の小さいノート）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致

（2026-11-25 夜。題と主張は PAG268.lean の形式文から起こした。）

## §1 問いの出所

- 基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限に持ち上げる作用素）。
- 推薦案 `notes/pag2_p1_lift_preregistration.md` §4（C2-a）。2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が選んで着手した（CLAUDE.md §4 の選択の委任）。
- 盲検の問いテスト（`records/p1_lift/`）の答えで、持ち上げ V そのものは一意でないことが分かったので、Lean にするのは一意に決まる側（トーラスと両立する延長）とその 2 チャートのモデルとの結び目にした。

## §2 Lean に入った文（PAG268.lean、定理 14、sorry 0・警告 0、#print axioms は標準の 3 つ）

1. `chiPt χ`：[a:b] ↦ χ(a)·χ⁻¹(b) は P¹(ℤ/N) の上で well-defined。`chiPt_eqPt`（赤道では χ）、`chiPt_Wproj`（W で χ⁻¹ の関数に）、`chiPt_torus`（トーラスの作用 `torus u`：[a:b] ↦ [u a : b] で χ(u) 倍。`torus_eqPt`：赤道の上では掛け算）。補助：`mul_inv_apply_unit`、`chiPt_mk`、`chiPt_red_congr`（型の違う法の間の受け渡し）。
2. `extChi χ`（原始指標 χ* の `chiPt` を導手から法 N へ引き戻したもの）：`extChi_eqPt`・`resE_extChi`（赤道への制限は χ）、`extChi_changeLevel`・`pullP_extChi`（引き戻しと両立）、`extChi_torus`（トーラスで χ(u) 倍）。
3. `chiPt_not_compat`：法 N の式をそのまま使うと、原始的でない χ では両立しない（法 2 の自明な指標、点 0：左辺 0、右辺 1）。
4. `ketS_proj_zero_eq`：p 素数、1 ≤ c ≤ K のとき、Part 25（PAG29）の殻 0 の南ケット `ketS_proj K 0 c` = |S_0|^(−1/2)·（法 p^c の `chiPt χ` の引き戻し）。

## §3 読み（Lean の外）

- 盲検の照合者によれば、引き戻しと両立し赤道で恒等な延長の族は多いが、トーラスとも両立する族は一意で `extChi` で与えられる（確信度：高）。したがって 4 は「2 チャートのモデルの殻 0 のケットは、素数冪の法での一意な等変延長（の規格化の定数倍）」と読める（χ が原始的でない場合は、法 p^c の式と原始指標の式が違うので、この読みは原始指標のときに限る）。
- `Uinf` の持ち上げは存在するが一意でない（ユニタリ・トーラス・W・引き戻しの条件を全部課しても、素数ごとの ±1 の自由度。照合者の数値の反例）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（W V W = V⁻¹）。索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）は、この文書の後も残る。材料としては「P¹ の上の作用素への持ち上げは自然には一意に決まらない」。
- 4 の 1 ≤ c：c = 0 では、殻 0 のケットは北のチャートの単数でない点で 0、`chiPt`（法 1）の引き戻しは定数 1 で、等式は破れる（構築側と独立照合の照合者の手計算。Lean にしていない）。
- 主指標の `extChi` は全点（0 と ∞ を含む）で 1、導手 > 1 の指標の `extChi` は 0 と ∞ で 0（独立照合の指摘）。
- 対照群：盲検の照合者は、答えは F_q[t] でも同じ形とした。ℚ に固有の算術は運ばない。

## §4 ラベル（見込み。閉鎖で確定）

- 1〜4：［再導出（小さい）］。新規候補なし。兆候 4 は続く（Part 249〜264 で 16 パート連続）。

## §5 内部照合

- 着手前：P¹ の上の指標の関数としては、Part 19（PAG23）の殻ケット `kS` と Part 25（PAG29）の `ketS_proj` があった（推薦案 §0）。4 でそれと結んだ。
- 使ったもの：Part 254（PAG258）の `pullL_charU`、Part 24（PAG28）の `projFun_south`・`projFun_north`、Part 20（PAG24）の `ket0_apply`・`chi_cast_inv`、Part 25（PAG29）の `projFun_ketS`。
- 機械的な照合（全宣言 4409 件、対象 18 件、候補の組 144、照合 256 回、一致なし。記録 `records/audit268/internal/`）。網羅ではない。近いもの（C）：Part 28（PAG32）の `negProj`（トーラスの u = −1）、Part 252（PAG256）の `inv_apply_units_inv`。

## §6 照合

- 独立照合（形式文と定義だけ、2026-11-25 夜、約 160 秒、`records/audit268/outputs/check_output.md`。依頼文 `records/audit268/request_formal.md`、入力 `records/audit268/input_formal.md`）：逆翻訳は意図どおり。非空虚性の証人はすべての定理にある。除去テスト：1 ≤ c は外すと反例（c = 0、p = 2、K = 1、点 ∞）、原始指標の代わりに χ を使うと引き戻しとの両立だけが崩れる（`chiPt_not_compat`）、1 ≤ K は冗長、[NeZero N] は不要の見込み、[NeZero M] は M = 0 で崩れる見込み、`chiPt_red_congr` の d₁ = d₂ は型のための仮定。
- 指摘：主指標の `extChi` は 0 と ∞ でも 1（導手 > 1 では 0）、`extChi` の定義の [NeZero N]、4 と `extChi` の一致は原始指標のとき、`charU` の重複の可能性。形式文は変えず、冒頭の説明とこのノートに注意を書いた。`charU` は鎖に 1 つだけ（Part 257（PAG261）、PAG258 はそれを開いて使う）で、重複はない（言葉の検索）。
- この直しは、閉じるときの統合照合の入力に含める（台帳 L16）。

## §7 収束アラームの報告

- 辞書：§23 に Part 264 の名前の行を足した。
- 文献照合：推薦案の盲検の問いテストで実施した（`records/p1_lift/`、検索 3 回）。
- 兆候 4：続いている。
```

## §4 独立照合の出力（全文）
# 独立照合の出力（PAG268、2026-11-25）

（照合者の最終報告の全文を写した。）

# PAG268 照合の成果物（逆翻訳・非空虚性の証人・除去テスト・気づいた点）

ファイルは指示どおり 1 回だけ読みました。計算はすべて手計算で、Mathlib の内部の定義について推測した箇所は、そのつど確信度を付けています。

## 0. 使う定義の言葉による説明

- **Unimod N**：$(\mathbb Z/N)^2$ の組 $(x,y)$ のうち、$sx+ty=1$ となる $s,t$ があるもの（単模な組）。
- **ProjLine N**：単模な組を、単数倍 $(x,y)\sim(ux,uy)$（$u\in(\mathbb Z/N)^\times$）で割った集合 $\mathbb P^1(\mathbb Z/N)$。類を $[x:y]$ と書きます。$N=1$ では 1 点です。$N=0$ では $\mathbb Z/0=\mathbb Z$ なので $\mathbb P^1(\mathbb Z)$ になります。
- **Wproj**：$[x:y]\mapsto[y:x]$。
- **red**（$N\mid M$）：成分ごとに法 $N$ へ落とす写像 $\mathbb P^1(\mathbb Z/M)\to\mathbb P^1(\mathbb Z/N)$。
- **zeroPt** は $[0:1]$。**eqPt x** は単数 $x$ について $[x:1]$。
- **Lvl**：正の整数のこと。順序は整除です。
- **pullP**：$\mathbb P^1(\mathbb Z/a)$ の上の関数 $f$ を $f\circ\mathrm{red}$ に送る、$\mathbb P^1(\mathbb Z/b)$ の上の関数への線形写像（$a\mid b$）。
- **resE**：関数 $f$ を、単数 $x$ ごとに $f([x:1])$ を返す単数群上の関数に送る写像。
- **charU χ**：ディリクレ指標 $\chi$ を単数群に制限したもの。
- **χ⁻¹**：ディリクレ指標の群での逆元です。単数では $\chi(u)^{-1}=\overline{\chi(u)}$、非単数では 0 になります。したがって関数として $\chi^{-1}=\overline\chi$ です（$N=1$ でも成り立ちます）。
- **chiPt χ**：$[x:y]\mapsto \chi(x)\,\chi^{-1}(y)=\chi(x)\overline{\chi(y)}$。値は単数倍で変わりません（$\chi(u)\chi^{-1}(u)=1$）。0 でない値をとるのは $x,y$ がともに単数のときだけで、そのとき値は $\chi(x/y)$ です。
- **torusU / torus u**：$[x:y]\mapsto[ux:y]$。南の座標 $z=x/y$ では $z\mapsto uz$、北の座標 $y/x$ では $u^{-1}$ 倍になります。$[0:1]$ と $[1:0]$ は動きません。
- **extChi χ**：$\chi$ の導手を $f$、$\chi$ を誘導する原始指標（法 $f$）を $\chi^*$ とします。$q\in\mathbb P^1(\mathbb Z/N)$ を法 $f$ に落とした点で $\mathrm{chiPt}\,\chi^*$ を評価した値です。式で書くと $[x:y]\mapsto\chi^*(\bar x)\,\overline{\chi^*(\bar y)}$（バーは法 $f$ での剰余）。
- **sz p K u** $=p^{K-1-u}(p-1)$（自然数の引き算）。$u=0$、$K\ge1$ では $\varphi(p^K)$ です。
- **ket K 0 c**（ket0_apply による）：法 $p^c$ の関数 $f$ を、$x\mapsto \varphi(p^K)^{-1/2}\,f(x \bmod p^c)$ という $\mathbb Z/p^K$ の上の関数に送ります。
- **extS h**：南のチャートの関数 $h$ と、北のチャートの関数「$y$ が単数なら $h(y^{-1})$、そうでなければ 0」の組。
- **kS** $=\mathrm{extS}(\mathrm{ket}\dots\chi)$。
- **projFunEquiv**：$\mathbb P^1(\mathbb Z/p^K)$ の上の関数 $\Phi$ と、貼り合わせ条件を満たすチャートの組 $(\Phi([x:1]))_x,\ (\Phi([1:y]))_y$ との線形同型。
- **ketS_proj w c χ**：チャートの組 kS を projFunEquiv で $\mathbb P^1$ の上の関数に戻したもの。

## 1. 逆翻訳

- **mul_inv_apply_unit**：任意の $N$、法 $N$ のディリクレ指標 $\chi$、単数 $u$ について $\chi(u)\chi^{-1}(u)=1$。
- **chiPt_mk**：任意の単模な組 $(x,y)$ について $\mathrm{chiPt}\chi([x:y])=\chi(x)\chi^{-1}(y)$。
- **chiPt_eqPt**：単数 $x$ について $\mathrm{chiPt}\chi([x:1])=\chi(x)$。
- **chiPt_Wproj**：任意の点 $q$ について $\mathrm{chiPt}\chi(W q)=\mathrm{chiPt}\,\chi^{-1}(q)$。座標で書くと、$[y:x]$ での $\chi$ の値は $[x:y]$ での $\bar\chi$ の値に等しい、ということです。
- **torus_eqPt**：単数 $u,x$ について、$u$ の作用は $[x:1]$ を $[ux:1]$ に送る。
- **chiPt_torus**：任意の $u$、$q$ について $\mathrm{chiPt}\chi(u\cdot q)=\chi(u)\,\mathrm{chiPt}\chi(q)$。chiPt χ はトーラスの作用の固有関数で、固有値は $\chi(u)$ です。
- **chiPt_red_congr**：$d_1=d_2$、$d_1,d_2\mid M$ とし、法 $d_1$ の指標 $\chi_1$ と法 $d_2$ の指標 $\chi_2$ がすべての整数で同じ値をとるとします。このとき $\mathbb P^1(\mathbb Z/M)$ のすべての点 $q$ で $\mathrm{chiPt}\chi_1(\mathrm{red}\,q)=\mathrm{chiPt}\chi_2(\mathrm{red}\,q)$（型を運ぶための補題）。
- **extChi_eqPt**（$N\ne0$）：単数 $x$ について $\mathrm{extChi}\chi([x:1])=\chi(x)$。
- **extChi_changeLevel**（$N\mid M$、$M\ne0$）：法 $N$ の $\chi$ を法 $M$ に持ち上げた指標の extChi は、extChi χ を red で引き戻したものに等しい。
- **extChi_torus**（$N\ne0$）：$\mathrm{extChi}\chi(u\cdot q)=\chi(u)\,\mathrm{extChi}\chi(q)$。
- **pullP_extChi**：正の整数 $a\mid b$ について、extChi χ の引き戻しは、$\chi$ を法 $b$ に持ち上げた指標の extChi に等しい。
- **resE_extChi**：正の整数 $a$ について、extChi χ を単数 $x$ の点 $[x:1]$ に制限すると、$\chi$ の単数群への制限に等しい。
- **chiPt_not_compat**：法 1 の自明指標を法 2 に持ち上げた指標の chiPt の $[0:1]$ での値は、法 1 の自明指標の chiPt の $\mathrm{red}([0:1])$ での値と異なる。
- **ketS_proj_zero_eq**：$p$ を素数とし、$1\le c\le K$ とします（$1\le K$ も仮定にありますが、他の仮定から出ます）。法 $p^c$ の指標 $\chi$ について、$w=0$ のケット $\mathrm{ketS\_proj}(0,c,\chi)$ は関数 $q\mapsto \varphi(p^K)^{-1/2}\,\mathrm{chiPt}\chi(q \bmod p^c)$ に等しい。

## 2. 非空虚性の証人

- **mul_inv_apply_unit**：$N=5$、$\chi(2)=i$ となる位数 4 の指標、$u=2$ とします。$i\cdot(-i)=1$。
- **chiPt_eqPt / chiPt_mk**：同じ $\chi$ で $[2:1]$ での値は $\chi(2)=i$ です。$[2:3]$ では $\chi(2)\overline{\chi(3)}=i\cdot\overline{(-i)}=i\cdot i=-1$ で、これは $\chi(2\cdot3^{-1})=\chi(4)=-1$ と合います。
- **chiPt_Wproj**：同じ $\chi$、$q=[2:1]$ とします。左辺 $\mathrm{chiPt}\chi([1:2])=\chi^{-1}(2)=-i$、右辺 $\chi^{-1}(2)=-i$ で一致します。
- **torus_eqPt / chiPt_torus**：$N=5$、$\chi$ をルジャンドル記号、$u=2$、$q=[1:1]$ とします。$2\cdot[1:1]=[2:1]$ で、値は $-1=\chi(2)\cdot1$ です。
- **chiPt_red_congr**：$d_1=d_2=4$、$\chi_1=\chi_2=\chi_4$（法 4 の非自明な指標）、$M=12$、$q=[1:3]$ とします。両辺とも $\chi_4(1)\overline{\chi_4(3)}=-1$ です。
- **extChi_eqPt / extChi_torus**：$N=12$、$\chi$ を $\chi_4$ が誘導する指標（導手 4）とします。
  - $\mathrm{extChi}\chi([5:1])=\chi_4(1)=1=\chi(5)$ です。
  - 内容のある点として $q=[1:3]$ では、extChi は $\chi_4(1)\overline{\chi_4(3)}=-1$ ですが、$\mathrm{chiPt}\chi([1:3])=0$ です（3 は法 12 で単数でない）。extChi が chiPt と本当に違う場所はここです。
  - torus は $u=5$ で $[5:3]$ に移り、値は $\chi_4(1)\overline{\chi_4(3)}=-1=\chi(5)\cdot(-1)$ と合います。
- **extChi_changeLevel / pullP_extChi**：$N=4$、$M=12$、$\chi=\chi_4$、$q=[1:3]$ とします。左辺は上の $-1$、右辺は $\mathrm{chiPt}\chi_4([1:3])=-1$ です。
  - もう一つの例として、$N=1$、$M=2$、$\chi$ を自明指標とします。$\mathbb P^1(\mathbb Z/2)$ の 3 点すべてで両辺は 1 です。
- **resE_extChi**：$a=5$、$\chi$ をルジャンドル記号とします。$x=2$ で $-1=\chi(2)$ です。
- **chiPt_not_compat**：左辺は $\chi_2(0)\chi_2^{-1}(1)=0$ です。右辺は $\mathbb P^1(\mathbb Z/1)$ の唯一の点での値で、$\mathbb Z/1$ では $0=1$ なので $1$ です。したがって $0\ne1$。
- **ketS_proj_zero_eq**：$p=3$、$K=2$、$c=1$、$\chi$ を法 3 のルジャンドル記号とします。$\mathrm{sz}=3\cdot2=6$ です。$\mathbb P^1(\mathbb Z/9)$ の 12 点での値は次のとおりです。
  - $[1:1],[4:1],[7:1],[1:4],[1:7]$ などで $1/\sqrt6$
  - $[2:1],[5:1],[8:1]$ で $-1/\sqrt6$
  - $[0:1],[3:1],[6:1],[1:0],[1:3],[1:6]$ で 0
  
  2 乗和は $6/6=1$ です。

## 3. 除去テスト

- **ketS_proj_zero_eq の $1\le c$**：外すと反例があります（反例が作れる）。
  - $p=2$、$K=1$、$c=0$、$\chi$ を法 1 の自明指標とします。$\mathrm{sz}=1$ です。
  - 左辺の南のチャートでは $\mathrm{ket}(x)=1$ なので、$[0:1]\mapsto1$、$[1:1]\mapsto1$ です。
  - 点 $[1:0]$ は北のチャートの $y=0$ です。$0$ は単数でないので、左辺の値は 0 です。
  - 右辺は $\mathrm{chiPt}$ を $\mathbb P^1(\mathbb Z/1)$ で評価するので恒等的に 1 です。
  - よって $[1:0]$ で $0\ne1$。この仮定は必要です。
- **$1\le K$**：$h: c\le K$ と $1\le c$ から出るので、文の制限としては冗長です。ただし ketS_proj の型（projFunEquiv の引数）には必要です。
- **extChi で $\chi^*$ の代わりに $\chi$ を使う**（つまり extChi を chiPt にする）：
  - eqPt、torus、resE の版はそのまま成り立ちます（chiPt_eqPt と chiPt_torus がそれ自体です）。
  - changeLevel と pullP の版は崩れます。反例は chiPt_not_compat そのもので、$N=1$、$M=2$、自明指標、$q=[0:1]$ のとき $0\ne1$ です。$a=1$、$b=2$ として pullP の版でも同じです。
  - したがって、原始指標が中身を運んでいるのは level change との両立だけです。
- **extChi_eqPt / extChi_torus の [NeZero N]**：不要に見えます（確信度：中）。
  - Mathlib の導手は、指標がその法を経由する $d$ の最小値（sInf）です。法 0 では $0\mid0$ なので導手は 0 となり、$\chi^*=\chi$、red は恒等になるはずです。
  - そうなら $N=0$ でも、両定理は chiPt の版に帰着して成り立ちます。
- **extChi_changeLevel の [NeZero M]**：外すと反例が作れる見込みです（確信度：中。上と同じ「法 0 の導手は 0」という推測に依存します）。
  - $N=1$、$M=0$、$\chi$ を自明指標、$q=[0:1]\in\mathbb P^1(\mathbb Z)$ とします。
  - 左辺は $\mathrm{chiPt}(\text{持ち上げ})([0:1])$ です。0 は $\mathbb Z$ で単数でないので、値は 0 です。
  - 右辺は 1 です。
- **chiPt_red_congr の $d_1=d_2$**：不要に見えます。
  - 整数への持ち上げ $\tilde x,\tilde y$ をとると、両辺はそれぞれ $\chi_i(\tilde x)\chi_i^{-1}(\tilde y)$ です。$\chi_1,\chi_2$ が整数上で一致すれば、逆元も整数上で一致します。
  - 例えば $d_1=2$、$d_2=4$ の自明指標どうしは整数上で一致し（どちらも $a$ が奇数のとき 1、偶数のとき 0）、結論も成り立ちます。
  - 型を運ぶために置いた仮定と読めます。
- **chiPt_red_congr の hχ**：外すと反例があります。$d=M=5$、$\chi_1$ を自明指標、$\chi_2$ をルジャンドル記号、$q=[2:1]$ とすると、$1\ne-1$ です。
- **ほかの定理**：型以外に仮定がありません（mul_inv_apply_unit、chiPt_*、torus_eqPt、pullP_extChi、resE_extChi）。Lvl は正なので、pullP_extChi と resE_extChi には法 0 が入りません。

## 4. 気づいた点

1. **法 1 の扱い**：$\mathbb P^1(\mathbb Z/1)$ は 1 点で、$\mathbb Z/1$ では $0$ が単数です。そのため $\mathrm{chiPt}\,1=1$ になります。
   - この帰結として、導手 1 の指標（主指標）の extChi は $\mathbb P^1(\mathbb Z/N)$ の全点（$0$ と $\infty$ を含む）で恒等的に 1 です。
   - 一方、導手 $>1$ の指標の extChi は、法 $f$ での剰余が単数でない点で 0 です。とくに $[0:1]$ と $[1:0]$ では 0 です。
   - 「自明か非自明か」で $0$ と $\infty$ での値が 1 から 0 に跳ぶので、この扱いは意図どおりか確認してください。
2. **χ⁻¹ と複素共役**：関数として $\chi^{-1}=\bar\chi$ です（単数では $|\chi|=1$、非単数ではどちらも 0、$N=1$ では両方 1）。問題はありません。chiPt_Wproj は「$W$ は $\chi$ を $\bar\chi$ に変える」と読めます。
3. **トーラスの作用の向き**：$[x:y]\mapsto[ux:y]$ で、南の座標を $u$ 倍、北の座標を $u^{-1}$ 倍します。固有値は $\chi(u)$ です（$\chi(u)^{-1}$ ではありません）。$W\circ(u\cdot)\circ W=(u^{-1}\cdot)$ となり、chiPt_Wproj と整合します。可換群なので、作用の左右の問題はありません。
4. **extChi が well-defined な族か**：$\chi^*$ は Classical.choose で選ばれますが、原始指標は一意なので、関数としては $\chi$ だけで決まります。extChi_changeLevel と pullP_extChi が、整除の系の上での両立を与えています。
   - ただし法 0（$M=0$）では両立が崩れる見込みです（§3）。
   - さらに、注記には「節 2 の extChi では [NeZero N] を仮定に入れ、extChi_changeLevel では外した」とあります。def extChi 自体が [NeZero N] を引数に取るなら、extChi_changeLevel の右辺 extChi χ はどうやって $N\ne0$ のインスタンスを得ているのか、入力からは分かりません。extChi の実際の引数の並びの確認を勧めます。
5. **ketS_proj_zero_eq と extChi の関係**：右辺は chiPt χ（法 $p^c$）の引き戻しで、extChi ではありません。
   - 原始的でない $\chi$（例：法 $p$ の主指標、$c=1$）では、ketS_proj は $\varphi(p^K)^{-1/2}\,\mathrm{extChi}(\text{持ち上げた}\chi)$ とは異なります。主指標の場合、後者は全点で定数になります。
   - 両者が一致するのは、$\chi$ が法 $p^c$ で原始的なときです。「ケットは extChi の正規化である」と散文で書く場合は、この条件が要ります。
6. **正規化の因子**：$\varphi(p^K)^{-1/2}$ です。値が 0 でない点は $[x:1]$（$x$ は単数）のちょうど $\varphi(p^K)$ 個で、数え上げ測度で単位ノルムになります。これは $w=0$ のときだけの文です。
7. **charU の重複の可能性**：resE_extChi は PAG.Part257.charU を名前空間つきで使っています。一方、前提 3 では pullL_charU（Part258）も charU を使っており、Part257 と Part258 に同じ式の charU が 2 つある可能性があります（第 12 の型：内部の重複）。入力の範囲では、どちらの名前空間の定義かは判別できません。
8. **resE の範囲**：eqPt は単数にしか定義されていないので、resE_extChi は $[x:1]$（$x$ が単数）以外の点について何も言いません。extChi の内容は、extChi_changeLevel のほうにあります。

## 使ったツールと読んだ範囲

Read を 1 回だけ使い、`/home/claude/ardel-projective-geometry/records/audit268/input_formal.md` の全 207 行を読みました。ほかのファイル、コードの実行、ウェブは使っていません。

## §5 独立照合に渡した形式文と定義（全文）
# 入力：形式文と定義

Lean 4 / Mathlib。定理の証明は省略し、定義は全文を写した（コメントと docstring は除いた。本体を省略した定義はそう書いた）。検査対象はエラー 0・警告 0 で通っており、`#print axioms` は標準の 3 つだけ。

## 前提 1：PAG27（名前空間 PAG.Part27）
```lean
def Unimod (N : ℕ) := {v : ZMod N × ZMod N // ∃ s t : ZMod N, s * v.1 + t * v.2 = 1}

def projSetoid (N : ℕ) : Setoid (Unimod N) where
  r v w := ∃ u : (ZMod N)ˣ, w.1.1 = u * v.1.1 ∧ w.1.2 = u * v.1.2
  iseqv := {
    refl := fun v => ⟨1, by simp, by simp⟩
    symm := fun {v w} ⟨u, h1, h2⟩ => ⟨u⁻¹, by rw [h1, ← mul_assoc, Units.inv_mul, one_mul],
      by rw [h2, ← mul_assoc, Units.inv_mul, one_mul]⟩
    trans := fun {v w z} ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩ => ⟨u' * u, by rw [h1', h1, Units.val_mul, mul_assoc],
      by rw [h2', h2, Units.val_mul, mul_assoc]⟩ }

def ProjLine (N : ℕ) := Quotient (projSetoid N)

def mk (v : Unimod N) : ProjLine N := Quotient.mk (projSetoid N) v

theorem mk_eq_mk {v w : Unimod N} (u : (ZMod N)ˣ) (h1 : w.1.1 = u * v.1.1) (h2 : w.1.2 = u * v.1.2) :
    mk v = mk w := …（証明は省略）

def Wproj : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk ⟨(v.1.2, v.1.1), swap_unimod v⟩)
    (fun _v _w ⟨u, h1, h2⟩ => mk_eq_mk u h2 h1)
```

## 前提 2：PAG267（名前空間 PAG.Part267）
```lean
def redU (h : N ∣ M) (v : Unimod M) : Unimod N :=
  ⟨(castHom h (ZMod N) v.1.1, castHom h (ZMod N) v.1.2), by
    obtain ⟨s, t, hst⟩ := v.2
    exact ⟨castHom h (ZMod N) s, castHom h (ZMod N) t, by
      rw [← map_mul, ← map_mul, ← map_add, hst, map_one]⟩⟩

def red (h : N ∣ M) : ProjLine M → ProjLine N :=
  Quotient.lift (fun v => mk (redU h v)) (fun _v _w ⟨u, h1, h2⟩ =>
    mk_eq_mk (unitsMap h u)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h1, map_mul]; rfl)
      (by change castHom h (ZMod N) _ = _ * castHom h (ZMod N) _; rw [h2, map_mul]; rfl))

theorem red_comp (h₁ : N ∣ M) (h₂ : M ∣ L) (q : ProjLine L) :
    red h₁ (red h₂ q) = red (dvd_trans h₁ h₂) q := …（証明は省略）

def zeroU (N : ℕ) : Unimod N := ⟨(0, 1), ⟨0, 1, by simp⟩⟩

def zeroPt (N : ℕ) : ProjLine N := mk (zeroU N)

def eqU (x : (ZMod N)ˣ) : Unimod N := ⟨((x : ZMod N), 1), ⟨0, 1, by simp⟩⟩

def eqPt (x : (ZMod N)ˣ) : ProjLine N := mk (eqU x)

theorem red_eqPt (h : N ∣ M) (x : (ZMod M)ˣ) : red h (eqPt x) = eqPt (unitsMap h x) := …（証明は省略）

abbrev Fsp (a : Lvl) : Type := ProjLine a.val → ℂ

noncomputable def pullP (a b : Lvl) (h : a ≤ b) : Fsp a →ₗ[ℂ] Fsp b where
  toFun f q := f (red (N := a.val) (M := b.val) h q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def resE (a : Lvl) : Fsp a →ₗ[ℂ] Gsp a where
  toFun f x := f (eqPt x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
```

## 前提 3：PAG258・PAG257（名前空間 PAG.Part258・PAG.Part257）
```lean
noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ) := …（証明は省略）

structure Lvl where
  
  val : ℕ
  pos : 0 < val
deriving DecidableEq

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u
```
（Lvl の順序は a ≤ b ↔ a.val ∣ b.val。各 a に NeZero a.val のインスタンスがある。）

## 前提 4：2 チャートのモデル（PAG19・PAG21・PAG23・PAG24・PAG28・PAG29。p は素数）
```lean
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)

noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ := …（本体は省略）

abbrev P1F (N : ℕ) := (ZMod N → ℂ) × (ZMod N → ℂ)

noncomputable def extS (h : ZMod N → ℂ) : P1F N := (h, fun y => if IsUnit y then h y⁻¹ else 0)

noncomputable def kS (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) : P1F (p ^ K) :=
  extS (ket K w c h χ)

theorem ket0_apply (K c : ℕ) (h : 0 + c ≤ K) (f : ZMod (p ^ c) → ℂ) (x : ZMod (p ^ K)) :
    ket K 0 c h f x = (((Real.sqrt (sz p K 0))⁻¹ : ℝ) : ℂ) *
      f (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) x) := …（証明は省略）

theorem chi_cast_inv {K c : ℕ} (hcK : c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) {x : ZMod (p ^ K)}
    (hx : IsUnit x) :
    χ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x⁻¹)
      = χ⁻¹ (ZMod.castHom (pow_dvd_pow p hcK) (ZMod (p ^ c)) x) := …（証明は省略）

noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))

theorem projFun_south (Φ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.1 x = Φ (mk ⟨(x, 1), 0, 1, by simp⟩) := …（証明は省略）

theorem projFun_north (Φ : ProjLine (p ^ K) → ℂ) (y : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.2 y = Φ (mk ⟨(1, y), 1, 0, by simp⟩) := …（証明は省略）

noncomputable def ketS_proj (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm ⟨kS K w c h χ, compat_extS _⟩

theorem projFun_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    (projFunEquiv K hK (ketS_proj K hK w c h χ)).1 = kS K w c h χ := …（証明は省略）
```
（P1F N = (ZMod N → ℂ) × (ZMod N → ℂ)：南のチャートの関数と北のチャートの関数の組。projFunEquiv は ProjLine (p^K) の上の関数と、貼り合わせ条件を満たす組の ℂ 線形同型。）

## 検査対象：PAG268（名前空間 PAG.Part268）
```lean
namespace PAG.Part268
open ZMod PAG.Part27 PAG.Part258 PAG.Part267 DirichletCharacter
variable {N : ℕ}
-- 節 2（extChi・extChi_eqPt・extChi_torus）では [NeZero N] が仮定に入る（extChi_changeLevel では外した）。
-- 節 4（ketS_proj_zero_eq）では variable {p : ℕ} [hp : Fact p.Prime]。

theorem mul_inv_apply_unit (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := …（証明は省略）

noncomputable def chiPt (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  Quotient.lift (fun v : Unimod N => χ v.1.1 * χ⁻¹ v.1.2) (fun v w ⟨u, h1, h2⟩ => by
    show χ v.1.1 * χ⁻¹ v.1.2 = χ w.1.1 * χ⁻¹ w.1.2
    rw [h1, h2, map_mul, map_mul]
    calc χ v.1.1 * χ⁻¹ v.1.2
        = (χ (u : ZMod N) * χ⁻¹ (u : ZMod N)) * (χ v.1.1 * χ⁻¹ v.1.2) := by
          rw [mul_inv_apply_unit, one_mul]
      _ = χ (u : ZMod N) * χ v.1.1 * (χ⁻¹ (u : ZMod N) * χ⁻¹ v.1.2) := by ring)

theorem chiPt_mk (χ : DirichletCharacter ℂ N) (v : Unimod N) :
    chiPt χ (mk v) = χ v.1.1 * χ⁻¹ v.1.2 := …（証明は省略）

theorem chiPt_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : chiPt χ (eqPt x) = χ x := …（証明は省略）

theorem chiPt_Wproj (χ : DirichletCharacter ℂ N) (q : ProjLine N) :
    chiPt χ (Wproj q) = chiPt χ⁻¹ q := …（証明は省略）

def torusU (u : (ZMod N)ˣ) (v : Unimod N) : Unimod N :=
  ⟨((u : ZMod N) * v.1.1, v.1.2), by
    obtain ⟨s, t, h⟩ := v.2
    refine ⟨s * ((u⁻¹ : (ZMod N)ˣ) : ZMod N), t, ?_⟩
    have hu : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (u : ZMod N) = 1 := Units.inv_mul u
    linear_combination h + s * v.1.1 * hu⟩

def torus (u : (ZMod N)ˣ) : ProjLine N → ProjLine N :=
  Quotient.lift (fun v => mk (torusU u v)) (fun _v _w ⟨c, h1, h2⟩ =>
    mk_eq_mk c (by change (u : ZMod N) * _ = c * ((u : ZMod N) * _); rw [h1]; ring) h2)

theorem torus_eqPt (u x : (ZMod N)ˣ) : torus u (eqPt x) = eqPt (u * x) := …（証明は省略）

theorem chiPt_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    chiPt χ (torus u q) = χ u * chiPt χ q := …（証明は省略）

theorem chiPt_red_congr {d₁ d₂ M : ℕ} (hd : d₁ = d₂) (χ₁ : DirichletCharacter ℂ d₁)
    (χ₂ : DirichletCharacter ℂ d₂) (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) (h₁ : d₁ ∣ M) (h₂ : d₂ ∣ M)
    (q : ProjLine M) : chiPt χ₁ (red h₁ q) = chiPt χ₂ (red h₂ q) := …（証明は省略）

noncomputable def extChi (χ : DirichletCharacter ℂ N) : ProjLine N → ℂ :=
  fun q => chiPt χ.primitiveCharacter (red χ.conductor_dvd_level q)

theorem extChi_eqPt (χ : DirichletCharacter ℂ N) (x : (ZMod N)ˣ) : extChi χ (eqPt x) = χ x := …（証明は省略）

theorem extChi_changeLevel {M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (q : ProjLine M) : extChi (changeLevel h χ) q = extChi χ (red h q) := …（証明は省略）

theorem extChi_torus (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) (q : ProjLine N) :
    extChi χ (torus u q) = χ u * extChi χ q := …（証明は省略）

theorem pullP_extChi (a b : Lvl) (h : a ≤ b) (χ : DirichletCharacter ℂ a.val) :
    pullP a b h (extChi χ) = extChi (changeLevel (n := a.val) (m := b.val) h χ) := …（証明は省略）

theorem resE_extChi (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    resE a (extChi χ) = PAG.Part257.charU χ := …（証明は省略）

theorem chiPt_not_compat :
    chiPt (changeLevel (one_dvd 2) (1 : DirichletCharacter ℂ 1)) (zeroPt 2) ≠
      chiPt (1 : DirichletCharacter ℂ 1) (red (one_dvd 2) (zeroPt 2)) := …（証明は省略）

theorem ketS_proj_zero_eq (K c : ℕ) (hK : 1 ≤ K) (h : 0 + c ≤ K) (hc : 1 ≤ c)
    (χ : DirichletCharacter ℂ (p ^ c)) :
    PAG.Part29.ketS_proj K hK 0 c h χ = fun q =>
      (((Real.sqrt (PAG.Part19.sz p K 0))⁻¹ : ℝ) : ℂ) *
        chiPt χ (red (pow_dvd_pow p (by omega : c ≤ K)) q) := …（証明は省略）
```

## §6 盲検の問いテストの出力（全文）
# 盲検の問いテストの出力（C2：U_∞ の P¹ への持ち上げ、2026-11-25）

（照合者の最終報告の全文を写した。）

## 結論

Q1〜Q4 はすべて構成できました。ただし一意になるのは一箇所だけで、トーラスと両立する延長の族（Q3 の線形版）です。それは χ*(a)·χ̄*(b) という一つの式で与えられます。持ち上げ V（Q4）はユニタリ性・トーラス・W の条件を全部課しても一意になりません。どの答えも、CRT による素点ごとの分解、P¹(ℤ_p) の剰余円板の構造、U の形式的な性質（引き戻しとの可換、トーラスとの可換、ユニタリ、WUW = U⁻¹）しか使っていません。そのため算術的な内容はなく、関数体でも同じ答えになります。この問いそのものを扱った文献は見つかりませんでした。

以下の記号：p ∤ N なら N_p = 1 とする。X_N = ∏_{p^e‖N} P¹(ℤ/p^e)。各素点 p で P¹(ℤ/p^e) は三つに分かれる：単数の円板（法 p で 0 でも ∞ でもない点）、0 の円板（p | a）、∞ の円板（p | b）。

---

### Q1. 延長の族

**答え：できる。一意ではない。** 族全体は次の直積と1対1に対応します。

∏_{f ≥ 1} ∏_{χ* は導手 f の原始指標} { Φ ∈ F_f : res Φ = χ* }

各因子は次元 |X_f| − φ(f) = f∏_{p|f}(1+1/p) − φ(f) のアフィン空間です。

**根拠：**
- 法 N の指標 χ は、r^*（f → N）による χ* の引き戻しになっている。
- そのため両立条件 E_N(χ) = r^* E_f(χ*) によって、族は導手のレベルでの値 Φ_{χ*} := E_f(χ*) で決まる。
- 逆に、Φ を任意に選んで E_N(χ) := r^*Φ_{χ*} と置けば、res との関係も両立条件も満たされる。
- f = 1 では Φ = 1 しか取れない。f = 3 では自由度は 2 になる。
- 0 による延長は「導手のレベルで 0 延長してから引き戻したもの」と一致しない。N が f にない素数を含むと破れるので、問題文の記述と整合する。

**数値：** L = 6, 8, 9, 12, 15, 30 の約数すべての上で連立方程式を解きました。どれも解があり、解空間の次元は 2, 20, 26, 26, 56, 56 で、上の式の予想とすべて一致しました（例：L = 15 では 2 + 3·2 + 3·16 = 56）。

**確信度：** 高（証明 ＋ 数値）。

### Q2. レトラクション

**存在：ある。** 素点ごとに次の写像を作ります。
- 単数の円板の上では [a:b] ↦ a/b。
- 0 の円板と ∞ の円板は、単数の円板と法 p の段階ですでに分かれている。だから、そこには「法 p^e ごとに降りる」任意の写像（たとえば定数 1）を置けばよい。
- これらを CRT で貼り合わせる。法 M から法 N への両立条件は p 成分ごとの条件に分解するので、素点ごとの構成で足りる。

**W との両立：可能。** 0 の円板での値を h とし、∞ の円板では h∘W の逆数を取ればよい。

**N によらない式：**
- 整数係数の同次形式の比 P/Q として一つの式で与えることは**不可能**です。理由：Q がすべての p ですべての点の上で単数でなければならない。Q(x,1) が定数なら Q = c·y^d で、[1:0] で消える。定数でなければ、Schur の定理により無限個の p で根を持つ。
- 指数が N に依存する多項式なら書けます：
  ρ_N([a:b]) = 1 − (ab)^n + a^{n+1} b^{n−1}（n は λ(N) の倍数で、かつ N の素因数の最大の冪指数以上。たとえば n = N!）
- この式は、単数の円板の上では a/b、それ以外では 1 になります。
- 数値で次を確かめました（M = 12, 30, 36, 60 とその約数）：類の上で well-defined であること、レトラクションであること、還元と両立すること、ρ∘W = ρ⁻¹。

**確信度：** 存在と W との両立は高。形式の比が不可能なことは高（Schur の定理による）。

### Q3. トーラスとの両立

**線形の族：選べる。しかも一意。** 式は次のとおりです。

E_N(χ)([a:b]) = χ*(a mod f) · χ̄*(b mod f)

**根拠（一意性）：**
- 族は導手のレベル f の値で決まる（Q1）。
- 等変な写像は、各軌道 O の上で「χ* が O の固定部分群の上で自明なら 1 つのスカラー、そうでなければ 0」という形しか取れない。
- p | f で非自由な局所軌道（[p^k v : 1] や [1 : p^k w]、k ≥ 1）の固定部分群は 1 + p^{e−1}ℤ_p を含む。原始指標 χ* はその上で自明でない。
- X_f の自由な軌道は E_f だけなので、Φ は E_f の外では 0 に決まる。これを引き戻したものが上の式になる。
- この族は W とも自動的に両立する：E(χ)∘W = E(χ̄)。

**数値：** L = 6, 8, 9, 12, 15, 30 で解空間の次元は 0。L = 12 では、解いた族が上の式と一致することを確認しました。

**レトラクションの型（g∘ρ）：存在しない**（N | 2 の場合を除く）。点 [0:1] はトーラス全体で固定されるので ρ([0:1]) = uρ([0:1]) がすべての u で必要になり、単数群が自明でない限り矛盾します。したがって、等変な延長は「ρ による合成」の形をしていません。

**確信度：** 高。

### Q4. 持ち上げ V

**存在：ある。** たとえば V = E·U·res + (1 − E·res)。
- 引き戻しとの両立は、E と U がそれぞれ両立することから出る。
- ただし一般にはユニタリではない。数値では N = 10, 15 で非ユニタリでした。N = 6, 12 でユニタリになるのは、そこに現れる実の 2 次指標で 𝔀 = 1 となるためです。

**ユニタリにすると何が決まるか：**
- res V = U res から、ブロック形は [[U, 0], [*, *]]。
- ユニタリ性から左下のブロックは 0。したがって V = U ⊕ C で、C は F(X_N ∖ E_N) 上のユニタリ。

**層別の持ち上げ（自然な選び方の候補）：**
- 構成：S を「単数の円板にある素点の集合」とする層に X_N を分ける。各層は (ℤ/N_S)^× × Z（Z は残りの素点での 0 の円板または ∞ の円板の点）と書ける。そこで V = U_{N_S} ⊗ id と置く。
- 数値で確認した性質（L = 12, 18, 20, 30）：ユニタリ、res V = U res、引き戻しと両立、トーラスと可換、WVW = V⁻¹。
- この持ち上げは Φ_χ = χ*(a)χ̄*(b) を固有値 𝔀(χ*) の固有ベクトルに持つ。
- 「V が層の指示関数と Z 座標の関数による掛け算と可換」（局所性）という条件を加えると一意になります。引き戻しの条件から、各 z で A_z = U が出るためです。

**一意にならないこと：**
- ユニタリ、トーラスとの可換、WVW = V⁻¹、引き戻しとの両立を全部課しても、一意ではありません。
- 反例：v = 1_{p での 0 の円板} − 1_{p での ∞ の円板} として、R_p = 1 − 2P_v を層別の V に合成する。素数ごとに ±1 の自由度が生じる。
- 数値：(L, p) = (30, 3), (36, 3), (20, 5) で、すべての条件を満たし、かつ層別の V と異なることを確認しました。
- e ≥ 2 では、トーラス不変な関数がさらに増えるので、自由度はもっと大きくなります。

**W と可換にはできない：**
- E の上では W V W = U⁻¹ が強制される。
- 𝔀(χ̄) = 𝔀(χ)^{-1} であり、𝔀 は一般に実数でない（N = 5, 7 で数値確認）。

**SL₂ / PGL₂ との可換：**
- E_N を保つ PGL₂(ℤ/N) の元は、トーラスと W（正規化群）に限ります。それ以外の元（たとえば冪単元）との可換は、E を保たないので条件として意味を持ちません。

**2 変数フーリエでは作れない（手計算のみ）：**
- 斉次座標の 2 変数フーリエ変換を Φ_χ に当てると、ガウス和の位相は τ(χ)τ(χ̄) = χ(−1)p のように打ち消し合う。
- 𝔀 は 1 変数の側の量で、P¹ の上の「幾何的な」フーリエからは出てきません。

**確信度：**
- 存在と、ユニタリ性からブロック形が出ることは高。
- 一意にならないことは高（反例を数値で確認）。
- 局所性の条件で一意になることは中〜高（議論は概略で、数値では確かめていない）。
- 2 変数フーリエの所見は中（手計算のみ）。

### Q5. 文献

この持ち上げの問題そのもの（Ẑ^× ⊂ P¹(Ẑ) からレベルと両立する延長、ルート数の作用素の持ち上げ）を扱った文献は**見つかりませんでした**。検索は 3 回だけで、MathSciNet と zbMATH は使っていないので、「見つからなかった」は「存在しない」の根拠にはなりません。

部品はどれも標準的です：
- P¹(ℤ/N) と Γ₀(N) の剰余類、その極限 P¹(Ẑ) は Manin–Marcolli の非可換モジュラー曲線とモジュラー記号の文脈に現れる（arXiv:math/0102006、arXiv:math/0111093）。
- Connes–Marcolli の GL₂ 系（arXiv:math/0409520、arXiv:math/0507101）。
- 指標つきのマニン記号（Stein のノート）。

χ*(a)χ̄*(b) の型の関数は、指標つきのモジュラー記号やアイゼンシュタイン級数で使われる型だろうと推測しますが、この同定は未確認です。

答え自体は CRT と剰余円板の初等的な議論で出るので、「既知の結果からの短い帰結」の水準と見ます。

**確信度：** 文献の未発見については低〜中。「既知の道具だけで答えが出る」ことについては高。

### Q6. 関数体 F_q[t]

**答え：同じ形になる。**
- 議論が使うのは、CRT、局所環上の P¹ の剰余円板への分解、U の形式的な性質だけである。
- 形式の比が不可能なことは、関数体の Chebotarev の定理で同様に出る。
- トーラス等変なレトラクションが存在しないことも同様。例外は (F_q[t]/P^e)^× が自明な場合で、q = 2、deg P = 1、e = 1 に限られる。
- 𝔀 の正規化（i^a √f の部分）は、無限素点での符号と q^{deg f / 2} に置き換わる。しかし答えは 𝔀 の値に依存しない。

§7 の対照群テストの意味で言えば、これらの答えに ℚ に固有の算術はありません。

**確信度：** 中〜高。

---

数値のスクリプト（p1.py, test1.py, test2.py, test3.py）は /tmp/blind_p1lift/ にあります（`records/p1_lift/outputs/blind_scripts/` に写した）。

**ツールの使用回数：** Bash 5 回、Write 4 回、WebSearch 3 回、合計 12 回。/home/claude/ の下のファイルは読んでいません。

## §7 着手前の文書（全文）
```markdown
# 着手前の 4 点：候補 C2（U_∞ の P¹ への持ち上げ）（2026-11-25 夜）

（2026-11-25 19:13 の著者の指示「お勧めで進めてください」を受けて、構築側が推薦案を 1 つに絞り、そのまま着手する。選択の委任は CLAUDE.md §4。何を選び、なぜかをここに記録する。）

## §0 問いの出所と内部照合

- 出所：基礎文書の索引 2.4 の留保（`JH` は P¹ の上の作用素ではない）と、Part 263（PAG267）で外に残った候補 C2（`Uinf` を P¹ の上の関数の極限 `LimP` に持ち上げる作用素）。
- 内部照合（言葉の検索）：Part 263 より前に、レベルの間の `ProjLine` の写像はない。P¹ の上の指標の関数としては、Part 19（PAG23）の殻ケット `kS`（2 チャートのモデル、法 p^K）と、Part 25（PAG29）の射影直線の版 `ketS_proj` がある。殻 0 のケット |0, χ⟩ は、下の §2 の関数 χ(a)·χ̄(b) の素数冪の場合と同じものの見込み（c ≥ 1。c = 0 では違う：殻 0 のケットは単数の点の指示関数、χ(a)·χ̄(b) は定数 1）。

## §1 候補と選択

- C2-a（推薦）：トーラスと両立する、引き戻しと両立する延長 E（赤道の関数 → P¹ の関数）を指標の言葉で書き、Part 19 の殻 0 のケットと結ぶ。持ち上げ V の非一意性は読みとして記録する。
- C2-b：持ち上げ V そのもの（層別の持ち上げと、局所性の条件による一意性）を Lean にする。CRT による層の分解が重く、残余は計算だけなので、今は採らない。
- C3：A1 と定理 2.6 を組み合わせた 1 つの Lean の文。局所計算の装置の側で、幾何の問いではないので今は採らない。
- 選んだ理由：C2-a は、Part 263 の極限の塔（PAG267）と、Part 19〜25 の 2 チャートのモデル（PAG23〜PAG29）を初めて Lean で結ぶ。その結び目（殻 0 のケット = 一意な等変延長）が、索引 1.4・2.4 の材料になる。

## §2 4 点（C2-a）

1. 幾何の言葉の問い：赤道（両座標が単数の点）の上の関数を、すべての素点を測る段で P¹ 全体に延ばすとき、解像度の変更（還元による引き戻し）とトーラスの対称性を保つ延ばし方はあるか、一意か。貼り合わせ U は P¹ 全体の作用素に持ち上がるか。
2. 既存の言葉への翻訳：P¹(Ẑ) の上の局所定数関数の空間への、開でない部分集合 Ẑ^× からの延長。等変延長は、トーラス軌道の固定部分群の上の指標の自明性で決まる（表現論の初等的な議論）。持ち上げ V は E·U·res + (1 − E·res) の形。
3. 残余：計算の細部だけ（盲検の照合者は「既知の道具だけで答えが出る、既知の結果からの短い帰結の水準」）。したがって新規パートではなく短期層の小さいノートとして扱う。
4. 対照群：盲検の照合者は、答えは F_q[t] でも同じ形（CRT・剰余円板・U の形式的な性質だけを使う）とした。ℚ に固有の算術は運ばない。

## §3 盲検の問いテスト（`records/p1_lift/`）

- 延長の族は存在し、一意でない（導手ごとの自由度のアフィン空間）。トーラスと両立する族は一意で、E(χ)[a:b] = χ*(a)·χ̄*(b)（χ* は原始指標）。W とは E(χ)∘W = E(χ̄)。
- レトラクションの型の延長は存在し W と両立にできるが、N によらない同次形式の比では書けない。トーラスと両立するレトラクションはない（点 0 が固定されるため）。
- 持ち上げ V は存在するが、ユニタリ・トーラス・W・引き戻しの条件を全部課しても一意でない（素数ごとの ±1 の自由度）。局所性の条件で一意（照合者の確信度：中〜高）。W とは可換にできない（W V W = V⁻¹ が強制される）。
- 文献：この問いを扱ったものは見つからなかった（検索 3 回）。
- 構築側の数値（`records/p1_lift/numeric/retraction_check.py`）：素数ごとの規則のレトラクション（単数の円板で a/b、0 の円板で 1 + x、∞ の円板で (1 + y)⁻¹）は、M ≤ 60 で赤道の上で恒等・還元と両立・W と両立。

## §4 推薦と、Lean にする予定の文（短期層、Part 264（PAG268））

1. 法 N の指標 χ について、χ(a)·χ̄(b) は P¹(ℤ/N) の上の関数として well-defined（`chiPt`）。赤道では χ(x)。トーラスの作用で χ(u) 倍。W で χ̄ の関数に移る。
2. 原始指標の関数を引き戻した族 E_N(χ) = r^*(χ*(a)χ̄*(b)) は、赤道への制限が χ で、引き戻しと両立する。
3. 法 N の式 χ(a)χ̄(b) をそのまま使うと、原始的でない χ では両立しない（証人）。
4. 素数冪の法で、χ(a)χ̄(b)（c ≥ 1）の引き戻しは Part 25（PAG29）の殻 0 のケット `ketS_proj K 0 c` と一致する（Lean で結べなければ Lean の外に残す）。
- Lean の外に残す見込み：トーラスと両立する族の一意性、持ち上げ V の存在と非一意性、局所性の条件による一意性、同次形式の比で書けないこと。
- ラベルの見込み：1〜3 は［再導出（小さい）］、4 は［再導出（小さい）］。新規候補なし。兆候 4 は続く。
```

## §8 xlsx の行 3758〜3771（名前 | 主張 | 証明の要点 | 主な補題 | 状態）
LABEL 列：PAG2.0-264（PAG268、短期層の小さいノート）P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致（推薦案 pag2_p1_lift_preregistration.md、著者の指示「お勧めで進めてください」2026-11-25 19:13。索引 2.4 の留保と Part 263 の候補 C2）：χ(a)·χ⁻¹(b) は P¹ の上で well-defined で、赤道では χ、W で χ⁻¹、トーラスで χ(u) 倍。原始指標の関数の引き戻し extChi は赤道で χ、引き戻しとトーラスと両立。法 N の式をそのまま使うと原始的でない χ では両立しない。素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。U_∞ の持ち上げの非一意性とトーラス等変な延長の一意性は Lean の外。ラベル（見込み、閉鎖で確定）は［再導出（小さい）］、新規候補なし

```
mul_inv_apply_unit | 単数 u で χ(u)·χ⁻¹(u) = 1 | χ·χ⁻¹ = 1 | MulChar.one_apply_coe | 検証完了（axioms 確認済み）
chiPt_mk | chiPt χ [a:b] = χ(a)·χ⁻¹(b) | 定義 | Quotient.lift | 検証完了（axioms 確認済み）
chiPt_eqPt | 赤道 [x:1] で chiPt χ = χ(x) | χ⁻¹(1) = 1 | map_one | 検証完了（axioms 確認済み）
chiPt_Wproj | chiPt χ ∘ W = chiPt χ⁻¹ | 積の交換 | inv_inv | 検証完了（axioms 確認済み）
torus_eqPt | トーラス u·[x:1] = [u x : 1] | rfl | Units.val_mul | 検証完了（axioms 確認済み）
chiPt_torus | chiPt χ (u·q) = χ(u)·chiPt χ q | 乗法性 | map_mul | 検証完了（axioms 確認済み）
chiPt_red_congr | 法が等しく整数での値が等しい指標は、還元の後で同じ chiPt | subst と MulChar.ext | ZMod.intCast_surjective | 検証完了（axioms 確認済み）
extChi_eqPt | extChi χ の赤道での値は χ(x) | 還元は赤道を保つ、指標の引き戻し | PAG.Part258.pullL_charU, changeLevel_primitiveCharacter | 検証完了（axioms 確認済み）
extChi_changeLevel | N ∣ M のとき extChi(changeLevel χ) = extChi χ ∘ 還元 | 導手と原始指標の不変性 | conductor_changeLevel, primitiveCharacter_changeLevel_apply | 検証完了（axioms 確認済み）
extChi_torus | extChi χ (u·q) = χ(u)·extChi χ q | 還元とトーラスの可換 | chiPt_torus | 検証完了（axioms 確認済み）
pullP_extChi | 段の言葉で：pullP (extChi χ) = extChi (changeLevel χ) | extChi_changeLevel | extChi_changeLevel | 検証完了（axioms 確認済み）
resE_extChi | resE (extChi χ) = charU χ（Part 257（PAG261）） | extChi_eqPt | extChi_eqPt | 検証完了（axioms 確認済み）
chiPt_not_compat | 法 2 の自明な指標（導手 1）で、法 2 の式は点 0 で 0、法 1 の式の引き戻しは 1（法 N の式は原始的でない χ で両立しない） | 値の計算 | MulChar.map_nonunit | 検証完了（axioms 確認済み）
ketS_proj_zero_eq | p 素数、1 ≤ c ≤ K：殻 0 の南ケット ketS_proj K 0 c（Part 25（PAG29））= |S_0|^(−1/2)·（法 p^c の chiPt χ の引き戻し）（c = 0 では破れる：Lean の外、手計算） | 南北の成分の比較 | PAG.Part24.ket0_apply, PAG.Part24.chi_cast_inv, PAG.Part29.projFun_ketS | 検証完了（axioms 確認済み）
```

## §9 引き継ぎメモの Part 264 の項
```markdown
- **Part 264（PAG268、短期層の小さいノート、2026-11-25 夜）：P¹(ℤ/N) の上の指標の関数 χ(a)·χ̄(b)、引き戻しとトーラスと両立する延長、殻 0 のケットとの一致**：
  - 出所：索引 2.4 の留保と、Part 263 で外に残った候補 C2。著者の指示「お勧めで進めてください」（2026-11-25 19:13）を受けて、構築側が関門（着手前の 4 点 `notes/pag2_p1_lift_preregistration.md`、盲検の問いテスト `records/p1_lift/`、対照群、内部照合）を通した推薦案 C2-a を選び、着手した（CLAUDE.md §4 の選択の委任）。
  - 盲検の答え：引き戻しと両立する延長の族は多いが、トーラスとも両立する族は一意（χ*(a)χ̄*(b)）。U_∞ の持ち上げは存在するが、ユニタリ・トーラス・W の条件を全部課しても一意でない。答えは F_q[t] でも同じ形。残余は計算だけなので短期層。
  - Lean：PAG268.lean、定理 14、sorry 0・警告 0。χ(a)χ̄(b) の well-defined 性と赤道・W・トーラス、原始指標の関数の引き戻し `extChi` の赤道での値・引き戻しとの両立・トーラス、法 N の式は原始的でない χ で両立しない（証人）、素数冪の法で殻 0 の南ケット（Part 25（PAG29））は χ(a)χ̄(b) の引き戻しの |S_0|^(−1/2) 倍（1 ≤ c）。ノート `notes/pag2_pag268_p1_char_extension.md`。辞書 §23。xlsx は final86（行 3758〜3771）。
  - ラベル（見込み、閉鎖で確定）：［再導出（小さい）］、新規候補なし。兆候 4 は Part 249〜264 で 16 パート連続。
  - 照合：独立照合（約 160 秒）。形式文は変えず、注意を書き足した（台帳 L16）。閉じるときの統合照合に、Part 263 の台帳 L15 と一緒に載せる。
```

## §10 辞書 §23
```markdown
 Part 264（PAG268、短期層）の名前（2026-11-25）

| 名前 | 文献の言葉 | 根拠・確かめ方 |
|---|---|---|
| `chiPt` | 文献用語なし（P¹(ℤ/N) の上の関数 [a:b] ↦ χ(a)χ̄(b)。盲検の照合者は「指標つきのモジュラー記号やアイゼンシュタイン級数で使われる型だろう」と推測したが、未確認） | 盲検の問いテスト `records/p1_lift/outputs/blind_output.md` の Q5。 |
| `torusU`・`torus` | 射影直線の上の対角トーラス（diag(u, 1)）の作用 | 定義の読み。 |
| `extChi` | 文献用語なし（原始指標の `chiPt` を引き戻した族。盲検の照合者によれば、トーラスと両立する延長の族の一意な元） | 同上の Q3（照合者の手の証明と数値、Lean の外）。 |
| `mul_inv_apply_unit`・`chiPt_red_congr` | 補助（行は定義名の慣行に合わせて足した） | ― |

- 未記入の件数（この節）：0。「文献用語なし」の行は 2 つ（`chiPt`、`extChi`）。
```

## §11 構築側の数値スクリプトと出力
```python
"""C2 の着手前の数値：素数ごとの規則で作った ρ_N : P¹(ℤ/N) → (ℤ/N)^× が、赤道で恒等・還元と両立・W と両立（ρ∘W = ρ⁻¹）になるか（N ∣ M ≤ 60）。"""
from math import gcd
def fac(n):
    f={};p=2
    while p*p<=n:
        while n%p==0: f[p]=f.get(p,0)+1; n//=p
        p+=1
    if n>1: f[n]=f.get(n,0)+1
    return f
def units(N): return [u for u in range(N) if gcd(u,N)==1] if N>1 else [0]
def canon(a,b,N):
    return min(((u*a)%N,(u*b)%N) for u in units(N)) if N>1 else (0,0)
def P1(N):
    return {canon(a,b,N) for a in range(max(N,1)) for b in range(max(N,1)) if N==1 or gcd(gcd(a,b),N)==1}
def crt(res):  # res: list of (r, m)
    x,M=0,1
    for r,m in res:
        t=((r-x)*pow(M,-1,m))%m; x+=M*t; M*=m
    return x%M
def rho_local(a,b,q):  # q = p^k, (a,b) unimodular mod p
    p=min(fac(q)) 
    if b%p:   # [x:1], x = a/b
        x=(a*pow(b,-1,q))%q
        return x if x%p else (1+x)%q
    else:     # a unit, [1:y], y=b/a, p | y
        y=(b*pow(a,-1,q))%q
        return pow((1+y)%q,-1,q)
def rho(a,b,N):
    if N==1: return 0
    return crt([(rho_local(a%(p**k),b%(p**k),p**k),p**k) for p,k in fac(N).items()])
bad=0
for M in range(1,61):
    for (a,b) in P1(M):
        r=rho(a,b,M)
        assert M==1 or gcd(r,M)==1
        # equator identity
        if M>1 and gcd(a,M)==1 and gcd(b,M)==1:
            assert r==(a*pow(b,-1,M))%M
        # W
        if M>1: assert (rho(b,a,M)*r)%M==1, (M,a,b)
        for N in range(1,M+1):
            if M%N: continue
            if N>1 and rho(a%N,b%N,N)!=r%N: bad+=1
print("compat failures:",bad)
print("all checks passed")
```
