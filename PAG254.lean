/-
  PAG 2.0 Part 250（2026-11-11）— 解像度と創発の定式化の試み（アーデル射影幾何、本来の道 C）
  問いの出所：著者の選択（候補 C）。定式化は Claude の案 1・2 を著者が了承したもので、著者の定義そのものではない。
  著者の定義（解釈の層）：基礎は離散的で、直線は解像度を落としたときに創発する。解像度のパラメータは未決定。
  ここでの置き方：基礎を正の有理数の群（素数が生成する可算群）とし、「解像度の取り方」を乗法で不変な擬距離 d、
  「解像度を落とす」を歩幅 ε 未満の鎖でつながるかどうか（chainIn）で表す。ε と d は粗視化の例で、
  著者の言う解像度のパラメータと同一視しない（N・K・Λ とも同一視しない）。
  1. 正の有理数の対数の集合 logSet は、ℝ の部分集合として可算で、区間を含まず、連結な部分集合は 1 点以下。
     一方で ℝ の中で稠密
  2. 歩幅 ε の鎖 chainIn の一般論（反射、ε についての単調性、鎖の上で不変な量）
  3. 無限素点の側：擬距離 d_∞ = |log q − log r| では、どの ε > 0 でも正の有理数の任意の 2 点が鎖でつながる。
     素数 1 個の冪 {p^k} の中では ε ≤ log p の鎖は動けない。素数 2 個（2 と 3）で ℝ の中で稠密になる
  4. 素数 p の側：擬距離 d_p = |v_p(q) − v_p(r)| では、ε ≤ 1 の鎖でつながる ⇔ v_p が等しい。v_p は ℤ の上に全射。
     ε > 1 では全体がつながる
  5. まとめ（emergence_contrast）と、有限レベル（Part 249 の稠密性）との接続
  6. 追補（独立照合 B の指摘）：d_∞・d_p は log・v_p による ℝ の距離の引き戻し。2 つの側を分ける基準は
     「どの ε > 0 でも鎖でつながるか」（d_∞ は成り立ち、d_p は成り立たない）と「像が ℝ で稠密か」。
     鎖でつながる点を同一視した商は、d_∞ ではどの ε でも 1 点で、ℝ ではない。ℝ は稠密な等長像の閉包として現れる
  どれも既知の事実の組み合わせ（稠密な部分群、鎖連結性、付値）。新規性の主張はしない
-/
import PAG253
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Order.IntermediateValue

namespace PAG.Part254

/-! ### 1. 基礎：正の有理数の対数の集合 -/

/-- 正の有理数の対数の全体。 -/
def logSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}

/-- **1a.** 基礎の点は区別できる：正の有理数では log q = log r なら q = r。 -/
theorem log_inj {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (h : Real.log q = Real.log r) : q = r := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : (q : ℝ) = r := Real.log_injOn_pos (Set.mem_Ioi.mpr hq') (Set.mem_Ioi.mpr hr') h
  exact_mod_cast h2

/-- **1b.** logSet は可算。 -/
theorem logSet_countable : logSet.Countable := by
  have h : logSet ⊆ Set.range (fun q : ℚ => Real.log q) := by
    rintro x ⟨q, _, rfl⟩
    exact ⟨q, rfl⟩
  exact (Set.countable_range _).mono h

/-- **1c. logSet は区間を含まない**：a < b なら [a, b] は logSet に含まれない（e^a と e^b の間に無理数がある）。 -/
theorem not_Icc_subset_logSet {a b : ℝ} (hab : a < b) : ¬ Set.Icc a b ⊆ logSet := by
  intro h
  obtain ⟨r, hr, har, hrb⟩ := exists_irrational_btwn (Real.exp_lt_exp.mpr hab)
  have hr0 : 0 < r := lt_trans (Real.exp_pos a) har
  have h1 : a ≤ Real.log r := by
    rw [Real.le_log_iff_exp_le hr0]
    exact le_of_lt har
  have h2 : Real.log r ≤ b := by
    rw [Real.log_le_iff_le_exp hr0]
    exact le_of_lt hrb
  obtain ⟨q, hq, hqe⟩ := h ⟨h1, h2⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : r = q := Real.log_injOn_pos (Set.mem_Ioi.mpr hr0) (Set.mem_Ioi.mpr hq') hqe
  exact hr ⟨q, h3.symm⟩

/-- **1d. logSet は ℝ の中で全不連結**：logSet に含まれる連結な集合は 1 点以下。 -/
theorem subsingleton_of_isPreconnected {S : Set ℝ} (hS : IsPreconnected S) (hSL : S ⊆ logSet) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra hne
  have hord : S.OrdConnected := isPreconnected_iff_ordConnected.mp hS
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact not_Icc_subset_logSet hlt ((hord.out hx hy).trans hSL)
  · exact not_Icc_subset_logSet hlt ((hord.out hy hx).trans hSL)

/-- **1e.** logSet は ℝ の中で稠密。 -/
theorem dense_logSet : Dense logSet := by
  rw [Metric.dense_iff]
  intro x ε hε
  have h1 : Real.exp (x - ε) < Real.exp (x + ε) := Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  have hq0 : (0 : ℝ) < q := lt_trans (Real.exp_pos _) hq1
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  refine ⟨Real.log q, ?_, ⟨q, hq0', rfl⟩⟩
  have h2 : x - ε < Real.log q := by
    rw [Real.lt_log_iff_exp_lt hq0]
    exact hq1
  have h3 : Real.log q < x + ε := by
    rw [Real.log_lt_iff_lt_exp hq0]
    exact hq2
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### 2. 歩幅 ε の鎖 -/

/-- S の中の、d で測った歩幅が ε 未満の鎖で x と y がつながる。 -/
def chainIn {α : Type*} (S : Set α) (d : α → α → ℝ) (ε : ℝ) (x y : α) : Prop :=
  ∃ (n : ℕ) (c : ℕ → α), c 0 = x ∧ c n = y ∧ (∀ i, i ≤ n → c i ∈ S) ∧ ∀ i, i < n → d (c i) (c (i + 1)) < ε

/-- **2a.** 鎖の反射性。 -/
theorem chainIn_refl {α : Type*} {S : Set α} (d : α → α → ℝ) (ε : ℝ) {x : α} (hx : x ∈ S) :
    chainIn S d ε x x :=
  ⟨0, fun _ => x, rfl, rfl, fun _ _ => hx, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- **2b. ε についての単調性**（解釈：解像度を落とすと、つながりは増える）：ε ≤ ε′ なら、歩幅 ε の鎖は歩幅 ε′ の鎖でもある。 -/
theorem chainIn_mono {α : Type*} {S : Set α} {d : α → α → ℝ} {ε ε' : ℝ} (h : ε ≤ ε') {x y : α}
    (hc : chainIn S d ε x y) : chainIn S d ε' x y := by
  obtain ⟨n, c, h0, hn, hS, hd⟩ := hc
  exact ⟨n, c, h0, hn, hS, fun i hi => lt_of_lt_of_le (hd i hi) h⟩

/-- **2c.** d(x, y) < ε なら 1 歩の鎖でつながる。 -/
theorem chainIn_of_lt {α : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (h : d x y < ε) : chainIn S d ε x y := by
  refine ⟨1, fun i => if i = 0 then x else y, by simp, by simp, ?_, ?_⟩
  · intro i _
    by_cases hi : i = 0
    · simp [hi, hx]
    · simp [hi, hy]
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using h

/-- **2d. 鎖の上で不変な量**：歩幅 ε 未満の 2 点で f が等しいなら、鎖の両端で f は等しい。 -/
theorem chainIn_invariant {α β : Type*} {S : Set α} {d : α → α → ℝ} {ε : ℝ} (f : α → β)
    (hf : ∀ x y, x ∈ S → y ∈ S → d x y < ε → f x = f y) {x y : α} (hc : chainIn S d ε x y) :
    f x = f y := by
  obtain ⟨n, c, h0, hn, hS, hd⟩ := hc
  have key : ∀ i, i ≤ n → f (c i) = f x := by
    intro i
    induction i with
    | zero => intro _; rw [h0]
    | succ j ih =>
      intro hj
      have h1 := hf (c j) (c (j + 1)) (hS j (by omega)) (hS (j + 1) hj) (hd j (by omega))
      rw [← h1]
      exact ih (by omega)
  rw [← hn]
  exact (key n le_rfl).symm

/-! ### 3. 無限素点の側 -/

/-- 正の有理数の集合。 -/
def posRat : Set ℚ := {q | 0 < q}

/-- 無限素点の擬距離 |log q − log r|。 -/
noncomputable def dInf (q r : ℚ) : ℝ := |Real.log q - Real.log r|

/-- **3a.** d_∞ は正の有理数の乗法で不変。 -/
theorem dInf_mul_left {s q r : ℚ} (hs : 0 < s) (hq : 0 < q) (hr : 0 < r) :
    dInf (s * q) (s * r) = dInf q r := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold dInf
  rw [Rat.cast_mul, Rat.cast_mul, Real.log_mul hs' hq', Real.log_mul hs' hr']
  congr 1
  ring

/-- 補題：m ≤ x, y（m > 0）なら |log x − log y| ≤ |x − y| / m。 -/
theorem abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx0 : 0 < x := lt_of_lt_of_le hm hx
  have hy0 : 0 < y := lt_of_lt_of_le hm hy
  have key : ∀ {u v : ℝ}, 0 < u → m ≤ v → Real.log u - Real.log v ≤ |u - v| / m := by
    intro u v hu hv
    have hv0 : 0 < v := lt_of_lt_of_le hm hv
    have h1 : Real.log u - Real.log v = Real.log (u / v) := (Real.log_div hu.ne' hv0.ne').symm
    have h2 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hu hv0)
    have h3 : u / v - 1 = (u - v) / v := by field_simp
    rw [h1]
    refine le_trans h2 ?_
    rw [h3]
    by_cases huv : u ≤ v
    · have h4 : (u - v) / v ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hv0.le
      exact le_trans h4 (div_nonneg (abs_nonneg _) hm.le)
    · have h5 : 0 ≤ u - v := by linarith
      rw [abs_of_nonneg h5]
      exact div_le_div_of_nonneg_left h5 hm hv
  rw [abs_le]
  constructor
  · have := key hy0 hx
    rw [abs_sub_comm] at this
    linarith
  · exact key hx0 hy

/-- **3b. 無限素点の側は well-chained**：どの ε > 0 でも、正の有理数の任意の 2 点は d_∞ の歩幅 ε 未満の鎖でつながる
（q と r を結ぶ線分の等分点を通る）。 -/
theorem chainIn_dInf {ε : ℝ} (hε : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat dInf ε q r := by
  set m : ℚ := min q r with hm
  have hm0 : 0 < m := lt_min hq hr
  have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
  obtain ⟨n, hn⟩ := exists_nat_gt (|(r : ℝ) - q| / (m * ε))
  have hn0 : (0 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
  have hn1 : |(r : ℝ) - q| / (m * ε) < (n + 1 : ℕ) := by
    push_cast
    linarith
  set c : ℕ → ℚ := fun i => q + (i : ℚ) * ((r - q) / (n + 1 : ℕ)) with hc
  have hnq : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hcm : ∀ i, i ≤ n + 1 → m ≤ c i := by
    intro i hi
    have hi' : (i : ℚ) ≤ (n + 1 : ℕ) := by exact_mod_cast hi
    have ht0 : (0 : ℚ) ≤ (i : ℚ) / (n + 1 : ℕ) := by positivity
    have ht1 : (i : ℚ) / (n + 1 : ℕ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast Nat.succ_pos n)]
      exact hi'
    have hci : c i = (1 - (i : ℚ) / (n + 1 : ℕ)) * q + ((i : ℚ) / (n + 1 : ℕ)) * r := by
      simp only [hc]
      field_simp
      ring
    rw [hci]
    have hmq : m ≤ q := min_le_left q r
    have hmr : m ≤ r := min_le_right q r
    nlinarith
  refine ⟨n + 1, c, ?_, ?_, ?_, ?_⟩
  · simp [hc]
  · simp only [hc]
    field_simp
    ring
  · intro i hi
    exact lt_of_lt_of_le hm0 (hcm i hi)
  · intro i hi
    have h1 : (m : ℝ) ≤ c i := by exact_mod_cast hcm i (by omega)
    have h2 : (m : ℝ) ≤ c (i + 1) := by exact_mod_cast hcm (i + 1) (by omega)
    have h3 := abs_log_sub_log_le hm0' h1 h2
    have h4 : (c i : ℝ) - c (i + 1) = -(((r : ℝ) - q) / (n + 1 : ℕ)) := by
      simp only [hc]
      push_cast
      ring
    unfold dInf
    refine lt_of_le_of_lt h3 ?_
    rw [h4, abs_neg, abs_div, abs_of_pos hn0, div_div, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn1
    linarith

/-- 1 つの素数 p の冪の集合 {p^k : k ∈ ℤ}。 -/
def primePow (p : ℕ) : Set ℚ := {q | ∃ k : ℤ, q = (p : ℚ) ^ k}

/-- 補題：d_∞(p^a, p^b) = |a − b|·|log p|。 -/
theorem dInf_zpow {p : ℕ} (a b : ℤ) :
    dInf ((p : ℚ) ^ a) ((p : ℚ) ^ b) = |((a - b : ℤ) : ℝ)| * |Real.log p| := by
  unfold dInf
  rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_natCast, Real.log_zpow, Real.log_zpow, ← sub_mul, abs_mul]
  push_cast
  rfl

/-- **3c. {p^k} は ε ≤ log p で動けない**：p ≥ 2、ε ≤ log p なら、{p^k} の中の d_∞ の歩幅 ε 未満の鎖は動けない。 -/
theorem eq_of_chainIn_primePow {p : ℕ} (hp : 2 ≤ p) {ε : ℝ} (hε : ε ≤ Real.log p) {x y : ℚ}
    (hc : chainIn (primePow p) dInf ε x y) : x = y := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log p := Real.log_pos hp1
  refine chainIn_invariant (fun q => q) ?_ hc
  rintro u v ⟨a, rfl⟩ ⟨b, rfl⟩ hd
  rw [dInf_zpow, abs_of_pos hlog] at hd
  have h1 : |((a - b : ℤ) : ℝ)| < 1 := by
    by_contra hcon
    have h2 : (1 : ℝ) ≤ |((a - b : ℤ) : ℝ)| := not_lt.mp hcon
    nlinarith
  have h3 : |a - b| < 1 := by
    have : ((|a - b| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]
      exact h1
    exact_mod_cast this
  have h4 : a - b = 0 := Int.abs_lt_one_iff.mp h3
  have h5 : a = b := by omega
  rw [h5]

/-- **3d. log 2 と log 3 で稠密**：log 2 と log 3 が生成する加法群は ℝ の中で稠密（最小の正の元があれば 2^K = 3^M となり矛盾）。 -/
theorem dense_closure_log_two_three :
    Dense ((AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) : AddSubgroup ℝ) : Set ℝ) := by
  set S : AddSubgroup ℝ := AddSubgroup.closure ({Real.log 2, Real.log 3} : Set ℝ) with hS
  have h2S : Real.log 2 ∈ S := AddSubgroup.subset_closure (by simp)
  have h3S : Real.log 3 ∈ S := AddSubgroup.subset_closure (by simp)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hbot : S ≠ ⊥ := by
    intro h
    rw [h, AddSubgroup.mem_bot] at h2S
    exact hl2.ne' h2S
  refine AddSubgroup.dense_of_no_min S hbot ?_
  rintro ⟨a, ⟨haS, ha0⟩, hmin⟩
  have key : ∀ g, g ∈ S → ∃ k : ℤ, g = k * a := by
    intro g hg
    refine ⟨⌊g / a⌋, ?_⟩
    have hr : g - (⌊g / a⌋ : ℝ) * a ∈ S := by
      have := S.sub_mem hg (S.zsmul_mem haS ⌊g / a⌋)
      rwa [zsmul_eq_mul] at this
    have h1 : (⌊g / a⌋ : ℝ) ≤ g / a := Int.floor_le _
    have h2 : g / a < ⌊g / a⌋ + 1 := Int.lt_floor_add_one _
    rw [le_div_iff₀ ha0] at h1
    rw [div_lt_iff₀ ha0] at h2
    by_contra hne
    have hpos : 0 < g - (⌊g / a⌋ : ℝ) * a := by
      rcases lt_or_eq_of_le (sub_nonneg.mpr h1) with h | h
      · exact h
      · exact absurd (by linarith) hne
    have := hmin ⟨hr, hpos⟩
    linarith
  obtain ⟨m, hm⟩ := key _ h2S
  obtain ⟨n, hn⟩ := key _ h3S
  have hm0 : 0 < m := by
    have : (0 : ℝ) < m := by
      by_contra hcon
      have : (m : ℝ) * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) ha0.le
      linarith
    exact_mod_cast this
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := by
      by_contra hcon
      have : (n : ℝ) * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) ha0.le
      linarith
    exact_mod_cast this
  obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hm0.le
  obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hn0.le
  have hM : 0 < M := by exact_mod_cast hm0
  have hK : 0 < K := by exact_mod_cast hn0
  have heq : (K : ℝ) * Real.log 2 = (M : ℝ) * Real.log 3 := by
    rw [hm, hn]
    push_cast
    ring
  have hpow : ((2 : ℝ) ^ K) = (3 : ℝ) ^ M := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow]
    exact heq
  have hnat : 2 ^ K = 3 ^ M := by exact_mod_cast hpow
  have hdvd : 2 ∣ 3 ^ M := by
    rw [← hnat]
    exact dvd_pow_self 2 hK.ne'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd
  omega

/-! ### 4. 素数 p の側 -/

/-- 素数 p の側の擬距離 |v_p(q) − v_p(r)|。 -/
noncomputable def dP (p : ℕ) (q r : ℚ) : ℝ := |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|

/-- **4a.** d_p は 0 でない有理数の乗法で不変。 -/
theorem dP_mul_left (p : ℕ) [Fact p.Prime] {s q r : ℚ} (hs : s ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    dP p (s * q) (s * r) = dP p q r := by
  unfold dP
  rw [padicValRat.mul hs hq, padicValRat.mul hs hr]
  congr 2
  ring

/-- **4b.** d_p(q, r) < 1 ⇔ v_p(q) = v_p(r)（d_p は整数値）。 -/
theorem dP_lt_one_iff (p : ℕ) (q r : ℚ) : dP p q r < 1 ↔ padicValRat p q = padicValRat p r := by
  unfold dP
  constructor
  · intro h
    have h3 : |padicValRat p q - padicValRat p r| < 1 := by
      have : ((|padicValRat p q - padicValRat p r| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]
        exact h
      exact_mod_cast this
    have h4 := Int.abs_lt_one_iff.mp h3
    omega
  · intro h
    rw [h, sub_self]
    simp

/-- **4c. ε ≤ 1 では v_p は鎖の不変量**：ε ≤ 1 なら、d_p の歩幅 ε 未満の鎖の両端で v_p は等しい。 -/
theorem padicValRat_eq_of_chainIn (p : ℕ) {ε : ℝ} (hε : ε ≤ 1) {q r : ℚ}
    (hc : chainIn posRat (dP p) ε q r) : padicValRat p q = padicValRat p r :=
  chainIn_invariant (fun x => padicValRat p x)
    (fun x y _ _ hd => (dP_lt_one_iff p x y).mp (lt_of_lt_of_le hd hε)) hc

/-- **4d.** 0 < ε ≤ 1 なら、正の有理数 q, r が d_p の鎖でつながる ⇔ v_p(q) = v_p(r)。 -/
theorem chainIn_dP_iff (p : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ padicValRat p q = padicValRat p r := by
  constructor
  · exact padicValRat_eq_of_chainIn p hε
  · intro h
    refine chainIn_of_lt hq hr ?_
    unfold dP
    rw [h, sub_self]
    simpa using hε0

/-- **4e.** v_p は正の有理数から ℤ の上に全射。 -/
theorem exists_padicValRat_eq (p : ℕ) [hp : Fact p.Prime] (k : ℤ) :
    ∃ q : ℚ, 0 < q ∧ padicValRat p q = k := by
  refine ⟨(p : ℚ) ^ k, ?_, ?_⟩
  · have : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
    positivity
  · rw [padicValRat.zpow, padicValRat.self hp.out.one_lt, mul_one]

/-- **4f.** ε > 1 なら、d_p ではすべての正の有理数が鎖でつながる（p 倍の 1 歩は d_p = 1 < ε）。
2026-11-11 の独立照合で、5a の対比が ε = 1 に固定されていると指摘されて足した。 -/
theorem chainIn_dP_of_one_lt (p : ℕ) [hp : Fact p.Prime] {ε : ℝ} (hε : 1 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hpne : (p : ℚ) ≠ 0 := hp0.ne'
  set δ : ℤ := padicValRat p r - padicValRat p q with hδ
  set s : ℤ := Int.sign δ with hs
  set k : ℕ := Int.natAbs δ with hk
  have hsk : s * (k : ℤ) = δ := Int.sign_mul_natAbs δ
  have hs1 : |s| ≤ 1 := by
    rcases lt_trichotomy δ 0 with h | h | h
    · rw [hs, Int.sign_eq_neg_one_of_neg h]; simp
    · rw [hs, h]; simp
    · rw [hs, Int.sign_eq_one_of_pos h]; simp
  have hv : ∀ i : ℕ, padicValRat p (q * (p : ℚ) ^ (s * (i : ℤ))) = padicValRat p q + s * i := by
    intro i
    rw [padicValRat.mul hq.ne' (zpow_ne_zero _ hpne), padicValRat.zpow, padicValRat.self hp.out.one_lt, mul_one]
  refine ⟨k + 1, fun i => if i ≤ k then q * (p : ℚ) ^ (s * (i : ℤ)) else r, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro i _
    by_cases hi : i ≤ k
    · simp only [hi, ite_true]
      exact mul_pos hq (zpow_pos hp0 _)
    · simp only [hi, ite_false]
      exact hr
  · intro i hi
    by_cases hik : i < k
    · have h1 : i ≤ k := by omega
      have h2 : i + 1 ≤ k := by omega
      simp only [h1, h2, ite_true]
      unfold dP
      rw [hv i, hv (i + 1)]
      have h3 : padicValRat p q + s * (i : ℤ) - (padicValRat p q + s * ((i + 1 : ℕ) : ℤ)) = -s := by
        push_cast
        ring
      rw [h3, Int.cast_neg, abs_neg]
      have h4 : |(s : ℝ)| ≤ 1 := by
        have : ((|s| : ℤ) : ℝ) ≤ 1 := by exact_mod_cast hs1
        rwa [Int.cast_abs] at this
      linarith
    · have h1 : i = k := by omega
      subst h1
      have h2 : ¬ (k + 1 ≤ k) := by omega
      simp only [le_refl, h2, ite_true, ite_false]
      unfold dP
      rw [hv k, hsk, hδ]
      have h3 : padicValRat p q + (padicValRat p r - padicValRat p q) - padicValRat p r = 0 := by ring
      rw [h3]
      simp
      linarith

/-- **4g. 素数 p の側の分類**：ε > 0 のとき、d_p の鎖でつながる ⇔（ε ≤ 1 ならば v_p が等しい）。
帰結（Lean の文ではない）：鎖の成分は、0 < ε ≤ 1 では v_p の値ごと、ε > 1 では 1 つ。 -/
theorem chainIn_dP_classification (p : ℕ) [Fact p.Prime] {ε : ℝ} (hε0 : 0 < ε) {q r : ℚ} (hq : 0 < q) (hr : 0 < r) :
    chainIn posRat (dP p) ε q r ↔ (ε ≤ 1 → padicValRat p q = padicValRat p r) := by
  constructor
  · intro hc hε
    exact padicValRat_eq_of_chainIn p hε hc
  · intro h
    by_cases hε : ε ≤ 1
    · exact (chainIn_dP_iff p hε0 hε hq hr).mpr (h hε)
    · exact chainIn_dP_of_one_lt p (not_le.mp hε) hq hr

/-! ### 5. まとめ -/

/-- **5a. ε = 1 での対比**（名前は内容より強い）：d_∞ ではどの ε > 0 でもすべての 2 点が鎖でつながるが、どの素数 p でも d_p の歩幅 1 未満の鎖は
1 と p をつながない（ε = 1 での対比。ε > 1 では d_p でも全体がつながる：4f・4g）。 -/
theorem emergence_contrast :
    (∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat dInf ε q r) ∧
    (∀ p : ℕ, p.Prime → ¬ chainIn posRat (dP p) 1 1 (p : ℚ)) := by
  refine ⟨fun ε hε q r hq hr => chainIn_dInf hε hq hr, fun p hp hc => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have h := padicValRat_eq_of_chainIn p le_rfl hc
  rw [padicValRat.one, padicValRat.self hp.one_lt] at h
  exact zero_ne_one h

/-- **5b. 有限レベルとの接続**：N と互いに素な正の整数 m, n だけでも log n − log m は ℝ の中で稠密
（Part 249 の `exists_cls_near` から）。 -/
theorem dense_logSet_coprime {N : ℕ} [NeZero N] (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ m.Coprime N ∧ n.Coprime N ∧ |Real.log n - Real.log m - t| < ε := by
  obtain ⟨m, n, hm, hn, hm0, hn0, _, h⟩ := PAG.Part253.exists_cls_near (1 : (ZMod N)ˣ) t hε
  exact ⟨m, n, hm0, hn0, hm, hn, h⟩

/-! ### 6. 追補（2026-11-11、独立照合 B の指摘）：等長な埋め込みと、2 つの側を分ける基準 -/

/-- **6a.** d_∞ は log による ℝ の距離の引き戻し：d_∞(q, r) = dist(log q, log r)。1e と合わせると、
(正の有理数, d_∞) は ℝ の稠密な部分集合と等長（完備化が ℝ であること自体は Lean にしていない）。 -/
theorem dInf_eq_dist (q r : ℚ) : dInf q r = dist (Real.log q) (Real.log r) := by
  unfold dInf
  rw [Real.dist_eq]

/-- **6b.** d_p は v_p による ℝ の距離の引き戻し：d_p(q, r) = dist(v_p(q), v_p(r))。 -/
theorem dP_eq_dist (p : ℕ) (q r : ℚ) :
    dP p q r = dist ((padicValRat p q : ℤ) : ℝ) ((padicValRat p r : ℤ) : ℝ) := by
  unfold dP
  rw [Real.dist_eq]
  push_cast
  rfl

/-- **6c.** v_p の像は ℝ で稠密でない：どの q でも |v_p(q) − 1/2| ≥ 1/2（像は ℤ の中にある）。 -/
theorem half_le_abs_padicValRat_sub_half (p : ℕ) (q : ℚ) :
    (1 / 2 : ℝ) ≤ |((padicValRat p q : ℤ) : ℝ) - 1 / 2| := by
  rcases le_or_gt (padicValRat p q) 0 with h | h
  · have h' : ((padicValRat p q : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h
    have := neg_le_abs (((padicValRat p q : ℤ) : ℝ) - 1 / 2)
    linarith
  · have h1 : (1 : ℤ) ≤ padicValRat p q := h
    have h' : (1 : ℝ) ≤ ((padicValRat p q : ℤ) : ℝ) := by exact_mod_cast h1
    have := le_abs_self (((padicValRat p q : ℤ) : ℝ) - 1 / 2)
    linarith

/-- **6d. 2 つの側を分ける基準**：素数 p では、「どの ε > 0 でもすべての 2 点が d_p の鎖でつながる」は成り立たない
（d_∞ では成り立つ：3b）。 -/
theorem not_forall_chainIn_dP (p : ℕ) (hp : p.Prime) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ q r : ℚ, 0 < q → 0 < r → chainIn posRat (dP p) ε q r := by
  intro h
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  exact emergence_contrast.2 p hp (h 1 one_pos 1 p one_pos hp0)

end PAG.Part254

#print axioms PAG.Part254.logSet
#print axioms PAG.Part254.log_inj
#print axioms PAG.Part254.logSet_countable
#print axioms PAG.Part254.not_Icc_subset_logSet
#print axioms PAG.Part254.subsingleton_of_isPreconnected
#print axioms PAG.Part254.dense_logSet
#print axioms PAG.Part254.chainIn
#print axioms PAG.Part254.chainIn_refl
#print axioms PAG.Part254.chainIn_mono
#print axioms PAG.Part254.chainIn_of_lt
#print axioms PAG.Part254.chainIn_invariant
#print axioms PAG.Part254.posRat
#print axioms PAG.Part254.dInf
#print axioms PAG.Part254.dInf_mul_left
#print axioms PAG.Part254.abs_log_sub_log_le
#print axioms PAG.Part254.chainIn_dInf
#print axioms PAG.Part254.primePow
#print axioms PAG.Part254.dInf_zpow
#print axioms PAG.Part254.eq_of_chainIn_primePow
#print axioms PAG.Part254.dense_closure_log_two_three
#print axioms PAG.Part254.dP
#print axioms PAG.Part254.dP_mul_left
#print axioms PAG.Part254.dP_lt_one_iff
#print axioms PAG.Part254.padicValRat_eq_of_chainIn
#print axioms PAG.Part254.chainIn_dP_iff
#print axioms PAG.Part254.exists_padicValRat_eq
#print axioms PAG.Part254.chainIn_dP_of_one_lt
#print axioms PAG.Part254.chainIn_dP_classification
#print axioms PAG.Part254.emergence_contrast
#print axioms PAG.Part254.dense_logSet_coprime
#print axioms PAG.Part254.dInf_eq_dist
#print axioms PAG.Part254.dP_eq_dist
#print axioms PAG.Part254.half_le_abs_padicValRat_sub_half
#print axioms PAG.Part254.not_forall_chainIn_dP
