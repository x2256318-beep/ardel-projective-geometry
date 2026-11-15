/-
アーデル射影幾何 — Part 257（PAG 2.0）：互いに素な法の並びの指標の積での、ガウス和と W の分解（すべての成分の局所因子の積）

問いの出所：著者の選択（2026-11-14 20:59、着手前の文書 `pag2_part257_preregistration.md` の候補 P1）。開始条件 2（方向βの
登録ファイルとの突き合わせ）は、著者の判断で保留のまま始めた（登録ファイルは届いていない）。
幾何の言葉での問い（読み）：大域の貼り合わせ（U の固有値 W）は、∞ を含む各点の局所の因子の積に分かれるか。
Lean が答えるのは、互いに素な法の並び N_1, …, N_k の指標の積（法 N_1·…·N_k）の上での、ガウス和 τ と W の式まで。

読みの言葉：「貼り合わせ U」「公準 A1 の位相」は Part 254（PAG258.lean）の `UA1`・`phaseA1`。W は Part 252（PAG256.lean）の
`rootNum`（= τ(χ)/(i^a·√n)。原始のときルート数）、偶奇の因子 `parFac`（偶で 1、奇で −i）。「素点」「局所因子」「重なり」は
著者の解釈の層の言葉で、Lean の文には出てこない。偶奇の因子が無限素点の局所因子にあたる、も読み。

Lean の文（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6 を繰り返したものと、そのルート数版）：
1. 法の並びの積 `lvl`（先頭 × 残り）と指標の積 `listChar`（先頭の指標と残りの積を Part 256 の `prodChar` でつなぐ）。
   値は成分の値の積（`listChar_natCast`：自然数で、`listChar_neg_one`：−1 で）。
2. ガウス和：τ(listChar χ l) = 交差項·∏_i τ(χ_i)（`gaussSum_listChar`。法は互いに素。原始性は要らない）。交差項 `cross` は
   漸化式で定め、閉じた形が 2 つ：形 (I) ∏_i χ_i(∏_{j≠i} N_j)（`cross_eq_formI`）と形 (II) ∏_i ∏_{j≠i} χ_j(N_i)
   （`cross_eq_formII`。成分 i の因子を、ほかの成分を N_i で読んだ値で書く形）。
3. W：W(listChar χ l) = ε_∞·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i（`rootNum_listChar_formI`）、
   = ε_∞·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)（`rootNum_listChar_formII`）。ε_∞ = `parFac`(listChar χ l)。
4. ∞ の因子の符号：ε_∞(listChar χ l) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数 `oddCount`。`parFac_listChar`）。
   したがって W(listChar χ l) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（`rootNum_listChar`。Part 256 の `rootNum_prodChar` の、
   成分 2 つから任意個への一般化）。
5. 原始性：すべての成分が原始 ⇔ 積が原始（`isPrimitive_listChar_iff`）。原始なら UA1 の固有値 phaseA1 も同じ式
   （`phaseA1_listChar`）。
6. 分解：法 lvl l の指標は、どれも成分の積 listChar χ l の形に書け（`exists_listChar`。並びに重複なし）、成分は一意
   （`listChar_injective`）。
7. すべての素数への分解：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)}（`ppow`）の成分 χ_p で、自然数での値が ∏_p χ_p(x)、
   τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（`gaussSum_primeFactors`。形 (II)）。退化例（成分 1 つ）は τ(listChar χ [a]) = τ(χ_a)
   （`gaussSum_listChar_singleton`）。

前の鎖の定理を使い、示し直していないもの：Part 189（PAG193）の `gaussSum_mul_coprime`・`mul_changeLevel_apply`、
Part 190（PAG194）の `decomp`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul`、Part 232（PAG236）の `charMul_injective`、
Part 252（PAG256）の `rootNum_eq`・`parFac_of_even`、Part 254（PAG258）の `phaseA1_of_isPrimitive`、Part 256（PAG260）の
`prodChar`・`prodChar_neg_one`・`parFac_prodChar`・`crossSign`。

言い方の注意：文献では、大域の ε 因子は局所の ε 因子の積（Tate、Deligne）。形 (II) の成分 i の因子 (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i) は、
加法指標を ψ_∞ = e^{−2πix}・ψ_p = e^{2πi{x}_p}（Tate の学位論文の規約）にとったときのイデール類指標の局所定数と一致し、
∞ の因子は i^{−a}（盲検の問いテストと私の手計算。Lean では示していない）。規約を逆にすると各因子が χ_p(−1) 倍、
∞ の因子が i^{a} になるが、積は変わらない。A1 は公準のまま。ここでの文は τ・W・phaseA1 についての恒等式で、A1 から何かを出すものではない。

範囲：互いに素な法の並び（リスト）の上の式。法 n の任意の指標についての文は 7 のガウス和と分解まで（W の形は、listChar の形の
指標の上で 3・4）。Lean にしていないこと（数値は step280.py の項目番号）：イデール類指標と Tate の局所定数そのもの、
原始でない指標の phaseA1 を導手を割る素点だけで書く形（着手前の数値 (5)）、並べ替えで listChar の値が変わらないこと
（数値 (10)）、対照群 F_q[t]（∞ の因子は √q/τ(η)。盲検の答えで、私は計算していない）。

内部照合（2026-11-14 からの必須の手順）：着手の前に、xlsx の「定理と証明」と Lean の全宣言の文を検索した。成分 2 つの式は
前の鎖にある（Part 189 の `gaussSum_mul_coprime`・`z_mul_coprime`、Part 256 の `rootNum_prodChar`）。任意個の成分の明示の積、
形 (II)、符号 (−1)^{k(k−1)/2} の文は見つからなかった（網羅ではない）。近いもの：Part 192（PAG196）の `z_hall`（ホール成分 2 つ、
ずれは「1 の冪根がある」の形）、Part 193（PAG197）の `LocalCrit`・`prod_root_iff_local`（平方因子のない素数成分での、1 の冪根に
なる条件）、Part 127（PAG131）以降の素数冪の成分の積の位数の定理（積 ∏ τ(χ_i)/√ の位数で、合成した指標の τ ではない）。
パートを閉じる前の照合の結果は、このパートのノート §（内部照合）に書く。
-/
import PAG260

open ZMod Complex

namespace PAG.Part261

variable {ι : Type*} (N : ι → ℕ) [hN : ∀ i, NeZero (N i)]

/-- 法の並びの積（先頭 × 残りの積）。 -/
def lvl : List ι → ℕ
  | [] => 1
  | a :: l => N a * lvl l

omit hN in
theorem lvl_cons (a : ι) (l : List ι) : lvl N (a :: l) = N a * lvl N l := rfl

omit hN in
theorem lvl_eq_prod (l : List ι) : lvl N l = (l.map N).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lvl, ih]

instance lvl_neZero (l : List ι) : NeZero (lvl N l) := ⟨by
  induction l with
  | nil => simp [lvl]
  | cons a l ih => exact mul_ne_zero (NeZero.ne (N a)) ih⟩

variable {N}

/-- 法の並びの指標の積（法 lvl l）。先頭の指標と残りの積を、Part 256 の `prodChar` でつなぐ。 -/
noncomputable def listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) :
    (l : List ι) → DirichletCharacter ℂ (lvl N l)
  | [] => 1
  | a :: l => PAG.Part260.prodChar (χ a) (listChar χ l)

/-- 交差項（漸化式）。 -/
noncomputable def cross (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℂ
  | [] => 1
  | a :: l => χ a (lvl N l : ZMod (N a)) * listChar χ l (N a : ZMod (lvl N l)) * cross χ l

omit hN in
theorem coprime_lvl {a : ι} {l : List ι} (h : ∀ j ∈ l, (N a).Coprime (N j)) :
    (N a).Coprime (lvl N l) := by
  induction l with
  | nil => simp [lvl]
  | cons b l ih =>
    rw [lvl_cons]
    exact Nat.Coprime.mul_right (h b (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem gaussSum_level_one (χ : DirichletCharacter ℂ 1) : gaussSum χ (stdAddChar (N := 1)) = 1 := by
  rw [gaussSum, Finset.sum_eq_single (1 : ZMod 1)]
  · rw [map_one, (by decide : (1 : ZMod 1) = 0), AddChar.map_zero_eq_one, mul_one]
  · intro b _ hb; exact absurd (Subsingleton.elim b 1) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **ガウス和の分解（漸化式の形）**。 -/
theorem gaussSum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    gaussSum (listChar χ l) stdAddChar =
      cross χ l * (l.map fun i => gaussSum (χ i) stdAddChar).prod := by
  induction l with
  | nil =>
    show gaussSum (1 : DirichletCharacter ℂ 1) stdAddChar = 1 * 1
    rw [gaussSum_level_one]; ring
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h : gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _ :=
      PAG.Part193.gaussSum_mul_coprime (coprime_lvl hl.1) (χ a) (listChar χ l)
    show gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _
    rw [h, ih hl.2]
    simp only [cross, List.map_cons, List.prod_cons]
    ring

theorem listChar_natCast (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (n : ℕ) :
    listChar χ l (n : ZMod (lvl N l)) = (l.map fun j => χ j (n : ZMod (N j))).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  | cons a l ih =>
    have h : PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _ :=
      PAG.Part193.mul_changeLevel_apply (χ a) (listChar χ l) (n : ZMod (N a * lvl N l))
    show PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _
    rw [h, ZMod.castHom_apply, ZMod.castHom_apply,
      ZMod.cast_natCast (dvd_mul_right _ _), ZMod.cast_natCast (dvd_mul_left _ _), ih]
    simp

theorem listChar_neg_one (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (l.map fun j => χ j (-1)).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact MulChar.one_apply isUnit_one.neg
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) (-1) = _
    rw [PAG.Part260.prodChar_neg_one, ih]
    simp

variable [DecidableEq ι]

/-- 交差項の形 (I)：∏_i χ_i(∏_{j≠i} N_j)。 -/
theorem cross_eq_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i))).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => χ i ((((a :: l).erase i).map N).prod : ZMod (N i))) =
        l.map fun i => χ i (N a : ZMod (N i)) * χ i (((l.erase i).map N).prod : ZMod (N i)) := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons, Nat.cast_mul,
        map_mul]
    rw [key, List.prod_map_mul]
    ring

/-- 交差項の形 (II)：∏_i ∏_{j≠i} χ_j(N_i)。 -/
theorem cross_eq_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => (((a :: l).erase i).map fun j => χ j (N i : ZMod (N j))).prod) =
        l.map fun i => χ a (N i : ZMod (N a)) *
          ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons]
    have hprod : χ a (((l.map N).prod : ℕ) : ZMod (N a)) =
        (l.map fun i => χ a (N i : ZMod (N a))).prod := by
      rw [Nat.cast_list_prod, map_list_prod, List.map_map, List.map_map]
      rfl
    rw [key, List.prod_map_mul, hprod]
    ring

omit hN [DecidableEq ι] in
theorem sqrt_lvl (l : List ι) :
    ((Real.sqrt (lvl N l) : ℝ) : ℂ) = (l.map fun i => ((Real.sqrt (N i) : ℝ) : ℂ)).prod := by
  induction l with
  | nil => simp [lvl]
  | cons a l ih =>
    rw [lvl_cons, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, ih]
    simp

omit hN [DecidableEq ι] in
theorem prod_map_div' {f g : ι → ℂ} (l : List ι) :
    (l.map fun i => f i / g i).prod = (l.map f).prod / (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, div_mul_div_comm]

/-- **W の分解（形 (II)）**：W(χ) = ε_∞(χ)·∏_i (τ(χ_i)/√N_i)·∏_{j≠i} χ_j(N_i)。 -/
theorem rootNum_listChar_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ) *
        ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formII χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

/-- **W の分解（形 (I)）**：W(χ) = ε_∞(χ)·∏_i χ_i(∏_{j≠i} N_j)·τ(χ_i)/√N_i。 -/
theorem rootNum_listChar_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i)) *
        (gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ))).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formI χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

omit [DecidableEq ι] in
open Classical in
/-- 奇の成分の個数。 -/
noncomputable def oddCount (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℕ
  | [] => 0
  | a :: l => (if (χ a).Odd then 1 else 0) + oddCount χ l

omit hN [DecidableEq ι] in
theorem not_odd_of_even {n : ℕ} {ψ : DirichletCharacter ℂ n} (h : ψ.Even) : ¬ψ.Odd := by
  intro h'
  unfold DirichletCharacter.Odd at h'; unfold DirichletCharacter.Even at h
  rw [h] at h'; norm_num at h'

omit [DecidableEq ι] in
theorem listChar_neg_one_pow (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (-1) ^ oddCount χ l := by
  rw [listChar_neg_one]
  induction l with
  | nil => simp [oddCount]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, oddCount, ih, pow_add]
    rcases (χ a).even_or_odd with h | h
    · have hn := not_odd_of_even h
      unfold DirichletCharacter.Even at h
      simp [hn, h]
    · have h' := h
      unfold DirichletCharacter.Odd at h'
      simp [h, h']

omit hN in
theorem tri_succ (k : ℕ) : (1 + k) * (1 + k - 1) / 2 = k * (k - 1) / 2 + k := by
  rcases k with _ | m
  · simp
  · have e : (1 + (m + 1)) * (1 + (m + 1) - 1) = (m + 1) * (m + 1 - 1) + (m + 1) * 2 := by
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num)]

omit [DecidableEq ι] in
/-- **∞ の因子の符号**：ε_∞(χ) = (−1)^{k(k−1)/2}·∏_i ε_∞(χ_i)（k は奇の成分の数。Part 256 の s の一般化）。 -/
theorem parFac_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    PAG.Part256.parFac (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) *
        (l.map fun i => PAG.Part256.parFac (χ i)).prod := by
  induction l with
  | nil =>
    show PAG.Part256.parFac (1 : DirichletCharacter ℂ 1) = _
    rw [PAG.Part256.parFac_of_even (MulChar.one_apply isUnit_one.neg)]
    simp [oddCount]
  | cons a l ih =>
    show PAG.Part256.parFac (PAG.Part260.prodChar (χ a) (listChar χ l)) = _
    rw [PAG.Part260.parFac_prodChar, ih]
    have hk := listChar_neg_one_pow χ l
    have hodd : (listChar χ l).Odd ↔ _root_.Odd (oddCount χ l) := by
      unfold DirichletCharacter.Odd
      rw [hk]
      exact neg_one_pow_eq_neg_one_iff_odd (by norm_num)
    simp only [oddCount, List.map_cons, List.prod_cons]
    unfold PAG.Part260.crossSign
    rcases (χ a).even_or_odd with h | h
    · have hn := not_odd_of_even h
      simp only [hn, false_and, ↓reduceIte, zero_add]
      ring
    · simp only [h, true_and, ↓reduceIte, hodd]
      rw [tri_succ, pow_add]
      by_cases hk2 : _root_.Odd (oddCount χ l)
      · simp only [hk2, ↓reduceIte, hk2.neg_one_pow]; ring
      · simp only [hk2, ↓reduceIte, (Nat.not_odd_iff_even.mp hk2).neg_one_pow]; ring

omit [DecidableEq ι] in
/-- **W の分解（符号つき）**：W(χ) = (−1)^{k(k−1)/2}·交差項·∏_i W(χ_i)（Part 256 の `rootNum_prodChar` の一般化）。 -/
theorem rootNum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    PAG.Part256.rootNum (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part256.rootNum (χ i)).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, parFac_listChar, sqrt_lvl]
  simp_rw [PAG.Part256.rootNum_eq]
  rw [prod_map_div', List.prod_map_mul]
  ring

omit [DecidableEq ι] in
/-- 原始性：互いに素な法で、すべての成分が原始 ⇔ 積が原始（Part 190 の `isPrimitive_mul`・`isPrimitive_iff`・`comp₁_mul`・`comp₂_mul` を使う）。 -/
theorem isPrimitive_listChar_iff (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    (listChar χ l).IsPrimitive ↔ ∀ i ∈ l, (χ i).IsPrimitive := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1).IsPrimitive ↔ _
    simpa using (DirichletCharacter.isPrimitive_one_level_one : (1 : DirichletCharacter ℂ 1).IsPrimitive)
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    have hiff := PAG.Part194.isPrimitive_iff hc (PAG.Part260.prodChar (χ a) (listChar χ l))
    have h1 : PAG.Part194.comp₁ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = χ a :=
      PAG.Part194.comp₁_mul hc (χ a) (listChar χ l)
    have h2 : PAG.Part194.comp₂ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = listChar χ l :=
      PAG.Part194.comp₂_mul hc (χ a) (listChar χ l)
    rw [h1, h2, ih hl.2] at hiff
    show (PAG.Part260.prodChar (χ a) (listChar χ l)).IsPrimitive ↔ _
    rw [hiff]
    simp

omit [DecidableEq ι] in
/-- 原始指標の上では、UA1 の固有値 phaseA1 も同じ式で分かれる。 -/
theorem phaseA1_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hp : ∀ i ∈ l, (χ i).IsPrimitive) :
    PAG.Part258.phaseA1 (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part258.phaseA1 (χ i)).prod := by
  rw [PAG.Part258.phaseA1_of_isPrimitive ((isPrimitive_listChar_iff χ l hl).mpr hp),
    rootNum_listChar χ l hl]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rw [PAG.Part258.phaseA1_of_isPrimitive (hp i hi)]

omit hN [DecidableEq ι] in
theorem listChar_congr {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (l : List ι)
    (h : ∀ i ∈ l, χ i = χ' i) : listChar χ l = listChar χ' l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) = PAG.Part260.prodChar (χ' a) (listChar χ' l)
    rw [h a (by simp), ih fun i hi => h i (by simp [hi])]

/-- **分解の存在**：法 lvl l（互いに素な法の積）の指標は、どれも成分の積 listChar χ l の形に書ける（Part 190 の `decomp` を使う）。 -/
theorem exists_listChar (l : List ι) (hnd : l.Nodup)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (Ψ : DirichletCharacter ℂ (lvl N l)) :
    ∃ χ : ∀ i, DirichletCharacter ℂ (N i), listChar χ l = Ψ := by
  induction l with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    show (1 : DirichletCharacter ℂ 1) = Ψ
    exact (DirichletCharacter.level_one Ψ).symm
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    obtain ⟨χ', hχ'⟩ := ih hnd.2 hl.2 (PAG.Part194.comp₂ hc Ψ)
    refine ⟨Function.update χ' a (PAG.Part194.comp₁ hc Ψ), ?_⟩
    show PAG.Part260.prodChar _ (listChar _ l) = Ψ
    rw [Function.update_self,
      listChar_congr l (fun i hi => Function.update_of_ne (fun h : i = a => hnd.1 (h ▸ hi)) _ _), hχ']
    exact (PAG.Part194.decomp hc Ψ).symm

omit [DecidableEq ι] in
/-- **分解の一意性**：listChar χ l = listChar χ' l なら、l の各成分で χ_i = χ'_i（Part 232 の `charMul_injective` を使う）。 -/
theorem listChar_injective (l : List ι) (hl : l.Pairwise fun i j => (N i).Coprime (N j))
    {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (h : listChar χ l = listChar χ' l) :
    ∀ i ∈ l, χ i = χ' i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h' : PAG.Part236.charMul (χ a) (listChar χ l) = PAG.Part236.charMul (χ' a) (listChar χ' l) := h
    obtain ⟨h1, h2⟩ := PAG.Part236.charMul_injective (coprime_lvl hl.1) h'
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact h1
    · exact ih hl.2 h2 i hi

omit [DecidableEq ι] in
/-- 退化例（成分 1 つ）：τ(listChar χ [a]) = τ(χ_a)。 -/
theorem gaussSum_listChar_singleton (χ : ∀ i, DirichletCharacter ℂ (N i)) (a : ι) :
    gaussSum (listChar χ [a]) stdAddChar = gaussSum (χ a) stdAddChar := by
  rw [gaussSum_listChar χ [a] (List.pairwise_singleton _ _)]
  have h1 : listChar χ [] (N a : ZMod (lvl N [])) = 1 := listChar_natCast χ [] (N a)
  have h2 : χ a (lvl N [] : ZMod (N a)) = 1 := by
    show χ a ((1 : ℕ) : ZMod (N a)) = 1
    rw [Nat.cast_one, map_one]
  simp only [cross, h1, h2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

end PAG.Part261

namespace PAG.Part261

/-- 法 n の p 成分の法 p^{v_p(n)}。 -/
def ppow (n p : ℕ) : ℕ := p ^ n.factorization p

instance ppow_neZero (n p : ℕ) : NeZero (ppow n p) := ⟨by
  unfold ppow
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [Nat.factorization_zero_right]
  · exact pow_ne_zero _ hp.ne'⟩

theorem pairwise_primeFactors (n : ℕ) :
    n.primeFactors.toList.Pairwise fun p q => (ppow n p).Coprime (ppow n q) := by
  refine (Finset.nodup_toList _).imp_of_mem (fun hp hq hne => ?_)
  have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)
  have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hq)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').mpr hne)

theorem lvl_primeFactors (n : ℕ) (hn : n ≠ 0) : lvl (ppow n) n.primeFactors.toList = n := by
  rw [lvl_eq_prod, Finset.prod_map_toList]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]
  rfl

/-- **すべての素数への分解**：法 n の指標 Ψ は、素数冪の法 p^{v_p(n)} の成分 χ_p の積で（自然数での値が ∏ χ_p）、
τ(Ψ) = ∏_p τ(χ_p)·∏_{q≠p} χ_q(p^{v_p(n)})（形 (II)）。 -/
theorem gaussSum_primeFactors (n : ℕ) [NeZero n] (Ψ : DirichletCharacter ℂ n) :
    ∃ χ : ∀ p, DirichletCharacter ℂ (ppow n p),
      (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (ppow n p))).prod) ∧
      gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
        ((n.primeFactors.toList.erase p).map fun q => χ q (ppow n p : ZMod (ppow n q))).prod).prod := by
  have key : ∀ (m : ℕ) [NeZero m], lvl (ppow n) n.primeFactors.toList = m →
      ∀ Ψ : DirichletCharacter ℂ m, ∃ χ : ∀ p, DirichletCharacter ℂ (ppow n p),
        (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (ppow n p))).prod) ∧
        gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
          ((n.primeFactors.toList.erase p).map fun q => χ q (ppow n p : ZMod (ppow n q))).prod).prod := by
    intro m _ hm Ψ
    subst hm
    obtain ⟨χ, hχ⟩ := exists_listChar _ (Finset.nodup_toList _) (pairwise_primeFactors n) Ψ
    refine ⟨χ, fun x => ?_, ?_⟩
    · rw [← hχ, listChar_natCast]
    · rw [← hχ, gaussSum_listChar χ _ (pairwise_primeFactors n),
        cross_eq_formII χ _ (Finset.nodup_toList _), List.prod_map_mul, mul_comm]
  exact key n (lvl_primeFactors n (NeZero.ne n)) Ψ

end PAG.Part261

#print axioms PAG.Part261.gaussSum_listChar
#print axioms PAG.Part261.cross_eq_formI
#print axioms PAG.Part261.cross_eq_formII
#print axioms PAG.Part261.rootNum_listChar_formI
#print axioms PAG.Part261.rootNum_listChar_formII
#print axioms PAG.Part261.parFac_listChar
#print axioms PAG.Part261.rootNum_listChar
#print axioms PAG.Part261.isPrimitive_listChar_iff
#print axioms PAG.Part261.phaseA1_listChar
#print axioms PAG.Part261.exists_listChar
#print axioms PAG.Part261.listChar_injective
#print axioms PAG.Part261.gaussSum_listChar_singleton
#print axioms PAG.Part261.gaussSum_primeFactors
