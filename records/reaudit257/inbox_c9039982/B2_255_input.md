あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、コンパイル済みの形式文と、それについて書かれた文面（ノート、表、Lean ファイルの docstring）を突き合わせ、文面が形式文の内容を正しく述べているかを判定してください。

## 守ってほしいこと
- この入力ファイルを Read で 1 回読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。この入力は長いので、Read が途中で切れたら、同じファイルの続き（offset を指定）を読むことだけは許します。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 文面には、著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）が出てきます。「読み」「解釈」と明示されていれば許容です。形式文の事実として書かれていれば、ずれとして挙げてください。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、6,000 字程度までにまとめてください。最後に、使ったツール（入力ファイルの Read 以外に使っていなければ「Read のみ（回数）」）を書いてください。

## Mathlib の前提
`padicValRat p q` は有理数 q の p 進付値（ℤ 値。q = 0 では 0）。`Real.log` は自然対数（log 0 = 0、負の数では log |x|）。`Nat.Primes` は素数の部分型。`Nat.Primes → ℤ` には直積の位相が入る（ℤ は離散。近傍は有限個の座標を指定する集合を含む）。`BoxCoord` は同じ集合に別の位相を入れた型で、その位相は定義の `instance` のとおり。`Dense s` は閉包が全体、`closure` は閉包、`DiscreteTopology A` は部分空間の位相が離散、`T1Space` は 1 点集合が閉。`⊥`（位相）は離散位相。`f '' A` は像。

## 入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG254.lean（文脈：namespace PAG.Part254）

def logSet : Set ℝ := {x | ∃ q : ℚ, 0 < q ∧ x = Real.log q}

-- PAG259.lean（文脈：namespace PAG.Part259）

def imgST (S T : Finset ℕ) : Set (ℝ × (T → ℤ)) :=
  {z | ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
    z = (Real.log q, fun t : T => padicValRat (t : ℕ) q)}

noncomputable def rho (q : ℚ) : ℝ × (Nat.Primes → ℤ) := (Real.log q, fun p => padicValRat p q)

def BoxCoord : Type := Nat.Primes → ℤ

instance : TopologicalSpace BoxCoord := ⊥

instance : DiscreteTopology BoxCoord := ⟨rfl⟩

noncomputable def rhoBox (q : ℚ) : ℝ × BoxCoord := (Real.log q, fun p => padicValRat p q)
```

## 入力 (2)：形式文の全文（PAG259.lean の定理 45 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
★ は、前回の照合の後に足した文・文を変えた文です。
```lean
theorem padicValRat_prime_ne {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (hne : s ≠ p) :
    padicValRat s (p : ℚ) = 0
theorem padicValRat_prime_zpow {s p : ℕ} (hs : s.Prime) (hp : p.Prime) (k : ℤ) :
    padicValRat s ((p : ℚ) ^ k) = if s = p then k else 0
theorem padicValRat_prod_zpow (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) {t : ℕ}
    (ht : t.Prime) :
    padicValRat t (∏ s ∈ S, (s : ℚ) ^ (k s)) = if t ∈ S then k t else 0
theorem eq_of_padicValRat_eq {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = padicValRat p r) : q = r
theorem eq_one_of_padicValRat_eq_zero {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → padicValRat p q = 0) : q = 1
theorem one_le_abs_intCast_sub {a b : ℤ} (hne : a ≠ b) : (1 : ℝ) ≤ |((a - b : ℤ) : ℝ)|
theorem exists_prime_one_le_abs {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
theorem eq_prod_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    q = ∏ s ∈ S, (s : ℚ) ^ (padicValRat s q)
theorem log_eq_sum_of_support (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) {q : ℚ} (hq : 0 < q)
    (hsupp : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) :
    Real.log q = ∑ s ∈ S, (padicValRat s q : ℝ) * Real.log s
theorem exists_padicValRat_eq (S : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (k : ℕ → ℤ) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ S, padicValRat s q = k s) ∧
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
theorem closure_logSet : closure PAG.Part254.logSet = Set.univ
theorem dense_closure_log_primes {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Dense ((AddSubgroup.closure ({Real.log p, Real.log r} : Set ℝ) : AddSubgroup ℝ) : Set ℝ)
theorem exists_zpow_near {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ a b : ℤ, |(a : ℝ) * Real.log p + (b : ℝ) * Real.log r - x| < ε
theorem irrational_log_div_log {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) :
    Irrational (Real.log r / Real.log p)
theorem padicValRat_mul_zpow_zpow {p r t : ℕ} (hp : p.Prime) (hr : r.Prime) (ht : t.Prime)
    {q₀ : ℚ} (hq₀ : q₀ ≠ 0) (a b : ℤ) :
    padicValRat t (q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b) =
      padicValRat t q₀ + (if t = p then a else 0) + (if t = r then b else 0)
theorem log_mul_zpow_zpow {p r : ℕ} (hp : p.Prime) (hr : r.Prime) {q₀ : ℚ} (hq₀ : 0 < q₀)
    (a b : ℤ) :
    Real.log ((q₀ * (p : ℚ) ^ a * (r : ℚ) ^ b : ℚ) : ℝ) =
      Real.log q₀ + (a : ℝ) * Real.log p + (b : ℝ) * Real.log r
theorem exists_near_of_two_unmeasured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ≠ p → t ≠ r → padicValRat t q = padicValRat t q₀) ∧
      |Real.log q - x| < ε
theorem exists_near_measured {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r)
    (M : Finset ℕ) (hpM : p ∉ M) (hrM : r ∉ M) {q₀ : ℚ} (hq₀ : 0 < q₀) (x : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ s ∈ M, s.Prime → padicValRat s q = padicValRat s q₀) ∧
      |Real.log q - x| < ε
theorem eq_mul_zpow_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q * (p : ℚ) ^ (padicValRat p q' - padicValRat p q)
theorem log_sep_of_agree {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q) (hq' : 0 < q')
    (h : ∀ t : ℕ, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
theorem exists_mem_one_le_abs_of_support (S : Finset ℕ) {q r : ℚ} (hq : 0 < q) (hr : 0 < r)
    (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hrS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t r = 0) (hne : q ≠ r) :
    ∃ p ∈ S, p.Prime ∧ (1 : ℝ) ≤ |((padicValRat p q - padicValRat p r : ℤ) : ℝ)|
theorem sep_of_inf_unmeasured (M : Finset ℕ) {q r : ℚ}
    (hne : ∃ s ∈ M, padicValRat s q ≠ padicValRat s r) :
    ∃ s ∈ M, (1 : ℝ) ≤ |((padicValRat s q - padicValRat s r : ℤ) : ℝ)|
theorem log_sep_one_unmeasured (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {q q' : ℚ} (hq : 0 < q)
    (hq' : 0 < q') (hqS : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0)
    (hq'S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0)
    (h : ∀ t ∈ S, t.Prime → t ≠ p → padicValRat t q' = padicValRat t q) :
    q' = q ∨ Real.log p ≤ |Real.log q' - Real.log q|
theorem exists_near_in_subgroup (S : Finset ℕ) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hne : p ≠ r) (hpS : p ∈ S) (hrS : r ∈ S) (T : Finset ℕ) (hpT : p ∉ T) (hrT : r ∉ T)
    {q₀ : ℚ} (hq₀ : 0 < q₀) (hq₀S : ∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q₀ = 0) (x : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) ∧
      (∀ s ∈ T, s.Prime → padicValRat s q = padicValRat s q₀) ∧ |Real.log q - x| < ε
theorem fiber_sep (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    ∃ c : ℝ, 0 < c ∧ ∀ q q' : ℚ, 0 < q → 0 < q' →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q = 0) →
      (∀ t : ℕ, t.Prime → t ∉ S → padicValRat t q' = 0) →
      (∀ t ∈ T, padicValRat t q' = padicValRat t q) →
      q' = q ∨ c ≤ |Real.log q' - Real.log q|
theorem threshold_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    (∃ k : T → ℤ, ∀ x : ℝ, (x, k) ∈ closure (imgST S T)) ↔
      ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
-- ★ 
theorem isClosed_and_discrete_of_subsingleton {X : Type*} [TopologicalSpace X] [T1Space X]
    {A : Set X} (h : ∀ z : X, ∃ U ∈ nhds z, (U ∩ A).Subsingleton) :
    IsClosed A ∧ DiscreteTopology A
-- ★ 
theorem dense_imgST_iff (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime) (hTS : T ⊆ S) :
    Dense (imgST S T) ↔ ∃ p r : ℕ, p ≠ r ∧ p ∈ S ∧ r ∈ S ∧ p ∉ T ∧ r ∉ T
-- ★ 
theorem isClosed_discrete_imgST (S T : Finset ℕ) (hS : ∀ s ∈ S, s.Prime)
    (h1 : ∀ p r : ℕ, p ∈ S → r ∈ S → p ∉ T → r ∉ T → p = r) :
    IsClosed (imgST S T) ∧ DiscreteTopology (imgST S T)
theorem rho_one : rho 1 = (0, 0)
theorem exists_two_primes_not_mem (I : Set Nat.Primes) (hI : I.Finite) :
    ∃ p r : Nat.Primes, p ∉ I ∧ r ∉ I ∧ (p : ℕ) ≠ (r : ℕ)
theorem val_ne_of_mem_of_not_mem {I : Set Nat.Primes} {i p : Nat.Primes} (hi : i ∈ I)
    (hp : p ∉ I) : (i : ℕ) ≠ p
theorem dense_rho_image : Dense (rho '' {q : ℚ | 0 < q})
theorem mem_closure_line_prod (x : ℝ) :
    (x, (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q})
theorem closure_rho_not_image :
    ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∈ closure (rho '' {q : ℚ | 0 < q}) ∧
      ((1 : ℝ), (0 : Nat.Primes → ℤ)) ∉ rho '' {q : ℚ | 0 < q}
theorem rho_one_mem_closure_ne_one :
    rho 1 ∈ closure (rho '' {q : ℚ | 0 < q ∧ q ≠ 1})
theorem rho_sep {q r : ℚ} (hq : 0 < q) (hr : 0 < r) (hne : q ≠ r) :
    ∃ p : Nat.Primes, (1 : ℝ) ≤ |(((rho q).2 p - (rho r).2 p : ℤ) : ℝ)|
-- ★ 
theorem isClosed_discrete_rhoBox_image :
    IsClosed (rhoBox '' {q : ℚ | 0 < q}) ∧ DiscreteTopology (rhoBox '' {q : ℚ | 0 < q})
theorem finite_support_padicValRat {q : ℚ} (hq : 0 < q) :
    {p : ℕ | p.Prime ∧ padicValRat p q ≠ 0}.Finite
theorem eq_prod_support {q : ℚ} (hq : 0 < q) :
    q = ∏ s ∈ (finite_support_padicValRat hq).toFinset, (s : ℚ) ^ (padicValRat s q)
theorem sep_of_mem_zmultiples {c x y : ℝ} (hc : 0 < c) (hx : ∃ m : ℤ, x = m * c)
    (hy : ∃ n : ℤ, y = n * c) (hne : x ≠ y) : c ≤ |x - y|
theorem mem_zmultiples_of_commensurable {L₁ L₂ : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b : ℤ) :
    (a : ℝ) * L₁ + b * L₂ = ((a * n + b * m : ℤ) : ℝ) * (L₁ / n)
theorem sep_of_commensurable {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) * L₂ = m * L₁) (a b a' b' : ℤ)
    (hne : (a : ℝ) * L₁ + b * L₂ ≠ a' * L₁ + b' * L₂) :
    L₁ / n ≤ |((a : ℝ) * L₁ + b * L₂) - (a' * L₁ + b' * L₂)|
theorem zpow_ge_of_one_lt {p : ℕ} (hp : p.Prime) {k : ℤ} (hk : 1 < (p : ℝ) ^ k) :
    (p : ℝ) ≤ (p : ℝ) ^ k
theorem exists_between_one {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hne : p ≠ r) {y : ℝ}
    (hy : 1 < y) :
    ∃ a b : ℤ, 1 < (p : ℝ) ^ a * (r : ℝ) ^ b ∧ (p : ℝ) ^ a * (r : ℝ) ^ b < y
```

## 入力 (3)：Lean ファイルの文面（ファイル冒頭の説明と、各宣言の docstring。原文のまま）
```
【ファイル冒頭の説明】
/-
アーデル射影幾何 — Part 255（PAG 2.0）：§1 の命題 3（解像度と有効な姿）の L1 の読み — 測る素点と、極限の取り方

問いの出所：Part 255 の着手前の文書（`pag2_part255_preregistration.md`）の候補 L1 を、著者が §1 の命題 3 の読みとして
採った（2026-11-13 08:38「L1 で Part 255 を始める」）。L1 は Claude の案で、著者の定義の文面そのものではない。
著者の定義（2026-11-13 08:41、原文）：「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。
連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。」

L1：基礎は正の有理数の群（または有限個の素数の集合 S が生成する部分群 ⟨S⟩）。解像度は測る素点の集合。
測った座標は (log q（∞ を測るとき）, (v_p(q))_{測る素数 p})。有限素点の座標は離散な ℤ。
このファイルが示すのは数学の事実だけ（どの位相で像が離散で、どこで閉包が連続な成分を含むか）。「解像度が落ちる」は
著者の定義で、ここでは示していない。

内容（すべて既知の事実の Lean 化。新しいのは置き方だけ）：
1. すべての素点の付値の組：単射（`eq_of_padicValRat_eq`、素因数分解の一意性）、異なる正の有理数はある素数の座標で
   1 以上離れる（`exists_prime_one_le_abs`。sup 距離の意味。位相の文は節 4）。∏_{s∈S} s^{k_s} の付値
   （`padicValRat_prod_zpow`）、付値の組への全射（`exists_padicValRat_eq`）、⟨S⟩ の元の表示（`eq_prod_of_support`）、
   積公式 log q = Σ v_s(q) log s（`log_eq_sum_of_support`：∞ の座標は有限素点の座標から決まる）。
2. ∞ だけを測る：log ℚ_{>0} の閉包は ℝ 全体（`closure_logSet`、Part 250 の `dense_logSet` から）。異なる 2 つの素数の
   対数が生成する群は稠密（`dense_closure_log_primes`・`exists_zpow_near`。Part 250 の 2 と 3 の一般化）。log r / log p は
   無理数（`irrational_log_div_log`）。
3. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）：
   - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`）。
   - 二分法：その条件のもとで像は稠密（`dense_imgST_iff`）。条件が成り立たない（測らない素数が高々 1 つ）なら像は閉かつ
     離散（`isClosed_discrete_imgST`。T の座標が同じ点は一定の間隔 c > 0 で離れる `fiber_sep` から）。
   - 部品：測らない素数 p ≠ r があれば、ほかの座標を保ったまま log を任意の x に近づけられる
     （`exists_near_of_two_unmeasured`・`exists_near_measured`・`exists_near_in_subgroup`）。p 以外の付値が一致する 2 元は
     q' = q·p^k で、等しいか log p 以上離れる（`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured`）。
     ℚ_{>0} を基礎にしたこれらの文は、測った座標が同じ点の集まり（ファイバー）の中の距離の文で、有限の解像度の文ではない
     （ℚ_{>0} では、有限の解像度の外に素数が無限個ある）。S の素数をすべて測れば離散
     （`exists_mem_one_le_abs_of_support`）、∞ を測らなければ整数の座標で離散（`sep_of_inf_unmeasured`。ほぼ同語反復）。
4. 極限の取り方：すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。集合は同じで、位相が 2 通り。
   - 直積の位相（`Nat.Primes → ℤ` の既定の位相。各近傍は有限個の素点しか測らない）：像は稠密（`dense_rho_image`）、
     ℝ × {0} の直線が閉包に入る（`mem_closure_line_prod`）、ρ(1) は孤立点でない（`rho_one_mem_closure_ne_one`）、閉包の点
     (1, 0) は積公式の形 x = Σ k_p log p を満たさず像にない（`closure_rho_not_image`）。
   - すべての素点を同時に測る位相（`BoxCoord`：離散位相。ℤ 値では箱・一様の位相と同じ）：像は閉かつ離散
     （`isClosed_discrete_rhoBox_image`）。sup 距離で 1 以上離れる（`rho_sep`）。
   - 離散になるかどうかは位相の選び方で決まり、有限台では決まらない（付値の組は有限台 `finite_support_padicValRat`、
     各元は台の段 ⟨T⟩ の元 `eq_prod_support` だが、`rho_one_mem_closure_ne_one` の近似点も有限台）。
5. 対照群：値が c·ℤ（c > 0）に入れば離散（`sep_of_mem_zmultiples`。F_q(t) では c = log q）。対数が通約的な
   一般化素数（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`）。
6. 順序版（大きさの順序 = 無限素点の絶対値）：⟨p⟩ では 1 より大きい最小の元は p（`zpow_ge_of_one_lt`）。
   ⟨p, r⟩（p ≠ r）では最小の元がない（`exists_between_one`）。
7. 退化例：すべての付値が 0 の正の有理数は 1（`eq_one_of_padicValRat_eq_zero`。S = ∅ で ⟨S⟩ = {1}）。
一般の補題：T1 空間で、どの点にも集合と高々 1 点でしか交わらない近傍があれば、その集合は閉かつ離散
（`isClosed_and_discrete_of_subsingleton`）。

独立照合の後に足したもの：A・C の後に `imgST`（def）・`fiber_sep`・`threshold_iff`・`irrational_log_div_log`・
`closure_rho_not_image`、`exists_mem_one_le_abs_of_support` の結論に「証人は素数」。B の後に `BoxCoord`・`rhoBox`（def）・
`isClosed_discrete_rhoBox_image`・`dense_imgST_iff`・`isClosed_discrete_imgST`・`isClosed_and_discrete_of_subsingleton`。

Lean にしていないこと：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限。離散）そのものと、それと `BoxCoord` の位相の
同一視（標準の事実）。S ∪ {∞} から 1 つ落としても格子であること（S 単数定理の形。数値 step278 の (9)）。⟨S⟩ の大きさの
順序の Dedekind 完備化が ℝ であること。F_q(t) そのもの（付値と積公式。数値 (15)）。測らない生成元が無限個の一般化素数の
反例（数値 (17)）。
ℝ は log の値域として定義に明示的に置かれていて、隠れた注入ではない。それを完備化と読み、著者の定義の「解像度が落ちる」に
あたると読むのは読み（数学の文ではない）。
-/

【padicValRat_prime_ne】
/-- 異なる素数 s ≠ p：v_s(p) = 0。 -/

【padicValRat_prime_zpow】
/-- v_s(p^k) は s = p なら k、そうでなければ 0。 -/

【padicValRat_prod_zpow】
/-- **1a.** ∏_{s∈S} s^{k_s} の付値：t ∈ S なら k_t、t ∉ S なら 0。 -/

【eq_of_padicValRat_eq】
/-- **1b. 全解像度の単射**（素因数分解の一意性）：すべての素数で付値が一致する正の有理数は等しい。 -/

【eq_one_of_padicValRat_eq_zero】
/-- **7. 退化例**：すべての付値が 0 の正の有理数は 1（S = ∅ で ⟨S⟩ = {1}）。 -/

【one_le_abs_intCast_sub】
/-- 異なる整数は、実数として 1 以上離れる（整数の座標の離散性）。 -/

【exists_prime_one_le_abs】
/-- **1c.** 異なる正の有理数は、ある素数の座標で 1 以上離れる（sup 距離の意味。位相の文は `isClosed_discrete_rhoBox_image`）。 -/

【eq_prod_of_support】
/-- **1d.** 台が S に入る正の有理数（⟨S⟩ の元）は q = ∏_{s∈S} s^{v_s(q)}。 -/

【log_eq_sum_of_support】
/-- **1e. 積公式**：⟨S⟩ の元では log q = Σ_{s∈S} v_s(q)·log s（全解像度では ∞ の座標は有限素点の座標から決まる）。 -/

【exists_padicValRat_eq】
/-- **1f. 付値の組への全射**：S の上の任意の整数の組 k に対し、v_s = k_s（s ∈ S）で S の外では付値 0 の正の有理数がある。 -/

【closure_logSet】
/-- **2a.** ∞ だけを測って完備化すると ℝ 全体（Part 250 の `dense_logSet` から）。 -/

【dense_closure_log_primes】
/-- **2b.** 異なる 2 つの素数 p, r の対数が生成する加法群は ℝ で稠密（最小の正の元があれば p^K = r^M となり矛盾）。Part 250 の 2 と 3 の一般化。 -/

【exists_zpow_near】
/-- **2c.** どの x と ε > 0 に対しても、|a·log p + b·log r − x| < ε となる整数 a, b がある。 -/

【irrational_log_div_log】
/-- 異なる素数 p, r で log r / log p は無理数（通約できない。対照群の通約的な場合との違い）。 -/

【padicValRat_mul_zpow_zpow】
/-- q₀·p^a·r^b の付値。 -/

【log_mul_zpow_zpow】
/-- q₀·p^a·r^b の log。 -/

【exists_near_of_two_unmeasured】
/-- p ≠ r 以外のすべての付値を q₀ と同じに保ったまま（p・r の付値だけが違いうるファイバーの中で）、log を任意の x に近づけられる。 -/

【exists_near_measured】
/-- 有限の解像度 M（∞ と M の素数を測る）：測らない素数 p ≠ r があれば、(x, (v_s(q₀))_{s∈M}) は像の閉包に入る。 -/

【eq_mul_zpow_of_agree】
/-- p 以外のすべての付値が一致すれば q' = q·p^k（k = v_p q' − v_p q）。 -/

【log_sep_of_agree】
/-- p 以外のすべての付値が一致する 2 元（p の付値だけが違いうるファイバー）は、等しいか、∞ の座標で log p 以上離れる。 -/

【exists_mem_one_le_abs_of_support】
/-- ⟨S⟩ の全解像度：S の素数をすべて測れば、異なる元は S のある素数の座標で 1 以上離れる。 -/

【sep_of_inf_unmeasured】
/-- ∞ を測らないとき：有限素点の座標は整数なので、異なる像は 1 以上離れる。 -/

【log_sep_one_unmeasured】
/-- ⟨S⟩ で S の素数 p だけを測らないとき：p 以外の S の座標が一致する 2 元は、等しいか、∞ の座標で log p 以上離れる。 -/

【exists_near_in_subgroup】
/-- ⟨S⟩ で S の素数 p ≠ r を測らないとき：⟨S⟩ の中にとどまり、T の座標を q₀ と同じに保ったまま、log を任意の x に
近づけられる（閉包は ℝ × ℤ^T を含む）。 -/

【imgST】
/-- 基礎 ⟨S⟩（S は素数の有限集合）で、∞ と T の素数を測るときの像 {(log q, (v_t(q))_{t∈T}) | q ∈ ⟨S⟩}。
T の座標は ℤ^T（T は有限なので離散）。 -/

【fiber_sep】
/-- 測らない素数（S ∖ T の元）が高々 1 つなら、T の座標が同じ ⟨S⟩ の 2 元は、等しいか、∞ の座標で一定の c > 0 以上離れる。 -/

【threshold_iff】
/-- **閾値の定理**（基礎 ⟨S⟩、T ⊆ S、∞ と T の素数を測る）：像の閉包がある水平な直線 ℝ × {k} 全体を含む
⇔ T の外に S の異なる素数が 2 つある（測らない素数が 2 つ以上）。 -/

【isClosed_and_discrete_of_subsingleton】
/-- 一般の補題：T1 空間で、どの点にも集合 A と高々 1 点でしか交わらない近傍があれば、A は閉かつ（部分空間として）離散。 -/

【dense_imgST_iff】
/-- **閾値の二分法（片側）**：像 `imgST S T` が ℝ × ℤ^T で稠密 ⇔ T の外に S の異なる素数が 2 つある。 -/

【isClosed_discrete_imgST】
/-- **閾値の二分法（もう片側）**：T の外に S の異なる素数が 2 つないとき（測らない素数が高々 1 つ）、像 `imgST S T` は
ℝ × ℤ^T の中で閉かつ離散。 -/

【rho】
/-- すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。有限素点の座標は ℤ（離散）。`Nat.Primes → ℤ` には直積の位相が入る。 -/

【rho_one】
/-- ρ(1) = (0, 0)。 -/

【exists_two_primes_not_mem】
/-- 有限個の素数の集合の外に、異なる素数が 2 つある。 -/

【val_ne_of_mem_of_not_mem】
/-- I の元と I の外の元は、自然数として異なる。 -/

【dense_rho_image】
/-- **直積の位相では、像は稠密**：ℝ × (素数 → ℤ) のどの点 (x, k) の近傍（∞ の座標の ε 近傍と、有限個の素数の座標の
指定）にも、正の有理数の像がある。各近傍は有限個の素点しか見ない。これを著者の言葉の「完備化（極限）」にあたると読むのは読み。 -/

【mem_closure_line_prod】
/-- 系：直積の位相では、ℝ × {0} の直線全体が像の閉包に入る（連続体に滑り落ちる）。 -/

【closure_rho_not_image】
/-- 直積の位相の閉包には、積公式を満たさない点が入る：(1, 0) は閉包に入るが、どの正の有理数の像でもない
（付値がすべて 0 なら q = 1 で log q = 0）。 -/

【rho_one_mem_closure_ne_one】
/-- 直積の位相では ρ(1) は孤立点でない：1 と異なる正の有理数の像が、ρ(1) のどの近傍にもある。 -/

【rho_sep】
/-- 異なる正の有理数の像は、ある素数の座標で 1 以上離れる（sup 距離で 1 以上。`exists_prime_one_le_abs` の言い換え。
位相の文は `isClosed_discrete_rhoBox_image`）。 -/

【BoxCoord】
/-- すべての素点の座標の組に、すべての素点を同時に測る位相を入れた型：離散位相（ℤ 値では箱の位相・一様の位相と同じ）。
`Nat.Primes → ℤ` の直積の位相（各近傍は有限個の素点しか測らない）と、集合としては同じで位相だけが違う。 -/

【rhoBox】
/-- ρ と同じ写像を、値域の有限素点の座標に離散位相（すべての素点を同時に測る）を入れて考える。 -/

【isClosed_discrete_rhoBox_image】
/-- **すべての素点を同時に測る位相では、像は閉かつ離散**（独立照合 B の指摘で追加）。同じ集合が直積の位相では稠密
（`dense_rho_image`）で、離散になるかどうかは有限台ではなく位相の選び方で決まる（`rho_one_mem_closure_ne_one` の近似点も
正の有理数なので有限台）。 -/

【finite_support_padicValRat】
/-- 付値の組は有限台：付値が 0 でない素数は有限個（各正の有理数は、有限個の素数が生成する段 ⟨T⟩ に住む）。有限台だけでは離散にならない（`rho_one_mem_closure_ne_one`）。 -/

【eq_prod_support】
/-- 各正の有理数は、その台 T の段 ⟨T⟩ の元：q = ∏_{s∈T} s^{v_s(q)}。 -/

【sep_of_mem_zmultiples】
/-- 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れる（F_q(t)：c = log q、通約的な一般化素数）。 -/

【mem_zmultiples_of_commensurable】
/-- 通約的な対数：n·L₂ = m·L₁（n > 0）なら a·L₁ + b·L₂ = (a n + b m)·(L₁/n)。 -/

【sep_of_commensurable】
/-- 対照群のまとめ：通約的な 2 つの対数の整数結合は、異なれば L₁/n 以上離れる（連続体は現れない）。 -/

【zpow_ge_of_one_lt】
/-- ⟨p⟩ の大きさの順序は離散：1 < p^k なら p ≤ p^k（1 より大きい最小の元は p）。 -/

【exists_between_one】
/-- ⟨p, r⟩（p ≠ r）の大きさの順序には 1 より大きい最小の元がない：どの y > 1 に対しても 1 < p^a r^b < y。 -/
```

## 入力 (4)：ノートの全文（原文のまま、行番号つき）
前回の照合の時点の版から変わった行（または足した行）の範囲：1〜3、14〜15、18、21〜39、42〜53、61、65〜66、75、79、85〜90、98、103〜106、109、114〜116、120〜122、128〜134、138〜139、158〜160、173、182〜195
```
   1| # アーデル射影幾何 — Part 255（PAG 2.0）：§1 の命題 3（解像度と有効な姿）の L1 の読み — 像が離散か稠密かは、測る素点の集合と位相の選び方で決まる。有限の基礎 ⟨S⟩ での二分法（∞ を測り、測らない素数が 2 つ以上なら稠密、高々 1 つなら閉かつ離散）と、すべての素点の座標での位相の対比（すべての素点を同時に測る位相では閉かつ離散、直積の位相では稠密）。既知の事実の Lean 化（小さいノート）
   2| 
   3| 2026-11-13。PAG259.lean（定理 45 個、定義 4 個と instance 2 個。独立照合 A・C の後に定理 4 個・定義 1 個、B の後に定理 4 個・定義 2 個を足した）、step278.py（21 項目）。
   4| 
   5| - **問いの出所。**
   6|   - 2026-11-13 08:38：著者が、着手前の文書（`pag2_part255_preregistration.md`）の候補 L1 を §1 の命題 3 の読みとして採りました（選択肢「L1 で Part 255 を始める」）。L1 は Claude の案です。著者の定義の文面そのものではありません。
   7|   - 同じとき、著者は CLAUDE.md §1 の K は「考える素数の個数」ではない、と答えました。L1（測る素点の集合）は、N・K・Λ のどれとも同一視しません。
   8|   - 2026-11-13 08:41：著者の定義（原文）。
   9|     > 完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します。
  10|   - この定義は CLAUDE.md §1 の解釈の層に置きます。数学の文ではないので、Lean では示していません（示せる種類の文でもありません）。
  11| - **L1（この定義のもとでの読み）。**
  12|   - 基礎は正の有理数の群 ℚ_{>0}、または有限個の素数の集合 S が生成する部分群 ⟨S⟩ です。
  13|   - 解像度は測る素点の集合です。測った座標は (log q（∞ を測るとき）, (v_p(q))_{測る素数 p}) で、有限素点の座標は離散な ℤ に入ります。
  14|   - 無限個の素点の座標を考えるときは、位相を決めないと「離散」は意味を持ちません。各近傍が有限個の素点しか測らない位相（直積の位相）と、すべての素点を同時に測る位相（離散位相。ℤ 値では箱・一様の位相と同じ）があります（独立照合 B の指摘で明記）。
  15|   - 読み：閉包をとる操作（完備化）は「解像度が落ちる」側の操作で、閉包に現れる連続体は観測したい姿ではなく、解像度が落ちた印です。極限は、すべての素点を同時に測る側（直極限。有限台で離散）でとります。これは読みで、Lean の文ではありません。
  16| - **着手前の文書からの直し（08:41 の定義を受けて）。**
  17|   - 着手前の文書は、L1 の「有効な姿」を「像の閉包」と書き、閉包に直線が現れることを中心に置いていました。数学は同じですが、向きを直しました。閉包に現れる連続体は解像度が落ちた印で、中心は「どこまで離散が保たれるか」です。
  18|   - **取り下げ 1。** 着手前の文書 §4 は「完備化（尺度 ε → 0）は解像度を上げる向き」として、完備化を候補から外しました。この理由を取り下げます。著者の定義では、完備化は解像度が落ちる側の操作です。L1 の閉包が、その完備化にあたると読みます。
  19|   - **取り下げ 2。** Part 250 の照合の記録（`pag2_part250_independent_audit.md`）の「これは『解像度を落とす』とは逆向き（ε → 0 の側）の操作です」という向きの判断も取り下げます。原文は残しています。
  20|   - **Part 250 の残る問いへの答え。** Part 250 のノートの残る問い（「完備化を『解像度を上げた極限』と読むなど…どれが著者の意図に近いかは、著者の判断です」）に、著者の答えが出ました：完備化は解像度が落ちる側です。
  21| - **結論（Lean の文。すべて既知の事実の Lean 化）。**
  22|   - **1. すべての素点の付値の組。**
  23|     - 単射です（`eq_of_padicValRat_eq`。素因数分解の一意性）。異なる正の有理数は、ある素数の座標で 1 以上離れます（`exists_prime_one_le_abs`。sup 距離の意味。位相の文は 4）。
  24|     - ∏_{s∈S} s^{k_s} の付値（`padicValRat_prod_zpow`）、付値の組への全射（`exists_padicValRat_eq`）、⟨S⟩ の元の表示 q = ∏ s^{v_s(q)}（`eq_prod_of_support`）。
  25|     - 積公式 log q = Σ_s v_s(q)·log s（`log_eq_sum_of_support`）。∞ の座標は有限素点の座標から決まります。
  26|   - **2. ∞ だけを測る。**
  27|     - log ℚ_{>0} の閉包は ℝ 全体です（`closure_logSet`。Part 250 の `dense_logSet` の言い換え）。
  28|     - 異なる 2 つの素数の対数が生成する群は稠密です（`dense_closure_log_primes`・`exists_zpow_near`。Part 250 の 2 と 3 の場合の一般化。最小の正の元があれば p^K = r^M となり矛盾）。log r / log p は無理数です（`irrational_log_div_log`。独立照合 A の指摘で足した）。
  29|   - **3. 有限の基礎 ⟨S⟩ での閾値（T ⊆ S、∞ と T の素数を測る。像 `imgST S T` ⊆ ℝ × ℤ^T）。**
  30|     - 閉包がある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（`threshold_iff`。独立照合 A の指摘で足した）。
  31|     - 二分法（独立照合 B の指摘で足した）：その条件のもとで像は稠密です（`dense_imgST_iff`）。条件が成り立たない（測らない素数が高々 1 つ）なら、像は閉かつ離散です（`isClosed_discrete_imgST`）。後者は、T の座標が同じ点が一定の間隔 c > 0 で離れること（`fiber_sep`。S ∖ T = {p} なら c = log p、S ⊆ T なら点は 1 つ）から出ます。
  32|     - 部品：p ≠ r 以外のすべての付値を保ったまま log を任意の x に近づけられる（`exists_near_of_two_unmeasured`、弱めた版 `exists_near_measured`、⟨S⟩ の中にとどまる版 `exists_near_in_subgroup`）。p 以外の付値が一致する 2 元は q' = q·p^k で、等しいか log p 以上離れる（`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured`）。S の素数をすべて測れば、異なる元は S のある素数の座標で 1 以上離れる（`exists_mem_one_le_abs_of_support`）。∞ を測らなければ整数の座標で離散（`sep_of_inf_unmeasured`。ほぼ同語反復）。
  33|     - 守備範囲：閾値（二分法）は有限の基礎 ⟨S⟩ の文です。ℚ_{>0} を基礎にした部品の文は、測った座標が同じ点の集まり（ファイバー）の中の距離の文で、有限の解像度の文ではありません。ℚ_{>0} では有限の解像度の外に素数が無限個あるので、「測らない素数がちょうど 1 つ」の場合は起きず、∞ を測ればどの有限の解像度でも像は稠密です（`exists_near_measured` と `exists_padicValRat_eq` から出る系。閉包の文にはしていない）。
  34|   - **4. 極限の取り方：すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)。集合は同じで、位相が 2 通り。**
  35|     - **直積の位相**（`Nat.Primes → ℤ` の既定の位相。各近傍は有限個の素点しか測らない）：像は稠密です（`dense_rho_image`）。ℝ × {0} の直線全体が閉包に入り（`mem_closure_line_prod`）、ρ(1) は孤立点ではなく（`rho_one_mem_closure_ne_one`）、閉包の点 (1, 0) は像にありません（`closure_rho_not_image`。(1, 0) は積公式の形 x = Σ k_p log p を満たさない点。独立照合 A の指摘）。
  36|     - **すべての素点を同時に測る位相**（`BoxCoord`：`Nat.Primes → ℤ` に離散位相。ℤ 値では箱・一様の位相と同じ。写像 `rhoBox` は ρ と同じ）：像は閉かつ離散です（`isClosed_discrete_rhoBox_image`。独立照合 B の指摘で足した）。sup 距離では、異なる像は 1 以上離れます（`rho_sep`）。
  37|     - 離散になるかどうかは位相の選び方で決まり、有限台では決まりません。付値の組は有限台で（`finite_support_padicValRat`）、各元は台の段 ⟨T⟩ の元ですが（`eq_prod_support`）、`rho_one_mem_closure_ne_one` の近似点も有限台です（独立照合 B の指摘）。
  38|     - Lean の外：直和 ⊕ℤ の直極限の位相（有限の段 ℤ^T の直極限）が離散であることと、それと `BoxCoord` の位相の同一視（標準の事実）。
  39|   - **5. 対照群（Lean では自明な文だけ）。** 値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れます（`sep_of_mem_zmultiples`）。対数が通約的な一般化素数でも同じです（`mem_zmultiples_of_commensurable`・`sep_of_commensurable`）。
  40|   - **6. 順序版（大きさの順序 = 無限素点の絶対値）。** ⟨p⟩ では 1 より大きい最小の元は p です（`zpow_ge_of_one_lt`）。⟨p, r⟩（p ≠ r）では最小の元がありません（`exists_between_one`）。
  41|   - **7. 退化例。** すべての付値が 0 の正の有理数は 1 です（`eq_one_of_padicValRat_eq_zero`。S = ∅ で ⟨S⟩ = {1}）。
  42|   - 一般の補題：T1 空間で、どの点にも集合と高々 1 点でしか交わらない近傍があれば、その集合は閉かつ離散（`isClosed_and_discrete_of_subsingleton`）。
  43|   - 冗長な文（独立照合 B の指摘）：`closure_logSet` は `dense_logSet` の言い換え、`exists_near_measured` は `exists_near_of_two_unmeasured` を弱めたもの、`sep_of_inf_unmeasured` は `one_le_abs_intCast_sub` そのもの、`rho_sep` は `exists_prime_one_le_abs` の言い換え、`mem_closure_line_prod` と `closure_rho_not_image` の前半は `dense_rho_image` の系。
  44|   - sorry 0、警告 0。`#print axioms` 45 行はすべて標準の公理の範囲です（44 行が [propext, Classical.choice, Quot.sound]、`val_ne_of_mem_of_not_mem` は [propext] だけ）。
  45| - **文献の言葉と対照群（Lean の外。独立照合 C、§7）。**
  46|   - ρ は ℚ の主 Arakelov 因子の写像で、像は次数 0 の Arakelov 因子（積公式）。すべての素点を同時に測る側は、有限イデールの制限直積の位相を単数 Ẑ^× で割ったもの。「ℚ^× はイデール群では離散、全直積では稠密」という古典的な対比の、値の群への像です。直積の位相での稠密性は弱近似（Artin–Whaples）から出ます。
  47|   - F_q(t) でも、直積の位相では像は稠密になります（どんな有限集合の外にも、十分大きいすべての次数の既約多項式がある）。ただし ∞ の座標が整数（次数）なので、連続体（ℝ）は現れません。直積の位相で離散が崩れるのは位相の選び方の一般の性質で、算術の内容ではありません。ℝ という連続体が現れるのはアルキメデス素点の性質です。
  48|   - F_q(t) では、閾値の「測らない素数が 2 つ以上」の場合が「稠密」から「離散だが単射でない（核の階数は |S ∖ T| − 1）」に変わり、⟨P, Q⟩ にも 1 より大きい最小の大きさ q^{gcd(deg P, deg Q)} があります。
  49| - **著者の定義との関係（正直な評価）。**
  50|   - Lean が示したのは数学の事実だけです：どの位相で像が離散で、どこで閉包が連続な成分を含むか。「それを解像度が落ちると言う」のは著者の定義で、Lean で確かめたものではありません。
  51|   - ℝ は、Lean では log の値域として定義（`rho`・`logSet`・`imgST`）に明示的に置かれていて、隠れた注入ではありません（確信度：高。独立照合 A も「ℝ は第 1 成分の log からだけ入る」と判定）。完備化の構成は Lean にありません。ℝ や直積の位相を「完備化」と読み、著者の定義の「解像度が落ちる」にあたると読むのは読みです（確信度：中。最初の版の「それが…ことそのもの」「確信度：高」は、独立照合 B の指摘で読みに直した）。
  52|   - Part 254 の極限も、完備化していない直極限でした（PAG258 は `Module.DirectLimit` だけを使い、完備化 L²(Ẑ^×) は「Lean にしていないこと」に書かれている）。これは事実です。「著者の方針と同じ向き」というのは読みです（確信度：中）。
  53| - **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。新しいのは置き方（著者の言葉と数学の対象の対応づけ）だけです。新規候補はありません（文献上の判断で、形式文が保証するものではありません）。兆候 4（既知の事実だけ）は 7 パート連続です（§6）。
  54| 
  55| ## 0. 内容
  56| 
  57| ### 0.0 ハンドシェイク（CLAUDE.md §0）
  58| 
  59| - (a) 形式化済み：Part 250（PAG254）の `logSet`・`dense_logSet`・`dense_closure_log_two_three`・`eq_of_chainIn_primePow`。Part 252〜254（PAG256〜258）のねじれた貼り合わせ U と、その代数的な帰納極限（完備化していない）。
  60| - (b) 著者の解釈の層：§1 の 3 命題。重なりはねじれた貼り合わせ（U）。A1 は公準。解像度は測る素点の集合（L1、08:38 に著者が読みとして採った）。「解像度が落ちる」＝完備化（極限）に逃げ込んで連続体に滑り落ちること、方針＝極限でも離散構造の観測を維持する（08:41、著者の定義）。K は考える素数の個数ではない（08:38）。
  61| - (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes。このパートで Lean にしたのは L1 の読みの数学的な内容で、§1 の命題 3 そのものではない（独立照合 B の指摘で言い方を直した）。
  62| 
  63| ### 0.1 4 点（着手前の文書 §1 から。08:41 の定義を受けて 1 を直した）
  64| 
  65| 1. 幾何の言葉：どの点（素数たちと無限素点）を、どの位相で測れば、離散な構造の観測が保たれるか。どこで、完備化によって連続体に滑り落ちる（解像度が落ちる）か。
  66| 2. 既存分野の言葉への最善の翻訳：素因数分解の一意性 ℚ_{>0} ≅ ⊕_p ℤ、主 Arakelov 因子と S 単数の対数埋め込み、ℝ の部分群は巡回か稠密、log p/log r が無理数であること。極限の取り方は、すべての素点を同時に測る位相（有限イデールを単数で割った 𝔸_f^×/Ẑ^× の位相、制限直積）と直積の位相の違い（独立照合 C の名前で補った）。
  67| 3. 残余：空（確信度：高）。小さいノート。
  68| 4. 対照群：F_q(t) では値が整数で、どの解像度でも連続体は現れない（完備化 F_q((1/t)) は全不連結）。一般化素数では、通約的な対数なら離散。測らない生成元が無限個だと判定が崩れる（盲検の反例、数値 (17)）。
  69| 
  70| ### 0.2 定義（PAG259.lean）
  71| 
  72| | 記号 | Lean | 内容 |
  73| |---|---|---|
  74| | ρ | `rho` | q ↦ (log q, (v_p(q))_{p 素数}) ∈ ℝ × (`Nat.Primes` → ℤ)。値域は直積の位相（ℤ は離散） |
  75| | ρ（すべての素点を同時に測る位相） | `BoxCoord`・`rhoBox` | `Nat.Primes → ℤ` と同じ集合に離散位相を入れた型と、ρ と同じ写像（独立照合 B の後に足した） |
  76| | log ℚ_{>0} | Part 250 の `logSet` | {log q : q > 0} |
  77| | ⟨S⟩ の像 | `imgST S T` | {(log q, (v_t(q))_{t∈T}) : q ∈ ⟨S⟩} ⊆ ℝ × ℤ^T（独立照合 A の後に足した） |
  78| 
  79| ⟨S⟩ そのもの、測る集合 M は定義せず、仮定（付値が S の外で 0、など）で述べています。
  80| 
  81| ### 0.3 ラベル（CLAUDE.md §7）
  82| 
  83| | 結果 | ラベル | 根拠 |
  84| |---|---|---|
  85| | 付値の組の単射、sup 距離で 1 以上、全射、積公式 | 既知 | 素因数分解の一意性 |
  86| | 異なる 2 素数の対数の群が稠密、log ℚ_{>0} が稠密、log r/log p は無理数 | 既知 | ℝ の部分群は巡回か稠密、p^K ≠ r^M（Gelfond–Schneider で超越的、C） |
  87| | 有限の基礎 ⟨S⟩ での閾値と二分法（測らない素数が 2 つ以上なら稠密、高々 1 つなら閉かつ離散） | 既知（再導出） | 上の 2 つと S 単数定理の ℚ の場合。三つの場合分けをまとめた名前は C も知らない |
  88| | 直積の位相で稠密、すべての素点を同時に測る位相で閉かつ離散 | 既知 | 弱近似（Artin–Whaples）、単射性。イデールの制限直積の位相との対比（C） |
  89| | 対照群、順序版 | 既知 | 自明 |
  90| | L1 の読み、「解像度が落ちる」の定義、ℝ・直積の位相を完備化と読むこと | 著者の解釈の層と読み | 08:38 の選択、08:41 の定義 |
  91| 
  92| - 新規候補：なし。CLAUDE.md §3 の 2 候補にも当たりません。
  93| 
  94| ## 1. 検証表
  95| 
  96| | 主張 | Lean | 数値（step278） | 新規性 |
  97| |---|---|---|---|
  98| | 付値の組は単射、異なる像はある座標で 1 以上離れる（sup 距離） | `eq_of_padicValRat_eq`・`exists_prime_one_le_abs`・`rho_sep` | (1)・(14) | 既知 |
  99| | 積公式 log q = Σ v_s(q) log s | `log_eq_sum_of_support` | (2)（2000 個） | 既知 |
 100| | ∏ s^{k_s} の付値、付値の組への全射、⟨S⟩ の元の表示 | `padicValRat_prod_zpow`・`exists_padicValRat_eq`・`eq_prod_of_support` | (3)（8000 回） | 既知 |
 101| | log ℚ_{>0} の閉包は ℝ | `closure_logSet` | (4) | 既知 |
 102| | 異なる 2 素数の対数の群は稠密、log r/log p は無理数 | `dense_closure_log_primes`・`exists_zpow_near`・`irrational_log_div_log` | (5)（6 組）・(20) | 既知 |
 103| | ファイバーの中：p・r 以外を保って log を近づけられる | `exists_near_of_two_unmeasured`・`exists_near_measured`・`exists_near_in_subgroup` | (7)・(11) | 既知 |
 104| | ファイバーの中：p 以外が同じなら q' = q·p^k、log の差は 0 か log p 以上 | `eq_mul_zpow_of_agree`・`log_sep_of_agree`・`log_sep_one_unmeasured` | (8) | 既知 |
 105| | S をすべて測れば離散、∞ を測らなければ離散 | `exists_mem_one_le_abs_of_support`・`sep_of_inf_unmeasured` | (10) | 既知 |
 106| | 有限の基礎 ⟨S⟩ の閾値と二分法：`imgST S T` の閉包が水平な直線を含む ⇔ 稠密 ⇔ T の外に S の異なる素数が 2 つ。そうでなければ閉かつ離散 | `threshold_iff`・`dense_imgST_iff`・`isClosed_discrete_imgST`・`fiber_sep` | (6)（16 通り）・(8)・(21)（仮定 T ⊆ S の除去テストと証人） | 既知（再導出） |
 107| | S ∪ {∞} から 1 つ落としても格子 | Lean にしていない | (9) | 既知（S 単数定理の形） |
 108| | 直積の位相で ρ の像は稠密、直線 ℝ × {0} が閉包に入る、ρ(1) は孤立点でない、閉包の点 (1, 0) は像にない | `dense_rho_image`・`mem_closure_line_prod`・`rho_one_mem_closure_ne_one`・`closure_rho_not_image` | (12)・(13)・(20) | 既知 |
 109| | すべての素点を同時に測る位相で ρ の像は閉かつ離散、有限台、⟨T⟩ の元 | `isClosed_discrete_rhoBox_image`・`finite_support_padicValRat`・`eq_prod_support` | (12)・(14) | 既知 |
 110| | 対照群（c·ℤ、通約的な対数） | `sep_of_mem_zmultiples`・`mem_zmultiples_of_commensurable`・`sep_of_commensurable` | (15)・(16) | 既知 |
 111| | 無限個の生成元の反例 | Lean にしていない | (17) | 既知（盲検の指摘） |
 112| | 順序版 | `zpow_ge_of_one_lt`・`exists_between_one` | (18) | 既知 |
 113| | 退化例 | `eq_one_of_padicValRat_eq_zero` | (19) | 既知 |
 114| | 補助 | `padicValRat_prime_ne`・`padicValRat_prime_zpow`・`one_le_abs_intCast_sub`・`padicValRat_mul_zpow_zpow`・`log_mul_zpow_zpow`・`rho_one`・`exists_two_primes_not_mem`・`val_ne_of_mem_of_not_mem`・`isClosed_and_discrete_of_subsingleton` | — | — |
 115| 
 116| ## 2. 数値照合（step278.py、21 項目すべて合格、約 5 秒）
 117| 
 118| - 最初の版は 19 項目で、1 回目は 18/19 でした。(18)（⟨p, r⟩ の 1 より大きい最小値が指数の範囲を広げると減ること）が {5, 11} で不合格でした。原因は照合の側です：指数の範囲 K = 5〜40 では最小値 125/121 が変わらず、次に減るのは連分数の次の近似分数（指数 49〜73）からです。K = 80 まで広げて合格しました。最小値は連分数の段で減るので、範囲によっては変わらない区間があります。
 119| - (20)（log r/log p が有理数でないことと、閉包の点 (1, 0) が像にないこと）は独立照合 A の後に足しました。
 120| - (12) は 08:41 の定義を受けて加えた項目です：q_n = p_{n+1}/p_n で log q_n → 0、直積の位相の距離 → 0（n = 15000 で 2^{−15001} の程度）、sup 距離（すべての素点を同時に測る位相）は 1 のまま。
 121| - 独立照合 B の後に足した Lean の文（二分法の 2 つ、すべての素点を同時に測る位相での閉かつ離散）は、(6)・(8)・(14) が数値の側の対応です。
 122| - (21) は B の後に足した第 11 の型の点検です（CLAUDE.md §7）。`threshold_iff` の仮定 T ⊆ S を外すと偽になる例：S = {2, 3}、T = {4}。右辺（T の外に S の異なる素数 2, 3）は真ですが、`padicValRat 4`（Mathlib では素数でない 4 でも 4 の重複度として定義される）を固定すると v_2 が高々 3 通りに決まり、ファイバーの log の値は log 3·ℤ の有限個の平行移動（閉かつ離散）なので、左辺は偽です。非空虚性の証人：S = {2, 3, 5}、T = {2} では両辺が真。
 123| - 数値の確認は証明ではありません。
 124| 
 125| ## 3. Lean（PAG259.lean）
 126| 
 127| - import は PAG258（鎖の続き）。Part 250 の `PAG.Part254.logSet`・`dense_logSet` を使います。名前空間は `PAG.Part259`（ファイル番号に合わせる、これまでの規約）。
 128| - 作業の記録：下書きは `scratch/t255/A.lean`（最初の 37 項目）、`B.lean`（独立照合 A・C の後の 4 項目と def `imgST`）、`C.lean`（B の後の 4 項目と def `BoxCoord`・`rhoBox`）で段階的にコンパイルしました。
 129|   - A.lean で直したもの：`haveI` の代わりに `have`（スタイルの警告）、`push_neg`・`if_pos`・`if_neg`・`dif_pos` の非推奨の警告、`push_cast` が natAbs を |·| に変えた箇所、`Set.Finite.mem_toFinset` の暗黙の引数、依存する if の扱い。
 130|   - 組み立ての 1 回目は、組み立ての script が docstring を挿す前に止まり（`rho_one` の名前の重なり）、ファイルがないままビルドして rc = 1 でした。script を直し、2 回目で rc = 0 です。
 131|   - B.lean で直したもの：`imgST` の関数の引数の型（`fun t : T => …` と書かないと ℕ と推論された）、`Nat.cast_natAbs`・`Int.cast_abs` で |·| に直す箇所、`(0 : Nat.Primes → ℤ) ⟨p, hp⟩` を simp に任せず定義の一致で閉じる箇所。
 132|   - C.lean で直したもの：`singletons_open_iff_discrete` はこの Mathlib にない（`discreteTopology_iff_isOpen_singleton` を使う）。
 133|   - B の後、docstring と節の見出しの「離散のまま」「完備化型の極限」「閾値の片側」などを、形式文に合わせて直しました。
 134| - sorry 0、警告 0、`#print axioms` 45 行（定理と同数）。前の版は `audit255/PAG259_v1.lean`（37 項目）、`PAG259_v2.lean`（41 項目）。
 135| 
 136| ## 4. 残る問い（本来の道）
 137| 
 138| - L1 の読みの数学的な内容は、既知の事実として Lean にできました（§1 の命題 3 そのものを形式化したのではありません）。残る大域の問いは、Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes です。
 139| - 08:41 の方針（極限でも離散構造の観測を維持する）のもとでは、Part 252〜254 の U の極限も、完備化（L²(Ẑ^×)）ではなく直極限の側（すべての素点を同時に測る側）で扱うのが方針に合う、と読めます［推論、確信度：中］。U は有限素点の情報（Ẑ^× の方向）に乗っていて、∞ だけを測る（解像度が落ちた）姿では見えません（自明な指標で位相は 1、`phaseA1_one`）［推論］。
 140| - 次のパートは著者の選択を待ちます（Part 256 は始めていません）。
 141| 
 142| ## 5. 文献の確認の記録（検索ログ）
 143| 
 144| - 着手前の文書で確認済み：arXiv:2608.12418（Washburn–Pardo-Guerra–Zlatanović, "Reciprocal Cost on the Positive Rationals"）の Lemma 4.1（異なる素数 r, s で ℤ log r + ℤ log s は ℝ で稠密）。Prasad, "An analogue of a conjecture of Mazur: a question in Diophantine approximation on tori"（math/0204359）。
 145| - 独立照合 C が挙げた名前のうち、次をウェブで確かめました（2026-11-13、WebSearch）。
 146|   - van der Geer–Schoof, "Effectivity of Arakelov divisors and the theta divisor of a number field", Selecta Math. (N.S.) 6 (2000) 377–398（arXiv:math/9802121）。主 Arakelov 因子は積公式により次数 0、という記述がある。
 147|   - Artin–Whaples, "Axiomatic characterization of fields by the product formula for valuations", Bull. AMS 51 (1945) 469–492。近似定理（弱近似）を含む。
 148|   - Neukirch, Algebraic Number Theory（Grundlehren 322、1999）第 III 章（Riemann–Roch Theory）。英訳では Arakelov 因子を "replete divisor" と呼ぶ（訳者の序文）。
 149|   - Munkres, Topology の定理 20.4：一様位相は直積の位相より細かく箱位相より粗く、添字が無限なら三つは異なる。
 150|   - Furstenberg, "Disjointness in ergodic theory, minimal sets, and a problem in Diophantine approximation", Math. Systems Theory 1 (1967) 1–49（非ラクナリーな乗法的半群）。
 151|   - Tijdeman, "On integers with many small prime factors", Compositio Math. 26 (1973) 319–330、"On the maximal distance between integers composed of small primes", Compositio Math. 28 (1974) 159–162。
 152|   - Cassels–Fröhlich（編）Algebraic Number Theory（1967）は書名を確認。Cassels の章 "Global Fields" の中身は開いていない。Weil の Basic Number Theory、Gelfond–Schneider、Bohr–Jessen、Voronin、Baker、Størmer、Kronecker、Northcott は標準の名前で、この回は個別に確かめていない。
 153| - 新規候補はないので、新規性のための検索ログはありません。
 154| 
 155| ## 6. 収束アラームの状況（CLAUDE.md §7、Part 255 の後）
 156| 
 157| - **兆候 4（既知の事実だけ）：7 パート連続**（Part 249〜255）。Part 255 は着手前から「既知の事実の Lean 化」と明記して行いました。
 158| - 辞書の未記入の件数：0（Part 255 の名前は辞書 §15）。文献照合の未実施の連続パート数：0（着手前の盲検の問いテストと、独立照合 C の名前のウェブでの確認）。兆候 1・2：出ていない（自前の名前 `rho`・`imgST`・`BoxCoord` には C が文献の名前を付けた。問いは構造・分類・次元の型ではない）。
 159| - **著者の補足による向きの直し。** 08:41 の定義は着手前の文書の後に届き、ノートの向き（閉包の連続体を中心にしない）と Lean の節 4 を変えました。これは著者の入力による直しで、こちらの発見ではありません。L1 の数学がこの定義を「確かめた」とは書きません。
 160| - **独立照合 B の検知（言い方の強さ）。** 最初の版の題と結論は、位相を明記しないまま「すべての素点を測れば離散」「極限でも離散のまま」と書いていました。ファイル自身の位相（直積の位相）ではこれは偽で（`rho_one_mem_closure_ne_one`）、成り立つのは sup 距離・すべての素点を同時に測る位相での読みです。また「それが著者の定義する『解像度が落ちる』ことそのもの（確信度：高）」は、数学の事実と読みを混ぜていました。どちらも直しました（§7）。著者の定義に寄せて強く書く向きの誤りで、CLAUDE.md §7 の第 3 の型（主張の格上げ）の検知として記録します。
 161| - §6 の表現：A1 は公準のまま（このパートでは使っていない）。A1 について「導いた」と書かず、「アプローチ」の表現も使っていません。§1 の命題 3 は参照の形（「§1 の命題 3（解像度と有効な姿）」）で書きました（2026-11-12 の著者の指示）。
 162| 
 163| ## 7. 検知記録：独立照合（2026-11-13）
 164| 
 165| - 手順：引き継ぎメモの「パートを閉じるたびに、独立照合を行う」。入力を中立化（自前の名前を Φ1・Ξ1・S1〜S37 に置き換え、`rename.json`）し、構築者の予想を結果の前に書き（`audit255/expected_before_results.md`）、A（逆翻訳）と C（盲検の命名）を新しいエージェントで並行に行った。どちらもツールなし（通知のツール使用回数は 0）。B（照合）は A の後。
 166| - **A（逆翻訳、S1〜S37）の結果**：すべて既知の事実で、標準を超える内容はない（予想どおり）。全体を「付値を固定しない素数が 2 個以上なら log は稠密、1 個なら間隔 log p、0 個なら q が決まる」という 1 つの初等的な原理の言い換えと要約した。予想しなかった指摘：
 167|   1. 閾値の「⇔」が 1 つの文になっていない（像・閉包・連続な成分の定義がなく、ファイバーごとの文から閉包の文への移行がない）。S22 は T = S ∖ {p} の形だけ。→ def `imgST`、`fiber_sep`、`threshold_iff` を足した。
 168|   2. S20・S21 の結論の証人が素数と言っていない（弱い）。→ S20（`exists_mem_one_le_abs_of_support`）の結論に足した。S21（`sep_of_inf_unmeasured`）はほぼ同語反復のまま、ノートにそう書いた。
 169|   3. S35 と S37 から log r/log p の無理数性が出るが、その文がない。→ `irrational_log_div_log` を足した。
 170|   4. 直積の位相の閉包では積公式が消える（x ≠ ℓ(k) の点や台が無限の点が入る）。→ `closure_rho_not_image` を足した。
 171|   5. 連続な成分は「積公式の線形汎関数 ℓ が直積の位相で不連続である」ことの言い換え。ℝ は log の座標からだけ入る。→ ノートの「著者の定義との関係」に記録（予想した第 2 の型の指摘と同じ向き）。
 172|   6. ρ は ℚ 全体で定義されていて、ρ(−q) = ρ(q)、ρ(0) = ρ(±1) = (0, 0)（符号と 0 の情報がない）。文はすべて正の有理数に限っているので影響はない。
 173|   7. 直和の側の「位相を変えると離散」という位相の文は形式化されていない（S30 は sup 距離の文）。→ ノートで、Lean は sup 距離までと書いた（予想どおり）。B の後に `isClosed_discrete_rhoBox_image` を足した。
 174| - **C（盲検の命名、P1〜P7）の結果**：ρ は ℚ の主 Arakelov 因子の写像（イデールの対数）で、像は次数 0 の Arakelov 因子。(i)/(ii) は直積の位相と制限直積（イデール）の位相の対比。P3 は弱近似（Artin–Whaples）の系で、「ℚ^× はイデール群では離散、全直積では稠密」の値の群への像。P4 の三つの場合分けをまとめた名前は知らない。どれも標準の事実で、標準を超える内容はない。予想しなかった指摘：
 175|   1. F_q(t) でも直積の位相では像が稠密（離散が崩れるのは位相の一般の性質）。連続体 ℝ が現れないのは ∞ の座標が整数だから。→ ノートの節 4 の対照群に記録。
 176|   2. F_q(t) では |S ∖ T| ≥ 2 の場合が「離散だが単射でない（核の階数 |S ∖ T| − 1）」に変わる。→ 節 5 に記録（Lean にしていない）。
 177|   3. sup 距離の球にも像の点が無限個入る（有限性は出ない）。有限性の道具は高さ h(q)（log p で重みを付けた ℓ¹ ノルムの半分。Northcott 性）。→ 辞書 §15 に記録。
 178|   4. 半群版は Furstenberg 1967 の非ラクナリー半群、音楽理論ではピタゴラス・コンマと 5 リミット純正律（Part 250 の C の読みと同じ）。
 179|   5. 意味のある主張になるのは量の形（Baker、Tijdeman、Størmer、Arakelov 因子の h⁰ と Riemann–Roch、Tate の学位論文）で、どれも深い既知の結果。
 180| - 予想との照合：A・C とも、主な判定（既知、新しい数学なし、ℝ は log から、積の位相の選び方に依存）は予想どおり。予想しなかったのは、A の 1・2・4・6、C の 1・2・3。C の F_q(t) の直積の位相の指摘は、節 4 の「直積の位相で連続体に滑り落ちる」のうち算術の内容がどこまでかを狭める（離散が崩れるのは一般、ℝ が現れるのはアルキメデス素点）。
 181| - 直したこと：Lean に定理 4 個・定義 1 個（上の 1〜4）、数値に 1 項目（(20)）、ノートの節 3〜5・ラベル・検証表。著者の定義（CLAUDE.md §1）と公理 A1 は変えていない。
 182| - **B（照合、S1〜S41。A の後、v2 に対して）**：S1〜S41 はすべて真で、(5) の主張の数学の部分もほぼ形式文どおり。別物・空虚はなし。S38〜S41 も手で確かめた（S40 の ⇐ は k = 0、⇒ は対偶が S39 の仮定そのもので、T が有限なので ℝ × {k} が開かつ閉）。ずれは言い方の守備範囲：
 183|   1. 「離散」と書くたびに位相を明記していない。題・結論 1・§3 には、ファイル自身の直積の位相では偽になる言い方がある（全素点の座標の像は直積の位相では離散でない）。
 184|   2. 「直和の側」：離散になる理由は有限台ではなく位相の選び方（直積の位相の近似点も有限台）。対比の実体は、同じ集合に細かい位相を入れるか粗い位相を入れるかの違い。位相の文を Lean に足すか、題から外す。
 185|   3. 閾値の守備範囲は有限の基礎 ⟨S⟩、T ⊆ S。ℚ_{>0} を基礎にした文はファイバーの中の距離の文で、有限の解像度の文ではない（ℚ_{>0} では測らない素数がいつも無限個）。強い二分法を書くなら、稠密 ⇔ と閉・離散の文を足す。
 186|   4. 「そのもの」「入口は完備化（確信度：高）」「命題 3 の定式化は書けた」は読み。Lean では ℝ は log の値域として明示的に置かれていて、完備化の構成はない。
 187|   5. 冗長な文を明示する。積公式を満たす点の集合を定義して像と一致させれば、`closure_rho_not_image` の言い方が支えられる。
 188| - B の予想との照合（予想は `expected_before_results.md` と、B の起動直後・結果を見る前に書いた `expected_before_results_B_v2.md`）：S38〜S41 が真、S40 の左辺が「水平な直線を含む」で狭い、題の「極限でも離散のまま」が強い、「完備化型の極限」は解釈の言葉、は予想どおり。予想しなかったのは、1（直積の位相では「全解像度で離散」が偽になること）、2 の「有限台は離散の理由にならない」、3 の「ℚ_{>0} の有限の解像度ではちょうど 1 つの場合が起きない」、4 の「入口は完備化」も読みであること。
 189| - **B の後に直したこと。**
 190|   - Lean：`BoxCoord`・`rhoBox`（def）と `isClosed_discrete_rhoBox_image`（すべての素点を同時に測る位相で像は閉かつ離散）、`dense_imgST_iff`・`isClosed_discrete_imgST`（有限の基礎 ⟨S⟩ の二分法）、一般の補題 `isClosed_and_discrete_of_subsingleton`。docstring と節の見出しを形式文に合わせた。
 191|   - ノート：題、L1 の節（位相の明記）、結論の 1・3・4（守備範囲と位相）、「文献の言葉と対照群（Lean の外）」を結論から分けた、「著者の定義との関係」（ℝ は明示的に置かれている＝高、完備化と読むのは読み＝中）、0.0 (c)、ラベル、検証表。
 192|   - xlsx：`exists_prime_one_le_abs`・`exists_near_of_two_unmeasured`・`exists_near_measured`・`eq_mul_zpow_of_agree`・`log_sep_of_agree`・`exists_near_in_subgroup`・`dense_rho_image`・`rho_sep`・`finite_support_padicValRat`・`closure_rho_not_image` の主張の言い方を直し、新しい 4 行を足した。
 193|   - 数値：(21)（`threshold_iff` の仮定 T ⊆ S の除去テストと非空虚性の証人。CLAUDE.md §7 の第 11 の型）。
 194|   - 直さなかったこと：B の 5 の後半（積公式を満たす点の集合の定義と、像との一致）は Lean にせず、`closure_rho_not_image` の言い方を「(1, 0) は積公式の形を満たさない点」に弱めた。B の後の追加（4 項目）は新しい B に見せていない（Lean のコンパイルで真であることだけを確かめた）。
 195| - 著者の定義（CLAUDE.md §1）と公理 A1 は変えていない。
 196| 
```

## 入力 (5)：表（xlsx）の見出しと各行（原文のまま。主張と証明の要点。★ は前回の照合の時点の版から足した・変えた行）
```
【見出し】PAG2.0-255 §1 の命題 3（解像度と有効な姿）の L1 の読み：測る素点と、極限の取り方（著者が 2026-11-13 08:38 に L1 を読みとして採り、08:41 に「完備化（極限）に逃げ込んで連続体に滑り落ちることを解像度が落ちると言います。連続体が観測されることを望んでいるのではなく、極限でも離散構造の観測を維持します」と定義。L1 は Claude の案。すべて既知の事実の Lean 化）
padicValRat_prime_ne
  主張：異なる素数 s ≠ p で v_s(p) = 0（補助）
  証明の要点：Nat の付値に直す
padicValRat_prime_zpow
  主張：v_s(p^k) は s = p なら k、そうでなければ 0（補助）
  証明の要点：zpow の付値は k 倍
padicValRat_prod_zpow
  主張：∏_{s∈S} s^{k_s}（S は素数の有限集合）の付値は、t ∈ S なら k_t、t ∉ S なら 0
  証明の要点：S の帰納法と積の付値
eq_of_padicValRat_eq
  主張：全解像度の単射（素因数分解の一意性）：すべての素数で付値が一致する正の有理数は等しい
  証明の要点：分子・分母の交差積の Nat の付値がすべて一致
eq_one_of_padicValRat_eq_zero
  主張：退化例：すべての付値が 0 の正の有理数は 1（S = ∅ で ⟨S⟩ = {1}）
  証明の要点：eq_of_padicValRat_eq を 1 と比べる
one_le_abs_intCast_sub
  主張：異なる整数は実数として 1 以上離れる（整数の座標の離散性。補助）
  証明の要点：0 でない整数の絶対値は 1 以上
★ exists_prime_one_le_abs
  主張：すべての素点の付値の組で、異なる正の有理数はある素数の座標で 1 以上離れる（sup 距離の意味。直積の位相では像は離散でない（rho_one_mem_closure_ne_one）。位相の文は isClosed_discrete_rhoBox_image。独立照合 B の指摘で言い方を直した）
  証明の要点：対偶と eq_of_padicValRat_eq
eq_prod_of_support
  主張：台が S に入る正の有理数（⟨S⟩ の元）は q = ∏_{s∈S} s^{v_s(q)}
  証明の要点：両辺の付値を比べる
log_eq_sum_of_support
  主張：積公式：⟨S⟩ の元で log q = Σ_{s∈S} v_s(q)·log s（全解像度では ∞ の座標は有限素点の座標から決まる）
  証明の要点：eq_prod_of_support と log の積・冪
exists_padicValRat_eq
  主張：付値の組への全射：S の上の任意の整数の組 k に、v_s = k_s（s ∈ S）で S の外では付値 0 の正の有理数がある
  証明の要点：q = ∏ s^{k_s}
closure_logSet
  主張：∞ だけを測って完備化すると ℝ 全体：log ℚ_{>0} の閉包は ℝ（Part 250 の dense_logSet から。著者の定義では解像度が落ちた姿）
  証明の要点：稠密なら閉包は全体
dense_closure_log_primes
  主張：異なる 2 つの素数 p, r の対数が生成する加法群は ℝ で稠密（Part 250 の 2 と 3 の場合の一般化）
  証明の要点：最小の正の元があれば両方がその整数倍になり p^K = r^M、素因数分解の一意性に反する
exists_zpow_near
  主張：どの x と ε > 0 にも、|a·log p + b·log r − x| < ε となる整数 a, b がある
  証明の要点：dense_closure_log_primes と 2 元の生成する部分群の元の形
irrational_log_div_log
  主張：異なる素数 p, r で log r / log p は無理数（通約できない。対照群の通約的な場合との違い。独立照合 A の指摘で追加）
  証明の要点：有理数 a/b なら |b|·log r = |a|·log p で r^{|b|} = p^{|a|}、素因数分解の一意性に反する
padicValRat_mul_zpow_zpow
  主張：q₀·p^a·r^b の付値（補助）
  証明の要点：積の付値
log_mul_zpow_zpow
  主張：q₀·p^a·r^b の log（補助）
  証明の要点：log の積・冪
★ exists_near_of_two_unmeasured
  主張：p ≠ r 以外のすべての付値を q₀ と同じに保ったまま（p・r の付値だけが違いうるファイバーの中で）、log を任意の x に ε 以内まで近づけられる（ファイバーの中の文。閉包の文は threshold_iff・dense_imgST_iff）
  証明の要点：q = q₀·p^a·r^b と exists_zpow_near
★ exists_near_measured
  主張：∞ と有限集合 M の素数を測るとき：M の外の素数 p ≠ r があれば、M の座標を q₀ と同じに保ったまま log を x に近づけられる（exists_near_of_two_unmeasured を弱めたもの。閉包が ℝ × {M 座標} を含むことは ε 近似から直ちに出る系で、文にはしていない）
  証明の要点：exists_near_of_two_unmeasured
★ eq_mul_zpow_of_agree
  主張：p 以外のすべての付値が一致する正の有理数は q' = q·p^k（k = v_p q' − v_p q）
  証明の要点：両辺の付値を比べる
★ log_sep_of_agree
  主張：p 以外のすべての付値が一致する 2 元（p の付値だけが違いうるファイバー）は、等しいか ∞ の座標で log p 以上離れる（ファイバーの中の距離の文。ℚ_{>0} の有限の解像度の文ではない。独立照合 B の指摘で言い方を直した）
  証明の要点：log q' − log q = k·log p で |k| ≥ 1
exists_mem_one_le_abs_of_support
  主張：⟨S⟩ の全解像度：S の素数をすべて測れば、⟨S⟩ の異なる元は S のある素数の座標で 1 以上離れる（証人が素数であることは独立照合 A の指摘で結論に足した）
  証明の要点：exists_prime_one_le_abs で見つかる素数は S の中
sep_of_inf_unmeasured
  主張：∞ を測らないとき：有限素点の座標が違えば 1 以上離れる（整数の座標なので。ほぼ同語反復）
  証明の要点：one_le_abs_intCast_sub
log_sep_one_unmeasured
  主張：⟨S⟩ で S の素数 p だけを測らないとき：p 以外の S の座標が一致する 2 元は、等しいか ∞ の座標で log p 以上離れる
  証明の要点：S の外では付値が 0 なので log_sep_of_agree
★ exists_near_in_subgroup
  主張：⟨S⟩ で S の素数 p ≠ r を測らないとき：⟨S⟩ の中にとどまり、T の座標を q₀ と同じに保ったまま log を x に近づけられる（閉包の文は threshold_iff・dense_imgST_iff）
  証明の要点：exists_near_of_two_unmeasured。p, r ∈ S なので S の外の付値は変わらない
fiber_sep
  主張：測らない素数（S ∖ T の元）が高々 1 つなら、T の座標が同じ ⟨S⟩ の 2 元は、等しいか、∞ の座標で一定の c > 0 以上離れる（c = log p、または S ⊆ T なら c = 1 で必ず等しい。独立照合 A の指摘で追加）
  証明の要点：S ∖ T = {p} なら log_sep_of_agree、S ⊆ T なら eq_of_padicValRat_eq
threshold_iff
  主張：閾値の定理（閉包の 1 つの文。独立照合 A の指摘で追加）：基礎 ⟨S⟩（S は素数の有限集合）、T ⊆ S、∞ と T の素数を測るときの像 imgST S T（def）の閉包が、ある水平な直線 ℝ × {k} 全体を含む ⇔ T の外に S の異なる素数が 2 つある（著者の定義では、閉包に連続体が入る＝解像度が落ちる）
  証明の要点：⇐：exists_near_in_subgroup を q₀ = 1 で使い、k = 0 の直線。⇒：測らない素数が高々 1 つなら fiber_sep の間隔 c で、x = log q₀ + c/2 の近くに像の点がないことと矛盾。ℤ^T は有限個の離散空間の積なので {k} は開集合
★ isClosed_and_discrete_of_subsingleton
  主張：一般の補題：T1 空間で、どの点にも集合 A と高々 1 点でしか交わらない近傍があれば、A は閉かつ（部分空間として）離散（独立照合 B の後に追加）
  証明の要点：補集合の点は、A と交わる点を除いた近傍で離れる。部分空間の 1 点集合は開集合の引き戻し
★ dense_imgST_iff
  主張：閾値の二分法（片側）：基礎 ⟨S⟩、T ⊆ S で、像 imgST S T が ℝ × ℤ^T で稠密 ⇔ T の外に S の異なる素数が 2 つある（独立照合 B の指摘で追加）
  証明の要点：⇒：threshold_iff。⇐：任意の (x, k) について、T の座標 k を実現する q₀（exists_padicValRat_eq）から exists_near_in_subgroup
★ isClosed_discrete_imgST
  主張：閾値の二分法（もう片側）：T の外に S の異なる素数が 2 つないとき（測らない素数が高々 1 つ）、像 imgST S T は ℝ × ℤ^T の中で閉かつ離散（独立照合 B の指摘で追加）
  証明の要点：fiber_sep の間隔 c で、近傍 B(x, c/2) × {k} は像と高々 1 点で交わる
rho_one
  主張：すべての素点の座標 ρ(q) = (log q, (v_p(q))_p)（def rho、値域 ℝ × (Nat.Primes → ℤ)）で ρ(1) = (0, 0)（補助）
  証明の要点：定義の計算
exists_two_primes_not_mem
  主張：素数の有限集合の外に、異なる素数が 2 つある（補助）
  証明の要点：素数は無限個
val_ne_of_mem_of_not_mem
  主張：I の元と I の外の元は自然数として異なる（補助）
  証明の要点：部分型の外延性
★ dense_rho_image
  主張：直積の位相（Nat.Primes → ℤ の既定の位相。各近傍は有限個の素点しか見ない）では ρ の像は ℝ × (Nat.Primes → ℤ) で稠密（これを著者の言葉の「完備化（極限）に逃げ込んで連続体に滑り落ちる」にあたると読むのは読み）
  証明の要点：近傍は ∞ の座標の ε 近傍と有限個の素数の座標の指定を含む。指定を q₀ で実現し、その外の 2 素数で log を合わせる
mem_closure_line_prod
  主張：系：直積の位相では、ℝ × {0} の直線全体が ρ の像の閉包に入る
  証明の要点：dense_rho_image
★ closure_rho_not_image
  主張：直積の位相の閉包には像にない点が入る：(1, 0) は ρ の像の閉包に入るが、どの正の有理数の像でもない。(1, 0) は積公式の形 x = Σ k_p log p（log_eq_sum_of_support）を満たさない（独立照合 A の指摘「閉包では積公式が消える」。像＝積公式を満たす点の集合という特徴づけは文にしていない）
  証明の要点：mem_closure_line_prod と、付値がすべて 0 なら q = 1 で log q = 0
rho_one_mem_closure_ne_one
  主張：直積の位相では ρ(1) は孤立点でない：1 と異なる正の有理数の像が ρ(1) のどの近傍にもある
  証明の要点：目標 ε/2 で近づけ、0 < log q < ε
★ rho_sep
  主張：異なる正の有理数の ρ の像は、ある素数の座標で 1 以上離れる（sup 距離で 1 以上。exists_prime_one_le_abs の言い換え。位相の文は isClosed_discrete_rhoBox_image。独立照合 B の指摘で言い方を直した）
  証明の要点：exists_prime_one_le_abs
★ isClosed_discrete_rhoBox_image
  主張：すべての素点を同時に測る位相（def BoxCoord：Nat.Primes → ℤ に離散位相。ℤ 値では箱・一様の位相と同じ。def rhoBox は ρ と同じ写像）では、正の有理数の像は閉かつ離散。同じ集合が直積の位相では稠密で、離散になるかどうかは位相の選び方で決まる（独立照合 B の指摘で追加）
  証明の要点：近傍 ℝ × {k} は像と高々 1 点で交わる（eq_of_padicValRat_eq）
★ finite_support_padicValRat
  主張：付値の組は有限台：付値が 0 でない素数は有限個（各正の有理数は有限の段 ⟨T⟩ に住む）。有限台だけでは離散にならない（rho_one_mem_closure_ne_one の近似点も有限台。独立照合 B の指摘）
  証明の要点：そのような素数は |分子|·分母 を割る
eq_prod_support
  主張：各正の有理数は、その台 T の段 ⟨T⟩ の元：q = ∏_{s∈T} s^{v_s(q)}
  証明の要点：eq_prod_of_support
sep_of_mem_zmultiples
  主張：対照群：値が c·ℤ（c > 0）に入れば、異なる値は c 以上離れる（F_q(t) では c = log q。自明）
  証明の要点：差は c の 0 でない整数倍
mem_zmultiples_of_commensurable
  主張：対照群：対数が通約的（n·L₂ = m·L₁、n > 0）なら a·L₁ + b·L₂ = (a n + b m)·(L₁/n)（自明）
  証明の要点：代入と通分
sep_of_commensurable
  主張：対照群のまとめ：通約的な 2 つの対数の整数結合は、異なれば L₁/n 以上離れる（連続体は現れない）
  証明の要点：sep_of_mem_zmultiples と mem_zmultiples_of_commensurable
zpow_ge_of_one_lt
  主張：順序版：⟨p⟩ の大きさの順序は離散（1 < p^k なら p ≤ p^k、1 より大きい最小の元は p）
  証明の要点：k ≥ 1 と冪の単調性
exists_between_one
  主張：順序版：⟨p, r⟩（p ≠ r）の大きさの順序には 1 より大きい最小の元がない（どの y > 1 にも 1 < p^a r^b < y）
  証明の要点：exists_zpow_near で 0 < a log p + b log r < log y
```

## 入力 (6)：逆翻訳の査読者 A2 の出力の全文（原文のまま）
A2 は ★ の文を、名前を中立化した入力で判定しました。名前の対応：S1 = `padicValRat_prime_ne`、S2 = `padicValRat_prime_zpow`、S3 = `padicValRat_prod_zpow`、S4 = `eq_of_padicValRat_eq`、S5 = `eq_one_of_padicValRat_eq_zero`、S6 = `one_le_abs_intCast_sub`、S7 = `exists_prime_one_le_abs`、S8 = `eq_prod_of_support`、S9 = `log_eq_sum_of_support`、S10 = `exists_padicValRat_eq`、S11 = `closure_logSet`、S12 = `dense_closure_log_primes`、S13 = `exists_zpow_near`、S14 = `padicValRat_mul_zpow_zpow`、S15 = `log_mul_zpow_zpow`、S16 = `exists_near_of_two_unmeasured`、S17 = `exists_near_measured`、S18 = `eq_mul_zpow_of_agree`、S19 = `log_sep_of_agree`、S20 = `exists_mem_one_le_abs_of_support`、S21 = `sep_of_inf_unmeasured`、S22 = `log_sep_one_unmeasured`、S23 = `exists_near_in_subgroup`、S24 = `rho_one`、S25 = `exists_two_primes_not_mem`、S26 = `val_ne_of_mem_of_not_mem`、S27 = `dense_rho_image`、S28 = `mem_closure_line_prod`、S29 = `rho_one_mem_closure_ne_one`、S30 = `rho_sep`、S31 = `finite_support_padicValRat`、S32 = `eq_prod_support`、S33 = `sep_of_mem_zmultiples`、S34 = `mem_zmultiples_of_commensurable`、S35 = `sep_of_commensurable`、S36 = `zpow_ge_of_one_lt`、S37 = `exists_between_one`、S38 = `irrational_log_div_log`、S39 = `fiber_sep`、S40 = `threshold_iff`、S41 = `closure_rho_not_image`、S42 = `isClosed_and_discrete_of_subsingleton`、S43 = `dense_imgST_iff`、S44 = `isClosed_discrete_imgST`、S45 = `isClosed_discrete_rhoBox_image`、Ξ1 = `logSet`、Ξ2 = `imgST`、Ξ3 = `BoxCoord`、Φ1 = `rho`、Φ2 = `rhoBox`

# 査読結果（S42〜S45）

記号の約束：v_p は p 進付値です。「S 単数」は、素因数がすべて S に入る正の有理数を指します。ℤ^T は T の元から ℤ への関数全体です。対象の文はコンパイル済みという前提を受け入れたうえで、真偽も数学的に独立に確かめました（すべて正しい）。

## 1. 翻訳（確信度 高）

- **Ξ3・Φ2**
  - Ξ3 は、集合としては ℤ^{素数}（素数全体から ℤ への関数）と同じで、位相だけを離散位相に置き換えた型です。
  - Φ2(q) = (log q, (v_p(q))_p) ∈ ℝ × Ξ3 です。式は Φ1 と同じです。q ≤ 0 では log 0 = 0、v_p(0) = 0 と約束され、符号は無視されます。
- **S42**：X を T1 位相空間、A ⊆ X とする。X のすべての点 z（A の点に限らない）に、U ∩ A が高々 1 点となる z の近傍 U があるとき、A は閉集合で、部分空間位相が離散である。
- **S43**：S を素数だけからなる有限集合、T ⊆ S とする。S 単数 q の像 Ξ2 S T = {(log q, (v_t(q))_{t∈T})} ⊆ ℝ × ℤ^T は、S \ T が相異なる 2 つの素数を含むとき、かつそのときに限り稠密である。ここで ℤ^T は有限個の離散空間の積なので離散。
- **S44**：S を素数だけからなる有限集合とする。T は任意の自然数の有限集合でよい（T ⊆ S も、T が素数からなることも仮定しない）。S \ T の元が高々 1 個なら、Ξ2 S T は ℝ × ℤ^T の閉集合で、部分空間位相が離散である。
- **S45**：正の有理数全体の像 Φ2(ℚ_{>0}) は、ℝ × Ξ3（第 2 成分は離散位相）の閉集合で、部分空間位相が離散である。

## 2. 判定

- **S42：実質的（標準）**（確信度 高）
  - 一般位相の小さな補題です。z ∈ A なら U ∩ A = {z} なので z は孤立点です。z ∉ A なら U ∩ A は空か {a}（a ≠ z）で、後者でも T1 から U \ {a} が A と交わらない近傍になります。
  - 逆（閉かつ離散 ⇒ 仮定）は任意の空間で成り立ちます。したがって S42 は、T1 空間での閉離散集合の特徴づけの片方向です。
- **S43：実質的（標準）**（確信度 高）
  - 中身は二つの組み合わせです。一つは、log p / log r が無理数（S38）なので {a log p + b log r} が稠密（S12・S13）という古典的な事実です。もう一つは、|S\T| ≤ 1 なら各ファイバー ℝ×{k} 上の点が 1 点か (log p)ℤ の平行移動になる、という観察です。
  - S40 に対する新しさは小さいです（5 節）。
- **S44：実質的（標準）**（確信度 高）
  - S39 は、同じ仮定 hS・h1 の下で一様な分離定数 c を与えます。これに S42 を当て、U = (x − c/2, x + c/2) × {k} を取れば、U ∩ Ξ2 は高々 1 点です。
  - S39 から定数 c を捨てた位相的な帰結なので、内容は S39 より弱いです。
- **S45：自明**（位相の選び方でほぼ決まり、ほぼ同語反復に近い。確信度 高）
  - Ξ3 が離散なので、ℝ × Ξ3 は開集合 ℝ×{k} の非交和です。像と ℝ×{k} の共通部分は、素因数分解の一意性（S4）から高々 1 点です。どのファイバーとも高々 1 点でしか交わらない集合は、常に閉かつ離散です。
  - ℝ 成分（log）はまったく使われず、log を任意の関数に替えても成り立ちます。
- 偽または空虚の疑いのある文はありません（確信度 高）。

## 3. 仮定の点検

**S42**（確信度 高）
- T1 を外すと、閉性の部分が偽になります。反例は 2 点の密着空間 X = {a, b} と A = {a} です。近傍 X との共通部分は {a} だけですが、{a} は閉ではありません。離散性の部分は T1 なしでも成り立ちます。
- h を外すと偽になります（ℝ の中の ℚ）。h が「X のすべての点」について要求していることが閉性に効いています。実際、ℝ の中の {1/n : n ≥ 1} は A の各点では条件を満たしますが、閉ではありません。
- 満たす例は ℝ の中の ℤ や A = ∅ で、空虚ではありません。

**S43**（確信度 高）
- hS は必要です。S = {4, 6}、T = ∅ では右辺は真です。しかし台の条件は素数にしか掛からないので q = 1 だけになり、Ξ2 = {0} ⊂ ℝ は稠密ではありません。
- hTS も必要です。S = {2, 3}、T = {5} では右辺は真です。しかし 5 の座標は恒等的に 0 なので、像は k(5) = 1 となる ℝ×{k} と交わらず、稠密ではありません。
- 満たす例は S = {2, 3}・T = ∅（両辺とも真）と、S = {2}・T = ∅（両辺とも偽）です。

**S44**
- h1 は必要です（確信度 高）。S = {2, 3}、T = ∅ では Ξ2 = {a log 2 + b log 3} が ℝ の中で可算かつ稠密になり、閉でも離散でもありません。
- **hS は不要です**（確信度 高）。
  - Ξ2 の条件は素数 t にしか掛からないので、Ξ2 S T = Ξ2 (S ∩ 素数) T です。
  - h1 は部分集合に遺伝し、S ∩ 素数は hS を満たします。したがって S44 を S ∩ 素数に当てれば、一般の S でも結論が出ます。
  - 無害ですが余分な仮定です。文脈の S39 の hS についても同じことが言えます。
- T ⊆ S を仮定しないのは正しい一般化です（T の座標が増えるほど分離は易しくなる）。ただし合成数 t の座標は付値ではないので、中身のある一般化ではありません（確信度 高）。
- 満たす例は S = {2}、T = ∅（Ξ2 = (log 2)ℤ）で、空虚ではありません。

**S45**：仮定はありません。像は Φ2(1) = (0, 0) を含むので空ではありません。

## 4. 定義の点検

- **Φ1・Φ2**（確信度 高）
  - どちらも q ↦ (log|q|, 付値の列) です。q ≤ 0 の規約（Φ(0) = Φ(1)、Φ(−q) = Φ(q)）は、対象の文がすべて q > 0 に制限しているので無害です。
  - 値域は全直積 ∏ℤ ですが、像は有限台の部分 ⊕ℤ に入ります。直積位相では ⊕ℤ が ∏ℤ で稠密であることが、S27 型の稠密性に効いています。
- **Ξ2**（確信度 高）：S 単数を「無限素点と T の素点」に埋め込んだ像です。S と T には任意の自然数の Finset が許されるので、次の 2 点に注意が要ります。
  - Ξ2 S T は、S に S ∩ 素数を通してしか依存しません。S43 では右辺が S の元そのものを数えるので hS が必要になり、S44 では不要になるのはこのためです。
  - T に合成数 t があると、padicValRat t は付値ではありません（t = 0, 1 では恒等的に 0）。S 外の素数なら、その座標は恒等的に 0 です。S43 では hS・hTS がこれを除きますが、S44 では除かれません（真偽には影響しない）。
- **Ξ3**
  - 離散位相は ∏ℤ の箱位相に一致します（確信度 高）。⊕ℤ に制限すれば、イデールを単数で割ったときの制限直積位相とも一致します（確信度 中）。したがって選び方自体は不自然ではありませんが、この選択で S45 は自明になります。
  - Ξ3 は `def`（abbrev ではない）なので、直積位相のインスタンスは推論されません。`⟨rfl⟩` が通っていることから、宣言した ⊥ が実際に使われていると分かります（確信度 高）。
- **細かい点**：コメントには Ξ3 を「S42〜S45 で使う」とありますが、実際に使うのは S45 だけです。Ξ1 は対象の文に出てきません。

## 5. 全体の所見

**言えていること**
- T ⊆ S の下では、S43 と S44 を合わせると二分法になります（確信度 高）。
  - |S\T| ≥ 2 なら稠密、|S\T| ≤ 1 なら閉かつ離散です。
  - 可算な稠密集合は ℝ × ℤ^T の中で閉になれないので、二つの場合は排他的です。
  - ただし、この二分法を 1 つの文として述べた定理はありません。
- 素数全体の座標を使う場合、結論は位相の選び方だけで決まります（確信度 高）。
  - 直積位相では稠密です（S27）。S29 によれば Φ1(1) は他の点の集積点です。
  - 離散（＝箱）位相では閉かつ離散です（S45）。
- S45 は、S44 の S\T = ∅ の場合を無限に広げた類似と見られます（確信度 中）。

**言えていないこと・注意**
- S44 の逆（h1 が破れれば閉離散ではない）は、T ⊆ S のときに S43 から従うだけです。T ⊄ S の場合は述べられていません。
- S44 は S39 の一様な分離定数を捨てています。
- S45 は、素因数分解の一意性（S4・S30）を離散位相で言い直したものにすぎません。ℝ 成分、余コンパクト性、商の構造については何も言いません。S45 を「有理数がアデール的な空間に離散に入る」という非自明な結果として読むのは過大評価です（確信度 高）。
- 4 文とも古典的・初等的で、標準を超える内容はありません（確信度 高）。

**入力 (2) との関係**
- **S42**：(2) とは独立な一般補題で、S44・S45 の道具です。
- **S43**：S40 の言い換えかつ強化です。
  - S40 の左辺は「ある k でファイバー全体が閉包に入る」（∃k）で、S43 の Dense は ∀k にあたります。
  - → は S40 から直ちに出ます（k = 0 を取る）。
  - ← は S10（T 上の付値を指定した q₀ を作る）と S23 から出ます。
- **S44**：S39 の位相的な系で、背景には S19・S22 があります。
- **S45**：S4（または S30）と S42 の系で、S27・S29・S41 と位相だけを替えた対になっています。

使ったツール：Read 1 回のみ

## 課題
1. 表（入力 (5)）：各行の主張と証明の要点を形式文と突き合わせ、「一致／主張が強い／主張が弱い／別物／偽」で判定してください。★ の行はすべて判定を書いてください。ほかの行は、ずれがあるものだけ挙げ、残りは「一致」とまとめて構いません。
2. ノート（入力 (4)）：題、冒頭の結論・位置づけ・読み、検証表、「Lean にしていないこと」を形式文と突き合わせてください。形式文より強い箇所、形式文にないことを形式文の事実として書いた箇所、解釈の言葉を事実として書いた箇所を、行番号つきで挙げてください。変わった行の範囲は必ず見てください。
3. Lean ファイルの文面（入力 (3)）：冒頭の説明と docstring について同じ観点で。★ の宣言は必ず見てください。
4. ★ の文について、A2 の訳と判定（入力 (6)）と、文面の言い方が食い違うところを挙げてください。
5. 直すべき点を重要な順に挙げてください。各点に、どこを、どう直すかを、形式文から起こした言い方の案で書いてください。
6. 全体：形式文に偽・空虚・別物があるか。標準を超える内容があるか。
