あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、コンパイル済みの形式文と、それについて書かれた文面（ノート、表、Lean ファイルの docstring）を突き合わせ、文面が形式文の内容を正しく述べているかを判定してください。

## 守ってほしいこと
- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 文面には、著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）が出てきます。「読み」「解釈」と明示されていれば許容です。形式文の事実として書かれていれば、ずれとして挙げてください。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、6,000 字程度までにまとめてください。最後に、使ったツール（使っていなければ「なし」）を書いてください。

## Mathlib の前提
`ZMod N` は ℤ/N、`(ZMod N)ˣ` は単数群、`t.val` は 0 以上 N 未満の代表。`stdAddChar` は t ↦ exp(2πi·t.val/N)。`DirichletCharacter ℂ N` は法 N のディリクレ指標（単数でないところで 0）。`IsPrimitive` は導手が法に等しいこと、`Even` は χ(−1) = 1、`Odd` は χ(−1) = −1。`gaussSum χ ψ = Σ_a χ(a)ψ(a)`。`χ.conductor` は導手、`χ.primitiveCharacter` は χ を誘導する原始指標（法は導手）、`changeLevel h χ` は法を倍数に上げた指標。`ZMod.unitsMap h` は (ℤ/M)ˣ → (ℤ/N)ˣ の自然な準同型。`starRingEnd ℂ` は複素共役。`Submodule.span` は張る部分空間、`iSupIndep` は部分空間の族の独立、`⨆` は族の和。`Module.DirectLimit` は加群の帰納極限（代数的な直極限、完備化はしない）。`Complex.normSq z = |z|²`。

## 入力 (1)：定義の全文（このファイルと前のファイル。原文のまま。コメントと docstring だけ除いた）
```lean
-- PAG256.lean（文脈：namespace PAG.Part256 / open ZMod Complex Finset / variable {N : ℕ} [NeZero N]）

noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

-- PAG257.lean（文脈：namespace PAG.Part257 / open ZMod Complex Finset PAG.Part256 / variable {N : ℕ} [NeZero N]）

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

-- PAG258.lean（文脈：namespace PAG.Part258 / open ZMod Complex Finset PAG.Part256 PAG.Part257 DirichletCharacter / variable {N : ℕ} [NeZero N]）

instance conductor_neZero (χ : DirichletCharacter ℂ N) : NeZero χ.conductor :=
  ⟨conductor_ne_zero (χ := χ)⟩

noncomputable def phaseA1 (χ : DirichletCharacter ℂ N) : ℂ := rootNum χ.primitiveCharacter

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

-- PAG260.lean（文脈：open DirichletCharacter ZMod Complex / namespace PAG.Part260 / variable {M N : ℕ} [NeZero M] [NeZero N]）

instance : NeZero (M * N) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne N)⟩

noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂

def crtMap (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))

open Classical in
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```

## 入力 (2)：形式文の全文（PAG260.lean の定理 23 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
★ は、前回の照合の後に足した文・文を変えた文です。
```lean
theorem cast_crtMap_fst (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
theorem cast_crtMap_snd (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
theorem crtMap_bijective (h : M.Coprime N) : Function.Bijective (crtMap M N)
theorem stdAddChar_crtMap (x : ZMod M × ZMod N) :
    stdAddChar (crtMap M N x) = stdAddChar x.1 * stdAddChar x.2
theorem prodChar_apply (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    prodChar χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
omit [NeZero M] [NeZero N] in
theorem crossSign_of_odd {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : crossSign χ₁ χ₂ = -1
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_left {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : crossSign χ₁ χ₂ = 1
omit [NeZero M] [NeZero N] in
theorem crossSign_of_even_right (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : crossSign χ₁ χ₂ = 1
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂)
theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (prodChar χ₁ χ₂).IsPrimitive
theorem phaseA1_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.phaseA1 (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)
theorem UA1_charU_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    PAG.Part258.UA1 (PAG.Part257.charU (prodChar χ₁ χ₂)) =
      (crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂)) •
        PAG.Part257.charU (prodChar χ₁ χ₂)
theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
    (w2 : PAG.Part256.rootNum χ₂ = 1) (w12 : PAG.Part256.rootNum (prodChar χ₁ χ₂) = 1) :
    crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
theorem exists_primitive_odd_five : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd
-- ★ 
theorem rootNum_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      χ₁.Odd ∧ χ₂.Odd ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) ≠ PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂
-- ★ 
theorem rootNum_prodChar_eq_neg_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 13), χ₁.IsPrimitive ∧
      χ₂.IsPrimitive ∧ χ₁.Odd ∧ χ₂.Odd ∧ χ₁ ((13 : ℕ) : ZMod 3) * χ₂ ((3 : ℕ) : ZMod 13) = 1 ∧
      PAG.Part256.rootNum (prodChar χ₁ χ₂) =
        -(PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂) ∧
      PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂ ≠ 0
theorem phaseA1_prodChar_ne_mul :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      PAG.Part258.phaseA1 (prodChar χ₁ χ₂) ≠ PAG.Part258.phaseA1 χ₁ * PAG.Part258.phaseA1 χ₂
theorem norm_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
omit [NeZero M] [NeZero N] in
theorem norm_cross (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    PAG.Part257.charU (prodChar χ₁ χ₂) u =
      PAG.Part257.charU χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        PAG.Part257.charU χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
```

## 入力 (3)：Lean ファイルの文面（ファイル冒頭の説明と、各宣言の docstring。原文のまま）
```
【ファイル冒頭の説明】
/-
アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法の原始指標の積の上での、貼り合わせ U の固有値 — 交差項の法則

問いの出所：著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の
「無限素点を含む大域対象」と「重なり」。Part 252〜254 の貼り合わせ U（公準 A1 の位相＝ルート数 W を固有値とする）を、
Part 255 の L1（測る素点の集合）とつなぐ問い：互いに素な法 M, N の局所の貼り合わせから、法 M·N の貼り合わせは決まるか。

答え（すべて既知の事実の Lean 化。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）：
1. 中国剰余定理の分解 a = a₁·N + a₂·M（`crtMap`・`crtMap_bijective`）と、加法指標の分解（`stdAddChar_crtMap`）。
2. 指標の積 `prodChar χ₁ χ₂`（法 M·N）とその値（`prodChar_apply`・`charU_prodChar`・`prodChar_neg_one`）。
3. ガウス和の乗法性 τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`。原始性は要らない）。
4. 無限素点の因子のずれ ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)、s = −1（両方が奇）か +1（`crossSign`・`parFac_prodChar`）。
5. 交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項の絶対値は 1
   （`norm_cross`）。
6. 原始指標の積は原始（`isPrimitive_prodChar`）。したがって公準 A1 の位相と貼り合わせ U でも同じ法則
   （`phaseA1_prodChar`・`UA1_charU_prodChar`）。
7. 法 15 = 3·5 で W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（`rootNum_prodChar_ne_mul`・
   `phaseA1_prodChar_ne_mul`）。法 39 = 3·13 で、交差項は 1 だが符号だけで W(χ₁χ₂) = −W(χ₁)·W(χ₂) となる組がある
   （`rootNum_prodChar_eq_neg_mul`。独立照合 B の指摘で追加）。等号になる組もあり、ずれは「一般には」起きる。
8. 3 つの位相がすべて 1 なら交差項は符号で打ち消される（`cross_eq_sign_of_rootNum_one`。条件つきの文。2 次の指標では
   平方剰余の相互法則と同じ形だが、3 つの仮定は外から入れるもので、ここから相互法則が出るのではない）。

言い方の注意（着手前の盲検の問いテストの指摘）：大域の ε 因子は局所の ε 因子の積である（Tate、Deligne）。ここで言う
ずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ のルート数の積と、χ₁χ₂ のルート数との差。交差項は、χ₁ の、
N を割る素点での局所成分（不分岐だが自明でない）から出る。「大域は局所の積ではない」とは書かない。
A1 は公準のまま。ここでの文は、ルート数という量についての恒等式で、A1 から何かを出すものではない。

範囲（独立照合 B の指摘）：ここでの文は、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値の式。法 M·N の
すべての指標が積の形に一意に書けること、作用素全体の式、素数冪ごとの分解は Lean にしていない。互いに素の仮定は、
ガウス和の法則と交差項の法則では外しても成り立つ（両辺 0）が、仮定つきのまま。

Lean にしていないこと：原始でない指標の位相の法則（導手 d₁, d₂ での交差項 χ₁*(d₂)·χ₂*(d₁)。数値 step279 の (4)）、
作用素の形（テンソル積と平行移動。指標の基底の上の文 `UA1_charU_prodChar` まで）、3 つ以上の法（数値 (7)）、
互いに素でない法（両辺が 0 になる。数値 (10)）、対照群 F_q[t]（数値 (5)）、イデール類指標の局所成分と局所の ε 因子。
-/

【（名前のない instance、45 行目）】
/-- 法の積は 0 でない。 -/

【prodChar】
/-- 互いに素な法 M, N の指標の積（法 M·N の指標）。 -/

【crtMap】
/-- 分解の写像 (a₁, a₂) ↦ a₁·N + a₂·M（mod M·N）。 -/

【cast_crtMap_fst】
/-- 分解の写像の法 M への像は a₁·N。 -/

【cast_crtMap_snd】
/-- 分解の写像の法 N への像は a₂·M。 -/

【crtMap_bijective】
/-- 互いに素な法では、分解の写像は全単射（中国剰余定理）。 -/

【stdAddChar_crtMap】
/-- 加法指標は分解の写像で積に分かれる：e((a₁N + a₂M)/(MN)) = e(a₁/M)·e(a₂/N)。 -/

【prodChar_apply】
/-- 積の指標の値：(χ₁χ₂)(a) = χ₁(a mod M)·χ₂(a mod N)（単数でない a では両辺 0）。 -/

【gaussSum_prodChar】
/-- **互いに素な法でのガウス和の乗法性**：τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)。原始性は要らない。 -/

【prodChar_neg_one】
/-- (χ₁χ₂)(−1) = χ₁(−1)·χ₂(−1)。 -/

【crossSign】
/-- 交差項の符号：両方が奇のとき −1、それ以外は +1。 -/

【crossSign_of_odd】
/-- 両方が奇なら符号は −1。 -/

【crossSign_of_even_left】
/-- 左が偶なら符号は 1。 -/

【crossSign_of_even_right】
/-- 右が偶なら符号は 1。 -/

【parFac_prodChar】
/-- 無限素点の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = parFac は 偶で 1、奇で −i）。 -/

【rootNum_prodChar】
/-- **交差項の法則**：W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。原始性は要らない。 -/

【isPrimitive_prodChar】
/-- 積の導手：χ₁, χ₂ が原始なら χ₁χ₂ も原始（法 M·N）。 -/

【phaseA1_prodChar】
/-- 公準 A1 の位相（Part 254 の `phaseA1`）での交差項の法則（原始指標）。 -/

【UA1_charU_prodChar】
/-- 貼り合わせ U（Part 254 の `UA1`）は、原始指標の積を、局所の位相の積に交差項を掛けた値で動かす。 -/

【cross_eq_sign_of_rootNum_one】
/-- 2 次の指標などで 3 つの位相がすべて 1 なら、交差項は符号で打ち消される（平方剰余の相互法則と同じ形。
3 つの仮定は外から入れるもので、ここからは出ない）。 -/

【exists_primitive_odd_five】
/-- 証人：法 5 の奇の原始指標がある。 -/

【rootNum_prodChar_ne_mul】
/-- **中国剰余定理の成分の積とのずれの例**（法 15 = 3·5）：原始指標 χ₁（法 3）、χ₂（法 5）で
W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となるものがある。 -/

【rootNum_prodChar_eq_neg_mul】
/-- **符号だけでずれる例**（法 39 = 3·13。独立照合 B の指摘で追加）：奇の原始指標 χ₁（法 3）、χ₂（法 13）で、
交差項 χ₁(13)·χ₂(3) = 1 だが W(χ₁χ₂) = −W(χ₁)·W(χ₂) となるものがある。 -/

【phaseA1_prodChar_ne_mul】
/-- 同じ例を貼り合わせ U の言葉で：法 15 で、U の固有値（公準 A1 の位相）が局所の位相の積と違う原始指標の組がある。 -/

【norm_char_unit】
/-- 単数での指標の値の絶対値は 1（Mathlib の `DirichletCharacter.unit_norm_eq_one` と同じ証明。そのモジュールは
この環境でビルドしていないので、ここに置く）。 -/

【norm_cross】
/-- 交差項の大きさは 1：互いに素な法では ‖χ₁(N)·χ₂(M)‖ = 1（位相だけのずれ）。 -/

【charU_prodChar】
/-- 積の指標は、中国剰余定理の 2 つの成分の関数の積：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)。 -/
```

## 入力 (4)：ノートの全文（原文のまま、行番号つき）
前回の照合の時点の版から変わった行（または足した行）の範囲：1〜3、6〜17、20〜21、74、80〜84、89、101〜103、115〜121、127、132〜143
```
   1| # アーデル射影幾何 — Part 256（PAG 2.0）：互いに素な法 M, N の原始指標の積の上での、貼り合わせ U の固有値 — 位相（ルート数）は W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)。中国剰余定理の成分の位相の積から、一般には、交差項 χ₁(N)·χ₂(M) と偶奇の符号 s だけずれる。既知の事実の Lean 化
   2| 
   3| 2026-11-13。PAG260.lean（定理 23 個、定義 3 個）、step279.py（13 項目）。
   4| 
   5| - **問いの出所。** 著者の選択（2026-11-13 18:15、着手前の文書 `pag2_part256_preregistration.md` の候補 M1）。本来の道の「無限素点を含む大域対象」と「重なり」に仕えます。Part 252〜254 の貼り合わせ U（公準 A1 の位相を固有値とする）と、Part 255 の L1（測る素点の集合）をつなぐ問いです：互いに素な法 M, N の貼り合わせから、法 M·N の貼り合わせは決まるか。
   6| - **問いへの答えの範囲（独立照合 B の指摘）。** Lean の文が答えるのは、互いに素な 2 つの法の、原始指標の積 1 つの上の固有値です：法 M と法 N の固有値と、交差項と符号から決まります。「素点ごとに分かれるか」「決まるか」の全体には答えていません。Lean にしていないのは、(i) 法 M·N のすべての指標が積の形に一意に書けること、(ii) 原始でない成分（数値だけ）、(iii) 作用素全体の式、(iv) 素数冪ごとの分解と 3 つ以上の法（数値だけ）です。題の最初の版「貼り合わせ U は素点ごとに分かれるか」は、この範囲に合わせて直しました。
   7| - **結論（Lean の文。すべて既知の事実の Lean 化）。**
   8|   1. **ガウス和の乗法性。** 互いに素な M, N と、法 M の指標 χ₁、法 N の指標 χ₂ について、τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（`gaussSum_prodChar`）。原始性は要りません。証明は a = a₁·N + a₂·M と分ける中国剰余定理です（`crtMap_bijective`・`stdAddChar_crtMap`・`prodChar_apply`）。互いに素の仮定を外しても等式は成り立ちますが、両辺が 0 になります（独立照合 A の手計算と数値 (10)。Lean の文は仮定つきのまま）。
   9|   2. **偶奇の因子のずれ。** ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)。s は、χ₁, χ₂ がともに奇なら −1、それ以外は +1（`crossSign`・`parFac_prodChar`）。ε は Part 252 の `parFac`（偶で 1、奇で −i）です。
  10|   3. **交差項の法則。** W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（`rootNum_prodChar`。原始性は要らない）。交差項 χ₁(N)·χ₂(M) の絶対値は 1 です（`norm_cross`）。ただし W（`rootNum`）がルート数であるのは原始指標のときだけで、原始でない指標では「法で正規化したガウス和」の恒等式です（A の指摘）。
  11|   4. **貼り合わせ U での形。** 原始指標の積は原始です（`isPrimitive_prodChar`）。したがって公準 A1 の位相 `phaseA1` でも同じ法則が成り立ち（`phaseA1_prodChar`）、U は関数 χ₁χ₂ をその値で動かします（`UA1_charU_prodChar`）。関数 χ₁χ₂ は、中国剰余定理の 2 つの成分の関数の積です（`charU_prodChar`）。これは原始指標の積 1 つの上の固有値の式で、作用素全体の等式ではありません。原始でない指標では、因子は導手での値 χ₁*(d₂)·χ₂*(d₁) に変わります（数値 (4)。Lean にしていない）。
  12|   5. **ずれは実際に起きる（存在の例）。**
  13|      - 法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組があります（`rootNum_prodChar_ne_mul`・`phaseA1_prodChar_ne_mul`）。この例では比が ∓i で、交差項と符号 s が混ざっています（A・B の手計算。比の値は Lean の文にない）。
  14|      - 符号 s だけでずれる例：法 39 = 3·13 に、交差項が 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組があります（`rootNum_prodChar_eq_neg_mul`。B が手計算で示した例を Lean にした。数値 (13)）。
  15|      - 交差項だけでずれる例（符号 s = 1 で交差項 ≠ 1）と、等号になる例（法 3 の奇の指標と法 5 の偶の 2 次の指標。数値 (13)）は Lean にしていません。ずれは指標の選び方によります。「積ではない」は「一般には積ではない」の意味です。
  16|   6. **条件つきの文。** W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（`cross_eq_sign_of_rootNum_one`）。互いに素の仮定 h は余分です（互いに素でなければ W(χ₁χ₂) = 0 ≠ 1。A の指摘。Lean の文は仮定つきのまま）。
  17|   - sorry 0、警告 0。`#print axioms` 23 行は標準の公理の範囲です（21 行が [propext, Classical.choice, Quot.sound]、2 行が [propext, Quot.sound]）。
  18| - **読み（解釈の言葉。Lean の文ではない）。**
  19|   - 「素点」「貼り合わせ」「重なり」は著者の言葉です。Lean の文は、指標とガウス和についての恒等式です。
  20|   - 互いに素な法ごとに見ると、法 M·N の貼り合わせ U の固有値は、一般には、法 M と法 N の固有値の積ではありません。ずれは 2 つです。交差項 χ₁(N)·χ₂(M) は、相手の法を自分の指標で読んだ値です。符号 s は偶奇の因子から出ます。偶奇の因子は、文献では無限素点の局所因子にあたります（Lean では偶奇の因子としてだけ現れます）。
  21|   - 文献の名前（独立照合 C、§7）：交差項は「不分岐な指標でひねったときの ε 因子の変化」、符号 s は (−1)^{a₁a₂} で、実素点のヒルベルト記号 (−1, −1)_∞ と同じ形。2 次の指標では、全体がヒルベルト記号の積公式と同値。
  22|   - **言い方の注意（着手前の盲検の指摘）。** 文献では、大域の ε 因子は局所の ε 因子の積です（Tate、Deligne）。ここで言うずれは、ディリクレ指標を中国剰余定理で分けた成分 χ₁, χ₂ と、イデール類指標の局所成分との違いです。交差項は、χ₁ の、N を割る素点での局所成分（不分岐だが自明でない）から出ます。「大域は局所の積ではない」とは書きません。
  23| - **2 次の指標と相互法則（観察。主な結果にしない）。** p, q が異なる奇素数で χ₁, χ₂ がルジャンドル記号のとき、数値では W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 で、6 の文は平方剰余の相互法則 (q/p)(p/q) = (−1)^{(p−1)(q−1)/4} と同じ形になります（step279 の (2)：奇素数の 28 組）。ただし、ここから相互法則が出るのではありません。合成の法 pq の 2 次の指標で W = 1 であることは外から入れる事実で、その証明の引き方によっては循環します（着手前の盲検の指摘）。
  24| - **公準 A1 との関係。** A1 は公準のままです。交差項の法則はルート数という量についての恒等式で、A1 から何かを出すものではありません。A1 を外すと位相は自由に戻り、この法則は位相の選び方への制約ではなくなります（除去テスト。CLAUDE.md §7 の第 2 の型）。
  25| - **位置づけ。** 既知の事実の Lean 化です（再導出、確信度：高）。Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合です。新規候補はありません。形式化としては、互いに素な法でのガウス和の乗法性は Mathlib と Isabelle AFP に見つかりませんでした（着手前の盲検と、この環境の Mathlib の grep。見落としの可能性あり）。兆候 4（既知の事実だけ）は 8 パート連続です（§6）。
  26| 
  27| ## 0. 内容
  28| 
  29| ### 0.0 ハンドシェイク（CLAUDE.md §0）
  30| 
  31| - (a) 形式化済み：Part 252〜254（PAG256〜258）の `rootNum`・`parFac`・`phaseA1`・`UA1`・`charU`・`Vprim`、直極限 `Uinf`。Part 255（PAG259）の測る素点と位相の二分法。
  32| - (b) 著者の解釈の層：§1 の 3 命題。重なりはねじれた貼り合わせ（U）。A1 は公準。解像度は測る素点の集合（L1）。「解像度が落ちる」の定義（2026-11-13 08:41）。
  33| - (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象（このパートは偶奇の因子のずれまで）、有限レベルの Bost–Connes。
  34| 
  35| ### 0.1 4 点（着手前の文書 §1 から）
  36| 
  37| 1. 幾何の言葉：2 つの点（素数）の上の貼り合わせから、両方を同時に見たときの貼り合わせは決まるか。決まらないなら、ずれは何か。
  38| 2. 既存分野の言葉への最善の翻訳：互いに素な法でのガウス和の乗法性、ルート数の局所因子への分解（Tate の局所定数）、2 次の指標では平方剰余の相互法則。
  39| 3. 残余：空（確信度：高。盲検も「ない」）。
  40| 4. 対照群：F_3[t] でも同じ交差項の法則が成り立ちます（step279 の (5)）。交差項は ℚ に固有ではありません。無限素点のずれは関数体にもあり、形が違います（盲検、こちらでは未確認）。一般化素数では指標とガウス和がなく、問いが立ちません。
  41| 
  42| ### 0.2 定義（PAG260.lean）
  43| 
  44| | 記号 | Lean | 内容 |
  45| |---|---|---|
  46| | χ₁χ₂ | `prodChar χ₁ χ₂` | 法 M·N の指標 a ↦ χ₁(a mod M)·χ₂(a mod N) |
  47| | 分解 | `crtMap M N` | (a₁, a₂) ↦ a₁·N + a₂·M（mod M·N） |
  48| | s | `crossSign χ₁ χ₂` | 両方が奇なら −1、それ以外は 1 |
  49| 
  50| ### 0.3 ラベル（CLAUDE.md §7）
  51| 
  52| | 結果 | ラベル | 根拠 |
  53| |---|---|---|
  54| | ガウス和の乗法性 | 既知 | Montgomery–Vaughan, Theorem 9.6 |
  55| | 偶奇の因子のずれ、交差項の法則（W の形） | 既知（再導出） | 上の短い帰結。この形の文献は盲検で見つからなかった |
  56| | 原始指標の積は原始 | 既知 | 導手の標準の事実 |
  57| | U の固有値の法則、法 15 の例 | 既知（再導出） | 上の言い換え |
  58| | 条件つきの文（相互法則と同じ形） | 既知（観察） | ガウス和による相互法則の証明の一部 |
  59| | 「貼り合わせ」「素点」「重なり」「無限素点の因子」の読み | 著者の解釈の層と読み | — |
  60| 
  61| - 新規候補：なし。
  62| 
  63| ## 1. 検証表
  64| 
  65| | 主張 | Lean | 数値（step279） | 新規性 |
  66| |---|---|---|---|
  67| | 中国剰余定理の分解と加法指標の分解 | `cast_crtMap_fst`・`cast_crtMap_snd`・`crtMap_bijective`・`stdAddChar_crtMap` | (1) | 既知 |
  68| | 積の指標の値 | `prodChar_apply`・`prodChar_neg_one`・`charU_prodChar` | (1) | 既知 |
  69| | ガウス和の乗法性 | `gaussSum_prodChar` | (1)（116 組）・(11)・(12) | 既知 |
  70| | 偶奇の因子のずれ | `crossSign_of_odd`・`crossSign_of_even_left`・`crossSign_of_even_right`・`parFac_prodChar` | (6) | 既知 |
  71| | 交差項の法則、絶対値 1 | `rootNum_prodChar`・`norm_char_unit`・`norm_cross` | (1)・(9) | 既知（再導出） |
  72| | 原始指標の積は原始 | `isPrimitive_prodChar` | (8)（64 組） | 既知 |
  73| | U の固有値の法則 | `phaseA1_prodChar`・`UA1_charU_prodChar` | (1) | 既知（再導出） |
  74| | 法 15 の例（ずれる）、法 39 の例（符号だけでずれる） | `exists_primitive_odd_five`・`rootNum_prodChar_ne_mul`・`phaseA1_prodChar_ne_mul`・`rootNum_prodChar_eq_neg_mul` | (3)・(13) | 既知 |
  75| | 条件つきの文 | `cross_eq_sign_of_rootNum_one` | (2)（観察） | 既知 |
  76| | 原始でない指標の位相の法則（導手での交差項） | Lean にしていない | (4)（116 組） | 既知 |
  77| | 3 つの法（交差項は 2 つずつの組の積） | Lean にしていない | (7)（68 組） | 既知 |
  78| | 対照群 F_3[t] | Lean にしていない | (5)（94 組） | 既知 |
  79| | 互いに素を外す（両辺が 0） | Lean にしていない | (10)（65 組） | 既知 |
  80| | 等号になる例（法 15、法 5 の偶の 2 次の指標） | Lean にしていない | (13) | 既知 |
  81| 
  82| - **文の重み（独立照合 A・B）。** 中身があるのは 4 つです：`crtMap_bijective`（中国剰余定理）、`gaussSum_prodChar`（核）、`rootNum_prodChar`（主な文）、`isPrimitive_prodChar`。ほかは、定義の展開（`cast_crtMap_*`・`stdAddChar_crtMap`・`prodChar_apply`・`prodChar_neg_one`・`crossSign_of_*`・`charU_prodChar`）、場合分け（`parFac_prodChar`）、言い換え（`phaseA1_prodChar`・`UA1_charU_prodChar`・`phaseA1_prodChar_ne_mul`）、1 行の帰結（`cross_eq_sign_of_rootNum_one`・`norm_cross`）、存在の例（`exists_primitive_odd_five`・`rootNum_prodChar_ne_mul`・`rootNum_prodChar_eq_neg_mul`）、補助（`norm_char_unit`）です。
  83| 
  84| ## 2. 数値照合（step279.py、13 項目すべて合格、1 回目で通った。(13) は B の後に足した）
  85| 
  86| - (10) 除去テスト（第 11 の型）：互いに素でない法（10 組）でも等式 τ(χ₁χ₂) = χ₁(N)χ₂(M)τ(χ₁)τ(χ₂) は成り立ちましたが、65 組すべてで両辺が 0 でした。互いに素の仮定は、等式が中身を持つために要ります。Lean の文は仮定つきです。
  87| - (11) 退化例：法 1（法則は τ(χ) = τ(χ) になる）、法 2（自明な指標だけ、τ = −1）。
  88| - (12) 規約（第 8 の型）：加法指標を 3 つとも同じ k で e(k·a/N) に変えても、同じ交差項で法則が成り立ちました（180 組）。
  89| - (13) 符号だけでずれる例：法 39 で、交差項 = 1 かつ W(χ₁χ₂) = −W(χ₁)W(χ₂) の奇の原始指標の組が 2 個。等号になる例：法 15 で、法 5 の偶の 2 次の指標との組。
  90| - 数値の確認は証明ではありません。
  91| 
  92| ## 3. Lean（PAG260.lean）
  93| 
  94| - import は PAG259（鎖の続き）。名前空間は `PAG.Part260`。
  95| - 作業の記録：下書き `scratch/t256/A.lean` で段階的にコンパイルしました。直したもの：
  96|   - 和の書き換え（`Finset.sum_mul_sum` の前に `mul_assoc` が要る）。
  97|   - `crossSign` の `if` の命題に Decidable の instance がない（`open Classical in` を付け、値は補題 `crossSign_of_*` で取り出す）。`if_pos`・`if_neg` は非推奨。
  98|   - `decide` は、文脈に `Fact` の仮定があると「自由変数」で止まる（`decide` で示す事実を先に `have` で置く）。
  99|   - `DirichletCharacter.unit_norm_eq_one` のモジュール（Bounds）はこの環境でビルドされていないので、同じ証明を `norm_char_unit` として置いた。
 100|   - 組み立ての 1 回目は、docstring を `omit … in` の前に置いて構文エラー（rc = 1）。後ろに移して 2 回目で rc = 0。
 101|   - `Nat.Prime 13` は `norm_num` で示せず、`by decide` で通った。
 102| - B の後に `rootNum_prodChar_eq_neg_mul` を足し、`rootNum_prodChar_ne_mul` の文に「両方が奇」を入れました（B の「主張がやや強い」への対応）。組み立て直して rc = 0。
 103| - sorry 0、警告 0、`#print axioms` 23 行（定理と同数）。鎖全体（PAG.lean〜PAG260.lean）は theorem/lemma 3525、`#print axioms` 3826。
 104| 
 105| ## 4. 残る問い（本来の道）
 106| 
 107| - 原始でない指標を含めた全体での法則（導手 d₁, d₂ での交差項。数値では成り立つ）と、作用素の形（テンソル積と平行移動）は Lean にしていません。原始でない部分では、平行移動の元が指標ごとに変わります（盲検の指摘）。
 108| - イデール類指標の局所成分と局所の ε 因子で書けば、交差項は局所因子に吸収されるはずです（Tate。Lean にしていない。Mathlib の状況は未確認）。
 109| - 残る大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、有限レベルの Bost–Connes。
 110| - 次のパートは著者の選択を待ちます（Part 257 は始めていません）。
 111| 
 112| ## 5. 文献の確認の記録（検索ログ）
 113| 
 114| - 着手前の盲検の問いテスト（WebSearch・WebFetch、25 回）が開いたもの：Montgomery–Vaughan, Multiplicative Number Theory I の第 9 章（Theorem 9.6）、Evertse の講義ノート、David–Florea–Lalín（arXiv:1901.00817）、Buzzard の ε 因子のノート、Mathlib の GaussSum のドキュメント（Bonn のミラー）、Isabelle AFP の Gauss_Sums、Loeffler–Stoll（arXiv:2503.00959）。私は開いていません。URL は `prereg256/agent_blind_question_test_output.md`。
 115| - 独立照合 C が挙げた名前を、私がウェブで確かめたもの（検索 3 回。結果の抜粋を読んだだけで、本そのものは開いていません）：
 116|   - 関数体の d 乗剰余の相互法則 (P/Q)_d·(Q/P)_d^{−1} = (−1)^{((q−1)/d)·deg P·deg Q}：Rosen, Number Theory in Function Fields（GTM 210, 2002）第 3 章 "The Reciprocity Law" の Theorem 3.3 として引かれていました（確認できた）。
 117|   - ガウス和の文献：Iwaniec–Kowalski, Analytic Number Theory（2004）の Section 3.4 がガウス和の節として引かれていました。互いに素な法の乗法性の式番号は確認できていません。
 118|   - 不分岐な指標でひねったときの ε 因子の変化 ε(χ₁χ₂, ψ) = χ₂(π)^{a(χ₁)+n(ψ)}·ε(χ₁, ψ)：Tate, Number theoretic background（Corvallis, 1979）の (3.2.6.3) として引かれていました（arXiv:1405.6145 の (2.12)。arXiv:2306.10928 の (18) は指数の符号の規約が違う形）。C の式と同じ形です。指数の規約は文献で違います。
 119|   - 大域の ε 因子が局所の ε 因子の積であること：Buzzard のノート（epsilon constants）に同じ文がありました。
 120|   - Isabelle AFP の Gauss_Sums は、Apostol, Introduction to Analytic Number Theory の第 8 章の形式化と説明されていました。
 121| - 確かめていないもの：符号 s とヒルベルト記号 (−1, −1)_∞ の対応、2 次の場合のヒルベルト記号の積公式との同値、関数体での「ヤコビ和型」の因子（C の記憶による。確度は C の申告のまま）。
 122| 
 123| ## 6. 収束アラームの状況（CLAUDE.md §7、Part 256 の後）
 124| 
 125| - **兆候 4（既知の事実だけ）：8 パート連続**（Part 249〜256）。着手前に報告し、著者が M1 を選びました。
 126| - 辞書の未記入の件数：0（辞書 §16）。文献照合の未実施の連続パート数：0。兆候 1・2：出ていない。
 127| - 第 2 の型：上の「公準 A1 との関係」。第 3 の型：着手前の盲検で、私の言い方 3 つ（「局所の積ではない」「ℚ に固有なのは符号だけ」「相互法則になる」）が直され、独立照合 B で題と「積ではない」の範囲が直されました（§7）。
 128| - §6 の表現：A1 は公準のまま。「導いた」「アプローチ」の表現は使っていません。
 129| 
 130| ## 7. 検知記録：独立照合（2026-11-13）
 131| 
 132| - **手順。** 構築者の予想を先に書き（`audit256/expected_before_results.md`）、入力を中立化し（`statements_neutral.lean`・`rename.json`）、新しいエージェント A（逆翻訳）と C（盲検の命名）をツールなしで起動、A の後に B（照合）を起動しました。ツール使用回数は A・B・C とも 0（`*_meta.txt`）。
 133| - **手順の弱点（記録）。** B への入力 (4) は A の出力の全文ではなく要約、入力 (6) はノートの題と結論の部分でした。B の出力は要点だけを保存しています（`agent_B_output_summary.md`。全文は会話の記録）。A・C の出力は全文（`agent_A_output.md`・`agent_C_output.md`）。
 134| - **A（逆翻訳）。** 22 文はすべて正しく読め、中身は標準（ガウス和の乗法性とそのルート数版）。作用素の等式と相互法則そのものは示されていない。指摘：互いに素の仮定は S6・S12 では真であるためには不要（両辺 0）、原始でない指標では W はルート数でない、S15 は固有ベクトル 1 つの上の値だけ、S16 の h は冗長、S18 の例は交差項と符号が混ざっていて符号だけの必要性を示していない、等号になる例がある。
 135| - **C（盲検の命名）。** ルート数、不分岐なひねりによる ε 因子の変化、無限素点の局所ルート数 i^{−a}、s は (−1)^{a₁a₂}（ヒルベルト記号 (−1, −1)_∞ と同じ形）。標準を超える内容はない（高〜中）。原始でない指標では因子が導手での値に変わる（例：M = 3、N = 25）。関数体では符号がヤコビ和型の因子になる（中）。
 136| - **B（照合）。** 偽・空虚・別物はなし。「主張がやや強い」が 1 つ（S18：「両方が奇」が形式文になかった）、「名前が強い」が 1 つ（S22）。題の問いに形式文は答え切っていない。「積ではない」は全称に読める。符号だけの例が Lean にない（手計算で法 3 と 13 の例を示した）。
 137| - **予想との比較。**
 138|   - 当たり：A の「互いに素でなくても成り立つ（両辺 0）」（予想の確度は中）、S16 は相互法則を示していない、S15 は固有ベクトル 1 つ、原始でない場合は述べていない。C の名前はほぼ予想どおり。B の「言い方が形式文より強い」。全体の「標準を超えない」。
 139|   - 外れ・予想になかったもの：S16 の h が冗長、「符号だけでずれる例がない」（A と B）、題の問いに答え切っていない（B）、S18 の「両方が奇」が形式文にない（B）、C の原始でない場合の具体例、s がテンソル積 A⊗B に吸収できないという A の補足（文にしていない、A の確度は中）。Hasse–Davenport は挙がらなかった。
 140| - **直したもの。** 題（範囲を「互いに素な法の原始指標の積の上」に）、「一般には積ではない」、「互いに素な法ごと」、問いへの答えの範囲の明記、文の重みの区別（§1）、`rootNum_prodChar_ne_mul` に「両方が奇」、`rootNum_prodChar_eq_neg_mul` の追加、数値 (13)、xlsx の行の言い方。
 141| - **直していないもの（記録）。** 互いに素の仮定を外した形の Lean 化（`gaussSum_prodChar`・`rootNum_prodChar`・`cross_eq_sign_of_rootNum_one` の h）、交差項だけでずれる例と等号の例の Lean 化、原始でない指標の法則、作用素の式、3 つ以上の法。
 142| - **第 3 の型（主張の格上げ）の検知。** 題と「固有値は積ではない」が、形式文（指標 1 つの上の式と存在の例）より広く読める形でした（B）。着手前の盲検でも 3 つの言い方が直されています。同じ向き（解釈の言葉に寄せて広く書く）の誤りが Part 255 に続いて出たので、記録します。
 143| - 詳しくは `pag2_part256_independent_audit.md`。
 144| 
```

## 入力 (5)：表（xlsx）の見出しと各行（原文のまま。主張と証明の要点。★ は前回の照合の時点の版から足した・変えた行）
```
【見出し】PAG2.0-256 互いに素な法の原始指標の積の上での、貼り合わせ U の固有値：交差項の法則 W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（著者が 2026-11-13 18:15 に候補 M1 を選んだ。すべて既知の事実の Lean 化：Montgomery–Vaughan の Theorem 9.6、Tate・Deligne の局所定数の GL(1)/ℚ の場合）  ★（前回の照合の時点から変わった）
cast_crtMap_fst
  主張：分解の写像 crtMap（def：(a₁, a₂) ↦ a₁·N + a₂·M mod M·N）の法 M への像は a₁·N（補助）
  証明の要点：自然数の cast と N·M ≡ 0
cast_crtMap_snd
  主張：分解の写像の法 N への像は a₂·M（補助）
  証明の要点：同じ
crtMap_bijective
  主張：互いに素な法では分解の写像は全単射（中国剰余定理）
  証明の要点：単射（N は法 M の単数、M は法 N の単数）と濃度の一致
stdAddChar_crtMap
  主張：加法指標は分解で積に分かれる：e((a₁N + a₂M)/(MN)) = e(a₁/M)·e(a₂/N)
  証明の要点：指数関数の加法性と通分
prodChar_apply
  主張：積の指標 prodChar χ₁ χ₂（def：法 M·N）の値は χ₁(a mod M)·χ₂(a mod N)（単数でない a では両辺 0。互いに素は要らない）
  証明の要点：単数では changeLevel の値、単数でなければ M か N と共通因数を持つ
gaussSum_prodChar
  主張：互いに素な法でのガウス和の乗法性：τ(χ₁χ₂) = χ₁(N)·χ₂(M)·τ(χ₁)·τ(χ₂)（原始性は要らない）
  証明の要点：和を分解の写像で付け替え、指標と加法指標を成分に分ける
prodChar_neg_one
  主張：(χ₁χ₂)(−1) = χ₁(−1)·χ₂(−1)（補助）
  証明の要点：prodChar_apply と −1 の還元
crossSign_of_odd
  主張：符号 crossSign（def：両方が奇なら −1、それ以外は 1）：両方が奇なら −1（補助）
  証明の要点：定義
crossSign_of_even_left
  主張：左が偶なら符号は 1（補助）
  証明の要点：偶なら奇でない
crossSign_of_even_right
  主張：右が偶なら符号は 1（補助）
  証明の要点：偶なら奇でない
parFac_prodChar
  主張：偶奇の因子のずれ：ε(χ₁χ₂) = s·ε(χ₁)·ε(χ₂)（ε = Part 252 の parFac は偶で 1、奇で −i。文献では無限素点の局所因子にあたる、は読み）
  証明の要点：偶奇の 4 通りの場合分け。両方が奇のとき (−i)(−i) = −1
rootNum_prodChar
  主張：交差項の法則：W(χ₁χ₂) = s·χ₁(N)·χ₂(M)·W(χ₁)·W(χ₂)（互いに素な法。原始性は要らない）
  証明の要点：rootNum_eq と gaussSum_prodChar・parFac_prodChar、√(MN) = √M·√N
isPrimitive_prodChar
  主張：互いに素な法の原始指標の積は原始（導手 = M·N）
  証明の要点：χ₁ = χ·χ₂⁻¹ の導手 M が lcm(cond χ, N) を割るので M ∣ cond χ。同様に N ∣ cond χ
phaseA1_prodChar
  主張：公準 A1 の位相（Part 254 の phaseA1）での交差項の法則（原始指標）
  証明の要点：原始なら phaseA1 = rootNum
UA1_charU_prodChar
  主張：貼り合わせ U（Part 254 の UA1）は、原始指標の積の関数を s·χ₁(N)·χ₂(M)·phaseA1(χ₁)·phaseA1(χ₂) 倍する（指標 1 つの上の固有値の式。作用素全体の等式ではない）
  証明の要点：UA1_charU と phaseA1_prodChar
cross_eq_sign_of_rootNum_one
  主張：条件つきの文：W(χ₁) = W(χ₂) = W(χ₁χ₂) = 1 なら s·χ₁(N)·χ₂(M) = 1（2 次の指標では平方剰余の相互法則と同じ形。3 つの仮定は外から入れるもので、相互法則を示してはいない）
  証明の要点：rootNum_prodChar に代入
exists_primitive_odd_five
  主張：証人：法 5 に奇の原始指標がある（補助）
  証明の要点：χ(−1) ≠ 1 の指標の存在
★ rootNum_prodChar_ne_mul
  主張：中国剰余定理の成分の積とのずれの例：法 15 = 3·5 に、W(χ₁χ₂) ≠ W(χ₁)·W(χ₂) となる奇の原始指標の組がある（存在の例 1 つ。比の値 ∓i は文にない）
  証明の要点：s = −1、χ₁(5) = −1、χ₂(3)² = −1 なので比 χ₂(3) ≠ 1
★ rootNum_prodChar_eq_neg_mul
  主張：符号だけでずれる例：法 39 = 3·13 に、交差項 χ₁(13)·χ₂(3) = 1 で W(χ₁χ₂) = −W(χ₁)·W(χ₂)、W(χ₁)·W(χ₂) ≠ 0 となる奇の原始指標の組がある（独立照合 B の手計算の例を Lean にした）
  証明の要点：法 13 の奇の指標 χ の 3 乗 χ₂ は奇で原始、χ₂(3) = χ(27) = χ(1) = 1。χ₁(13) = χ₁(1) = 1。s = −1
phaseA1_prodChar_ne_mul
  主張：同じ例を公準 A1 の位相で：法 15 で phaseA1(χ₁χ₂) ≠ phaseA1(χ₁)·phaseA1(χ₂) となる原始指標の組がある
  証明の要点：rootNum_prodChar_ne_mul と原始性
norm_char_unit
  主張：単数での指標の値の絶対値は 1（Mathlib の unit_norm_eq_one と同じ証明。そのモジュールがこの環境で未ビルドのため。補助）
  証明の要点：単数群の位数乗が 1
norm_cross
  主張：交差項の絶対値は 1：互いに素な法で ‖χ₁(N)·χ₂(M)‖ = 1
  証明の要点：N は法 M の単数、M は法 N の単数
★ charU_prodChar
  主張：積の指標の関数の単数での値：(χ₁χ₂)(u) = χ₁(u mod M)·χ₂(u mod N)（prodChar_apply の単数への制限。互いに素は要らない。「中国剰余定理の成分の関数の積」は読み）
  証明の要点：prodChar_apply
```

## 入力 (6)：逆翻訳の査読者 A2 の出力の全文（原文のまま）
A2 は ★ の文を、名前を中立化した入力で判定しました。名前の対応：S1 = `cast_crtMap_fst`、S2 = `cast_crtMap_snd`、S3 = `crtMap_bijective`、S4 = `stdAddChar_crtMap`、S5 = `prodChar_apply`、S6 = `gaussSum_prodChar`、S7 = `prodChar_neg_one`、S8 = `crossSign_of_odd`、S9 = `crossSign_of_even_left`、S10 = `crossSign_of_even_right`、S11 = `parFac_prodChar`、S12 = `rootNum_prodChar`、S13 = `isPrimitive_prodChar`、S14 = `phaseA1_prodChar`、S15 = `UA1_charU_prodChar`、S16 = `cross_eq_sign_of_rootNum_one`、S17 = `exists_primitive_odd_five`、S18 = `rootNum_prodChar_ne_mul`、S19 = `phaseA1_prodChar_ne_mul`、S20 = `norm_char_unit`、S21 = `norm_cross`、S22 = `charU_prodChar`、S23 = `rootNum_prodChar_eq_neg_mul`、Θ1 = `crossSign`、Ξ1 = `rootNum`、Ξ2 = `parFac`、Ξ3 = `phaseA1`、Ξ4 = `UA1`、Ξ5 = `charU`、Ξ6 = `ip`、Φ1 = `prodChar`、Ψ1 = `crtMap`。前のファイルの文：R1 = `rootNum_eq`、R2 = `rootNum_ne_zero`、R3 = `phaseA1_of_isPrimitive`、R4 = `UA1_charU`、R5 = `exists_primitive_odd_three`、R6 = `isPrimitive_of_prime_of_ne_one`

{{A2_OUTPUT}}

## 課題
1. 表（入力 (5)）：各行の主張と証明の要点を形式文と突き合わせ、「一致／主張が強い／主張が弱い／別物／偽」で判定してください。★ の行はすべて判定を書いてください。ほかの行は、ずれがあるものだけ挙げ、残りは「一致」とまとめて構いません。
2. ノート（入力 (4)）：題、冒頭の結論・位置づけ・読み、検証表、「Lean にしていないこと」を形式文と突き合わせてください。形式文より強い箇所、形式文にないことを形式文の事実として書いた箇所、解釈の言葉を事実として書いた箇所を、行番号つきで挙げてください。変わった行の範囲は必ず見てください。
3. Lean ファイルの文面（入力 (3)）：冒頭の説明と docstring について同じ観点で。★ の宣言は必ず見てください。
4. ★ の文について、A2 の訳と判定（入力 (6)）と、文面の言い方が食い違うところを挙げてください。
5. 直すべき点を重要な順に挙げてください。各点に、どこを、どう直すかを、形式文から起こした言い方の案で書いてください。
6. 全体：形式文に偽・空虚・別物があるか。標準を超える内容があるか。
