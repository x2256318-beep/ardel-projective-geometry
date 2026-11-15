あなたは独立の査読者です。ある Lean 4（Mathlib）の形式化の定義と形式文を読み、意味を正確に訳して判定してください。構築の経緯や意図は知らせません。

## 守ってほしいこと
- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、4,000 字程度までにまとめてください。最後に、使ったツール（使っていなければ「なし」）を書いてください。

## Mathlib の前提
`DirichletCharacter ℂ n` は法 n のディリクレ指標（ZMod n → ℂ、単数でないところで 0）。`changeLevel` は法を倍数に上げた指標。`gaussSum χ stdAddChar = Σ_a χ(a)·e^{2πi a/n}`。`χ.Even` は χ(−1) = 1、`χ.Odd` は χ(−1) = −1。`IsPrimitive` は導手が法に等しいこと、`primitiveCharacter` は χ を誘導する原始指標（法は導手）。`ZMod.unitsMap` は法の割り算による単数群の写像。`(a.cast : ZMod M)` は ZMod (M*N) から ZMod M への還元。

## 入力 (1)：定義
```lean
variable {M N : ℕ} [NeZero M] [NeZero N]

-- このファイルの定義
noncomputable def Φ1 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂

def Ψ1 (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))

open Classical in
noncomputable def Θ1 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1

-- 前のファイルの定義（n は法、[NeZero n]）
noncomputable def Ξ1 (χ : DirichletCharacter ℂ n) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt n : ℂ))
noncomputable def Ξ2 (χ : DirichletCharacter ℂ n) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
noncomputable def Ξ3 (χ : DirichletCharacter ℂ n) : ℂ := Ξ1 χ.primitiveCharacter
def Ξ5 (χ : DirichletCharacter ℂ n) : (ZMod n)ˣ → ℂ := fun u => χ u
-- ip f g = Σ_u conj(f u)·g u
noncomputable def Ξ4 : ((ZMod n)ˣ → ℂ) →ₗ[ℂ] ((ZMod n)ˣ → ℂ) :=
  f ↦ ∑ χ : DirichletCharacter ℂ n, (Ξ3 χ * ip (Ξ5 χ) f / (Nat.totient n : ℂ)) • Ξ5 χ
```

## 入力 (2)：前のファイルで示されている事実（ここでは使うだけ）
- R1：Ξ1 χ = Ξ2 χ * gaussSum χ stdAddChar / √n。
- R2：χ が原始なら Ξ1 χ ≠ 0、Ξ3 χ = Ξ1 χ。
- R3：Ξ4 (Ξ5 χ) = Ξ3 χ • Ξ5 χ（すべての χ）。
- R4：法 3 に奇の原始指標がある。

## 入力 (3)：形式文（S1〜S22。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）
```lean
theorem S1 (x : ZMod M × ZMod N) :
    ((Ψ1 M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
theorem S2 (x : ZMod M × ZMod N) :
    ((Ψ1 M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
theorem S3 (h : M.Coprime N) : Function.Bijective (Ψ1 M N)
theorem S4 (x : ZMod M × ZMod N) :
    stdAddChar (Ψ1 M N x) = stdAddChar x.1 * stdAddChar x.2
theorem S5 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    Φ1 χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
theorem S6 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (Φ1 χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
theorem S7 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    Φ1 χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
theorem S8 {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : Θ1 χ₁ χ₂ = -1
theorem S9 {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : Θ1 χ₁ χ₂ = 1
theorem S10 (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : Θ1 χ₁ χ₂ = 1
theorem S11 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    Ξ2 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * Ξ2 χ₁ * Ξ2 χ₂
theorem S12 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    Ξ1 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ1 χ₁ * Ξ1 χ₂)
theorem S13 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (Φ1 χ₁ χ₂).IsPrimitive
theorem S14 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    Ξ3 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ3 χ₁ * Ξ3 χ₂)
theorem S15 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    Ξ4 (Ξ5 (Φ1 χ₁ χ₂)) =
      (Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ3 χ₁ * Ξ3 χ₂)) •
        Ξ5 (Φ1 χ₁ χ₂)
theorem S16 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : Ξ1 χ₁ = 1)
    (w2 : Ξ1 χ₂ = 1) (w12 : Ξ1 (Φ1 χ₁ χ₂) = 1) :
    Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
theorem S17 : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd
theorem S18 :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      Ξ1 (Φ1 χ₁ χ₂) ≠ Ξ1 χ₁ * Ξ1 χ₂
theorem S19 :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      Ξ3 (Φ1 χ₁ χ₂) ≠ Ξ3 χ₁ * Ξ3 χ₂
theorem S20 {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
theorem S21 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
theorem S22 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    Ξ5 (Φ1 χ₁ χ₂) u =
      Ξ5 χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        Ξ5 χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
```

## 課題
1. S1〜S22 のそれぞれを、量化子と仮定を落とさずに数学の言葉に訳してください（補助的な文は 1 行で構いません）。
2. 各文を次のどれかで判定してください：実質的／自明（定義の展開・1 行の帰結）／循環またはほぼ同語反復／条件つきで弱い／端の場合だけ。理由を 1 行で。
3. 全体の所見：この一連の文で何が言えて、何が言えていないか。とくに
   (a) S6・S12 の仮定（互いに素）は必要か。外すと偽になるか、自明になるか。原始性を仮定していないことの意味。
   (b) S14・S15 は Ξ4 という作用素について何を言っているか。作用素の等式としてどこまで言えているか。
   (c) S16 は何の定理に近く、何が足りないか。
   (d) S18・S19 の例は何を示し、何を示していないか。
   (e) この組に、標準の事実を超える内容はあるか。
4. 定義の気になる点と、規約への依存（Ψ1 の定義、加法指標の規約、Ξ1 の正規化、Θ1 の定義で偶でも奇でもない場合があるか、など）。
