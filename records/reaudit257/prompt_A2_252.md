あなたは独立の査読者です。ある Lean 4（Mathlib）の形式化の定義と形式文を読み、意味を正確に訳して判定してください。構築の経緯や意図は知らせません。名前は中立化してあります（Φ・Ψ・Θ・Ξ・Ω は定義、S・R は定理）。

## 守ってほしいこと
- ツールは一切使わないでください（ファイル、シェル、検索、エージェントの起動もしない）。
- 判断ごとに確信度（高・中・低）を付けてください。
- 回答は日本語で、5,000 字程度までにまとめてください。最後に、使ったツール（使っていなければ「なし」）を書いてください。

## Mathlib の前提
`ZMod N` は ℤ/N、`(ZMod N)ˣ` は単数群、`t.val` は 0 以上 N 未満の代表。`stdAddChar` は t ↦ exp(2πi·t.val/N)。`DirichletCharacter ℂ N` は法 N のディリクレ指標（ZMod N → ℂ、単数でないところで 0）。`IsPrimitive` は導手が N に等しいこと、`Even` は χ(−1) = 1、`Odd` は χ(−1) = −1。`gaussSum χ ψ = Σ_a χ(a)ψ(a)`。`Complex.normSq z = |z|²`。`IsUnit x` は x が単数。`(1 : DirichletCharacter ℂ N)` は自明な指標（単数で 1、単数でないところで 0）。

## 入力 (1)：定義（このファイルの定義。内容は原文のまま、名前だけ置き換えた）
```lean
variable {N : ℕ} [NeZero N]
open Complex

noncomputable def Φ1 (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

noncomputable def Φ2 (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * Φ1 (x * y)

noncomputable def Φ3 (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2

open Classical in
noncomputable def Φ4 (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

noncomputable def Φ5 (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  Φ2 f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)
```

## 入力 (2)：同じファイルの文（S1〜S15。文脈として示す。判定の対象ではない。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）
```lean
theorem S1 (t : ZMod N) :
    Φ1 t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2
omit [NeZero N] in
theorem S2 {χ : DirichletCharacter ℂ N} (h : χ.Even) : Φ3 χ = 1
omit [NeZero N] in
theorem S3 {χ : DirichletCharacter ℂ N} (h : χ.Odd) : Φ3 χ = -I
omit [NeZero N] in
theorem S4 (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
theorem S5 (χ : DirichletCharacter ℂ N) (y : ZMod N) :
    ∑ x : ZMod N, χ x * stdAddChar (x * y) = gaussSum χ (stdAddChar.mulShift y)
theorem S6 {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    Φ2 (χ : ZMod N → ℂ) y = Φ3 χ * gaussSum χ stdAddChar * χ⁻¹ y
theorem S7 {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : Φ2 (χ : ZMod N → ℂ) y = 0
theorem S8 (χ : DirichletCharacter ℂ N) :
    Φ4 χ = Φ3 χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)
omit [NeZero N] in
theorem S9 (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u
theorem S10 {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    Φ5 (χ : ZMod N → ℂ) u = Φ4 χ * χ u
theorem S11 {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (Φ4 χ) = 1
theorem S12 {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive
theorem S13 : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd
theorem S14 :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1
theorem S15 :
    ¬(1 : DirichletCharacter ℂ 2).IsPrimitive ∧ ¬IsUnit (0 : ZMod 2) ∧
      Φ2 ((1 : DirichletCharacter ℂ 2) : ZMod 2 → ℂ) 0 = 1
```

## 入力 (3)：判定の対象の文（S16〜S22。すべてコンパイル済みで sorry なし、公理は標準の 3 つ以内）
```lean
theorem S16 (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    Φ2 (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * Φ2 (χ : ZMod N → ℂ) 1
omit [NeZero N] in
theorem S17 (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1
theorem S18 (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar
theorem S19 (χ : DirichletCharacter ℂ N) :
    Φ2 (χ : ZMod N → ℂ) 1 = Φ3 χ * gaussSum χ stdAddChar
theorem S20 (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    Φ5 (χ : ZMod N → ℂ) u = Φ4 χ * χ u
theorem S21 :
    Complex.normSq (Φ4 (1 : DirichletCharacter ℂ 2)) = 1 / 2
theorem S22 :
    (∃ χ : DirichletCharacter ℂ (2 ^ 2), χ.IsPrimitive) ∧
    ¬(1 : DirichletCharacter ℂ 4).IsPrimitive ∧ ¬IsUnit (2 : ZMod 4) ∧
      Φ2 ((1 : DirichletCharacter ℂ 4) : ZMod 4 → ℂ) 2 = -2 ∧
      Complex.normSq (Φ4 (1 : DirichletCharacter ℂ 4)) = 0
```

## 課題
1. 入力 (3) の各文（S16〜S22）を、量化子・暗黙の引数・仮定を落とさずに数学の言葉に訳してください。
2. 各文を判定してください：実質的（標準）／実質的（標準を超える可能性）／自明／ほぼ同語反復／条件つきで弱い／端の場合だけ（具体例・証人）／偽または空虚の疑い。理由を短く。
3. 仮定の点検：各仮定を外すと偽になるか、不要な仮定はないか、仮定が空虚に満たされないか（満たす例があるか）。
4. 定義の点検：入力 (3) の文に出てくる定義が、何を表しているか。気になる点（規約、型の選び方、位相などの構造の入れ方、法や引数の順など）があれば挙げてください。
5. 全体の所見：入力 (3) の文で言えていること・言えていないこと。入力 (2) の文との関係（言い換え・特別な場合・独立）にも触れてください。
