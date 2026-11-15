# 根拠（2 回目）：注記ごとの、対象と前の宣言の形式文の全文（docstring とコメントを除いた文。定理は証明を除く）

番号の対応：PAG 2.0 の Part n は PAG(n+4).lean。PAG.lean は Part 1、PAG2.lean・PAG3.lean は付録 A の Part 2・Part 3。PAG3・PAG5・PAG6 は鎖に import されていない。名前空間 PAG.PartNNN の NNN はファイル番号。

根拠のファイル：MechChecks.lean（直接の当てはめで通った組を名前つきにしたもの、44 定理）、ManualChecks2.lean（14 件）、SampleC2.lean（6 件）。.out に #print axioms の出力がある。lean_mechanical_summary.md は直接の当てはめの表。


## Part 252：`PAG256::inv_apply_neg_one`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
omit [NeZero N] in
theorem inv_apply_neg_one (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
```
### 前の宣言 `PAG9::inv_apply_neg_one`
```lean
omit [NeZero N] in
theorem inv_apply_neg_one (χ : MulChar (ZMod N) ℂ) : χ⁻¹ (-1) = χ (-1)
```
### 前の宣言 `PAG25::chi_inv_neg_one`
```lean
omit hp in
theorem chi_inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
```
### 前の宣言 `PAG81::inv_neg_one`
```lean
theorem inv_neg_one {N : ℕ} (χ : DirichletCharacter ℂ N) : χ⁻¹ (-1) = χ (-1)
```

## Part 252：`PAG256::neg_one_mul_self`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
omit [NeZero N] in
theorem neg_one_mul_self (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1
```
### 前の宣言 `PAG9::chi_neg_one_sq`
```lean
omit [NeZero N] in
theorem chi_neg_one_sq (χ : MulChar (ZMod N) ℂ) : χ (-1) * χ (-1) = 1
```
### 前の宣言 `PAG29::chi_neg_one_sq'`
```lean
theorem chi_neg_one_sq' {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) * χ (-1) = 1
```

## Part 252：`PAG256::isPrimitive_of_prime_of_ne_one`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem isPrimitive_of_prime_of_ne_one {p : ℕ} [hp : Fact p.Prime] {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive
```
### 前の宣言 `PAG171::primitive_of_ne_one`
```lean
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive
```

## Part 252：`PAG256::casKer`（判定 A（値））
根拠：ManualChecks2.lean の casKer_eq_casK（定義から直接）

### 対象の文
```lean
noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)
```
### 前の宣言 `PAG3::casK`
```lean
noncomputable def casK (t : ZMod N) : ℂ := PAG.Kloosterman.cas (ZMod.stdAddChar t)
```
### 前の宣言 `PAG2::cas`
```lean
noncomputable def cas (z : ℂ) : ℂ := ((z.re + z.im : ℝ) : ℂ)
```

## Part 252：`PAG256::rootNum`（判定 B（値））
根拠：ManualChecks2.lean の rootNum_eq_zN_div_gs

### 対象の文
```lean
open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))
```
### 前の宣言 `PAG196::zN`
```lean
noncomputable def zN {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((Real.sqrt (N : ℝ) : ℝ) : ℂ)


```
### 前の宣言 `PAG198::gs`
```lean
noncomputable def gs {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ := if χ (-1) = 1 then 1 else I
```

## Part 252：`PAG256::inv_apply_units_inv`（判定 B）
根拠：ManualChecks2.lean の inv_apply_units_inv_of_PAG3（type_of%）

### 対象の文
```lean
omit [NeZero N] in
theorem inv_apply_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    χ⁻¹ ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u
```
### 前の宣言 `PAG3::apply_inv_eq_inv_apply`
```lean
theorem apply_inv_eq_inv_apply (χ : DirichletCharacter ℂ N) {a : ZMod N} (ha : IsUnit a) :
    χ a⁻¹ = χ⁻¹ a
```

## Part 252：`PAG256::sum_mul_stdAddChar_neg`（判定 B）
根拠：ManualChecks2.lean の sum_mul_stdAddChar_neg_of_PAG3（type_of%）

### 対象の文
```lean
theorem sum_mul_stdAddChar_neg (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * stdAddChar (-x) = χ (-1) * gaussSum χ stdAddChar
```
### 前の宣言 `PAG3::sum_neg_twist`
```lean
lemma sum_neg_twist (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, ZMod.stdAddChar (-(x * y)) * χ y
      = χ (-1) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```

## Part 252：`PAG256::hartley_one`（判定 C（Lean で確認））
根拠：SampleC2.lean の hartley_one_of_PAG3（type_of%）

### 対象の文
```lean
theorem hartley_one (χ : DirichletCharacter ℂ N) :
    hartley (χ : ZMod N → ℂ) 1 = parFac χ * gaussSum χ stdAddChar
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```
### 前の宣言 `PAG256::hartley`
```lean
noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)
```
### 前の宣言 `PAG256::parFac`
```lean
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
```

## Part 252：`PAG256::casKer_eq`（判定 C（Lean で確認））
根拠：SampleC2.lean の casKer_eq_of_PAG3（type_of%）

### 対象の文
```lean
theorem casKer_eq (t : ZMod N) :
    casKer t = ((1 - I) * stdAddChar t + (1 + I) * stdAddChar (-t)) / 2
```
### 前の宣言 `PAG3::casK_even_part`
```lean
lemma casK_even_part (t : ZMod N) :
    casK t + casK (-t) = ZMod.stdAddChar t + ZMod.stdAddChar (-t)
```
### 前の宣言 `PAG3::casK_odd_part`
```lean
lemma casK_odd_part (t : ZMod N) :
    casK t - casK (-t) = -I * (ZMod.stdAddChar t - ZMod.stdAddChar (-t))
```

## Part 252：`PAG256::normSq_rootNum`（判定 C（Lean で確認））
根拠：SampleC2.lean の normSq_rootNum_of_PAG16（type_of%）

### 対象の文
```lean
theorem normSq_rootNum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (rootNum χ) = 1
```
### 前の宣言 `PAG16::normSq_gaussSum`
```lean
theorem normSq_gaussSum {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    Complex.normSq (gaussSum χ stdAddChar) = N
```

## Part 252：`PAG256::exists_primitive_odd_three`（判定 C（Lean で確認））
根拠：SampleC2.lean（type_of%）

### 対象の文
```lean
theorem exists_primitive_odd_three : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd
```
### 前の宣言 `PAG119::Lc`
```lean
noncomputable def Lc (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
```
### 前の宣言 `PAG119::Lc_ne_one`
```lean
theorem Lc_ne_one (hp2 : p ≠ 2) : Lc p ≠ 1
```
### 前の宣言 `PAG171::primitive_of_ne_one`
```lean
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive
```
### 前の宣言 `PAG167::Lc_neg_one_pow`
```lean
theorem Lc_neg_one_pow (m : ℕ) (hpm : p = 2 * m + 1) : (PAG.Part119.Lc p (-1) : ℂ) = (-1) ^ m
```

## Part 252：`PAG256::hartley_eq_of_isPrimitive`（判定 C（照合者 R2、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem hartley_eq_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (y : ZMod N) :
    hartley (χ : ZMod N → ℂ) y = parFac χ * gaussSum χ stdAddChar * χ⁻¹ y
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```
### 前の宣言 `PAG203::dft_rk`
```lean
theorem dft_rk (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) [NeZero d] (hd : d ∣ W)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) (ξ : ZMod N) :
    𝓕 (rk (N := N) v d Ψ) ξ =
      if W / d ∣ ξ.val then
        ((W / d : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar * Ψ⁻¹ ((ξ.val / (W / d) : ℕ) : ZMod d)
      else 0
```

## Part 252：`PAG256::hartley_eq_zero_of_not_isUnit`（判定 C（照合者 R2、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem hartley_eq_zero_of_not_isUnit {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {y : ZMod N} (hy : ¬IsUnit y) : hartley (χ : ZMod N → ℂ) y = 0
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```
### 前の宣言 `PAG203::dft_rk`
```lean
theorem dft_rk (v W N : ℕ) [NeZero N] (h : v * W = N) (d : ℕ) [NeZero d] (hd : d ∣ W)
    (Ψ : DirichletCharacter ℂ d) (hΨ : Ψ.IsPrimitive) (ξ : ZMod N) :
    𝓕 (rk (N := N) v d Ψ) ξ =
      if W / d ∣ ξ.val then
        ((W / d : ℕ) : ℂ) * Ψ⁻¹ (-1) * gaussSum Ψ stdAddChar * Ψ⁻¹ ((ξ.val / (W / d) : ℕ) : ZMod d)
      else 0
```

## Part 252：`PAG256::hartley_units_inv`（判定 C（照合者 R2、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem hartley_units_inv (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    hartley (χ : ZMod N → ℂ) ((u⁻¹ : (ZMod N)ˣ) : ZMod N) = χ u * hartley (χ : ZMod N → ℂ) 1
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```

## Part 252：`PAG256::JH_eq_rootNum_mul`（判定 C（照合者 R2、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem JH_eq_rootNum_mul {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```
### 前の宣言 `PAG3::casK`
```lean
noncomputable def casK (t : ZMod N) : ℂ := PAG.Kloosterman.cas (ZMod.stdAddChar t)
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```

## Part 252：`PAG256::JH_eq_rootNum_mul_any`（判定 C（照合者 R2、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem JH_eq_rootNum_mul_any (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ) :
    JH (χ : ZMod N → ℂ) u = rootNum χ * χ u
```
### 前の宣言 `PAG3::hartley_char`
```lean
theorem hartley_char (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    ∑ y : ZMod N, casK (x * y) * χ y
      = (if χ.Even then 1 else -I) * ∑ y : ZMod N, ZMod.stdAddChar (x * y) * χ y
```
### 前の宣言 `PAG3::casK`
```lean
noncomputable def casK (t : ZMod N) : ℂ := PAG.Kloosterman.cas (ZMod.stdAddChar t)
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```

## Part 252：`PAG256::exists_primitive_even_five`（判定 C（照合者 R2））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem exists_primitive_even_five :
    ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even ∧ χ ≠ 1
```
### 前の宣言 `PAG119::Lc`
```lean
noncomputable def Lc (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
```
### 前の宣言 `PAG119::Lc_ne_one`
```lean
theorem Lc_ne_one (hp2 : p ≠ 2) : Lc p ≠ 1
```
### 前の宣言 `PAG171::primitive_of_ne_one`
```lean
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive
```
### 前の宣言 `PAG167::Lc_neg_one_pow`
```lean
theorem Lc_neg_one_pow (m : ℕ) (hpm : p = 2 * m + 1) : (PAG.Part119.Lc p (-1) : ℂ) = (-1) ^ m
```

## Part 252：`PAG256::parFac`（判定 C（照合者 R2））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
noncomputable def parFac (χ : DirichletCharacter ℂ N) : ℂ := ((1 - I) + (1 + I) * χ (-1)) / 2
```
### 前の宣言 `PAG198::gs`
```lean
noncomputable def gs {N : ℕ} (χ : DirichletCharacter ℂ N) : ℂ := if χ (-1) = 1 then 1 else I
```
### 前の宣言 `PAG198::neg_one_sq_eq`
```lean
theorem neg_one_sq_eq {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) = 1 ∨ χ (-1) = -1
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```

## Part 252：`PAG256::rootNum_eq`（判定 C（照合者 R2））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem rootNum_eq (χ : DirichletCharacter ℂ N) :
    rootNum χ = parFac χ * gaussSum χ stdAddChar / (Real.sqrt N : ℂ)
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```

## Part 252：`PAG256::parFac_of_even`（判定 D（一般化、照合者 R2））
根拠：照合者の判定

### 対象の文
```lean
omit [NeZero N] in
theorem parFac_of_even {χ : DirichletCharacter ℂ N} (h : χ.Even) : parFac χ = 1
```
### 前の宣言 `PAG2::parity_weight`
```lean
lemma parity_weight (χ : DirichletCharacter ℂ N) (r : ℕ) :
    ((1 + χ (-1)) + (-I) ^ r * (1 - χ (-1))) / 2 = if χ.Even then 1 else (-I) ^ r
```

## Part 253：`PAG257::charU`（判定 A（値））
根拠：ManualChecks2.lean の charU_eq_charFun（NeZero なし）

### 対象の文
```lean
def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u
```
### 前の宣言 `PAG::charFun`
```lean
-- PAG.lean（Part 1）。文脈：namespace PAG、variable {G : Type*} [CommGroup G]
def charFun (χ : G →* ℂˣ) : G → ℂ := fun g => (χ g : ℂ)
```

## Part 253：`PAG257::ip`（判定 A（定義、範囲の中））
根拠：ManualChecks2.lean の ip_eq_ipG（rfl）

### 対象の文
```lean
noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u
```
### 前の宣言 `PAG253::ipG`
```lean
noncomputable def ipG {G : Type*} [Fintype G] (f g : G → ℂ) : ℂ := ∑ x, starRingEnd ℂ (f x) * g x
```

## Part 253：`PAG257::eq_one_of_two`（判定 B）
根拠：MechChecks.lean

### 対象の文
```lean
theorem eq_one_of_two (χ : DirichletCharacter ℂ 2) : χ = 1
```
### 前の宣言 `PAG198::level_two_trivial`
```lean
theorem level_two_trivial {L : ℕ} (hL : L = 2) (φ : DirichletCharacter ℂ L) : φ = 1
```

## Part 253：`PAG257::not_isPrimitive_one_of_two_le`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem not_isPrimitive_one_of_two_le (hN : 2 ≤ N) : ¬(1 : DirichletCharacter ℂ N).IsPrimitive
```
### 前の宣言 `PAG195::ne_one_of_isPrimitive`
```lean
theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : χ ≠ 1
```

## Part 253：`PAG257::charU_one_mem_Vimprim`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem charU_one_mem_Vimprim (hN : 2 ≤ N) : charU (1 : DirichletCharacter ℂ N) ∈ Vimprim N
```
### 前の宣言 `PAG195::ne_one_of_isPrimitive`
```lean
theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (hN : 2 ≤ N) (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) : χ ≠ 1
```

## Part 253：`PAG257::not_isPrimitive_one_prime`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem not_isPrimitive_one_prime (p : ℕ) [hp : Fact p.Prime] :
    ¬(1 : DirichletCharacter ℂ p).IsPrimitive
```
### 前の宣言 `PAG32::prim_level_p_iff`
```lean
theorem prim_level_p_iff (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1
```

## Part 253：`PAG257::Vprim_two`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem Vprim_two : Vprim 2 = ⊥
```
### 前の宣言 `PAG30::no_prim_mod_two`
```lean
theorem no_prim_mod_two (χ : DirichletCharacter ℂ 2) : ¬ χ.IsPrimitive
```

## Part 253：`PAG257::ip_charU`（判定 C（照合者 R3））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
open Classical in
theorem ip_charU (χ ψ : DirichletCharacter ℂ N) :
    ip (charU χ) (charU ψ) = if χ = ψ then (Nat.totient N : ℂ) else 0
```
### 前の宣言 `PAG218::sum_units_char`
```lean
open Classical in
theorem sum_units_char (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ∑ a : (ZMod N)ˣ, ψ (a : ZMod N) = if ψ = 1 then (Nat.totient N : ℂ) else 0
```
### 前の宣言 `PAG3::conj_apply_eq_inv`
```lean
theorem conj_apply_eq_inv (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    starRingEnd ℂ (χ a) = χ⁻¹ a
```

## Part 253：`PAG257::Vprim_ne_bot_prime`（判定 C（照合者 R3、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem Vprim_ne_bot_prime (p : ℕ) [hp : Fact p.Prime] (h3 : 3 ≤ p) : Vprim p ≠ ⊥
```
### 前の宣言 `PAG119::Lc_ne_one`
```lean
theorem Lc_ne_one (hp2 : p ≠ 2) : Lc p ≠ 1
```
### 前の宣言 `PAG171::primitive_of_ne_one`
```lean
theorem primitive_of_ne_one (χ : DirichletCharacter ℂ p) (hne : χ ≠ 1) : χ.IsPrimitive
```

## Part 254：`PAG258::gaussSum_inv`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar)
```
### 前の宣言 `PAG9::conj_gaussSum`
```lean
theorem conj_gaussSum (χ : MulChar (ZMod N) ℂ) :
    starRingEnd ℂ (gaussSum χ ZMod.stdAddChar) = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar
```
### 前の宣言 `PAG9::chi_neg_one_sq`
```lean
omit [NeZero N] in
theorem chi_neg_one_sq (χ : MulChar (ZMod N) ℂ) : χ (-1) * χ (-1) = 1
```

## Part 254：`PAG258::rootNum_one_of_eq_one`（判定 C（Lean で確認））
根拠：SampleC2.lean（type_of%）

### 対象の文
```lean
omit [NeZero N] in
theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1
```
### 前の宣言 `PAG196::zN_level_one`
```lean
theorem zN_level_one {L : ℕ} [NeZero L] (hL : L = 1) (φ : DirichletCharacter ℂ L) : zN φ = 1
```

## Part 254：`PAG258::phaseA1_one`（判定 C（照合者 R4、低））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1
```
### 前の宣言 `PAG196::zN_level_one`
```lean
theorem zN_level_one {L : ℕ} [NeZero L] (hL : L = 1) (φ : DirichletCharacter ℂ L) : zN φ = 1
```

## Part 251：`PAG255::units_eq_of_coprime_parts`（判定 C（Lean で確認））
根拠：SampleC2.lean（type_of%）

### 対象の文
```lean
theorem units_eq_of_coprime_parts {N A B : ℕ} [NeZero N] (hN : N = A * B) (hAB : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (b c : (ZMod N)ˣ)
    (h1 : ZMod.unitsMap hA b = ZMod.unitsMap hA c) (h2 : ZMod.unitsMap hB b = ZMod.unitsMap hB c) :
    b = c
```
### 前の宣言 `PAG196::crt_unique`
```lean
theorem crt_unique {N A B : ℕ} [NeZero A] [NeZero B] (hAB : A * B = N) (hcop : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) {x y : ZMod N}
    (h₁ : ZMod.castHom hA (ZMod A) x = ZMod.castHom hA (ZMod A) y)
    (h₂ : ZMod.castHom hB (ZMod B) x = ZMod.castHom hB (ZMod B) y) : x = y
```

## Part 256：`PAG260::prodChar`（判定 A（定義））
根拠：MechChecks.lean（HEq rfl）

### 対象の文
```lean
noncomputable def prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ (M * N) :=
  changeLevel (dvd_mul_right M N) χ₁ * changeLevel (dvd_mul_left N M) χ₂
```
### 前の宣言 `PAG199::cmul`
```lean
noncomputable def cmul {c₁ c₂ : ℕ} (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) :
    DirichletCharacter ℂ (c₁ * c₂) :=
  X₁.changeLevel (dvd_mul_right c₁ c₂) * X₂.changeLevel (dvd_mul_left c₂ c₁)
```
### 前の宣言 `PAG236::charMul`
```lean
noncomputable def charMul {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ * DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂
```

## Part 256：`PAG260::crtMap`（判定 A（定義））
根拠：ManualChecks2.lean の crtMap_eq_param（rfl）

### 対象の文
```lean
def crtMap (M N : ℕ) [NeZero M] [NeZero N] (x : ZMod M × ZMod N) : ZMod (M * N) :=
  ((x.1.val * N + x.2.val * M : ℕ) : ZMod (M * N))
```
### 前の宣言 `PAG193::param`
```lean
noncomputable def param (N₁ N₂ : ℕ) (x : ZMod N₁ × ZMod N₂) : ZMod (N₁ * N₂) :=
  ((x.1.val * N₂ + x.2.val * N₁ : ℕ) : ZMod (N₁ * N₂))
```

## Part 256：`PAG260::crossSign`（判定 A（値））
根拠：ManualChecks2.lean の crossSign_eq_rs（NeZero なし）

### 対象の文
```lean
open Classical in
noncomputable def crossSign (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) : ℂ :=
  if χ₁.Odd ∧ χ₂.Odd then -1 else 1
```
### 前の宣言 `PAG198::rs`
```lean
noncomputable def rs {M N : ℕ} (ψ : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ N) : ℂ :=
  if ψ (-1) = 1 then 1 else χ (-1)


```

## Part 256：`PAG260::gaussSum_prodChar`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem gaussSum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (prodChar χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
```
### 前の宣言 `PAG193::gaussSum_mul_coprime`
```lean
theorem gaussSum_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
```

## Part 256：`PAG260::isPrimitive_prodChar`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem isPrimitive_prodChar (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (prodChar χ₁ χ₂).IsPrimitive
```
### 前の宣言 `PAG194::isPrimitive_mul`
```lean
theorem isPrimitive_mul (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)).IsPrimitive
```
### 前の宣言 `PAG236::isPrimitive_charMul`
```lean
theorem isPrimitive_charMul {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ : DirichletCharacter ℂ m} {χ₂ : DirichletCharacter ℂ n} (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (charMul χ₁ χ₂).IsPrimitive
```

## Part 256：`PAG260::prodChar_apply`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem prodChar_apply (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    prodChar χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
```
### 前の宣言 `PAG193::mul_changeLevel_apply`
```lean
theorem mul_changeLevel_apply (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) (x : ZMod (N₁ * N₂)) :
    (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) x
      = χ₁ (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x) *
        χ₂ (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x)
```
### 前の宣言 `PAG199::cmul_apply`
```lean
theorem cmul_apply {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (X₁ : DirichletCharacter ℂ c₁)
    (X₂ : DirichletCharacter ℂ c₂) (x : ZMod (c₁ * c₂)) :
    cmul X₁ X₂ x = X₁ (ZMod.castHom (dvd_mul_right c₁ c₂) (ZMod c₁) x) *
      X₂ (ZMod.castHom (dvd_mul_left c₂ c₁) (ZMod c₂) x)
```
### 前の宣言 `PAG236::charMul_apply`
```lean
theorem charMul_apply {m n : ℕ} [NeZero m] [NeZero n] (χ₁ : DirichletCharacter ℂ m)
    (χ₂ : DirichletCharacter ℂ n) (x : ZMod (m * n)) :
    charMul χ₁ χ₂ x = χ₁ (ZMod.cast x) * χ₂ (ZMod.cast x)
```

## Part 256：`PAG260::crtMap_bijective`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem crtMap_bijective (h : M.Coprime N) : Function.Bijective (crtMap M N)
```
### 前の宣言 `PAG193::param_bijective`
```lean
theorem param_bijective (hcop : N₁.Coprime N₂) : Function.Bijective (param N₁ N₂)
```

## Part 256：`PAG260::stdAddChar_crtMap`（判定 A）
根拠：MechChecks.lean（両向き）

### 対象の文
```lean
theorem stdAddChar_crtMap (x : ZMod M × ZMod N) :
    stdAddChar (crtMap M N x) = stdAddChar x.1 * stdAddChar x.2
```
### 前の宣言 `PAG193::stdAddChar_param`
```lean
theorem stdAddChar_param (x : ZMod N₁ × ZMod N₂) :
    stdAddChar (param N₁ N₂ x) = stdAddChar x.1 * stdAddChar x.2
```

## Part 256：`PAG260::cast_crtMap_fst`（判定 B）
根拠：MechChecks.lean

### 対象の文
```lean
theorem cast_crtMap_fst (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
```
### 前の宣言 `PAG193::param_cast₁`
```lean
omit [NeZero N₂] in
theorem param_cast₁ (x : ZMod N₁ × ZMod N₂) :
    ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) (param N₁ N₂ x) = x.1 * (N₂ : ZMod N₁)
```

## Part 256：`PAG260::cast_crtMap_snd`（判定 B）
根拠：MechChecks.lean

### 対象の文
```lean
theorem cast_crtMap_snd (x : ZMod M × ZMod N) :
    ((crtMap M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
```
### 前の宣言 `PAG193::param_cast₂`
```lean
omit [NeZero N₁] in
theorem param_cast₂ (x : ZMod N₁ × ZMod N₂) :
    ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) (param N₁ N₂ x) = x.2 * (N₁ : ZMod N₂)
```

## Part 256：`PAG260::charU_prodChar`（判定 B）
根拠：MechChecks.lean

### 対象の文
```lean
theorem charU_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    PAG.Part257.charU (prodChar χ₁ χ₂) u =
      PAG.Part257.charU χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        PAG.Part257.charU χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
```
### 前の宣言 `PAG236::charMul_apply_unit`
```lean
theorem charMul_apply_unit {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n)
    (u : (ZMod (m * n))ˣ) :
    charMul χ₁ χ₂ (u : ZMod (m * n)) =
      χ₁ (ZMod.cast (u : ZMod (m * n))) * χ₂ (ZMod.cast (u : ZMod (m * n)))
```

## Part 256：`PAG260::prodChar_neg_one`（判定 B）
根拠：ManualChecks2.lean（type_of%）

### 対象の文
```lean
theorem prodChar_neg_one (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    prodChar χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
```
### 前の宣言 `PAG204::changeLevel_neg_one`
```lean
theorem changeLevel_neg_one {d c : ℕ} (hd : d ∣ c) (Ψ : DirichletCharacter ℂ d) :
    Ψ.changeLevel hd (-1) = Ψ (-1)
```

## Part 256：`PAG260::norm_char_unit`（判定 C（照合者 R5））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem norm_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
```
### 前の宣言 `PAG202::normSq_chi_unit`
```lean
theorem normSq_chi_unit {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (a : (ZMod d)ˣ) :
    Complex.normSq (Ψ a) = 1
```
### 前の宣言 `PAG198::neg_one_sq_eq`
```lean
theorem neg_one_sq_eq {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) = 1 ∨ χ (-1) = -1
```

## Part 256：`PAG260::norm_cross`（判定 C（照合者 R5））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
omit [NeZero M] [NeZero N] in
theorem norm_cross (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
```
### 前の宣言 `PAG199::normSq_chi_natCast`
```lean
theorem normSq_chi_natCast {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Complex.normSq (Ψ (n : ZMod d)) = 1
```
### 前の宣言 `PAG200::chi_level_one`
```lean
theorem chi_level_one (χ : DirichletCharacter ℂ 1) (y : ZMod 1) : χ y = 1
```

## Part 256：`PAG260::parFac_prodChar`（判定 C（照合者 R5））
根拠：照合者の判定（Lean では未確認）

### 対象の文
```lean
theorem parFac_prodChar (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.parFac (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * PAG.Part256.parFac χ₁ * PAG.Part256.parFac χ₂
```
### 前の宣言 `PAG204::changeLevel_neg_one`
```lean
theorem changeLevel_neg_one {d c : ℕ} (hd : d ∣ c) (Ψ : DirichletCharacter ℂ d) :
    Ψ.changeLevel hd (-1) = Ψ (-1)
```
### 前の宣言 `PAG198::neg_one_sq_eq`
```lean
theorem neg_one_sq_eq {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) = 1 ∨ χ (-1) = -1
```
### 前の宣言 `PAG198::gs_combine`
```lean
theorem gs_combine (s₁ s₂ : ℂ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) :
    (if s₁ * s₂ = 1 then (1 : ℂ) else I) =
      (if s₁ = 1 then (1 : ℂ) else s₂) * (if s₁ = 1 then (1 : ℂ) else I) * (if s₂ = 1 then (1 : ℂ) else I)
```

## Part 256：`PAG260::rootNum_prodChar`（判定 D（C との境目、照合者 R5））
根拠：照合者の判定 D。注記は中身の説明（Lean ではつないでいない）

### 対象の文
```lean
theorem rootNum_prodChar (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    PAG.Part256.rootNum (prodChar χ₁ χ₂) =
      crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (PAG.Part256.rootNum χ₁ * PAG.Part256.rootNum χ₂)
```
### 前の宣言 `PAG193::z_mul_coprime`
```lean
theorem z_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
        / ((Real.sqrt ((N₁ * N₂ : ℕ) : ℝ) : ℝ) : ℂ)
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) *
        ((gaussSum χ₁ stdAddChar / ((Real.sqrt (N₁ : ℝ) : ℝ) : ℂ)) *
          (gaussSum χ₂ stdAddChar / ((Real.sqrt (N₂ : ℝ) : ℝ) : ℂ))) ∧
      ∃ M : ℕ, 0 < M ∧ (χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂)) ^ M = 1
```
### 前の宣言 `PAG193::gaussSum_mul_coprime`
```lean
theorem gaussSum_mul_coprime (hcop : N₁.Coprime N₂) (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) :
    gaussSum (χ₁.changeLevel (dvd_mul_right N₁ N₂) * χ₂.changeLevel (dvd_mul_left N₂ N₁)) stdAddChar
      = χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
```
### 前の宣言 `PAG198::gs_combine`
```lean
theorem gs_combine (s₁ s₂ : ℂ) (h₁ : s₁ = 1 ∨ s₁ = -1) (h₂ : s₂ = 1 ∨ s₂ = -1) :
    (if s₁ * s₂ = 1 then (1 : ℂ) else I) =
      (if s₁ = 1 then (1 : ℂ) else s₂) * (if s₁ = 1 then (1 : ℂ) else I) * (if s₂ = 1 then (1 : ℂ) else I)
```

## Part 256：`PAG260::cross_eq_sign_of_rootNum_one`（判定 D（関係の注記））
根拠：照合者の判定 D。注記は関係の説明（数学として、Lean ではつないでいない）

### 対象の文
```lean
theorem cross_eq_sign_of_rootNum_one (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : PAG.Part256.rootNum χ₁ = 1)
    (w2 : PAG.Part256.rootNum χ₂ = 1) (w12 : PAG.Part256.rootNum (prodChar χ₁ χ₂) = 1) :
    crossSign χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
```
### 前の宣言 `PAG198::gauss_sign_real`
```lean
theorem gauss_sign_real (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (h2 : χ ^ 2 = 1) : zN χ = gs χ
```
### 前の宣言 `PAG198::real_reciprocity`
```lean
theorem real_reciprocity {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂] (hcop : N₁.Coprime N₂)
    (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂) (h₁ : χ₁.IsPrimitive)
    (h₂ : χ₂.IsPrimitive) (h₁2 : χ₁ ^ 2 = 1) (h₂2 : χ₂ ^ 2 = 1) :
    χ₁ (N₂ : ZMod N₁) * χ₂ (N₁ : ZMod N₂) = rs χ₁ χ₂
```
### 前の宣言 `PAG198::gauss_sign_aux`
```lean
theorem gauss_sign_aux (N : ℕ) : ∀ (_ : NeZero N) (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    χ ^ 2 = 1 → zN χ = gs χ ∧
      ∀ (q f : ℕ) (_ : Fact q.Prime), 1 ≤ f → q.Coprime N →
        ∀ ψ : DirichletCharacter ℂ (q ^ f), ψ.IsPrimitive → ψ ^ 2 = 1 →
          ψ ((N : ℕ) : ZMod (q ^ f)) * χ ((q ^ f : ℕ) : ZMod N) = rs ψ χ
```

## Part 256：`PAG194::decomp（「Lean にしていない (i)」への注記の根拠）`（判定 関係（監査者の読み））
根拠：監査者の読み（Lean ではつないでいない）

### 対象の文
```lean
theorem decomp (hcop : N₁.Coprime N₂) (χ : DirichletCharacter ℂ (N₁ * N₂)) :
    χ = (comp₁ hcop χ).changeLevel (dvd_mul_right N₁ N₂) *
      (comp₂ hcop χ).changeLevel (dvd_mul_left N₂ N₁)
```
### 前の宣言 `PAG236::charMul_injective`
```lean
theorem charMul_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ χ₁' : DirichletCharacter ℂ m} {χ₂ χ₂' : DirichletCharacter ℂ n}
    (h : charMul χ₁ χ₂ = charMul χ₁' χ₂') : χ₁ = χ₁' ∧ χ₂ = χ₂'
```
### 前の宣言 `PAG236::primEquiv`
```lean
noncomputable def primEquiv {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Prim m × Prim n ≃ Prim (m * n) :=
  Equiv.ofBijective (primMul hmn) (primMul_bijective hmn)
```