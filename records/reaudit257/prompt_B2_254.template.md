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

noncomputable def casKer (t : ZMod N) : ℂ :=
  ((Real.cos (2 * Real.pi * t.val / N) + Real.sin (2 * Real.pi * t.val / N) : ℝ) : ℂ)

noncomputable def hartley (f : ZMod N → ℂ) (y : ZMod N) : ℂ :=
  ∑ x : ZMod N, f x * casKer (x * y)

open Classical in
noncomputable def rootNum (χ : DirichletCharacter ℂ N) : ℂ :=
  gaussSum χ stdAddChar / ((if χ.Even then (1 : ℂ) else I) * (Real.sqrt N : ℂ))

noncomputable def JH (f : ZMod N → ℂ) (u : (ZMod N)ˣ) : ℂ :=
  hartley f ((u⁻¹ : (ZMod N)ˣ) : ZMod N) / (Real.sqrt N : ℂ)

-- PAG257.lean（文脈：namespace PAG.Part257 / open ZMod Complex Finset PAG.Part256 / variable {N : ℕ} [NeZero N]）

open Classical in
noncomputable def extL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun g x := if h : IsUnit x then g h.unit else 0
  map_add' f g := by
    funext x
    by_cases h : IsUnit x <;> simp [h]
  map_smul' c f := by
    funext x
    by_cases h : IsUnit x <;> simp [h]

noncomputable def JHL : (ZMod N → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) where
  toFun f := JH f
  map_add' f g := by
    funext u
    show JH (f + g) u = JH f u + JH g u
    unfold JH hartley
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.add_apply, add_mul])
  map_smul' c f := by
    funext u
    show JH (c • f) u = c * JH f u
    unfold JH hartley
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc])

noncomputable def TopL : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ) := JHL.comp extL

def charU (χ : DirichletCharacter ℂ N) : (ZMod N)ˣ → ℂ := fun u => χ u

noncomputable def ip (f g : (ZMod N)ˣ → ℂ) : ℂ := ∑ u, (starRingEnd ℂ) (f u) * g u

noncomputable def Vprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.IsPrimitive} => charU χ.1)

noncomputable def Vimprim (N : ℕ) [NeZero N] : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // ¬χ.IsPrimitive} => charU χ.1)

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

noncomputable def pullL {M : ℕ} (hNM : N ∣ M) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod M)ˣ → ℂ) where
  toFun f u := f (ZMod.unitsMap hNM u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

structure Lvl where
  
  val : ℕ
  pos : 0 < val
deriving DecidableEq

instance : Preorder Lvl where
  le a b := a.val ∣ b.val
  le_refl a := dvd_refl a.val
  le_trans _ _ _ := dvd_trans

instance : IsDirectedOrder Lvl :=
  ⟨fun a b => ⟨⟨a.val * b.val, Nat.mul_pos a.pos b.pos⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

instance : Nonempty Lvl := ⟨⟨1, Nat.one_pos⟩⟩

instance (a : Lvl) : NeZero a.val := ⟨a.pos.ne'⟩

abbrev Gsp (a : Lvl) : Type := (ZMod a.val)ˣ → ℂ

noncomputable def pullSys (a b : Lvl) (h : a ≤ b) : Gsp a →ₗ[ℂ] Gsp b :=
  pullL (N := a.val) (M := b.val) h

instance : DirectedSystem Gsp (fun a b h => (pullSys a b h : Gsp a → Gsp b)) where
  map_self a f := by
    funext u
    show f (ZMod.unitsMap (dvd_refl a.val) u) = f u
    rw [ZMod.unitsMap_self]
    rfl
  map_map c b a hab hbc f := by
    funext u
    show f (ZMod.unitsMap hab (ZMod.unitsMap hbc u)) = f (ZMod.unitsMap (dvd_trans hab hbc) u)
    rw [← ZMod.unitsMap_comp hab hbc]
    rfl

abbrev Lim : Type := Module.DirectLimit Gsp pullSys

noncomputable abbrev ofL (a : Lvl) : Gsp a →ₗ[ℂ] Lim := Module.DirectLimit.of ℂ Lvl Gsp pullSys a

noncomputable def Uinf : Lim →ₗ[ℂ] Lim :=
  Module.DirectLimit.map (fun a => UA1 (N := a.val)) (fun a b h => by
    refine LinearMap.ext (fun f => ?_)
    exact UA1_comp_pullL (N := a.val) (M := b.val) h f)

noncomputable def ipn {a : Lvl} (f g : Gsp a) : ℂ := ip f g / (Nat.totient a.val : ℂ)

noncomputable def ipLim (z w : Lim) : ℂ :=
  ipn (Module.DirectLimit.exists_of₂ z w).choose_spec.choose
    (Module.DirectLimit.exists_of₂ z w).choose_spec.choose_spec.choose

noncomputable def condPart (N : ℕ) [NeZero N] (q : ℕ) : Submodule ℂ ((ZMod N)ˣ → ℂ) :=
  Submodule.span ℂ (Set.range fun χ : {χ : DirichletCharacter ℂ N // χ.conductor = q} => charU χ.1)

noncomputable def ipR (f : (ZMod N)ˣ → ℂ) : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ℂ where
  toFun := ip f
  map_add' := ip_add_right f
  map_smul' c g := by rw [ip_smul_right, smul_eq_mul, RingHom.id_apply]
```

## 入力 (2)：形式文の全文（PAG258.lean の定理 57 個すべて。原文のまま、証明だけ除いた。すべてコンパイル済みで sorry なし、公理は標準の範囲）
★ は、前回の照合の後に足した文・文を変えた文です。
```lean
omit [NeZero N] in
theorem rootNum_congr {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂] (h : d₁ = d₂)
    (χ₁ : DirichletCharacter ℂ d₁) (χ₂ : DirichletCharacter ℂ d₂)
    (hχ : ∀ a : ℤ, χ₁ a = χ₂ a) : rootNum χ₁ = rootNum χ₂
theorem phaseA1_of_isPrimitive {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    phaseA1 χ = rootNum χ
theorem normSq_phaseA1 (χ : DirichletCharacter ℂ N) : Complex.normSq (phaseA1 χ) = 1
theorem phaseA1_changeLevel {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    phaseA1 (changeLevel hNM χ) = phaseA1 χ
omit [NeZero N] in
theorem rootNum_one_of_eq_one {d : ℕ} [NeZero d] (hd : d = 1) :
    rootNum (1 : DirichletCharacter ℂ d) = 1
theorem phaseA1_one : phaseA1 (1 : DirichletCharacter ℂ N) = 1
theorem ip_add_right (f g h : (ZMod N)ˣ → ℂ) : ip f (g + h) = ip f g + ip f h
theorem ip_smul_right (f g : (ZMod N)ˣ → ℂ) (c : ℂ) : ip f (c • g) = c * ip f g
theorem UA1_charU (χ : DirichletCharacter ℂ N) : UA1 (charU χ) = phaseA1 χ • charU χ
theorem ip_UA1 (f g : (ZMod N)ˣ → ℂ) : ip (UA1 f) (UA1 g) = ip f g
theorem UA1_eq_TopL_of_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f = TopL f
omit [NeZero N] in
theorem pullL_charU {M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter ℂ N) :
    pullL hNM (charU χ) = charU (changeLevel hNM χ)
theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
    UA1 (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))
theorem UA1_unique (U : ((ZMod N)ˣ → ℂ) →ₗ[ℂ] ((ZMod N)ˣ → ℂ))
    (hU : ∀ χ : DirichletCharacter ℂ N,
      U (charU χ) = pullL χ.conductor_dvd_level (TopL (charU χ.primitiveCharacter))) :
    U = UA1
theorem UA1_comp_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f : (ZMod N)ˣ → ℂ) :
    UA1 (pullL hNM f) = pullL hNM (UA1 f)
theorem TopL_not_compat :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd 2) f) ≠ pullL (one_dvd 2) (TopL f)
theorem UA1_ne_TopL_prime (p : ℕ) [hp : Fact p.Prime] :
    charU (1 : DirichletCharacter ℂ p) ∈ Vimprim p ∧
      UA1 (charU (1 : DirichletCharacter ℂ p)) ≠ TopL (charU (1 : DirichletCharacter ℂ p))
theorem UA1_mem_Vprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vprim N) : UA1 f ∈ Vprim N
theorem UA1_mem_Vimprim {f : (ZMod N)ˣ → ℂ} (hf : f ∈ Vimprim N) : UA1 f ∈ Vimprim N
theorem UA1_comp_TopL (f : (ZMod N)ˣ → ℂ) : UA1 (TopL f) = TopL (UA1 f)
theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
    rootNum (1 : DirichletCharacter ℂ p) = -(((Real.sqrt p)⁻¹ : ℝ) : ℂ)
theorem TopL_not_compat_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ f : (ZMod 1)ˣ → ℂ, TopL (pullL (one_dvd p) f) ≠ pullL (one_dvd p) (TopL f)
theorem gaussSum_inv (χ : DirichletCharacter ℂ N) :
    gaussSum χ⁻¹ (stdAddChar (N := N)) = χ (-1) * (starRingEnd ℂ) (gaussSum χ stdAddChar)
theorem rootNum_inv (χ : DirichletCharacter ℂ N) :
    rootNum χ⁻¹ = (starRingEnd ℂ) (rootNum χ)
theorem primitiveCharacter_inv_apply (χ : DirichletCharacter ℂ N) (a : ℤ) :
    (χ⁻¹).primitiveCharacter a = (χ.primitiveCharacter)⁻¹ a
theorem phaseA1_inv (χ : DirichletCharacter ℂ N) :
    phaseA1 χ⁻¹ = (starRingEnd ℂ) (phaseA1 χ)
theorem UA1_star (f : (ZMod N)ˣ → ℂ) :
    UA1 (fun u => (starRingEnd ℂ) (f u)) = fun u => (starRingEnd ℂ) (UA1 f u)
omit [NeZero N] in
theorem pullL_injective {M : ℕ} [NeZero M] (hNM : N ∣ M) : Function.Injective (pullL hNM)
theorem sum_units_unitsMap {M : ℕ} [NeZero M] (hNM : N ∣ M) (F : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ∑ u : (ZMod M)ˣ, F (ZMod.unitsMap hNM u) =
      (Nat.totient M : ℂ) * ∑ v : (ZMod N)ˣ, F v
theorem ip_pullL {M : ℕ} [NeZero M] (hNM : N ∣ M) (f g : (ZMod N)ˣ → ℂ) :
    (Nat.totient N : ℂ) * ip (pullL hNM f) (pullL hNM g) = (Nat.totient M : ℂ) * ip f g
theorem UA1_bijective : Function.Bijective (UA1 (N := N))
theorem UA1_family_unique (U : ∀ a : Lvl, Gsp a →ₗ[ℂ] Gsp a)
    (hT : ∀ (a : Lvl) (f : Gsp a), f ∈ Vprim a.val → U a f = TopL f)
    (hc : ∀ (a b : Lvl) (h : a ≤ b) (f : Gsp a), U b (pullSys a b h f) = pullSys a b h (U a f))
    (a : Lvl) : U a = UA1
theorem ofL_injective (a : Lvl) : Function.Injective (ofL a)
theorem Uinf_ofL (a : Lvl) (f : Gsp a) : Uinf (ofL a f) = ofL a (UA1 f)
theorem Uinf_unique (V : Lim →ₗ[ℂ] Lim) (hV : ∀ a (f : Gsp a), V (ofL a f) = ofL a (UA1 f)) :
    V = Uinf
theorem Uinf_bijective : Function.Bijective Uinf
theorem Uinf_ofL_of_mem_Vprim (q : Lvl) {f : Gsp q} (hf : f ∈ Vprim q.val) :
    Uinf (ofL q f) = ofL q (TopL f)
theorem ofL_charU (a : Lvl) (χ : DirichletCharacter ℂ a.val) :
    ofL a (charU χ) =
      ofL ⟨χ.conductor, Nat.pos_of_ne_zero (conductor_ne_zero χ)⟩ (charU χ.primitiveCharacter)
theorem span_ofL_Vprim : Submodule.span ℂ (⋃ q : Lvl, ofL q '' (Vprim q.val : Set (Gsp q))) = ⊤
theorem Uinf_unique_TopL (V : Lim →ₗ[ℂ] Lim)
    (hV : ∀ q (f : Gsp q), f ∈ Vprim q.val → V (ofL q f) = ofL q (TopL f)) : V = Uinf
theorem totient_ne_zero' (a : Lvl) : (Nat.totient a.val : ℂ) ≠ 0
theorem ipn_pullSys {a b : Lvl} (h : a ≤ b) (f g : Gsp a) :
    ipn (pullSys a b h f) (pullSys a b h g) = ipn f g
theorem ipn_eq_of_ofL_eq {a b : Lvl} {f g : Gsp a} {f' g' : Gsp b}
    (hf : ofL a f = ofL b f') (hg : ofL a g = ofL b g') : ipn f g = ipn f' g'
theorem ipLim_ofL (a : Lvl) (f g : Gsp a) : ipLim (ofL a f) (ofL a g) = ipn f g
theorem ipLim_Uinf (z w : Lim) : ipLim (Uinf z) (Uinf w) = ipLim z w
theorem ipLim_add_right (z w w' : Lim) : ipLim z (w + w') = ipLim z w + ipLim z w'
theorem ipLim_smul_right (z w : Lim) (r : ℂ) : ipLim z (r • w) = r * ipLim z w
theorem ipLim_conj (z w : Lim) : ipLim w z = (starRingEnd ℂ) (ipLim z w)
theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0
theorem ipLim_self_nonneg (z : Lim) : ∃ r : ℝ, 0 ≤ r ∧ ipLim z z = r
-- ★ 
theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
    (hg : g ∈ Vprim N) : UA1 (pullL hNM g) = pullL hNM (TopL g)
-- ★ 
theorem condPart_eq_map {M : ℕ} [NeZero M] (hNM : N ∣ M) :
    condPart M N = (Vprim N).map (pullL hNM)
-- ★ 
theorem ip_condPart {q q' : ℕ} (hqq : q ≠ q') {f g : (ZMod N)ˣ → ℂ}
    (hf : f ∈ condPart N q) (hg : g ∈ condPart N q') : ip f g = 0
-- ★ 
theorem iSup_condPart : ⨆ q, condPart N q = ⊤
-- ★ 
theorem iSupIndep_condPart : iSupIndep (condPart N)
-- ★ 
theorem UA1_mem_condPart {q : ℕ} {f : (ZMod N)ˣ → ℂ} (hf : f ∈ condPart N q) :
    UA1 f ∈ condPart N q
-- ★ 
theorem ipLim_ofL_Vprim {q q' : Lvl} (hqq : q.val ≠ q'.val) {f : Gsp q} {g : Gsp q'}
    (hf : f ∈ Vprim q.val) (hg : g ∈ Vprim q'.val) : ipLim (ofL q f) (ofL q' g) = 0
```

## 入力 (3)：Lean ファイルの文面（ファイル冒頭の説明と、各宣言の docstring。原文のまま）
```
【ファイル冒頭の説明】
/-
アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、法を上げた組み立て（Part 252 の残る問い）

問いの出所：著者の指示（2026-11-13 06:43「Part 252, Part 254 を解決してください」）を、Part 254 で Part 252 の
「残る問い」2 つを解く、と読んだ。
1. 法 N の境界ユニタリ全体（原始的でない指標を含む）を、J∘H_q（q ∣ N）の新しい部分の直和として書く文
   （Part 253 の着手前の候補 K2。盲検の問いテスト T2：既知の結果の短い帰結）。
2. 法を上げた組み立て（引き戻しと両立し、1 つの作用素にまとまること。着手前の盲検 T3 の注意：Ẑ に移るのは
   引き戻しと両立する作用素だけ）。

記号：G_N = (ℤ/N)ˣ、単数の上の関数、⟨f, g⟩ = Σ_u conj(f u)·g u（Part 253 の `ip`）、T = Part 253 の `TopL`。
χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）。
- `phaseA1 χ` = W(χ*)（Part 252 の `rootNum`）。A1 の位相を、原始的でない指標には誘導元から入れたもの。
- `UA1` = Σ_χ phaseA1(χ)·P_χ（P_χ f = (⟨χ, f⟩/φ(N))·χ）。法 N の A1 の境界ユニタリ U_N。
- `pullL hNM`（N ∣ M）：単数の上の関数の引き戻し f ↦ f ∘ (ℤ/M)ˣ → (ℤ/N)ˣ。

内容：
1. 位相：原始指標では phaseA1 χ = W(χ)（`phaseA1_of_isPrimitive`）、|phaseA1|² = 1（`normSq_phaseA1`）、
   法を上げても変わらない（`phaseA1_changeLevel`）、自明な指標では 1（`phaseA1_one`）。型の違う法の間の受け渡しは
   `rootNum_congr`（法が等しく、整数での値が等しい指標は同じ W を持つ）。
2. U_N：すべての指標で U_N χ = phaseA1(χ)·χ（`UA1_charU`）。U_N は ⟨·,·⟩ を保つ（`ip_UA1`、全体でユニタリ）。
   原始部分では U_N = T（`UA1_eq_TopL_of_mem_Vprim`）。
3. 指標ごとの式（残る問い 1）：すべての χ で U_N χ = π_{q→N}(T_q χ*)（`UA1_charU_eq_pull_TopL`。位相の定義の
   言い換え）。U_N はこの性質で一意に決まる（`UA1_unique`。基底の上の値による）。直和そのものは 10。
4. 組み立て（残る問い 2）：法を上げる引き戻しと両立する：U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。
   T は両立しない（`TopL_not_compat`：法 1 → 2、`TopL_not_compat_prime`：法 1 → p）。
5. 原始的でない部分では U_N ≠ T：素数 p の自明な指標で U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p（`UA1_ne_TopL_prime`）。
   W(1 mod p) = −1/√p（`rootNum_one_prime`）。素数の法 p では、T の極分解のユニタリ因子のこの指標での固有値は
   −1 なので、U_p（固有値 1）はそのユニタリ因子でもない（極分解そのものは Lean にしていない）。法によっては一致する
   （法 1・6。独立照合 B の反例、数値 step277 の (20)）。
   U_N は V_prim・V_imprim を保ち（`UA1_mem_Vprim`・`UA1_mem_Vimprim`）、T と可換（`UA1_comp_TopL`）。
6. 実数性：τ(χ⁻¹) = χ(−1)·conj τ(χ)（`gaussSum_inv`）、W(χ⁻¹) = conj W(χ)（`rootNum_inv`）、
   phaseA1(χ⁻¹) = conj phaseA1(χ)（`phaseA1_inv`）、U_N は複素共役と可換（`UA1_star`：核は実数値、KUK = U）。
7. 両立する族の一意性：各法で原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけ
   （`UA1_family_unique`）。原始的でない指標の上の位相は、両立から決まる。
8. 極限：法の集合（正の整数を割り算の順で並べたもの、`Lvl`）の上の帰納系（引き戻し `pullSys`）と、その帰納極限
   `Lim`（Mathlib の `Module.DirectLimit`）。極限への写像は単射（`ofL_injective`）。U_N の族は極限の上の
   作用素 U_∞ を与え（`Uinf`、`Uinf_ofL`）、それは一意（`Uinf_unique`）で全単射（`Uinf_bijective`）。各法の原始部分の
   像は極限を張り（`span_ofL_Vprim`）、U_∞ はその上で T_q（`Uinf_ofL_of_mem_Vprim`）。U_∞ はこの性質でも一意
   （`Uinf_unique_TopL`）。
9. 極限の上の内積：引き戻しの和 φ(N)·Σ F(πu) = φ(M)·Σ F（`sum_units_unitsMap`）から、正規化した内積
   ⟨f, g⟩/φ(N) は引き戻しで変わらない（`ip_pullL`・`ipn_pullSys`）。代表によらない（`ipn_eq_of_ofL_eq`）ので
   極限の上の内積 `ipLim` が決まり、右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、
   正定値（`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`）。U_∞ はこれを保つ（`ipLim_Uinf`）。

10. 有限レベルの直和（独立照合 B の指摘で追加）：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q))
   に等しく（`condPart_eq_map`、q ∣ M）、導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、
   独立（`iSupIndep_condPart`）。つまり単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和。U_M は各部分を
   保ち（`UA1_mem_condPart`）、その上で π∘T_q（`UA1_pullL_of_mem_Vprim`：g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
   極限でも、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`）。

A1 との関係：U_N は A1 の位相を「定義として」入れた作用素で、3・4 は A1 の位相の選び方（誘導元から取る）の
帰結。7 は、原始的でない指標の位相が（原始部分の A1 と両立から）一通りに決まることを言う。A1 は公準のまま
（導いていない）。

Lean にしていないこと：U_N の明示の核（導手とメビウスの式。数値は step277 の (8)）。帰納極限 `Lim` と Ẑ^× の上の
局所定数関数の空間との同一視、`ipLim` による完備化（L²(Ẑ^×)）と、その上へのユニタリの延長（どちらも標準の事実）。
4 の `TopL_not_compat_prime`、5 の 2 文目以降、6〜9 は独立照合 A・C の後に、10 は独立照合 B の後に足した
（ノートの §7）。一般の N ∣ M（N < M）での T の非両立と、N ≥ 2 一般での U_N ≠ T（τ(1 mod N) = μ(N)）は Lean に
していない。
-/

【conductor_neZero】
/-- 導手は 0 でない。 -/

【phaseA1】
/-- A1 の位相 phaseA1(χ) = W(χ*)（χ* は χ を誘導する原始指標）。 -/

【rootNum_congr】
/-- 法が等しく、整数での値が等しい 2 つの指標は、同じ W を持つ（型の違う法の間の受け渡し）。 -/

【phaseA1_of_isPrimitive】
/-- 原始指標では phaseA1 χ = W(χ)。 -/

【normSq_phaseA1】
/-- |phaseA1 χ|² = 1（χ* は原始的）。 -/

【phaseA1_changeLevel】
/-- 法を上げても位相は変わらない：phaseA1(changeLevel χ) = phaseA1(χ)。 -/

【rootNum_one_of_eq_one】
/-- 法 1 の自明な指標の W は 1。 -/

【phaseA1_one】
/-- 自明な指標の位相は 1。 -/

【ip_add_right】
/-- 内積の右側の加法性。 -/

【ip_smul_right】
/-- 内積の右側のスカラー倍。 -/

【UA1】
/-- 法 N の A1 の境界ユニタリ U_N = Σ_χ phaseA1(χ)·P_χ。 -/

【UA1_charU】
/-- すべての指標で U_N χ = phaseA1(χ)·χ。 -/

【ip_UA1】
/-- U_N は ⟨·,·⟩ を保つ（単数の上の関数の空間全体でユニタリ）。 -/

【UA1_eq_TopL_of_mem_Vprim】
/-- 原始部分では U_N = T（Part 253 の `TopL_eq_of_A1`）。 -/

【pullL】
/-- 単数の上の関数の引き戻し π_{N→M}（N ∣ M）。 -/

【pullL_charU】
/-- 指標の引き戻しは、法を上げた指標。 -/

【UA1_charU_eq_pull_TopL】
/-- **指標ごとの式**（直和の文の指標ごとの形。直和そのものは §8）：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（q = cond χ、χ* は誘導元の原始指標）。 -/

【UA1_unique】
/-- U_N は指標ごとの式で一意に決まる（基底の上の値による）：すべての指標で U χ = π_{q→N}(T_q χ*) となる線形写像 U は U_N。 -/

【UA1_comp_pullL】
/-- 引き戻しとの両立：U_M ∘ π = π ∘ U_N。 -/

【TopL_not_compat】
/-- T は引き戻しと両立しない（法 1 → 2 の自明な指標：W(1 mod 2) の |·|² は 1/2、W(1 mod 1) = 1）。 -/

【UA1_ne_TopL_prime】
/-- 素数 p では、自明な指標は V_imprim に入り、U(1) = 1 だが T(1) = W(1)·1（|W(1)|² = 1/p）なので U ≠ T。 -/

【UA1_mem_Vprim】
/-- V_prim は U_N で不変。 -/

【UA1_mem_Vimprim】
/-- V_imprim は U_N で不変。 -/

【UA1_comp_TopL】
/-- U_N と T は可換（どちらも指標で対角）。 -/

【rootNum_one_prime】
/-- 素数 p の自明な指標の W は −1/√p（実数で負）。法 p の T の極分解のユニタリ因子なら、この指標での固有値は −1
（U_p の固有値は 1）。 -/

【TopL_not_compat_prime】
/-- すべての素数 p で、T は法 1 → p の引き戻しと両立しない（法 1 → 2 の `TopL_not_compat` の一般化）。 -/

【gaussSum_inv】
/-- τ(χ⁻¹) = χ(−1)·conj τ(χ)。 -/

【rootNum_inv】
/-- W(χ⁻¹) = conj W(χ)（すべての指標で）。 -/

【primitiveCharacter_inv_apply】
/-- (χ⁻¹)* と (χ*)⁻¹ は整数での値が等しい（法はどちらも導手）。 -/

【phaseA1_inv】
/-- phaseA1(χ⁻¹) = conj phaseA1(χ)。 -/

【UA1_star】
/-- **実数性**：U_N は複素共役と可換（U_N の核は実数値。KUK = U）。 -/

【pullL_injective】
/-- 引き戻しは単射（(ℤ/M)ˣ → (ℤ/N)ˣ は全射）。 -/

【sum_units_unitsMap】
/-- 引き戻しの和：φ(N)·Σ_{u ∈ (ℤ/M)ˣ} F(πu) = φ(M)·Σ_{v ∈ (ℤ/N)ˣ} F(v)。 -/

【ip_pullL】
/-- 正規化した内積の両立：φ(N)·⟨πf, πg⟩ = φ(M)·⟨f, g⟩。 -/

【UA1_bijective】
/-- U_N は全単射（ip を保ち、⟨f, f⟩ = 0 なら f = 0、有限次元）。 -/

【Lvl】
/-- 法の集合：正の整数を、割り算の順で並べたもの。 -/

【Gsp】
/-- 法 a の単数の上の関数の空間。 -/

【pullSys】
/-- 系の写像：a ∣ b なら引き戻し π_{a→b}。 -/

【UA1_family_unique】
/-- **両立する族の一意性**（独立照合 A の指摘で追加）：各法で原始部分の上では T と一致し、引き戻しと両立する
作用素の族は U_N だけ。原始的でない指標の上の位相は、両立から決まる（仮定に A1 の位相は原始部分にしか入らない）。 -/

【Lim】
/-- 帰納極限 lim_N (単数の上の関数)。 -/

【ofL】
/-- 法 a の成分から極限への写像。 -/

【ofL_injective】
/-- 極限への写像は単射。 -/

【Uinf】
/-- 極限の作用素 U_∞：各法の U_N が引き戻しと両立することから。 -/

【Uinf_ofL】
/-- U_∞ は各法で U_N。 -/

【Uinf_unique】
/-- U_∞ は各法で U_N となる線形写像として一意。 -/

【Uinf_bijective】
/-- U_∞ は全単射。 -/

【Uinf_ofL_of_mem_Vprim】
/-- 原始部分の像の上では U_∞ = T_q。 -/

【ofL_charU】
/-- 導手の法の成分：法 a の指標 χ の像は、導手 q の成分の χ* の像。 -/

【span_ofL_Vprim】
/-- 各法の原始部分の像は極限を張る。 -/

【Uinf_unique_TopL】
/-- U_∞ は「各導手 q の原始部分の像の上で T_q」となる線形写像として一意。 -/

【ipn】
/-- 法 a の正規化した内積 ⟨f, g⟩/φ(a)。 -/

【ipn_pullSys】
/-- 正規化した内積は引き戻しで変わらない。 -/

【ipn_eq_of_ofL_eq】
/-- 代表の取り方によらない：極限で同じ元を表す組では、正規化した内積は等しい。 -/

【ipLim】
/-- 極限の上の内積：共通の法の代表で ⟨f, g⟩/φ(a)。 -/

【ipLim_Uinf】
/-- U_∞ は極限の内積を保つ。 -/

【ipLim_add_right】
/-- 極限の内積の右側の加法性。 -/

【ipLim_smul_right】
/-- 極限の内積の右側のスカラー倍。 -/

【ipLim_conj】
/-- 極限の内積のエルミート性：⟨w, z⟩ = conj ⟨z, w⟩。 -/

【eq_zero_of_ipLim_self】
/-- 極限の内積の正定値性：⟨z, z⟩ = 0 なら z = 0。 -/

【ipLim_self_nonneg】
/-- 極限の内積で ⟨z, z⟩ は 0 以上の実数（`eq_zero_of_ipLim_self` と合わせて正定値）。 -/

【UA1_pullL_of_mem_Vprim】
/-- 新しい部分の上の U_N：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)。 -/

【condPart】
/-- 導手が q の指標が張る部分（法 N）。 -/

【condPart_eq_map】
/-- 導手が q の指標が張る部分は π_{q→M}(V_prim(q))（q ∣ M）。 -/

【ip_condPart】
/-- 導手の違う部分は直交する。 -/

【iSup_condPart】
/-- 導手ごとの部分は全体を張る。 -/

【ipR】
/-- 内積の右側を線形写像として（補題）。 -/

【iSupIndep_condPart】
/-- 導手ごとの部分は独立（直和）。 -/

【UA1_mem_condPart】
/-- U_N は導手ごとの部分を保つ。 -/

【ipLim_ofL_Vprim】
/-- 極限で、導手の違う原始部分の像は直交する。 -/
```

## 入力 (4)：ノートの全文（原文のまま、行番号つき）
前回の照合の時点の版から変わった行（または足した行）の範囲：1〜3、7、10〜21、25〜31、34〜35、41、61〜62、65〜67、74〜81、99〜102、105、108、114、117〜118、121、125、144〜147、152〜153、157〜160、164、184、189、193、204〜215
```
   1| # アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 単数の上の関数は導手ごとの新しい部分 π(V_prim(q)) の直交直和で、U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）
   2| 
   3| 2026-11-13。PAG258.lean（57 項目、定義 9 個・abbrev 3 個・構造体 1 個・instance 6 個）、step277.py（21 項目）。
   4| 
   5| - **問いの出所。** 著者の指示「Part 252, Part 254 を解決してください」（2026-11-13 06:43）を、「Part 254 で Part 252 の残る問い 2 つを解く」と読みました（作業の初めに著者へ伝えた読み）。
   6|   - Part 252 のノート §4 の残る問い：(1) 法 N の境界ユニタリ全体（原始的でない指標を含む）を、J∘H_q（q ∣ N）の新しい部分の直和として書く文。(2) 法を動かした組み立て（L²(Ẑ^×) の上の 1 つの作用素）。
   7|   - 解けた範囲：(1) は Lean の文になりました。(2) は代数的な帰納極限の上までです。完備化 L²(Ẑ^×) と、Ẑ^× の上の局所定数関数との同一視は Lean の外です（下の「解決の範囲」）。
   8|   - 着手前の 4 点・対照群・盲検の問いテストは、Part 253 の着手前の文書 `pag2_part253_preregistration.md` の候補 K2 と、盲検の文 T2（既知の結果の短い帰結）・T3（標準的な演習。注意：Ẑ に移るのは引き戻しと両立する作用素だけ）で済んでいます。
   9| - **問い（幾何の言葉で。解釈）。** 重なりの読みは「ねじれた貼り合わせ（U）」です（著者の決定、2026-11-12 17:14）。法 N の貼り合わせ U_N に、A1 の位相をすべての指標に入れます（原始的でない指標には、誘導元の原始指標の位相）。(1) U_N は、各導手 q の原始部分の貼り合わせ T_q を組み合わせたものか。(2) 法を上げたとき、U_N はまとまって 1 つの作用素になるか。
  10| - **記号。** Part 253 の記号を使います：単数の上の関数、内積 ⟨f, g⟩ = Σ_u conj(f(u))·g(u)（`ip`）、T = Part 253 の `TopL`。T は J∘H_N/√N を単数に圧縮し、反転 u ↦ u⁻¹ と合成した作用素です（離散 Hartley 変換を単数に制限しただけのものではありません。独立照合 A の注意）。χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）です。W(χ) は Part 252 の `rootNum`（原始指標ならルート数。原始的でない指標ではルート数ではなく、0 や絶対値 1 未満になる）です。
  11|   - 位相 `phaseA1 χ` = W(χ*)。法 N の境界ユニタリ `UA1` = Σ_χ phaseA1(χ)·P_χ（P_χ f = (⟨χ, f⟩/φ(N))·χ）。引き戻し `pullL`（N ∣ M）：f ↦ f ∘ ((ℤ/M)ˣ → (ℤ/N)ˣ)。
  12| - **結論（Lean）。**
  13|   - **残る問い (1)（直和の文）。**
  14|     - 直和：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q)) に等しい（`condPart_eq_map`、q ∣ M）。導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、独立です（`iSupIndep_condPart`）。つまり単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和です（独立照合 B の指摘で追加）。
  15|     - その上の U：U_M は各部分を保ち（`UA1_mem_condPart`）、g ∈ V_prim(q) なら U_M(π g) = π(T_q g) です（`UA1_pullL_of_mem_Vprim`）。
  16|     - 指標ごとの式：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（`UA1_charU_eq_pull_TopL`）。これは位相の定義の言い換えです。この式を満たす線形写像は U_N だけです（`UA1_unique`。基底の上の値による一意性）。
  17|   - **残る問い (2)（組み立て）。**
  18|     - 有限レベル：U_N は法を上げる引き戻しと両立します：N ∣ M なら U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。T は法 1 → 2 と、すべての素数 p で法 1 → p で両立しません（`TopL_not_compat`・`TopL_not_compat_prime`）。一般の N < M でも両立しないはずですが（原始的でない指標のガウス和の式による）、Lean の外です［既知、確信度：中］。
  19|     - **族の一意性**（このパートの実質的な内容）：法の集合（正の整数を割り算の順で並べた型 `Lvl`）の各法で、原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけです（`UA1_family_unique`）。原始的でない指標の上の位相は仮定に入らず、両立から一通りに決まります（独立照合 A の指摘で追加）。
  20|     - 極限：引き戻しの帰納系の代数的な帰納極限 `Lim`（Mathlib の `Module.DirectLimit`）を作りました。極限への写像は単射です（`ofL_injective`）。U_N の族は極限の上の 1 つの作用素 U_∞ を与えます（`Uinf`、各法の像の上で U_N：`Uinf_ofL`）。U_∞ はこの性質で一意（`Uinf_unique`）で、全単射です（`Uinf_bijective`）。各法の原始部分の像は極限を張り（`span_ofL_Vprim`）、導手の違う像は直交し（`ipLim_ofL_Vprim`。極限での独立性は文にしていない）、U_∞ はその上で T_q です（`Uinf_ofL_of_mem_Vprim`）。U_∞ は「各導手の原始部分の像の上で T_q」という性質でも一意です（`Uinf_unique_TopL`）。
  21|     - 極限の上の内積：引き戻しの和 φ(N)·Σ_u F(πu) = φ(M)·Σ_v F(v)（`sum_units_unitsMap`）から、正規化した内積 ⟨f, g⟩/φ(N) は引き戻しで変わりません（`ip_pullL`・`ipn_pullSys`）。代表の取り方によらない（`ipn_eq_of_ofL_eq`）ので、極限の上の内積 `ipLim` が決まります。右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、⟨z, z⟩ は 0 以上の実数（`ipLim_self_nonneg`）、非退化（`eq_zero_of_ipLim_self`）です（Mathlib の内積の構造にはしていません）。U_∞ はこれを保ちます（`ipLim_Uinf`）。
  22|   - そのほか：
  23|     - 位相：原始指標では phaseA1 χ = W(χ)（`phaseA1_of_isPrimitive`）。|phaseA1 χ|² = 1（`normSq_phaseA1`）。法を上げても変わらない（`phaseA1_changeLevel`）。自明な指標では 1（`phaseA1_one`）。法の型が違う指標の間の受け渡しは `rootNum_congr`（法が等しく、整数での値が等しい指標は同じ W を持つ）で行いました。
  24|     - U_N：すべての指標で U_N χ = phaseA1(χ)·χ（`UA1_charU`）。単数の上の関数の空間全体で ⟨·,·⟩ を保ち（`ip_UA1`）、全単射（`UA1_bijective`）。原始部分では U_N = T（`UA1_eq_TopL_of_mem_Vprim`）。V_prim・V_imprim を保ち（`UA1_mem_Vprim`・`UA1_mem_Vimprim`）、T と可換（`UA1_comp_TopL`）。
  25|     - 原始的でない部分では U ≠ T：素数 p の自明な指標は V_imprim に入り、U_p(1) ≠ T(1) です（`UA1_ne_TopL_prime`。値 U(1) = 1 は `phaseA1_one`・`UA1_charU`、T(1) = W(1)·1 と |W(1)|² = 1/p は Part 253 の `TopL_charU`・`normSq_rootNum_one_prime`）。N ≥ 2 一般でも成り立ちます（T(1) = μ(N)/√N·1）が、Lean の外です。N = 1 では V_imprim = 0 です。
  26|     - 極分解：W(1 mod p) = −1/√p（`rootNum_one_prime`）。素数の法 p では、T の極分解のユニタリ因子のこの指標での固有値は −1 なので、U_p（固有値 1）はそのユニタリ因子ではありません（独立照合 A の指摘。極分解そのものは Lean にしていない）。**法によっては一致します**：法 1・6 では U_N は T_N の極分解のユニタリ因子そのものです（独立照合 B の反例。T_6 = diag(1/√6, 1/√2)）。T_N が可逆な N ≤ 60 のうち、一致するのは N = 1・6 だけでした（数値 (20)）。
  27|     - 実数性：τ(χ⁻¹) = χ(−1)·conj τ(χ)（`gaussSum_inv`）、W(χ⁻¹) = conj W(χ)（`rootNum_inv`、原始的でなくてもよい）、phaseA1(χ⁻¹) = conj phaseA1(χ)（`phaseA1_inv`）から、U_N は複素共役と可換です（`UA1_star`：U_N の核は実数値。定理 2.6 の条件 KUK = U。独立照合 C の「証明できる」を受けて追加）。
  28|   - sorry 0、警告 0。`#print axioms` 57 行はすべて [propext, Classical.choice, Quot.sound]。
  29| - **「解決」の範囲（正直な評価）。**
  30|   - 残る問い (1)：直和の文を Lean で示しました（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` と `UA1_pullL_of_mem_Vprim`）。ただし中身は、指標を導手で分けることと、各レベルでの Part 253 の結果の組み合わせです。U_N の明示の核（導手とメビウスの式）は数値だけです（step277 の (8)、60/60）。
  31|   - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。実質的な内容は族の一意性（`UA1_family_unique`）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。
  32|     - 帰納極限 `Lim` を Ẑ^× = lim (ℤ/N)^× の上の局所定数関数の空間と同一視すること。
  33|     - `ipLim` による完備化（L²(Ẑ^×)）と、その上へのユニタリの延長（内積を保つ全単射は完備化の上のユニタリに一意に延びる）。
  34| - **A1 との関係（第 2 の型の注意）。** U_N は A1 の位相を定義として入れた作用素です。指標ごとの式と両立は、位相を誘導元の原始指標から取るという選び方と、Mathlib の導手の性質（導手と誘導元は法を上げても変わらない）から出ます。族の一意性（`UA1_family_unique`）は、この選び方が「原始部分で A1（T と一致）＋法の間の両立」から一通りに決まることを言います。原始部分の A1 は仮定のままで、A1 は公準のままです。導いていません（CLAUDE.md §2・§6）。
  35| - **位置づけ。** 既知の枠組みの書き直しです（再導出、確信度：高）。独立照合 C の名前：U_∞ は Ẑ^× の上の、原始指標のルート数 W(χ*) を記号とするフーリエ乗数（Ẑ^× の双対群は原始ディリクレ指標の全体）。導手による分解は新形式・旧形式分解の GL(1) 版、引き戻しは inflation です（§5 と辞書 §14）。新規候補はありません。
  36| 
  37| ## 0. 内容
  38| 
  39| ### 0.0 ハンドシェイク（CLAUDE.md §0）
  40| 
  41| - (a) 形式化済み：Part 253（PAG257）の作用素 T、内積 `ip`、V_prim・V_imprim、`TopL_charU`・`TopL_eq_of_A1`・`span_charU_eq_top`・`ip_charU`・`ip_sum_sum`・`charU_one_mem_Vimprim`・`normSq_rootNum_one_prime`・`gaussSum_one_prime`・`eq_zero_of_ip_self`。Part 252（PAG256）の `rootNum`・`rootNum_eq`・`parFac_of_even`・`normSq_rootNum`・`removal_counterexample_normSq`。
  42| - (b) 著者の解釈の層：重なりはねじれた貼り合わせ（U）。A1 は解釈の層の公準（内容は Tate の定理）。解像度のパラメータは未決定（N・K・Λ と同一視しない）。
  43| - (c) 未完の大域の問い：Ẑ の上の定理 A、無限素点を含む大域対象、解像度と有効な姿（§1 の命題 3）の定式化、有限レベルの Bost–Connes。
  44| 
  45| ### 0.1 4 点（Part 253 の着手前の文書の K2 から）
  46| 
  47| 1. 幾何の言葉：上の「問い」。
  48| 2. 既存分野の言葉への最善の翻訳：導手による指標の分解（法 N の指標 ↔ N の約数 q と法 q の原始指標）と、各レベルでの Part 253 の結果。両立する族は帰納系の自己射で、帰納極限の上の作用素を与える。
  49| 3. 残余：計算だけ（明示の核）と、標準的な極限の構成。
  50| 4. 対照群テスト：関数体でも同じ形になるはず（導手の分解は同じで、核のうち無限素点の部分だけが違う）［推論］。一般化素数では指標がなく、文が定義できない。
  51| 
  52| ### 0.2 定義（PAG258.lean）
  53| 
  54| | 記号 | Lean | 内容 |
  55| |---|---|---|
  56| | 導手 ≠ 0 | `conductor_neZero`（instance） | χ* の法に `NeZero` を与える |
  57| | phaseA1(χ) | `phaseA1` | W(χ*)（誘導元の原始指標のルート数の式） |
  58| | U_N | `UA1` | Σ_χ phaseA1(χ)·P_χ |
  59| | π_{N→M} | `pullL` | 単数の上の関数の引き戻し |
  60| | 法の集合 | `Lvl`（構造体）と instance（Preorder：a ≤ b ⇔ a ∣ b、有向、空でない、NeZero） | 正の整数を割り算の順で並べたもの |
  61| | 系 | `Gsp`（abbrev）・`pullSys`、instance `DirectedSystem` | 法 a の単数の上の関数の空間と、引き戻し |
  62| | 帰納極限 | `Lim`・`ofL`（abbrev） | `Module.DirectLimit` と、法 a からの写像 |
  63| | U_∞ | `Uinf` | `Module.DirectLimit.map` で U_N の族から作る |
  64| | 正規化した内積 | `ipn` | ⟨f, g⟩/φ(a) |
  65| | 極限の内積 | `ipLim` | 共通の法の代表を選んで `ipn`（選び方によらない：`ipLim_ofL`） |
  66| | 導手ごとの部分 | `condPart M q` | 法 M の、導手が q の指標が張る部分 |
  67| | 補助 | `ipR f` | g ↦ ⟨f, g⟩ を線形写像にしたもの |
  68| 
  69| ### 0.3 ラベル（CLAUDE.md §7）
  70| 
  71| | 結果 | ラベル | 根拠 |
  72| |---|---|---|
  73| | 位相の性質（原始的なら W、絶対値 1、法を上げても不変、自明な指標で 1、逆で共役） | 既知 | 誘導元の原始指標の定義と Mathlib の導手の性質、τ(χ̄) = χ(−1)·conj τ(χ) |
  74| | U_N χ = phaseA1(χ)χ、U_N はユニタリ（`ip` に関して）・全単射、原始部分で U_N = T | 再導出 | 直交性、\|W(χ*)\| = 1、Part 253 |
  75| | T との可換、V_prim・V_imprim の不変、実数性 | 既知 | 同じ指標の基底で対角、ε(χ̄) = conj ε(χ) |
  76| | 指標ごとの式 U_N χ = π(T_q χ*) | 再導出 | 位相の定義と Part 253 の `TopL_charU` |
  77| | 指標ごとの式による一意性 | 既知（線形代数） | 基底の上の値 |
  78| | 有限レベルの直和（導手ごとの部分 = π(V_prim(q))、直交、全体、独立）と、その上で U = π∘T_q | 再導出 | 指標の導手による分割、直交性 |
  79| | 引き戻しとの両立（T は両立しない）と、両立する族の一意性 | 再導出 | 位相が誘導元から決まること |
  80| | 帰納極限の上の U_∞ と内積、原始部分の像の直交 | 既知 | 帰納極限の普遍性、ファイバーの元の数が一定 |
  81| | 原始的でない部分で U ≠ T（素数の法） | 既知 | 主指標のガウス和 −1（ラマヌジャン和 c_p(1) = μ(p)） |
  82| 
  83| - 新規候補：なし。CLAUDE.md §3 の 2 候補にも当たりません。
  84| 
  85| ## 1. 検証表
  86| 
  87| | 主張 | Lean | 数値（step277） | 新規性 |
  88| |---|---|---|---|
  89| | 法が等しく整数での値が等しい指標は同じ W | `rootNum_congr` | — | 既知 |
  90| | 原始指標では phaseA1 χ = W(χ) | `phaseA1_of_isPrimitive` | (3) | 既知 |
  91| | \|phaseA1 χ\|² = 1 | `normSq_phaseA1` | (2) | 既知 |
  92| | 法を上げても位相は変わらない | `phaseA1_changeLevel` | (4)（201/201） | 既知 |
  93| | 法 1 の自明な指標の W は 1、自明な指標の位相は 1 | `rootNum_one_of_eq_one`・`phaseA1_one` | (7) | 既知 |
  94| | 内積の右側の線形性 | `ip_add_right`・`ip_smul_right` | — | 既知 |
  95| | U_N χ = phaseA1(χ)·χ | `UA1_charU` | (1) | 再導出 |
  96| | U_N は ⟨·,·⟩ を保つ、全単射 | `ip_UA1`・`UA1_bijective` | (2)（60/60） | 再導出 |
  97| | 原始部分で U_N = T | `UA1_eq_TopL_of_mem_Vprim` | (3)（60/60） | 再導出 |
  98| | 指標の引き戻しは法を上げた指標 | `pullL_charU` | — | 既知 |
  99| | 指標ごとの式 U_N χ = π_{q→N}(T_q χ*) | `UA1_charU_eq_pull_TopL` | (1)（60/60） | 再導出 |
 100| | 指標ごとの式を満たす線形写像は U_N だけ | `UA1_unique` | — | 既知（線形代数） |
 101| | 有限レベルの直和：導手ごとの部分 = π(V_prim(q))、直交、全体を張る、独立 | `condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` | (21)（60/60） | 再導出 |
 102| | U は導手ごとの部分を保ち、その上で π∘T_q | `UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim` | (1) | 再導出 |
 103| | 引き戻しとの両立 U_M π = π U_N | `UA1_comp_pullL` | (5)（201/201） | 再導出 |
 104| | T は引き戻しと両立しない（法 1 → 2、法 1 → p） | `TopL_not_compat`・`TopL_not_compat_prime` | (5)（T が両立する組 0/201）、(12) | 既知 |
 105| | 素数 p で、V_imprim の自明な指標の上で U_p ≠ T | `UA1_ne_TopL_prime` | (6)（素数 25 個） | 既知 |
 106| | U_N は V_prim・V_imprim を保ち、T と可換 | `UA1_mem_Vprim`・`UA1_mem_Vimprim`・`UA1_comp_TopL` | (11) | 既知 |
 107| | W(1 mod p) = −1/√p | `rootNum_one_prime` | (12) | 既知 |
 108| | U_N が T_N の極分解のユニタリ因子に等しい法（T_N 可逆、N ≤ 60）は N = 1・6 だけ | Lean にしていない | (20) | — |
 109| | τ(χ⁻¹) = χ(−1)conj τ(χ)、W(χ⁻¹) = conj W(χ)、phaseA1 も同じ | `gaussSum_inv`・`rootNum_inv`・`primitiveCharacter_inv_apply`・`phaseA1_inv` | (13)（指標 1,102 個） | 既知 |
 110| | 実数性：U_N は複素共役と可換（核は実数値） | `UA1_star` | (9) | 既知 |
 111| | 引き戻しは単射、引き戻しの和、正規化した内積の両立 | `pullL_injective`・`sum_units_unitsMap`・`ip_pullL` | (10)（191/191） | 既知 |
 112| | 両立する族の一意性 | `UA1_family_unique` | — | 再導出 |
 113| | 極限への写像は単射、U_∞ は各法で U_N、一意、全単射 | `ofL_injective`・`Uinf_ofL`・`Uinf_unique`・`Uinf_bijective` | — | 既知 |
 114| | 原始部分の像は極限を張り、導手の違う像は直交し、U_∞ はその上で T_q、この性質で一意 | `ofL_charU`・`span_ofL_Vprim`・`ipLim_ofL_Vprim`・`Uinf_ofL_of_mem_Vprim`・`Uinf_unique_TopL` | — | 再導出 |
 115| | 極限の内積：正規化、代表によらない、右で線形、エルミート、正定値、U_∞ が保つ | `totient_ne_zero'`・`ipn_pullSys`・`ipn_eq_of_ofL_eq`・`ipLim_ofL`・`ipLim_add_right`・`ipLim_smul_right`・`ipLim_conj`・`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`・`ipLim_Uinf` | — | 既知 |
 116| | U_N の明示の核（導手とメビウスの式） | Lean にしていない | (8)（60/60） | 既知の組み合わせ |
 117| | 独立照合 C の主張：素数の核の式、核の両立と ℓ¹ ノルム、UJ の対合、W の乗法の式、実の原始指標で W = 1、原始的でない指標の W | Lean にしていない | (14)〜(19) | 既知 |
 118| | 一般の N < M での T の非両立、N ≥ 2 一般での U ≠ T | Lean にしていない | (5)・(19) | 既知 |
 119| | Lim ≅ Ẑ^× の上の局所定数関数、完備化 L²(Ẑ^×) とユニタリの延長 | Lean にしていない | — | 既知（標準） |
 120| 
 121| ## 2. 数値照合（step277.py、21 項目すべて合格、約 6 秒）
 122| 
 123| | 項目 | 結果 |
 124| |---|---|
 125| | (1) 指標ごとの式：すべての χ で U_N χ = π_{q→N}(T_q χ*)（左辺はスペクトル和、右辺は法 q の T の核から別々に計算） | 60/60（1 ≤ N ≤ 60）、最大誤差 1.0×10⁻¹³ |
 126| | (2) U_N は ⟨·,·⟩ を保つ | 60/60、最大誤差 9.2×10⁻¹⁵ |
 127| | (3) 原始部分で U_N = T | 60/60、最大誤差 1.0×10⁻¹³ |
 128| | (4) 法を上げても位相は変わらない | 201/201（N·k ≤ 60 の組）、最大誤差 1.4×10⁻¹⁴ |
 129| | (5) 引き戻しとの両立 | U は 201/201（最大誤差 2.2×10⁻¹⁴）。T が両立する組は 0/201 |
 130| | (6) 原始的でない部分で U ≠ T | 素数 25 個（p ≤ 100）で、自明な指標の U(1) = 1、T(1) = −1/√p |
 131| | (7) 自明な指標の位相は 1、W(1 mod 1) = 1 | 1 ≤ N ≤ 60 |
 132| | (8) 核の式 U_N(u, v) = (1/φ(N)) Σ_{f∣N} f^{−1/2} Σ_{x∈G_f} cas(2πxū⁻¹/f) Σ_{d∣f, x≡v̄ (mod d)} μ(f/d)φ(d) | 60/60、最大誤差 1.4×10⁻¹⁴（Lean にしていない） |
 133| | (9) 核は実数値 | 虚部の最大 7.8×10⁻¹⁵（独立照合の後に Lean にした：`UA1_star`） |
 134| | (10) ⟨πf, πg⟩ = (φ(M)/φ(N))⟨f, g⟩ | 191/191（独立照合の後に Lean にした：`ip_pullL`） |
 135| | (11) U_N と T は可換 | 1 ≤ N ≤ 60、最大誤差 1.1×10⁻¹⁴ |
 136| | (12) W(1 mod p) = −1/√p、T は法 1 → p で両立しない | 素数 25 個（p ≤ 100）、W の最大誤差 9.0×10⁻¹⁶ |
 137| | (13) W(χ⁻¹) = conj W(χ)、phaseA1(χ⁻¹) = conj phaseA1(χ) | 指標 1,102 個（1 ≤ N ≤ 60）、最大誤差 5.0×10⁻¹⁴ |
 138| | (14) 素数 p の核 k_p(w) = p^{−1/2}cas(2πw⁻¹/p) + (1 + p^{−1/2})/(p − 1)（U_p(u, v) = k_p(u/v)。C の主張） | 素数 25 個、最大誤差 4.9×10⁻¹⁵ |
 139| | (15) 核は u/v だけの関数で、法を上げるとファイバーの和で両立する。ℓ¹ ノルムは N ∣ M で増える（C の主張：有限加法的な分布で、測度ではない） | 両立 201 組、最大誤差 1.1×10⁻¹⁴。素数 p ≤ 60 で ℓ¹/√p は 0.577〜0.886、N ≤ 60 の最大 6.80（N = 59） |
 140| | (16) J（u ↦ u⁻¹）について JUJ = U*、(UJ)² = I、UJ は自己共役（C の主張） | 1 ≤ N ≤ 60、最大誤差 2.4×10⁻¹⁴ |
 141| | (17) 導手が互いに素な原始指標で W(χ₁χ₂) = (−1)^{a₁a₂}χ₁(q₂)χ₂(q₁)W(χ₁)W(χ₂)（C の主張：素数ごとの積には分かれない） | 178 組（q₁q₂ ≤ 60）、最大誤差 1.7×10⁻¹⁴。W(χ₁χ₂) ≠ W(χ₁)W(χ₂) の組 144 個 |
 142| | (18) 実の原始指標では W = 1（C の主張） | 40 個、最大誤差 1.5×10⁻¹⁴ |
 143| | (19) 原始的でない指標で W(χ) = μ(N/q)χ*(N/q)√(q/N)·W(χ*)、\|W(χ)\| ∈ {0, √(q/N)}（C の主張） | 440 個、最大誤差 1.5×10⁻¹⁴ |
 144| | (20) U_N が T_N の極分解のユニタリ因子に等しい法（B の反例の確認） | T_N が可逆な 37 個のうち、等しいのは N = 1・6 だけ。素数を含む 35 個で等しくない。T_N が可逆でない法（極分解が一意でない）は 23 個 |
 145| | (21) 有限レベルの直和：導手 q の指標が張る部分 = π_{q→N}(V_prim(q))、直交、全体を張る | 60/60、直交の最大誤差 3.4×10⁻¹³ |
 146| 
 147| - 数値の確認は証明ではありません。(11)〜(19) は独立照合 A・C の後、(20)・(21) は B の後に足しました（前の版の記録は `audit254/step277_v1.*`・`step277_v2_before_B.*`）。
 148| 
 149| ## 3. Lean（PAG258.lean）
 150| 
 151| - import：PAG257 と Mathlib.Algebra.Colimit.Module（ビルド済みのモジュール。Mathlib の追加ビルドなし）。
 152| - 主に使った Mathlib の補題：`DirichletCharacter.primitiveCharacter`・`primitiveCharacter_apply_of_isCoprime`・`apply_eq_zero_iff`・`primitiveCharacter_isPrimitive`・`conductor_changeLevel`・`primitiveCharacter_changeLevel_apply`・`primitiveCharacter_one`・`conductor_one`・`conductor_inv`・`changeLevel_primitiveCharacter`・`changeLevel_injective`・`changeLevel_trans`・`changeLevel_eq_cast_of_dvd'`・`star_gaussSum_eq`・`AddChar.inv_mulShift`・`gaussSum_mulShift_eq`・`MulChar.star_apply'`・`ZMod.unitsMap_surjective`・`ZMod.unitsMap_self`・`ZMod.unitsMap_comp`・`MonoidHom.card_fiber_eq_of_mem_range`・`Finset.sum_fiberwise`・`Module.DirectLimit`（`of`・`of_f`・`map`・`map_apply_of`・`hom_ext`・`exists_of`・`exists_of₂`・`exists_eq_of_of_eq`）・`iSupIndep_def`・`Submodule.disjoint_def`・`LinearMap.ext_on_range`・`LinearMap.ext_on`・`LinearMap.injective_iff_surjective`。
 153| - 法の型の違い：χ* の法は `χ.conductor` で、N とは命題としてしか等しくありません。`rootNum_congr`（法を変数にして `subst` し、整数での値から指標の等式を出す）で受け渡しました。(χ⁻¹)* と (χ*)⁻¹ も同じ方法です（`conductor_inv`）。`condPart_eq_map` でも、法の等式を変数にして `subst` しました。
 154| - 極限の内積 `ipLim` は、`exists_of₂` で選んだ共通の法の代表で定義しました（選択公理）。`ipLim_ofL` で、どの代表でも値が同じことを示しています。
 155| - コンパイルの経過：
 156|   - 最初の版（17 項目）：試しのファイルの 2 回目で通過（1 回目は約 3 分 34 秒、2 回目以降は数秒）。1 回目のエラー：法 1 のガウス和の計算で `stdAddChar default = 1` の `default` に `show` の形が合わなかった（すべての x : ZMod 1 で stdAddChar x = 1 を示してから使った）。警告：`pullL` の証明の使わない変数名、`pullL_charU` で使わない section の instance（`omit [NeZero N] in`）。
 157|   - 独立照合 A・C の後の 33 項目：試しのファイル（PAG258 を import）の 5 回目で通過（各回 3〜7 秒）。エラーの内訳：`card_eq_sum_card_fiberwise` を逆向きに書き換えた、`DirectedSystem` の `map_map` で `← unitsMap_comp` が引数なしでは別の場所に当たった（引数を明示）、和集合の元の添字が推論されなかった（明示）、`simpa` の後の形が `mem_iUnion₂` と合わなかった（`simp only` に変更）、`eq_zero_of_ip_self` の引数の数、`UA1_comp_TopL` で 1 回目の書き換えが両辺に当たった、`rw` で閉じたゴールの後の `simp`・`ring`、`parFac` を展開する前に `χ⁻¹ (-1)` を書き換えようとした。
 158|   - 独立照合 B の後の 7 項目：試しのファイルの 1 回目で通過。
 159|   - pagpkg での本番のコンパイルはエラー・警告なし。
 160| - 件数：theorem/lemma 57、定義 9（`phaseA1`・`UA1`・`pullL`・`pullSys`・`Uinf`・`ipn`・`ipLim`・`condPart`・`ipR`）、abbrev 3（`Gsp`・`Lim`・`ofL`）、構造体 1（`Lvl`）、instance 6、`#print axioms` 57 行。通算で theorem/lemma 3,457、`#print axioms` 3,758、xlsx 3,484 項目（行 3429〜3485）、検証手順 274。
 161| 
 162| ## 4. 残る問い（本来の道）
 163| 
 164| - Part 252 の残る問いは、上の範囲で文になりました。残るのは、Lim と Ẑ^× の上の局所定数関数の同一視、完備化 L²(Ẑ^×) の上のユニタリ、極限での独立性、一般の N < M での T の非両立、核の明示の式で、どれも計算の細部か標準の構成です。主役にしません。
 165| - 解像度のパラメータは未決定のままです（CLAUDE.md §1 の禁止との緊張は記録済み）。
 166| 
 167| ## 5. 文献の確認の記録（検索ログ）
 168| 
 169| - 着手前の盲検の問いテスト（`prereg253/`）の T2：既知の結果の短い帰結。原始指標の和のメビウスの式は Ma–Niu（arXiv:1912.13153）の Lemma 4（盲検が取得）。核の式そのものの文献は見つからなかった。T3：標準的な演習（引き戻しと両立するものだけが Ẑ に移る、という注意つき）。
 170| - 独立照合 C が挙げた文献（2026-11-13 にウェブで実在を確認）：
 171|   - Iwaniec–Kowalski, Analytic Number Theory（AMS Colloquium Publ. 53, 2004）の Theorem 4.15（ディリクレ L 関数の関数等式、p. 84）。Davenport, Multiplicative Number Theory の第 9 章（関数等式）・第 5 章（原始指標）。
 172|   - Atkin–Lehner, Hecke operators on Γ₀(m), Math. Ann. 185 (1970) 134–160。W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285–315。
 173|   - Tate, Number theoretic background, Proc. Sympos. Pure Math. 33, Part 2 (1979) 3–26。Deligne, Les constantes des équations fonctionnelles des fonctions L, LNM 349 (1973) 501–597。
 174|   - Hartley, A more symmetrical Fourier analysis applied to transmission problems, Proc. IRE 30 (1942) 144–150。
 175| - U_∞ そのもの（ルート数を記号とする Ẑ^× の上のフーリエ乗数）に名前を付けた文献は、C も知らないと答えた。
 176| - MathSciNet・zbMATH：未実施（このコンテナからは使えない）。見つからなかったことは、存在しないことの証明ではありません。
 177| 
 178| ## 6. 収束アラームの状況（CLAUDE.md §7、Part 254 の後）
 179| 
 180| - 辞書の未記入の件数：0（Part 254 の名前は辞書 §14 に足した）。
 181| - 文献照合の未実施の連続パート数：0（着手前の盲検の問いテスト T2・T3、独立照合 C の文献のウェブでの確認）。
 182| - **兆候 4（初等的な部品の組み合わせだけ）：6 パート連続**（Part 249〜254）。Part 254 は、著者の指示で Part 252 の残る問いを閉じたものです。
 183| - **第 2 の型（注入→回収）**：U_N は A1 の位相を定義として入れた作用素です。`UA1_family_unique` で、原始的でない指標の位相は両立から決まることを示しましたが、原始部分の A1 は仮定のままです。
 184| - **第 11 の型（形式文のずれ）**：B の判定で、xlsx の主張 50 文はすべて形式文と同じか弱い（強いものはなし）。ずれはノートの側で 5 か所。そのうち 1 つは数学として誤りでした（下の §7、極分解）。
 185| - 兆候 1〜3：出ていません。
 186| 
 187| ## 7. 検知記録：独立照合（2026-11-13）
 188| 
 189| - 手順：構築者の予想を先に書いた（`audit254/expected_before_results.md`、B の前に追補 `expected_before_results_B_v2.md`）。入力は中立化した（`rename.json`・`rename_v2.json`。Φ・Ψ・Θ・Ξ・S の名前）。A（逆翻訳）と C（盲検の名前づけ）を、ツールなしの新しいエージェントで同時に立て、A の後に B（照合）を立てた。3 つともツール使用 0 回（通知の usage で確認）。出力はそのまま `agent_A_output.md`・`agent_C_output.md`・`agent_B_output.md`。
 190| - **A（S1〜S17）**：S1・S2・S3・S6・S7・S8・S11・S12・S14 は自明、S9・S13 はほぼ同語反復、S5・S16 は端の場合だけ、S17 は条件つきで弱い、S4 は軽い実質、S10・S15 は実質的だが標準（S15 の中身は S4）。全体：固有値の絶対値 1 と法を上げても不変なことは Θ1 の定義に組み込まれている。予想どおりだった点：S1・S2・S9・S11・S13・S14・S15 の評価、証人が法 1 → 2・素数だけ、核の式などが文にないこと。
 191|   - 予想していなかった指摘と対応：
 192|     - 「各レベルで原始部分の上で Ψ3 と一致し、引き戻しと可換な族は Θ2 しかない」が書かれていない。一意性に本質的なのはレベル間の両立。→ `UA1_family_unique` を足した。
 193|     - Θ2 は Ψ3 の極分解のユニタリ因子でもない。→ `rootNum_one_prime` を足し、本文に書いた。**この一般の文は誤りだった**（B が法 1・6 の反例を出した）。A の主張を確かめずに一般の形で採用したのは構築者の誤り。素数の法に限って直した。
 194|     - Θ2 と Ψ3 は可換で、Ψ6・Ψ7 を保つが、書かれていない。→ `UA1_comp_TopL`・`UA1_mem_Vprim`・`UA1_mem_Vimprim` を足した。
 195|     - S16 は最も退化した組だけ。→ `TopL_not_compat_prime`（すべての素数 p で法 1 → p）を足した。一般の N ∣ M は原始的でない指標のガウス和の式が要るので Lean にしていない。
 196|     - Ψ3 には u⁻¹ が入っていて、「ハートレー変換を単数に制限したもの」と読むのは不正確。→ 本文の記号の段落に書いた。
 197| - **C（P1〜P5）**：Θ1 は原始指標のルート数 ε(χ*)（IK・Davenport。非原始指標に χ* の値を当てるのは通例）、Θ3 は inflation、P3 は新形式・旧形式分解の GL(1) 版（Atkin–Lehner・Li に似る、確信度：中）、P4 は帰納系の自己射、族は Ẑ^× の上のルート数を記号とするフーリエ乗数（正規化したハール測度で、完備化は L²(Ẑ^×)）。Θ2 そのものの名前は知らない。どれも標準的な事実で、新しい定理はない。
 198|   - 予想との比較：Θ1 = ε 因子、Θ3 = inflation、Ẑ^× の上の局所定数関数と L²(Ẑ^×) は予想どおり。Θ2 を「Tate の局所関数等式の作用素」とは呼ばなかった（フーリエ乗数と呼んだ）。Atkin–Lehner は予想（確信度：低）より強く、新形式の理論の類似として挙がった。
 199|   - 予想していなかった指摘と対応：
 200|     - P5（核の実数性）は τ(χ̄) = χ(−1)·conj τ(χ) から証明できる。→ `gaussSum_inv`・`rootNum_inv`・`phaseA1_inv`・`UA1_star` を足した。正規化した内積の両立も、ファイバーの元の数から証明できる。→ `sum_units_unitsMap`・`ip_pullL` を足した。
 201|     - 数え上げの内積では引き戻しは等長でなく、極限は正規化した測度で取る必要がある。→ 極限の内積 `ipLim` を 1/φ(N) で正規化して作った。
 202|     - 核は Ẑ^× の上の有限加法的な分布で、測度ではない（ℓ¹ ノルムが √p 程度で増える）、JΘ2J = Θ2*・Θ2∘J は対合、素数ごとの積には分かれない、実の原始指標で Θ1 = 1、非原始指標で |Φ4| ∈ {0, √(q/N)}。→ 数値で確かめた（step277 の (14)〜(19)、すべて合格）。Lean にはしていない。
 203|   - C が挙げた文献はウェブで実在を確認した（§5）。
 204| - **構築者の判断（A・C の後）**：極限の作用素を Lean で作れると見て、代数的な帰納極限 `Module.DirectLimit` の上に U_∞ と内積を作った（最初の版のノートでは「極限の作用素そのものは Lean で作っていない」と書いていた）。A・C の後に足した 33 項目（S18〜S50）は A が見ていないので、B に手で確かめてもらった。
 205| - **B（S1〜S50 と、ノートの題・結論・解決の範囲・ラベル・検証表）**：
 206|   - xlsx の主張：50 文すべて「一致」で、主張が強い・別物・空虚はなし。注記つきが 7 文（S13 は「直和の文」が名前だけ、S16 は法 1 → 2 だけ、S17 の括弧の値は別の定理から、S21 の極分解は N = p なら正しい、S25 の「導手は逆で変わらない」は独立の文でない、S27 の核の実数性は同値な言い換え、S50 は Inner の構造ではない）。xlsx の該当の主張は、注記に合わせて直した。S18〜S50 は手ですべて真と確認（S32 の仮定で足りる、Ξ7 は選択によらない）。
 207|   - ノートへの指摘（重要な順）と対応：
 208|     1. 極分解の文は一般には偽（法 1・6 で U_N は T_N の極分解のユニタリ因子そのもの）。→ 素数の法に限って直し、反例を本文に書いた。数値 (20) で確認：T_N が可逆な N ≤ 60 では、一致するのは N = 1・6 だけ。
 209|     2. 「直和の文」「(1) を解決」は、指標ごとの式（定義の言い換え）と基底による一意性だけで、直和分解は Lean にない。→ 有限レベルの直和を Lean にした（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim`、極限で `ipLim_ofL_Vprim`）。指標ごとの式は「定義の言い換え」と書き直し、実質的な内容が族の一意性であることを明記した。数値 (21) で確認。
 210|     3. 「T は両立しない」「原始的でない部分で U ≠ T」を一般の形で書いていた。→ Lean の範囲（法 1 → p、素数の法）に合わせ、一般の場合は Lean の外と書いた。N = 1 では V_imprim = 0。
 211|     4. 題と問いの出所から、(2) が代数的な帰納極限までであることが読み取れない。→ 題と問いの出所に書いた。
 212|     5. 二つの表のラベルの食い違い（T との可換・実数性・一意性）と、記号 ε の重なり、定義の個数（abbrev）。→ ラベルをそろえ、ルート数を W(χ*) と書き、個数を直した。
 213|   - B の補足：A の §3(a)「外から入っている事実は R2・R3 と導手の性質だけ」は、R1（S13 が使う）と R4（S11 が使う）が抜けている。A の極分解の一般文も同じ誤り。
 214|   - 予想との比較：「1 つの作用素にまとまる」「全単射」「一意」「内積」は形式文で支えられている、と判定された（予想では題に注文がつくと見ていた：(2) が代数的な帰納極限までと読み取れない、という形で当たった）。`ipLim` の選択による定義が代表によらないことは、B が手で確かめた（予想どおり）。`UA1_family_unique` の仮定に原始部分の A1 が残ることは、B は指摘しなかった（ノートに書いてあったため）。**極分解の文の誤りは予想していなかった。**
 215| - B の後に直した文面と、足した Lean（7 項目）・数値（2 項目）は、照合を受けていません。
 216| 
```

## 入力 (5)：表（xlsx）の見出しと各行（原文のまま。主張と証明の要点。★ は前回の照合の時点の版から足した・変えた行）
```
【見出し】PAG2.0-254 法 N の境界ユニタリ U_N 全体と、法を上げた組み立て（Part 252 の残る問い。著者の指示「Part 252, Part 254 を解決してください」、2026-11-13 06:43。重なりはねじれた貼り合わせ U と決定済み。A1 は位相の規約で、Lean の公理ではない）
rootNum_congr
  主張：法が等しく（d₁ = d₂ は命題としての等式）、すべての整数 a で値が等しい 2 つの指標は、同じ W（Part 252 の rootNum）を持つ。型の違う法の間の受け渡し
  証明の要点：法の等式で subst し、整数での値から指標の等式
phaseA1_of_isPrimitive
  主張：A1 の位相 phaseA1(χ) = W(χ*)（def phaseA1。χ* は χ を誘導する原始指標、法は導手）は、χ が原始的なら W(χ)
  証明の要点：原始的なら導手 = 法で、χ* は χ と整数での値が等しい
normSq_phaseA1
  主張：すべての指標で |phaseA1(χ)|² = 1
  証明の要点：χ* は原始的で、Part 252 の |W|² = 1
phaseA1_changeLevel
  主張：法を上げても位相は変わらない：N ∣ M なら phaseA1(changeLevel χ) = phaseA1(χ)
  証明の要点：導手は法を上げても同じで、誘導元の原始指標は整数での値が等しい
rootNum_one_of_eq_one
  主張：法 1 の自明な指標の W は 1（d = 1 は命題としての等式）
  証明の要点：法 1 のガウス和は 1、偶の指標
phaseA1_one
  主張：自明な指標の位相は 1
  証明の要点：自明な指標の導手は 1、誘導元は法 1 の自明な指標
ip_add_right
  主張：単数の上の内積（Part 253 の ip）の右側の加法性
  証明の要点：項ごと
ip_smul_right
  主張：単数の上の内積の右側のスカラー倍
  証明の要点：項ごと
UA1_charU
  主張：法 N の境界ユニタリ U_N = Σ_χ phaseA1(χ)·P_χ（def UA1、P_χ f = (⟨χ, f⟩/φ(N))·χ）は、すべての指標で U_N χ = phaseA1(χ)·χ
  証明の要点：指標の直交性（Part 253 の ip_charU）
ip_UA1
  主張：U_N は単数の上の関数の空間全体で内積を保つ（ユニタリ）：⟨U_N f, U_N g⟩ = ⟨f, g⟩
  証明の要点：指標が張ることと |phaseA1|² = 1
UA1_eq_TopL_of_mem_Vprim
  主張：原始部分 V_prim の上で U_N = T（Part 253 の TopL）
  証明の要点：原始指標で A1 の位相を満たすので、Part 253 の TopL_eq_of_A1
pullL_charU
  主張：単数の上の関数の引き戻し π_{N→M}（def pullL、N ∣ M、f ↦ f ∘ ((ℤ/M)ˣ → (ℤ/N)ˣ)）は、指標を法を上げた指標に送る
  証明の要点：changeLevel の値の式
★ UA1_charU_eq_pull_TopL
  主張：指標ごとの式（Part 252 の残る問い 1 の文の指標ごとの形。位相の定義の言い換え）：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（q = cond χ）。直和への分解そのものは condPart の行
  証明の要点：Part 253 の T_q χ* = W(χ*)χ*、引き戻しと changeLevel_primitiveCharacter
★ UA1_unique
  主張：指標ごとの式を満たす線形写像は U_N だけ（すべての指標 χ で U χ = π_{q→N}(T_q χ*) なら U = U_N。基底の上の値による一意性）
  証明の要点：張る集合の上で一致する線形写像
UA1_comp_pullL
  主張：引き戻しとの両立（Part 252 の残る問い 2 の有限レベルの部分）：N ∣ M なら U_M ∘ π_{N→M} = π_{N→M} ∘ U_N。極限の作用素は下の Uinf
  証明の要点：指標で確かめる：π χ = changeLevel χ と phaseA1_changeLevel
★ TopL_not_compat
  主張：法 1 → 2 では、Part 253 の T は引き戻しと両立しない：自明な指標で T(π f) ≠ π(T f)（一般の N ∣ M の文ではない。法 1 → p は TopL_not_compat_prime）
  証明の要点：法 1 の自明な指標は原始的で |W|² = 1、|W(1 mod 2)|² = 1/2
★ UA1_ne_TopL_prime
  主張：すべての素数 p で、自明な指標は V_imprim に入り、U_p(1) ≠ T(1)（値 U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p は phaseA1_one・UA1_charU・TopL_charU・normSq_rootNum_one_prime による。N ≥ 2 一般の U_N ≠ T は Lean にしていない）
  証明の要点：Part 253 の charU_one_mem_Vimprim・normSq_rootNum_one_prime と phaseA1_one
UA1_mem_Vprim
  主張：原始部分 V_prim は U_N で不変（独立照合 A の指摘で追加）
  証明の要点：生成元で U_N χ = phaseA1(χ)χ
UA1_mem_Vimprim
  主張：原始的でない部分 V_imprim も U_N で不変（独立照合 A の指摘で追加）
  証明の要点：生成元で U_N χ = phaseA1(χ)χ
UA1_comp_TopL
  主張：U_N と T は可換：U_N(T f) = T(U_N f)（どちらも指標で対角。独立照合 A の指摘で追加）
  証明の要点：指標で確かめる
★ rootNum_one_prime
  主張：素数 p の自明な指標の W は −1/√p（実数で負。U_p の固有値 1 と符号が違う。法 p の T の極分解のユニタリ因子ならこの指標での固有値は −1 なので、U_p はそのユニタリ因子でもない：この読みは Lean にしていない。法 1・6 では一致する（独立照合 B の反例）。独立照合 A の指摘で追加）
  証明の要点：偶なので W = τ/√p、τ = −1
TopL_not_compat_prime
  主張：すべての素数 p で、T は法 1 → p の引き戻しと両立しない（TopL_not_compat の法 1 → 2 を一般の素数に。一般の N ∣ M は Lean にしていない。独立照合 A の指摘で追加）
  証明の要点：|W(1 mod p)|² = 1/p ≠ 1 = |W(1 mod 1)|²
gaussSum_inv
  主張：τ(χ⁻¹) = χ(−1)·conj τ(χ)（すべての指標）
  証明の要点：共役は両方の指標を逆にし、加法的指標の逆は −1 倍のずらし
rootNum_inv
  主張：W(χ⁻¹) = conj W(χ)（すべての指標。原始的でなくてもよい）
  証明の要点：偶奇で場合分けして gaussSum_inv
★ primitiveCharacter_inv_apply
  主張：(χ⁻¹)* と (χ*)⁻¹ は整数での値が等しい（法はどちらも導手。導手が逆で変わらないことは Mathlib の conductor_inv）
  証明の要点：法を上げる写像の単射性。導手と互いに素でない整数では両辺 0
phaseA1_inv
  主張：phaseA1(χ⁻¹) = conj phaseA1(χ)
  証明の要点：rootNum_congr と rootNum_inv
UA1_star
  主張：実数性：U_N は複素共役と可換（U_N(conj ∘ f) = conj ∘ U_N f。U_N の核は実数値で、定理 2.6 の条件 KUK = U。step277 の (9) を Lean に。独立照合 C の「証明できる」を受けて追加）
  証明の要点：指標で展開し、conj χ = χ⁻¹ と phaseA1_inv
pullL_injective
  主張：引き戻し π_{N→M} は単射
  証明の要点：(ℤ/M)ˣ → (ℤ/N)ˣ は全射
sum_units_unitsMap
  主張：引き戻しの和：φ(N)·Σ_{u∈(ℤ/M)ˣ} F(πu) = φ(M)·Σ_{v∈(ℤ/N)ˣ} F(v)
  証明の要点：全射準同型のファイバーの元の数は一定
ip_pullL
  主張：正規化した内積の両立：φ(N)·⟨πf, πg⟩ = φ(M)·⟨f, g⟩（step277 の (10) を Lean に）
  証明の要点：sum_units_unitsMap
UA1_bijective
  主張：U_N は全単射
  証明の要点：内積を保つので単射、有限次元なので全射
UA1_family_unique
  主張：両立する族の一意性：法の集合（正の整数を割り算の順で並べた型 Lvl）の各法で原始部分の上では T と一致し、引き戻しと両立する（U_b ∘ π = π ∘ U_a）作用素の族は、すべての法で U_N に等しい。原始的でない指標の上の位相は仮定に入らず、両立から決まる（独立照合 A の指摘で追加）
  証明の要点：法 a の指標 χ は導手 q の χ* の引き戻しで、χ* ∈ V_prim(q)
ofL_injective
  主張：帰納極限 Lim（引き戻しの帰納系の Module.DirectLimit）への写像は単射
  証明の要点：極限で等しければある法で引き戻すと等しく、引き戻しは単射
Uinf_ofL
  主張：極限の作用素 U_∞（def Uinf。U_N の族が引き戻しと両立することから Module.DirectLimit.map で作る）は、各法の像の上で U_N
  証明の要点：map の定義
Uinf_unique
  主張：各法の像の上で U_N となる極限の線形写像は U_∞ だけ
  証明の要点：極限からの線形写像は各成分で決まる
Uinf_bijective
  主張：U_∞ は全単射
  証明の要点：各元はある法の像、各法で U_N は全単射、極限への写像は単射
Uinf_ofL_of_mem_Vprim
  主張：原始部分 V_prim(q) の像の上では U_∞ = T_q
  証明の要点：Uinf_ofL と UA1_eq_TopL_of_mem_Vprim
ofL_charU
  主張：法 a の指標 χ の極限での像は、導手 q の成分の χ* の像に等しい
  証明の要点：χ は χ* の引き戻し
★ span_ofL_Vprim
  主張：各法 q の原始部分 V_prim(q) の像の和集合は極限を張る（像どうしの直交は ipLim_ofL_Vprim。極限での独立性は文にしていない）
  証明の要点：各元はある法の像で、指標の 1 次結合。指標の像は導手の成分の原始指標の像
Uinf_unique_TopL
  主張：各導手 q の原始部分の像の上で T_q となる極限の線形写像は U_∞ だけ
  証明の要点：張る集合の上で一致する線形写像
totient_ne_zero'
  主張：法 a で φ(a) ≠ 0（補題）
  証明の要点：φ は正
ipn_pullSys
  主張：正規化した内積 ⟨f, g⟩/φ(a)（def ipn）は引き戻しで変わらない
  証明の要点：ip_pullL
ipn_eq_of_ofL_eq
  主張：極限で同じ元を表す組では、正規化した内積は等しい（代表の取り方によらない）
  証明の要点：共通の法へ引き戻して ofL_injective
ipLim_ofL
  主張：極限の内積 ipLim（def：共通の法の代表を選んで ⟨f, g⟩/φ(a)）は、各法の像の上で正規化した内積に等しい
  証明の要点：代表によらない
ipLim_Uinf
  主張：U_∞ は極限の内積を保つ
  証明の要点：共通の法の代表と ip_UA1
ipLim_add_right
  主張：極限の内積の右側の加法性
  証明の要点：3 つの元の共通の法
ipLim_smul_right
  主張：極限の内積の右側のスカラー倍
  証明の要点：共通の法の代表
ipLim_conj
  主張：極限の内積のエルミート性：⟨w, z⟩ = conj⟨z, w⟩
  証明の要点：共通の法で項ごと
eq_zero_of_ipLim_self
  主張：極限の内積の非退化：⟨z, z⟩ = 0 なら z = 0
  証明の要点：代表と eq_zero_of_ip_self
★ ipLim_self_nonneg
  主張：極限の内積で ⟨z, z⟩ は 0 以上の実数。上の 4 つと合わせて ipLim はエルミート内積の性質を持つ（Mathlib の Inner の構造にはしていない。左側の共役線形性は ipLim_conj から出る。完備化 L²(Ẑ^×) は作っていない）
  証明の要点：代表で Σ|f(u)|²/φ(a)
★ UA1_pullL_of_mem_Vprim
  主張：新しい部分の上の U：q ∣ M、g ∈ V_prim(q) なら U_M(π_{q→M} g) = π_{q→M}(T_q g)（独立照合 B の指摘で追加）
  証明の要点：UA1_comp_pullL と UA1_eq_TopL_of_mem_Vprim
★ condPart_eq_map
  主張：導手が q の指標が張る部分（def condPart M q）は π_{q→M}(V_prim(q)) に等しい（q ∣ M。独立照合 B の指摘で追加）
  証明の要点：⊆：導手 q の指標は χ* の引き戻し（法の等式で subst）。⊇：原始指標を法を上げた指標の導手は q
★ ip_condPart
  主張：導手の違う部分は直交する（q ≠ q' なら condPart q と condPart q' の元の内積は 0）
  証明の要点：指標の直交性
★ iSup_condPart
  主張：導手ごとの部分は全体を張る（⨆_q condPart q = ⊤）
  証明の要点：各指標は自分の導手の部分に入る
★ iSupIndep_condPart
  主張：導手ごとの部分は独立（iSupIndep）。iSup_condPart・condPart_eq_map と合わせて、単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和（Part 252 の残る問い 1 の直和の文。独立照合 B の指摘で追加）
  証明の要点：ほかの部分の和の元とは直交するので、共通部分の元 x は ⟨x, x⟩ = 0
★ UA1_mem_condPart
  主張：U_N は導手ごとの部分を保つ（その上での作用は UA1_pullL_of_mem_Vprim）
  証明の要点：生成元で U_N χ = phaseA1(χ)χ
★ ipLim_ofL_Vprim
  主張：極限で、導手の違う原始部分の像は直交する（span_ofL_Vprim の和は直交和。極限での独立性は文にしていない）
  証明の要点：共通の法 q·q' に引き戻して ip_condPart
```

## 入力 (6)：逆翻訳の査読者 A2 の出力の全文（原文のまま）
A2 は ★ の文を、名前を中立化した入力で判定しました。名前の対応：S1 = `rootNum_congr`、S2 = `phaseA1_of_isPrimitive`、S3 = `normSq_phaseA1`、S4 = `phaseA1_changeLevel`、S5 = `rootNum_one_of_eq_one`、S6 = `phaseA1_one`、S7 = `ip_add_right`、S8 = `ip_smul_right`、S9 = `UA1_charU`、S10 = `ip_UA1`、S11 = `UA1_eq_TopL_of_mem_Vprim`、S12 = `pullL_charU`、S13 = `UA1_charU_eq_pull_TopL`、S14 = `UA1_unique`、S15 = `UA1_comp_pullL`、S16 = `TopL_not_compat`、S17 = `UA1_ne_TopL_prime`、S18 = `UA1_mem_Vprim`、S19 = `UA1_mem_Vimprim`、S20 = `UA1_comp_TopL`、S21 = `rootNum_one_prime`、S22 = `TopL_not_compat_prime`、S23 = `gaussSum_inv`、S24 = `rootNum_inv`、S25 = `primitiveCharacter_inv_apply`、S26 = `phaseA1_inv`、S27 = `UA1_star`、S28 = `pullL_injective`、S29 = `sum_units_unitsMap`、S30 = `ip_pullL`、S31 = `UA1_bijective`、S32 = `UA1_family_unique`、S33 = `ofL_injective`、S34 = `Uinf_ofL`、S35 = `Uinf_unique`、S36 = `Uinf_bijective`、S37 = `Uinf_ofL_of_mem_Vprim`、S38 = `ofL_charU`、S39 = `span_ofL_Vprim`、S40 = `Uinf_unique_TopL`、S41 = `totient_ne_zero'`、S42 = `ipn_pullSys`、S43 = `ipn_eq_of_ofL_eq`、S44 = `ipLim_ofL`、S45 = `ipLim_Uinf`、S46 = `ipLim_add_right`、S47 = `ipLim_smul_right`、S48 = `ipLim_conj`、S49 = `eq_zero_of_ipLim_self`、S50 = `ipLim_self_nonneg`、S51 = `UA1_pullL_of_mem_Vprim`、S52 = `condPart_eq_map`、S53 = `ip_condPart`、S54 = `iSup_condPart`、S55 = `iSupIndep_condPart`、S56 = `UA1_mem_condPart`、S57 = `ipLim_ofL_Vprim`、Θ1 = `phaseA1`、Θ2 = `UA1`、Θ3 = `pullL`、Ξ0 = `Lvl`、Ξ1 = `Gsp`、Ξ2 = `pullSys`、Ξ3 = `Lim`、Ξ4 = `ofL`、Ξ5 = `Uinf`、Ξ6 = `ipn`、Ξ7 = `ipLim`、Φ4 = `rootNum`、Ψ3 = `TopL`、Ψ4 = `charU`、Ψ5 = `ip`、Ψ6 = `Vprim`、Ψ7 = `Vimprim`、Ω1 = `condPart`、Ω2 = `ipR`。前のファイルの文：R1 = `ip_charU`、R2 = `span_charU_eq_top`、R3 = `eq_zero_of_ip_self`

{{A2_OUTPUT}}

## 課題
1. 表（入力 (5)）：各行の主張と証明の要点を形式文と突き合わせ、「一致／主張が強い／主張が弱い／別物／偽」で判定してください。★ の行はすべて判定を書いてください。ほかの行は、ずれがあるものだけ挙げ、残りは「一致」とまとめて構いません。
2. ノート（入力 (4)）：題、冒頭の結論・位置づけ・読み、検証表、「Lean にしていないこと」を形式文と突き合わせてください。形式文より強い箇所、形式文にないことを形式文の事実として書いた箇所、解釈の言葉を事実として書いた箇所を、行番号つきで挙げてください。変わった行の範囲は必ず見てください。
3. Lean ファイルの文面（入力 (3)）：冒頭の説明と docstring について同じ観点で。★ の宣言は必ず見てください。
4. ★ の文について、A2 の訳と判定（入力 (6)）と、文面の言い方が食い違うところを挙げてください。
5. 直すべき点を重要な順に挙げてください。各点に、どこを、どう直すかを、形式文から起こした言い方の案で書いてください。
6. 全体：形式文に偽・空虚・別物があるか。標準を超える内容があるか。
