あなたは独立の照合者です。ある Lean 4（Mathlib）の形式化について、前の照合者（B2）が文面のずれを指摘し、構築者が文面を直しました。直しが正しく入ったかを、形式文と突き合わせて判定してください。

## 守ってほしいこと
- この入力ファイルを Read で読んだあとは、ツールを一切使わないでください（ほかのファイル、シェル、検索、Web、エージェントの起動もしない）。長くて 1 回で読み切れないときは、同じファイルの続き（offset を指定）を読むことだけ許します。
- 定義名・定理名は意味の根拠にしないでください。定義の本文と文の形で判断してください。
- 著者の解釈の言葉（貼り合わせ、素点、重なり、解像度、公準 A1 など）は、「読み」「解釈」と明示されていれば許容です。
- 判断ごとに確信度（高・中・低）を付けてください。回答は日本語で、3,000 字程度までにまとめてください。最後に Read の回数を書いてください。

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


## 入力 (3)：B2 の出力の全文（原文のまま。行番号はノートの直す前の版のもの）

**照合結果（PAG258 / Part 254、★ の 7 文と変更行を中心に）**

形式文に偽・空虚・別物はありません（確信度：高）。文面は全体として形式文と同じか弱く書かれています。ずれは主に 4 つです。
- 「直和の文」の言い方
- ノートの 2 つの表のラベルが、変更範囲の中でまた食い違っていること
- docstring の参照誤りと法の書き違い
- 冒頭の説明 5 の書き残し

## 1. 表（入力 (5)）

**★ の行**
- `UA1_charU_eq_pull_TopL`：一致（高）。「位相の定義の言い換え」という説明も正しいです。
- `UA1_unique`・`UA1_ne_TopL_prime`（括弧内の値の出典も正しい）・`primitiveCharacter_inv_apply`・`span_ofL_Vprim`・`ipLim_self_nonneg`：一致（高）。
- `TopL_not_compat`：一致（高）。形式文は「ある f : (ℤ/1)ˣ → ℂ で」です。「自明な指標で」は証明の証人の話です。(ℤ/1)ˣ は 1 点なので線形性で同値になりますが、その一歩は文の外にあります。
- `rootNum_one_prime`：一致（高）。極分解の読みは「Lean にしていない」と明記されています。数学としても正しいです。
- `UA1_pullL_of_mem_Vprim`・`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`UA1_mem_condPart`：一致（高）。condPart の引数の順（法, 導手）も正しいです。
- `iSupIndep_condPart`：本体は一致です。付記の「iSup_condPart・condPart_eq_map と合わせて ⊕_{q∣M} π(V_prim(q)) の直交直和」はやや強いです（高）。
  - 直交を言うには ip_condPart も要ります。
  - 形式文の添字は ℕ 全体です。q ∤ M（と q = 0）で condPart M q = 0 になることは文にありません（導手は法を割るので自明ではあります）。
  - この直和を 1 つにまとめた文はありません。
- `ipLim_ofL_Vprim`：一致（高）。「直交和」は、成分どうしが直交するという意味でだけ支えられています。独立性は文にないことが明記されています。

**★ 以外**：すべて一致です。注記だけ挙げます。
- `eq_zero_of_ipLim_self` の「非退化」：形式文は ⟨z,z⟩ = 0 ⇒ z = 0（定値性）で、通常の意味の非退化より強いです。弱く言っているだけです（高）。
- `UA1_star` の「核は実数値・KUK = U」は同値な言い換えで、Lean の文ではありません。「定理 2.6」は入力にない参照です（中）。
- 見出しの「重なりはねじれた貼り合わせ U と決定済み」には「読み」がありません。ノート 9 行では「重なりの読み」と書いています（中）。

## 2. ノート（入力 (4)）

- **1・7・14・30・209 行**：「(1) は Lean の文になりました」「直和の文を Lean で示しました」「つまり…直交直和です」などと書いています（高）。
  - 形式文にあるのは部品（condPart_eq_map ほか）だけで、⊕_{q∣M} の形の文はありません。q ∤ M の成分が 0 であることも文にありません。
  - 30 行の「中身は組み合わせ」という但し書きは正しいです。
- **79 行と 104 行**：「T は両立しない」が §0.3 では再導出、§1 では既知になっています（高）。
- **80 行と 114 行**：`ipLim_ofL_Vprim`（原始部分の像の直交）が §0.3 では既知、§1 では再導出になっています。B が前回指摘した種類の食い違いが、変更範囲の中で再発しています（高）。
- **75 行**：根拠欄に ε(χ̄) = conj ε(χ) が残っています。212 行の「ルート数を W(χ*) と書き」と合いません（高）。
- **35 行**：C の名前（Ẑ^× の上のフーリエ乗数、新形式・旧形式分解の GL(1) 版）を断定で書いています（中）。
  - 前者は、Lim と Ẑ^× の上の局所定数関数の同一視（32 行で Lean の外としているもの）を前提にした読みです。
  - 後者は、C 自身の確信度が中でした（197 行）。
- **19・31 行**の「実質的な内容は族の一意性」は評価の言葉です（中）。UA1_family_unique は、指標ごとの式・UA1_unique・仮定を組み合わせた数行の帰結です。
- **31 行**の「Lean にしていないのは次の 2 つ」には、20・164 行で自分で挙げている「極限での独立性」が入っていません（中）。
- **10 行**「原始的でない指標では 0 や絶対値 1 未満」は既知の式ですが、ラベルがありません。Lean にあるのは素数の自明な指標の場合だけです（低）。
- **問題のない箇所**（高）：
  - 題の「代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射」と「完備化は Lean の外」
  - 3・160 行の件数（定理 57・定義 9・abbrev 3・構造体 1・instance 6。入力と一致）
  - 9・16・18・20・21・25・34 行
  - 26・108・144 行（極分解）。理論とも整合します。T_N が可逆になるのは N が無平方のとき（N ≤ 60 で 37 個）です。一致の条件は、すべての χ で μ(N/q)χ*(N/q) = 1 となることで、N ≤ 60 に限らず N = 1・6 だけになることが短く示せます［推論、高］。

## 3. Lean ファイルの文面（入力 (3)）

- **`UA1_charU_eq_pull_TopL` の docstring**：「直和そのものは §8」とありますが、冒頭の説明では 8 は極限で、直和は 10 です。冒頭 3 にも「直和そのものは 10」とあります（高）。
- **★ `UA1_pullL_of_mem_Vprim`**：見出しは「U_N」ですが、式は U_M です。A2 の注意どおり、法を取り違えると偽の文になります（中）。
- **冒頭 5**：「原始的でない部分では U_N ≠ T：…|W(1)|² = 1/p（UA1_ne_TopL_prime）」と書いています。形式文は「素数 p で、V_imprim に入り、かつ U ≠ T」だけで、値は別の定理から来ています（中）。
- **`eq_zero_of_ipLim_self`**：「正定値性」と書いていますが、この文だけでは定値性です（中）。
- **`rootNum_one_prime`**：極分解の文に「Lean にしていない」がありません（低）。
- **冒頭 10 と「Lean にしていないこと」**：ノートと同じ問題です（直和の文、極限での独立性）（高）。
- そのほかの ★ の docstring は一致です（高）。

## 4. A2 との食い違い（★ の文）

- **直和**：A2 は「一つの定理としては述べられていない」「添字は ℕ で、q ∤ N の成分は {0}」としています。文面は、⊕_{q∣M} の文が Lean にあるように読めます（高）。
- **S51**：A2 は「自明（S15 + S11）」です。文面は「解決」の柱として扱っていますが、30 行とは整合します（中）。
- **S57**：A2 は「実質的（標準）」です。文面の側が、既知（80 行）と再導出（114 行）に割れています（高）。
- **A2 の前置き**「Ξ3 は Ẑˣ の上の局所定数関数」は、形式文の外の読みです。この点は文面の方が正確です（高）。
- **成分ごとの不変性**：A2 が挙げた「U_∞ が各 ofL_q(V_prim(q)) を保つ」は、文面に記載がありません（中）。

## 5. 直すべき点（重要な順）

1. **直和**（ノート 1・7・14・30・209 行、冒頭 10、表）。案は次のとおりです。
   - 「法 M で、condPart M q（q ∈ ℕ）は互いに直交し（ip_condPart）、全体を張り（iSup_condPart）、独立（iSupIndep_condPart）。q ∣ M なら condPart M q = π_{q→M}(V_prim(q))（condPart_eq_map）。q ∤ M の成分は 0（文にしていない）。合わせて ⊕_{q∣M} の直交直和（1 つの定理にはしていない）」
   - Lean で閉じるなら、condPart M q = ⊥（q ∤ M）と DirectSum.IsInternal を足します。
2. **ラベル**：79 行と 104 行、80 行と 114 行をそろえます（A2 に合わせるなら既知（標準））。75 行の ε は W に直します。
3. **docstring の参照**：「直和そのものは §8」を「10」に直します。
4. **冒頭 5**：「素数 p では自明な指標は V_imprim に入り、U_p(1) ≠ T_p(1)（UA1_ne_TopL_prime）。値は phaseA1_one・UA1_charU と、Part 253 の TopL_charU・normSq_rootNum_one_prime」とします。
5. **★ の docstring**：「新しい部分の上の U_M」に直します。
6. **定値性**：`eq_zero_of_ipLim_self` の docstring を「定値性：⟨z,z⟩ = 0 なら z = 0（正値は ipLim_self_nonneg）」にします。ノート 21 行と表の「非退化」も同じ言い方にそろえます。
7. **35 行**：「C の名前（読み。Ẑ^× との同一視は Lean の外）」と書き、GL(1) 版には「C の確信度：中」を戻します。
8. **「Lean にしていないこと」**（冒頭・31 行・§1）に、次の 3 つを足します。
   - 極限での独立性
   - U_∞ が成分ごとに不変であること
   - 直和を 1 つの文にすること
9. **小さいもの**：
   - `rootNum_one_prime` の docstring に「極分解は Lean にしていない」を足す。
   - 表の TopL_not_compat を「ある f : (ℤ/1)ˣ → ℂ で」にする。
   - 表の見出しを「重なりの読みは」にする。
   - 10 行にラベルを付ける。
   - 19・31 行の「実質的な内容」を「定義の言い換えでない内容（短い組み合わせ）」にする。
   - 206 行の「注記に合わせて直した」に対し、S27（UA1_star）の行には ★ がありません。どちらかに合わせます（低）。

## 6. 全体

- **偽・空虚・別物**：ありません（高）。一意性の 4 文の仮定は UA1・Uinf 自身が満たすので、空虚ではありません。★ の 7 文は A2 の訳どおりです。
- **標準を超える内容**：ありません（高）。導手による指標の分割、ガウス和、帰納極限の普遍性の組み合わせです。

使ったツール：Read のみ（4 回、すべて入力ファイル。うち 1 回はサイズ上限のエラーで内容が返らず、範囲を分けて読み直しました）

## 入力 (4)：Lean ファイルの文面の差分（形式文は変えていない。冒頭の説明と docstring だけ）
```diff
--- PAG258.lean（直す前）
+++ PAG258.lean（直した後）
@@ -26,3 +26,5 @@
    T は両立しない（`TopL_not_compat`：法 1 → 2、`TopL_not_compat_prime`：法 1 → p）。
-5. 原始的でない部分では U_N ≠ T：素数 p の自明な指標で U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p（`UA1_ne_TopL_prime`）。
+5. 原始的でない部分では U_N ≠ T：素数 p では自明な指標は V_imprim に入り、U_p(1) ≠ T_p(1)（`UA1_ne_TopL_prime`）。
+   値（U(1) = 1、T(1) = W(1)·1、|W(1)|² = 1/p）は `phaseA1_one`・`UA1_charU` と Part 253 の `TopL_charU`・
+   `normSq_rootNum_one_prime` から。
    W(1 mod p) = −1/√p（`rootNum_one_prime`）。素数の法 p では、T の極分解のユニタリ因子のこの指標での固有値は
@@ -43,3 +45,3 @@
    極限の上の内積 `ipLim` が決まり、右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、
-   正定値（`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`）。U_∞ はこれを保つ（`ipLim_Uinf`）。
+   正値（`ipLim_self_nonneg`）と定値性（`eq_zero_of_ipLim_self`：⟨z, z⟩ = 0 なら z = 0）。U_∞ はこれを保つ（`ipLim_Uinf`）。
 
@@ -47,5 +49,7 @@
    に等しく（`condPart_eq_map`、q ∣ M）、導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、
-   独立（`iSupIndep_condPart`）。つまり単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和。U_M は各部分を
-   保ち（`UA1_mem_condPart`）、その上で π∘T_q（`UA1_pullL_of_mem_Vprim`：g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
-   極限でも、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`）。
+   独立（`iSupIndep_condPart`）。添字は q ∈ ℕ 全体で、q ∤ M の部分が 0 であることは文にしていない。合わせると
+   ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になるが、1 つの定理にはしていない。U_M は各部分を保ち（`UA1_mem_condPart`）、
+   原始部分の引き戻しの上で π∘T_q（`UA1_pullL_of_mem_Vprim`：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)）。
+   極限では、導手の違う原始部分の像は直交する（`ipLim_ofL_Vprim`。前ヒルベルト空間での直交。極限での独立性と、
+   U_∞ が各部分を保つことは文にしていない）。
 
@@ -59,3 +63,4 @@
 （ノートの §7）。一般の N ∣ M（N < M）での T の非両立と、N ≥ 2 一般での U_N ≠ T（τ(1 mod N) = μ(N)）は Lean に
-していない。
+していない。10 について：q ∤ M の部分が 0 であること、直和を 1 つの文（DirectSum.IsInternal）にすること、極限での
+独立性、U_∞ が各部分を保つことは Lean にしていない。
 -/
@@ -226,3 +231,3 @@
 
-/-- **指標ごとの式**（直和の文の指標ごとの形。直和そのものは §8）：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（q = cond χ、χ* は誘導元の原始指標）。 -/
+/-- **指標ごとの式**（直和の文の指標ごとの形。直和の部品は冒頭の説明の 10）：すべての指標 χ で U_N χ = π_{q→N}(T_q χ*)（q = cond χ、χ* は誘導元の原始指標）。 -/
 theorem UA1_charU_eq_pull_TopL (χ : DirichletCharacter ℂ N) :
@@ -313,3 +318,3 @@
 /-- 素数 p の自明な指標の W は −1/√p（実数で負）。法 p の T の極分解のユニタリ因子なら、この指標での固有値は −1
-（U_p の固有値は 1）。 -/
+（U_p の固有値は 1）。極分解そのものは Lean にしていない。 -/
 theorem rootNum_one_prime (p : ℕ) [Fact p.Prime] :
@@ -694,3 +699,3 @@
 
-/-- 極限の内積の正定値性：⟨z, z⟩ = 0 なら z = 0。 -/
+/-- 極限の内積の定値性：⟨z, z⟩ = 0 なら z = 0（正値は `ipLim_self_nonneg`）。 -/
 theorem eq_zero_of_ipLim_self (z : Lim) (h : ipLim z z = 0) : z = 0 := by
@@ -718,3 +723,3 @@
 
-/-- 新しい部分の上の U_N：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)。 -/
+/-- 新しい部分の上の U_M：q ∣ M、g ∈ V_prim(q) なら U_M(π g) = π(T_q g)（左辺の U は法 M、右辺の T は法 q）。 -/
 theorem UA1_pullL_of_mem_Vprim {M : ℕ} [NeZero M] (hNM : N ∣ M) {g : (ZMod N)ˣ → ℂ}
@@ -775,3 +780,3 @@
 
-/-- 導手ごとの部分は独立（直和）。 -/
+/-- 導手ごとの部分は独立（内部直和の独立性。添字は q ∈ ℕ 全体）。 -/
 theorem iSupIndep_condPart : iSupIndep (condPart N) := by
```

## 入力 (5)：ノートの差分
```diff
--- pag2_part254_full_gluing.md（直す前）
+++ pag2_part254_full_gluing.md（直した後）
@@ -1,2 +1,2 @@
-# アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 単数の上の関数は導手ごとの新しい部分 π(V_prim(q)) の直交直和で、U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）
+# アーデル射影幾何 — Part 254（PAG 2.0）：法 N の境界ユニタリ U_N 全体と、代数的な帰納極限の上の U_∞ — 単数の上の関数の空間で、導手ごとの部分 π(V_prim(q)) は互いに直交し、独立で、全体を張る（合わせると直交直和。1 つの定理にはしていない）。U_N はその上で T_q を引き戻したもの。原始部分で T と一致し引き戻しと両立する族は U_N だけで、代数的な帰納極限の上の、正規化した内積を保つ 1 つの全単射 U_∞ にまとまる（Part 252 の残る問い。完備化 L²(Ẑ^×) は Lean の外）
 
@@ -6,6 +6,6 @@
   - Part 252 のノート §4 の残る問い：(1) 法 N の境界ユニタリ全体（原始的でない指標を含む）を、J∘H_q（q ∣ N）の新しい部分の直和として書く文。(2) 法を動かした組み立て（L²(Ẑ^×) の上の 1 つの作用素）。
-  - 解けた範囲：(1) は Lean の文になりました。(2) は代数的な帰納極限の上までです。完備化 L²(Ẑ^×) と、Ẑ^× の上の局所定数関数との同一視は Lean の外です（下の「解決の範囲」）。
+  - 解けた範囲：(1) は部品の文（直交・張る・独立・各部分の形）として Lean にしました（直和を 1 つの文にはしていない）。(2) は代数的な帰納極限の上までです。完備化 L²(Ẑ^×) と、Ẑ^× の上の局所定数関数との同一視は Lean の外です（下の「解決の範囲」）。
   - 着手前の 4 点・対照群・盲検の問いテストは、Part 253 の着手前の文書 `pag2_part253_preregistration.md` の候補 K2 と、盲検の文 T2（既知の結果の短い帰結）・T3（標準的な演習。注意：Ẑ に移るのは引き戻しと両立する作用素だけ）で済んでいます。
 - **問い（幾何の言葉で。解釈）。** 重なりの読みは「ねじれた貼り合わせ（U）」です（著者の決定、2026-11-12 17:14）。法 N の貼り合わせ U_N に、A1 の位相をすべての指標に入れます（原始的でない指標には、誘導元の原始指標の位相）。(1) U_N は、各導手 q の原始部分の貼り合わせ T_q を組み合わせたものか。(2) 法を上げたとき、U_N はまとまって 1 つの作用素になるか。
-- **記号。** Part 253 の記号を使います：単数の上の関数、内積 ⟨f, g⟩ = Σ_u conj(f(u))·g(u)（`ip`）、T = Part 253 の `TopL`。T は J∘H_N/√N を単数に圧縮し、反転 u ↦ u⁻¹ と合成した作用素です（離散 Hartley 変換を単数に制限しただけのものではありません。独立照合 A の注意）。χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）です。W(χ) は Part 252 の `rootNum`（原始指標ならルート数。原始的でない指標ではルート数ではなく、0 や絶対値 1 未満になる）です。
+- **記号。** Part 253 の記号を使います：単数の上の関数、内積 ⟨f, g⟩ = Σ_u conj(f(u))·g(u)（`ip`）、T = Part 253 の `TopL`。T は J∘H_N/√N を単数に圧縮し、反転 u ↦ u⁻¹ と合成した作用素です（離散 Hartley 変換を単数に制限しただけのものではありません。独立照合 A の注意）。χ* は χ を誘導する原始指標（Mathlib の `primitiveCharacter`、法は導手 q = cond χ）です。W(χ) は Part 252 の `rootNum`（原始指標ならルート数。原始的でない指標ではルート数ではなく、0 や絶対値 1 未満になる［既知。Lean にあるのは素数の自明な指標の場合だけ］）です。
   - 位相 `phaseA1 χ` = W(χ*)。法 N の境界ユニタリ `UA1` = Σ_χ phaseA1(χ)·P_χ（P_χ f = (⟨χ, f⟩/φ(N))·χ）。引き戻し `pullL`（N ∣ M）：f ↦ f ∘ ((ℤ/M)ˣ → (ℤ/N)ˣ)。
@@ -13,3 +13,3 @@
   - **残る問い (1)（直和の文）。**
-    - 直和：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q)) に等しい（`condPart_eq_map`、q ∣ M）。導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、独立です（`iSupIndep_condPart`）。つまり単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和です（独立照合 B の指摘で追加）。
+    - 直和：導手が q の指標が張る部分 `condPart M q` は π_{q→M}(V_prim(q)) に等しい（`condPart_eq_map`、q ∣ M）。導手の違う部分は直交し（`ip_condPart`）、全体を張り（`iSup_condPart`）、独立です（`iSupIndep_condPart`）。添字は q ∈ ℕ 全体で、q ∤ M の部分が 0 であることは文にしていません。合わせると ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になりますが、1 つの定理にはしていません（独立照合 B の指摘で追加。この言い方は再照合 B2 の指摘で直した）。
     - その上の U：U_M は各部分を保ち（`UA1_mem_condPart`）、g ∈ V_prim(q) なら U_M(π g) = π(T_q g) です（`UA1_pullL_of_mem_Vprim`）。
@@ -18,5 +18,5 @@
     - 有限レベル：U_N は法を上げる引き戻しと両立します：N ∣ M なら U_M ∘ π = π ∘ U_N（`UA1_comp_pullL`）。T は法 1 → 2 と、すべての素数 p で法 1 → p で両立しません（`TopL_not_compat`・`TopL_not_compat_prime`）。一般の N < M でも両立しないはずですが（原始的でない指標のガウス和の式による）、Lean の外です［既知、確信度：中］。
-    - **族の一意性**（このパートの実質的な内容）：法の集合（正の整数を割り算の順で並べた型 `Lvl`）の各法で、原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけです（`UA1_family_unique`）。原始的でない指標の上の位相は仮定に入らず、両立から一通りに決まります（独立照合 A の指摘で追加）。
+    - **族の一意性**（定義の言い換えでない内容。指標ごとの式・`UA1_unique`・仮定を組み合わせた短い帰結）：法の集合（正の整数を割り算の順で並べた型 `Lvl`）の各法で、原始部分の上では T と一致し、引き戻しと両立する作用素の族は U_N だけです（`UA1_family_unique`）。原始的でない指標の上の位相は仮定に入らず、両立から一通りに決まります（独立照合 A の指摘で追加）。
     - 極限：引き戻しの帰納系の代数的な帰納極限 `Lim`（Mathlib の `Module.DirectLimit`）を作りました。極限への写像は単射です（`ofL_injective`）。U_N の族は極限の上の 1 つの作用素 U_∞ を与えます（`Uinf`、各法の像の上で U_N：`Uinf_ofL`）。U_∞ はこの性質で一意（`Uinf_unique`）で、全単射です（`Uinf_bijective`）。各法の原始部分の像は極限を張り（`span_ofL_Vprim`）、導手の違う像は直交し（`ipLim_ofL_Vprim`。極限での独立性は文にしていない）、U_∞ はその上で T_q です（`Uinf_ofL_of_mem_Vprim`）。U_∞ は「各導手の原始部分の像の上で T_q」という性質でも一意です（`Uinf_unique_TopL`）。
-    - 極限の上の内積：引き戻しの和 φ(N)·Σ_u F(πu) = φ(M)·Σ_v F(v)（`sum_units_unitsMap`）から、正規化した内積 ⟨f, g⟩/φ(N) は引き戻しで変わりません（`ip_pullL`・`ipn_pullSys`）。代表の取り方によらない（`ipn_eq_of_ofL_eq`）ので、極限の上の内積 `ipLim` が決まります。右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、⟨z, z⟩ は 0 以上の実数（`ipLim_self_nonneg`）、非退化（`eq_zero_of_ipLim_self`）です（Mathlib の内積の構造にはしていません）。U_∞ はこれを保ちます（`ipLim_Uinf`）。
+    - 極限の上の内積：引き戻しの和 φ(N)·Σ_u F(πu) = φ(M)·Σ_v F(v)（`sum_units_unitsMap`）から、正規化した内積 ⟨f, g⟩/φ(N) は引き戻しで変わりません（`ip_pullL`・`ipn_pullSys`）。代表の取り方によらない（`ipn_eq_of_ofL_eq`）ので、極限の上の内積 `ipLim` が決まります。右側で線形（`ipLim_add_right`・`ipLim_smul_right`）、エルミート（`ipLim_conj`）、⟨z, z⟩ は 0 以上の実数（`ipLim_self_nonneg`）、定値性（`eq_zero_of_ipLim_self`：⟨z, z⟩ = 0 なら z = 0）です（Mathlib の内積の構造にはしていません）。U_∞ はこれを保ちます（`ipLim_Uinf`）。
   - そのほか：
@@ -29,4 +29,4 @@
 - **「解決」の範囲（正直な評価）。**
-  - 残る問い (1)：直和の文を Lean で示しました（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` と `UA1_pullL_of_mem_Vprim`）。ただし中身は、指標を導手で分けることと、各レベルでの Part 253 の結果の組み合わせです。U_N の明示の核（導手とメビウスの式）は数値だけです（step277 の (8)、60/60）。
-  - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。実質的な内容は族の一意性（`UA1_family_unique`）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。
+  - 残る問い (1)：直和の部品の文を Lean で示しました（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart` と `UA1_pullL_of_mem_Vprim`。直和を 1 つの文にすること、q ∤ M の部分が 0 であることは文にしていない）。ただし中身は、指標を導手で分けることと、各レベルでの Part 253 の結果の組み合わせです。U_N の明示の核（導手とメビウスの式）は数値だけです（step277 の (8)、60/60）。
+  - 残る問い (2)：代数的な帰納極限の上の作用素 U_∞ と、その上の内積を Lean で作り、U_∞ が内積を保つ全単射であることを示しました。定義の言い換えでない内容は族の一意性（`UA1_family_unique`。短い組み合わせ）です。Lean にしていないのは次の 2 つです。どちらも標準の事実です［既知、確信度：高］。ほかに、極限での独立性と、U_∞ が導手ごとの各部分を保つことも Lean にしていません。
     - 帰納極限 `Lim` を Ẑ^× = lim (ℤ/N)^× の上の局所定数関数の空間と同一視すること。
@@ -34,3 +34,3 @@
 - **A1 との関係（第 2 の型の注意）。** U_N は A1 の位相を定義として入れた作用素です。指標ごとの式と両立は、位相を誘導元の原始指標から取るという選び方と、Mathlib の導手の性質（導手と誘導元は法を上げても変わらない）から出ます。族の一意性（`UA1_family_unique`）は、この選び方が「原始部分で A1（T と一致）＋法の間の両立」から一通りに決まることを言います。原始部分の A1 は仮定のままで、A1 は公準のままです。導いていません（CLAUDE.md §2・§6）。
-- **位置づけ。** 既知の枠組みの書き直しです（再導出、確信度：高）。独立照合 C の名前：U_∞ は Ẑ^× の上の、原始指標のルート数 W(χ*) を記号とするフーリエ乗数（Ẑ^× の双対群は原始ディリクレ指標の全体）。導手による分解は新形式・旧形式分解の GL(1) 版、引き戻しは inflation です（§5 と辞書 §14）。新規候補はありません。
+- **位置づけ。** 既知の枠組みの書き直しです（再導出、確信度：高）。独立照合 C の名前（読み。`Lim` と Ẑ^× の上の局所定数関数の同一視は Lean の外）：U_∞ は Ẑ^× の上の、原始指標のルート数 W(χ*) を記号とするフーリエ乗数（Ẑ^× の双対群は原始ディリクレ指標の全体）。導手による分解は新形式・旧形式分解の GL(1) 版（C の確信度：中）、引き戻しは inflation です（§5 と辞書 §14）。新規候補はありません。
 
@@ -74,3 +74,3 @@
 | U_N χ = phaseA1(χ)χ、U_N はユニタリ（`ip` に関して）・全単射、原始部分で U_N = T | 再導出 | 直交性、\|W(χ*)\| = 1、Part 253 |
-| T との可換、V_prim・V_imprim の不変、実数性 | 既知 | 同じ指標の基底で対角、ε(χ̄) = conj ε(χ) |
+| T との可換、V_prim・V_imprim の不変、実数性 | 既知 | 同じ指標の基底で対角、W(χ̄*) = conj W(χ*) |
 | 指標ごとの式 U_N χ = π(T_q χ*) | 再導出 | 位相の定義と Part 253 の `TopL_charU` |
@@ -78,4 +78,4 @@
 | 有限レベルの直和（導手ごとの部分 = π(V_prim(q))、直交、全体、独立）と、その上で U = π∘T_q | 再導出 | 指標の導手による分割、直交性 |
-| 引き戻しとの両立（T は両立しない）と、両立する族の一意性 | 再導出 | 位相が誘導元から決まること |
-| 帰納極限の上の U_∞ と内積、原始部分の像の直交 | 既知 | 帰納極限の普遍性、ファイバーの元の数が一定 |
+| 引き戻しとの両立（T は両立しない）と、両立する族の一意性 | 両立と一意性は再導出、T の非両立は既知 | 位相が誘導元から決まること |
+| 帰納極限の上の U_∞ と内積、原始部分の像の直交 | 内積と直交は既知、U_∞ の性質は再導出 | 帰納極限の普遍性、ファイバーの元の数が一定 |
 | 原始的でない部分で U ≠ T（素数の法） | 既知 | 主指標のガウス和 −1（ラマヌジャン和 c_p(1) = μ(p)） |
@@ -113,3 +113,3 @@
 | 極限への写像は単射、U_∞ は各法で U_N、一意、全単射 | `ofL_injective`・`Uinf_ofL`・`Uinf_unique`・`Uinf_bijective` | — | 既知 |
-| 原始部分の像は極限を張り、導手の違う像は直交し、U_∞ はその上で T_q、この性質で一意 | `ofL_charU`・`span_ofL_Vprim`・`ipLim_ofL_Vprim`・`Uinf_ofL_of_mem_Vprim`・`Uinf_unique_TopL` | — | 再導出 |
+| 原始部分の像は極限を張り、導手の違う像は直交し、U_∞ はその上で T_q、この性質で一意 | `ofL_charU`・`span_ofL_Vprim`・`ipLim_ofL_Vprim`・`Uinf_ofL_of_mem_Vprim`・`Uinf_unique_TopL` | — | 直交は既知、U_∞ の性質は再導出 |
 | 極限の内積：正規化、代表によらない、右で線形、エルミート、正定値、U_∞ が保つ | `totient_ne_zero'`・`ipn_pullSys`・`ipn_eq_of_ofL_eq`・`ipLim_ofL`・`ipLim_add_right`・`ipLim_smul_right`・`ipLim_conj`・`ipLim_self_nonneg`・`eq_zero_of_ipLim_self`・`ipLim_Uinf` | — | 既知 |
@@ -205,6 +205,6 @@
 - **B（S1〜S50 と、ノートの題・結論・解決の範囲・ラベル・検証表）**：
-  - xlsx の主張：50 文すべて「一致」で、主張が強い・別物・空虚はなし。注記つきが 7 文（S13 は「直和の文」が名前だけ、S16 は法 1 → 2 だけ、S17 の括弧の値は別の定理から、S21 の極分解は N = p なら正しい、S25 の「導手は逆で変わらない」は独立の文でない、S27 の核の実数性は同値な言い換え、S50 は Inner の構造ではない）。xlsx の該当の主張は、注記に合わせて直した。S18〜S50 は手ですべて真と確認（S32 の仮定で足りる、Ξ7 は選択によらない）。
+  - xlsx の主張：50 文すべて「一致」で、主張が強い・別物・空虚はなし。注記つきが 7 文（S13 は「直和の文」が名前だけ、S16 は法 1 → 2 だけ、S17 の括弧の値は別の定理から、S21 の極分解は N = p なら正しい、S25 の「導手は逆で変わらない」は独立の文でない、S27 の核の実数性は同値な言い換え、S50 は Inner の構造ではない）。xlsx の該当の主張は、注記に合わせて直した（S27 の行は直していなかった。再照合の後に直した）。S18〜S50 は手ですべて真と確認（S32 の仮定で足りる、Ξ7 は選択によらない）。
   - ノートへの指摘（重要な順）と対応：
     1. 極分解の文は一般には偽（法 1・6 で U_N は T_N の極分解のユニタリ因子そのもの）。→ 素数の法に限って直し、反例を本文に書いた。数値 (20) で確認：T_N が可逆な N ≤ 60 では、一致するのは N = 1・6 だけ。
-    2. 「直和の文」「(1) を解決」は、指標ごとの式（定義の言い換え）と基底による一意性だけで、直和分解は Lean にない。→ 有限レベルの直和を Lean にした（`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim`、極限で `ipLim_ofL_Vprim`）。指標ごとの式は「定義の言い換え」と書き直し、実質的な内容が族の一意性であることを明記した。数値 (21) で確認。
+    2. 「直和の文」「(1) を解決」は、指標ごとの式（定義の言い換え）と基底による一意性だけで、直和分解は Lean にない。→ 有限レベルの直和の部品を Lean にした（直和を 1 つの文にはしていない。`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`UA1_pullL_of_mem_Vprim`、極限で `ipLim_ofL_Vprim`）。指標ごとの式は「定義の言い換え」と書き直し、実質的な内容が族の一意性であることを明記した。数値 (21) で確認。
     3. 「T は両立しない」「原始的でない部分で U ≠ T」を一般の形で書いていた。→ Lean の範囲（法 1 → p、素数の法）に合わせ、一般の場合は Lean の外と書いた。N = 1 では V_imprim = 0。
@@ -216 +216,11 @@
 
+## 8. 再照合（2026-11-14、著者側の補足3 の開始条件 1）
+
+- **対象。** 照合 B の後に足した定理 7 個（`UA1_pullL_of_mem_Vprim`・`condPart_eq_map`・`ip_condPart`・`iSup_condPart`・`iSupIndep_condPart`・`UA1_mem_condPart`・`ipLim_ofL_Vprim`）と定義 2 個（`condPart`・`ipR`）、B の後に直した文面。
+- **手順。** 新しいエージェント A2（逆翻訳。中立化した名前で判定）と B2（照合。形式文と定義の全文、Lean の docstring の全文、ノートの全文、表の全行、A2 の出力の全文を渡した）。照合者は入力ファイルを Read で読む形（A2 は 1 回、B2 は 4 回。1 回はサイズ上限のエラーで、範囲を分けて読み直した。どれも入力ファイルだけ）。記録は `pag2_reaudit_252_256.md` と `reaudit257/`。
+- **A2。** 7 文とも真。`condPart_eq_map` が中身のある文（標準）で、ほかは自明か標準の短い帰結。`ipR` は文に出てこない（証明の補助）。`ipLim_ofL_Vprim` は前ヒルベルト空間での直交で、L²(Ẑ^×) の文ではない。極限での独立性と、U_∞ が各部分を保つことは文にない。
+- **B2。** 形式文 57 個に偽・空虚・別物はない。ずれは「直和の文を Lean で示した」の言い方（添字は ℕ 全体で、⊕_{q∣M} を 1 つにまとめた文はない）、ラベルの食い違い（79 行と 104 行、80 行と 114 行）、75 行の ε、Lean の docstring の参照誤り（「直和そのものは §8」）と法の書き違い（`UA1_pullL_of_mem_Vprim` の「U_N」は U_M）、冒頭の説明 5 の書き方など。
+- **直したもの。** Lean の冒頭の説明 4 か所と docstring 5 個（形式文は変えていない。組み立て直して確認）。ノートの上の行（題、7・10・14・19・21・30・31・35・75・79・80・114・206・209 行）と、表の見出しと 4 行（`TopL_not_compat`・`UA1_star`・`eq_zero_of_ipLim_self`・`iSupIndep_condPart`）。
+- **直していないもの。** 直和を 1 つの文（DirectSum.IsInternal）にすること、q ∤ M の部分が 0 であることの文、極限での独立性（Lean の文を足すと、また照合されていない文が増えるため、文面を形式文に合わせる方で直した）。
+- **第 3 の型の検知。** 「直和の文を Lean で示した」は、部品の文を合わせた読みを、1 つの定理があるかのように書いていた。B の後の直しが Lean の docstring に入っていなかった。
+
```

## 入力 (6)：表（xlsx）の差分
```
【見出し（直す前）】PAG2.0-254 法 N の境界ユニタリ U_N 全体と、法を上げた組み立て（Part 252 の残る問い。著者の指示「Part 252, Part 254 を解決してください」、2026-11-13 06:43。重なりはねじれた貼り合わせ U と決定済み。A1 は位相の規約で、Lean の公理ではない）
【見出し（直した後）】PAG2.0-254 法 N の境界ユニタリ U_N 全体と、法を上げた組み立て（Part 252 の残る問い。著者の指示「Part 252, Part 254 を解決してください」、2026-11-13 06:43。重なりの読みはねじれた貼り合わせ U。A1 は位相の規約で、Lean の公理ではない）

【TopL_not_compat の主張（直す前）】法 1 → 2 では、Part 253 の T は引き戻しと両立しない：自明な指標で T(π f) ≠ π(T f)（一般の N ∣ M の文ではない。法 1 → p は TopL_not_compat_prime）
【TopL_not_compat の主張（直した後）】法 1 → 2 では、Part 253 の T は引き戻しと両立しない：ある f : (ℤ/1)ˣ → ℂ で T(π f) ≠ π(T f)（証明の証人は自明な指標）（一般の N ∣ M の文ではない。法 1 → p は TopL_not_compat_prime）

【UA1_star の主張（直す前）】実数性：U_N は複素共役と可換（U_N(conj ∘ f) = conj ∘ U_N f。U_N の核は実数値で、定理 2.6 の条件 KUK = U。step277 の (9) を Lean に。独立照合 C の「証明できる」を受けて追加）
【UA1_star の主張（直した後）】実数性：U_N は複素共役と可換（U_N(conj ∘ f) = conj ∘ U_N f。「U_N の核は実数値」「KUK = U」は同値な言い換えで、Lean の文ではない。step277 の (9) を Lean に。独立照合 C の「証明できる」を受けて追加）

【eq_zero_of_ipLim_self の主張（直す前）】極限の内積の非退化：⟨z, z⟩ = 0 なら z = 0
【eq_zero_of_ipLim_self の主張（直した後）】極限の内積の定値性：⟨z, z⟩ = 0 なら z = 0（正値は ipLim_self_nonneg）

【iSupIndep_condPart の主張（直す前）】導手ごとの部分は独立（iSupIndep）。iSup_condPart・condPart_eq_map と合わせて、単数の上の関数の空間は ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和（Part 252 の残る問い 1 の直和の文。独立照合 B の指摘で追加）
【iSupIndep_condPart の主張（直した後）】導手ごとの部分は独立（iSupIndep。添字は q ∈ ℕ 全体）。ip_condPart（直交）・iSup_condPart（張る）・condPart_eq_map（各部分の形）と合わせると ⊕_{q∣M} π_{q→M}(V_prim(q)) の直交直和になるが、1 つの定理にはしていない（q ∤ M の部分が 0 であることも文にしていない。Part 252 の残る問い 1 の直和の部品。独立照合 B の指摘で追加）
```

## 課題
1. B2 の「直すべき点」の各項目について、直しが「入った／不十分／入っていない／直しが誤り」のどれかを、短い理由とともに書いてください。直していない項目は、その扱いが文面（ノートの記録など）に書かれているかも見てください。
2. 差分の中の新しい文面に、形式文より強い言い方、形式文にないことを事実として書いた箇所、計算や参照の誤りがないかを見てください。あれば、場所と直し方の案を書いてください。
3. 全体の判定を 1 行で：直しで残ったずれ（あれば重要な順に）。
