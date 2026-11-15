# 依頼：Part 258（PAG262.lean）の独立照合

あなたは、このパートの作成に関わっていない照合者です。この 1 つのファイルだけを Read で読んでください（ほかのツールは使わないでください）。答えは日本語で。

背景：Lean 4 / Mathlib の形式化の鎖。PAG 2.0 の Part n はファイル PAG(n+4).lean、名前空間 PAG.PartNNN の NNN はファイル番号。PAG.lean・PAG2・PAG3・PAG4 は「最初の形式化の Part 1〜4」。
「見方」「殻構造と両立」「素点」は著者の解釈の層と登録の言葉で、Lean の文には出てこない。数値の確認は証明ではない。

確かめてほしいこと：
1. 形式文：各定理の文は（仮定のもとで）偽・空虚・自明すぎるものがないか。とくに `no_compatible_hom` と `exists_compatible_hom_iff` が、登録の受容条件（着手前の文書 §2）を正しく表しているか、仮定が強すぎ・弱すぎないか、条件 (ii) の span の取り方（t ∣ M でない t を含む）が問題にならないか。`exists_compatible_hom` の (i)(ii) が実際に中身を持つか。
2. 文面と形式文のずれ：Lean の冒頭の説明・docstring・ノートの「結論」「読み」「位置づけ」「検証表」が、形式文の言える範囲を越えていないか（格上げ、範囲の書き落とし、「Lean で確認」「Lean にしていない」の書き分け）。題は形式文から起こしてあるか。「β の前提は素数冪の段で閉じる」の読みの言い方。
3. 内部照合：下の前の鎖の宣言と比べて、PAG262 の文が同じ文・直ちに出る・数行で出るものはないか（ノート §7 と食い違わないか）。
4. 数値照合 step281 と盲検の答えが、Lean の文と対応しているか。
5. ラベル（既知／再導出／新規候補）の付け方、確信度の付け方、収束アラームの書き方。

出力：## 1. 形式文の判定（定理ごとに 1 行）　## 2. 文面の指摘（表：場所｜問題｜直し方の案｜確信度）　## 3. 内部照合の指摘　## 4. 数値・盲検との対応　## 5. 総評（3 行まで）。見ていないもの・確かめていないものも書いてください。

---
# A. PAG262.lean（全文）
```lean
/-
アーデル射影幾何 — Part 258（PAG 2.0）：方向βの前提 — N ∣ M で、引き戻しと両立し殻を混ぜない代数準同型 A_N → A_M があるのは
gcd(N, M/N) = 1 のときに限る

問いの出所：著者側の申し送り補足7（2026-11-14）の決定。登録 `preregistration-part255-beta-premise.md` の問いを、突き合わせの記録
`pag2_beta_registration_check.md` §3 の切り分けで修正して行った（着手前の文書 `pag2_part258_preregistration.md`）。
幾何の言葉での問い（読み）：見方を変える（N を上げる）操作は、代数の側で 1 つの写像として実現できるか。

A_N は Part 214（PAG218）の `shellAlg N`：End(ℂ^{ℤ/N}) の中で D_s（空間の殻 gcd(N, x) = s の指示関数の掛け算、`dind`）と
E_s（双対殻の射影 ε_s の畳み込み、`geps`）が生成する代数。単数の軌道によるアソシエーションスキームの、基点 0 での
Terwilliger 代数 T(0) にあたる（辞書）。「見方」「殻構造と両立」は著者の解釈の層と登録の言葉で、Lean の文には出てこない。
登録の受容条件の Lean での形（この Part での読み）：(1) 代数準同型 φ : A_N →ₐ[ℂ] A_M（単位元を保つ）。(2) 射影と両立：
すべての S ∈ A_N で φ(S) π^* = π^* S（π^* は ℤ/M → ℤ/N に沿った引き戻し、Part 197 の `pull`）。(3) 殻を混ぜない（強い読み）：
φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合。

Lean の文：
1. 存在（gcd(a, b) = 1）：`shellLift`（S ↦ Θ(S ⊗ 1)、Θ は Part 228（PAG232）の `shellAlgTensorEquiv`）。CRT の共役で L(S) に移る
   （`crtConj_shellLift`）。条件 2（`shellLift_pull`）。条件 3 は明示の形 φ(D_s) = Σ_{u ∣ b} D_{su}、φ(E_s) = Σ_{u ∣ b} E_{su}
   （`shellLift_dind`・`shellLift_geps`、s ∣ a）。単射（`shellLift_injective`）。まとめて `exists_compatible_hom`。
2. 不存在（素数 p が N と M/N の両方を割る）：`no_compatible_hom`。使うのは A_N の D_N・E_N と、関係 D_N E_N D_N = (1/N) D_N
   （`dTop_eTop_dTop`）、E_N² = E_N（`eTop_mul_self`）だけ。条件 2・3 から φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の
   掛け算、φ(E_N) は ε の線形結合 g の畳み込みで、𝓕g は双対殻の上で定数かつ 0・1 値。関係から H の上で g = (1/N)·δ₀、
   H の上の指標の和（`sum_ker_stdAddChar`）で数えると、ξ ≡ 1 (mod M/N) の剰余類に 𝓕g = 1 の点がちょうど 1 つ。
   ところが u = 1 + M/p は単数で（(M/p)² ≡ 0）、ξ ↦ uξ はその剰余類と双対殻を保つので、点が 2 つになり矛盾。
3. 二分法：`exists_compatible_hom_iff`（N ∣ M のとき、1・2 の性質の写像がある ⇔ gcd(N, M/N) = 1）。

範囲：Lean の文は単位元を保つ代数準同型（→ₐ）と、条件 3 の強い読みについて。単位元を保たない版（盲検の手計算と数値では、
条件から自動的に単位元を保つ）、条件 3 の弱い読み（像が A_M に入るだけ）、条件 2 を外したとき（登録 §5 の除去テスト）、
対照群 F_q[t]/(t^e) は Lean にしていない。互いに素な組で、CRT の写像のほかにも条件を満たす写像があること（数値：(2,6) で
φ(E_1) = E_3 + E_2）も Lean にしていない。

位置づけ：存在の側は既知（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Theorem 3.1。鎖では Part 228）。
不存在の側は、着手前の盲検の問いテストで文献が見つからなかった（確信度 中。見つからなかったというだけ）。初等的な議論で、
ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項。A1 は公準のまま。ここでの文は A_N についての代数の事実で、
A1 とは関係しない。

内部照合（着手の前）：Part 228（PAG232）の `shellAlgTensorEquiv`・`leftHom`（互いに素な段のテンソル積）、Part 202（PAG206）の
`mem_geps_pull_iff`（関数のレベルの事実：E^{Nt}_{ts} の固定空間は E^N_s の固定空間の引き戻し）。商に沿った A_N → A_M の
写像の宣言は前の鎖に見つからなかった（網羅ではない）。
閉じる前の照合（全宣言 4339 件、PAG262 の 30 件、候補上位 20、`#dupcheck`・`#defeqcheck` を両向きに 1140 回）：下書きの
`dind_self_apply` は Part 247（PAG251）の同名の定理と、`rightOp_one` は Part 247 の `rightOp_one'` と同じ文だった（両向きに確認）。
2 つとも消して前の鎖のものを使った。`crtConj_shellLift` は Part 228 の `crtConj_shellAlgTensorEquiv_tmul` から直ちに出る（B）。
候補選びの外で、宣言の文を言葉で検索して（`geps N N`・`dind N N`・`Pi.single 0 1`）、下書きの `geps_self` が Part 239（PAG243）の
同名の定理（各点の形）と同じ内容だと分かったので消した。`conv_single` は Part 107（PAG111）の `conv_single_gen` の左右を入れ替えた形に
書き直した。`dTop_eTop_dTop` は Part 247 の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と対の式。
-/
import PAG261

open Complex Finset

namespace PAG.Part262


open PAG.Part205 PAG.Part218 PAG.Part232
open ZMod (stdAddChar)
open scoped ZMod

variable {a b : ℕ} [NeZero a] [NeZero b]

/-- 互いに素な a, b で、A_a → A_{ab}、S ↦ Θ(S ⊗ 1)（Θ は Part 228 の `shellAlgTensorEquiv`）。 -/
noncomputable def shellLift (hab : a.Coprime b) : shellAlg a →ₐ[ℂ] shellAlg (a * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp
    (Algebra.TensorProduct.includeLeft : shellAlg a →ₐ[ℂ] TensorProduct ℂ (shellAlg a) (shellAlg b))

theorem shellLift_apply (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab S = shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] (1 : shellAlg b)) := rfl

/-- C(φ(S)) = L(S)（C は CRT の共役）。
内部照合（2026-11-14）：Part 228（PAG232）の `crtConj_shellAlgTensorEquiv_tmul` の T = 1 の場合で、そこから直ちに出る（Lean で確認）。 -/
theorem crtConj_shellLift (hab : a.Coprime b) (S : shellAlg a) :
    crtConj hab (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) := by
  rw [shellLift_apply, crtConj_shellAlgTensorEquiv_tmul]
  have h1 : ((1 : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) = 1 := rfl
  rw [h1, PAG.Part251.rightOp_one' a, mul_one]

omit [NeZero a] [NeZero b] in
/-- CRT の逆の点の、法 a への還元は第 1 成分。 -/
theorem castHom_crt_symm (hab : a.Coprime b) (q : ZMod a × ZMod b) :
    ZMod.castHom (dvd_mul_right a b) (ZMod a) ((ZMod.chineseRemainder hab).symm q) = q.1 := by
  have h := congrArg Prod.fst ((ZMod.chineseRemainder hab).apply_symm_apply q)
  rw [← h]
  set y := (ZMod.chineseRemainder hab).symm q
  show ZMod.castHom (dvd_mul_right a b) (ZMod a) y =
    ((ZMod.castHom (Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)) (ZMod a × ZMod b)) y).1
  rw [ZMod.castHom_apply, ZMod.castHom_apply, Prod.fst_zmod_cast]

omit [NeZero a] [NeZero b] in
theorem crtLin_pull (hab : a.Coprime b) (f : ZMod a → ℂ) (q : ZMod a × ZMod b) :
    crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) q = f q.1 := by
  rw [crtLin_apply, PAG.Part201.pull_apply, castHom_crt_symm]

/-- **条件 2（射影との両立）**：φ(S)(π^* f) = π^*(S f)（π : ℤ/ab → ℤ/a）。 -/
theorem shellLift_pull (hab : a.Coprime b) (S : shellAlg a) (f : ZMod a → ℂ) :
    (shellLift hab S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
      PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f) := by
  apply (crtLin hab).injective
  have h1 : ∀ (T : Module.End ℂ (ZMod (a * b) → ℂ)) (g : ZMod (a * b) → ℂ),
      crtLin hab (T g) = crtConj hab T (crtLin hab g) := by
    intro T g; rw [crtConj_apply, LinearEquiv.symm_apply_apply]
  rw [h1, crtConj_shellLift]
  funext p
  rw [leftOp_apply, crtLin_pull]
  have h2 : (fun x : ZMod a => crtLin hab (PAG.Part201.pull (dvd_mul_right a b) f) (x, p.2)) = f := by
    funext x; rw [crtLin_pull]
  rw [h2]

set_option synthInstance.maxHeartbeats 200000 in
/-- **条件 3（殻と両立、D）**：φ(D_s) = Σ_{u ∣ b} D_{su}（s ∣ a）。 -/
theorem shellLift_dind (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, LinearMap.mulLeft ℂ (dind (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, mulLeft_dind_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_mulLeft_dind b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_dind hab hs (Nat.dvd_of_mem_divisors hu)

set_option synthInstance.maxHeartbeats 200000 in
/-- **条件 3（殻と両立、E）**：φ(E_s) = Σ_{u ∣ b} E_{su}（s ∣ a）。 -/
theorem shellLift_geps (hab : a.Coprime b) {s : ℕ} (hs : s ∣ a) :
    (shellLift hab ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) =
      ∑ u ∈ b.divisors, PAG.Part15.convL (geps (a * b) (s * u)) := by
  have h1 : (1 : shellAlg b) = ∑ u ∈ b.divisors, (⟨_, convL_geps_mem b u⟩ : shellAlg b) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_convL_geps b).symm
  rw [shellLift_apply, h1, TensorProduct.tmul_sum, map_sum, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro u hu
  exact shellAlgTensorEquiv_geps hab hs (Nat.dvd_of_mem_divisors hu)

/-- φ は単射。 -/
theorem shellLift_injective (hab : a.Coprime b) : Function.Injective (shellLift hab) := by
  intro S S' h
  apply Subtype.ext
  apply leftHom_injective a b
  rw [leftHom_apply, leftHom_apply, ← crtConj_shellLift hab, ← crtConj_shellLift hab, h]

/-- **存在（互いに素な段）**：gcd(a, b) = 1 なら、代数準同型 φ : A_a → A_{ab} で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものがある。 -/
theorem exists_compatible_hom (hab : a.Coprime b) :
    ∃ φ : shellAlg a →ₐ[ℂ] shellAlg (a * b),
      (∀ (S : shellAlg a) (f : ZMod a → ℂ),
        (φ S : Module.End ℂ (ZMod (a * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right a b) f) =
          PAG.Part201.pull (dvd_mul_right a b) ((S : Module.End ℂ (ZMod a → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind (a * b) t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem a s⟩ : Module.End ℂ (ZMod (a * b) → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps (a * b) t))) := by
  refine ⟨shellLift hab, shellLift_pull hab, fun s => ?_, fun s => ?_⟩
  · by_cases hs : s ∣ a
    · rw [shellLift_dind hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, mulLeft_dind_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show LinearMap.mulLeft ℂ (dind a s) = 0
        rw [dind_eq_zero_of_not_dvd hs]; exact LinearMap.mulLeft_zero_eq_zero ℂ _
      rw [h0, map_zero]
      exact Submodule.zero_mem _
  · by_cases hs : s ∣ a
    · rw [shellLift_geps hab hs]
      exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
    · have h0 : (⟨_, convL_geps_mem a s⟩ : shellAlg a) = 0 := by
        apply Subtype.ext
        show PAG.Part15.convL (geps a s) = 0
        rw [geps_eq_zero_of_not_dvd hs, map_zero]
      rw [h0, map_zero]
      exact Submodule.zero_mem _




/-! ### 不存在の側の準備 -/

/-- δ との畳み込み：g ⋆ δ₀ = g。
内部照合（2026-11-14）：Part 107（PAG111）の `conv_single_gen`（δ₀ ⋆ g = g）の左右を、Part 15 の `conv_comm` で入れ替えたもの。 -/
theorem conv_single (M : ℕ) [NeZero M] (g : ZMod M → ℂ) :
    PAG.Part15.conv g (Pi.single 0 1) = g := by
  rw [PAG.Part15.conv_comm]; exact PAG.Part111.conv_single_gen g

/-- A_N の中の D_N（{0} の指示関数の掛け算）。 -/
noncomputable def dTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, mulLeft_dind_mem N N⟩
/-- A_N の中の E_N（定数 1/N の畳み込み）。 -/
noncomputable def eTop (N : ℕ) [NeZero N] : shellAlg N := ⟨_, convL_geps_mem N N⟩

/-- **A_N の関係**：D_N E_N D_N = (1/N) D_N。
内部照合（2026-11-14）：Part 247（PAG251）の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と対の式。前の鎖に同じ文は見つからなかった。 -/
theorem dTop_eTop_dTop (N : ℕ) [NeZero N] :
    dTop N * eTop N * dTop N = (N : ℂ)⁻¹ • dTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f; funext x
  show dind N N x * PAG.Part15.conv (geps N N) (dind N N * f) x = (N : ℂ)⁻¹ * (dind N N x * f x)
  rw [show geps N N = fun _ => (N : ℂ)⁻¹ from funext (PAG.Part243.geps_self N)]
  by_cases hx : x = 0
  · subst hx
    unfold PAG.Part15.conv
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · simp [PAG.Part251.dind_self_apply]
    · intro y _ hy
      simp [PAG.Part251.dind_self_apply, hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [PAG.Part251.dind_self_apply, hx]

/-- **E_N はべき等**。 -/
theorem eTop_mul_self (N : ℕ) [NeZero N] : eTop N * eTop N = eTop N := by
  apply Subtype.ext
  apply LinearMap.ext; intro f
  show PAG.Part15.conv (geps N N) (PAG.Part15.conv (geps N N) f) = PAG.Part15.conv (geps N N) f
  rw [← PAG.Part89.conv_assoc', geps_conv_geps]; simp

/-- D の線形結合は掛け算の作用素。 -/
theorem exists_mulLeft_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    ∃ h : ZMod M → ℂ, T = LinearMap.mulLeft ℂ h := by
  have hle : Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)) ≤
      LinearMap.range (LinearMap.mul ℂ (ZMod M → ℂ)) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨dind M t, rfl⟩
  obtain ⟨h, hh⟩ := hle hT
  exact ⟨h, hh.symm⟩

/-- E の線形結合は、ε の線形結合 g の畳み込み。 -/
theorem exists_convL_of_mem_span (M : ℕ) [NeZero M] {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :
    ∃ g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t), T = PAG.Part15.convL g := by
  have heq : (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) =
      (PAG.Part15.convL : (ZMod M → ℂ) →ₗ[ℂ] _) '' (Set.range fun t : ℕ => geps M t) := by
    rw [← Set.range_comp]; rfl
  rw [heq, Submodule.span_image] at hT
  obtain ⟨g, hg, rfl⟩ := hT
  exact ⟨g, hg, rfl⟩

/-- ε の線形結合のフーリエ変換は、双対殻の上で定数（gcd(M, ξ) だけで決まる）。 -/
theorem dft_const_on_shells (M : ℕ) [NeZero M] {g : ZMod M → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun t : ℕ => geps M t)) (ξ ξ' : ZMod M)
    (h : Nat.gcd M ξ.val = Nat.gcd M ξ'.val) : 𝓕 g ξ = 𝓕 g ξ' := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    rw [dft_geps]; unfold dind; rw [h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
  | smul c x _ hx => rw [map_smul, Pi.smul_apply, Pi.smul_apply, hx]

/-- 引き戻しの 1 は 1。 -/
theorem pull_one {N M : ℕ} (hNM : N ∣ M) : PAG.Part201.pull hNM (fun _ : ZMod N => (1 : ℂ)) = fun _ => 1 := rfl

/-- 核 H = ker(ℤ/M → ℤ/N) の元は N の倍数。 -/
theorem mem_ker_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (y : ZMod M) :
    ZMod.castHom hNM (ZMod N) y = 0 ↔ ∃ c : ZMod M, y = (N : ZMod M) * c := by
  constructor
  · intro hy
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hy
    obtain ⟨c, hc⟩ := hy
    refine ⟨(c : ZMod M), ?_⟩
    rw [← ZMod.natCast_zmod_val y, hc]; push_cast; ring
  · rintro ⟨c, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- **H の上の指標の和**：Σ_{y ∈ H} ψ(a y) = [a·N = 0]·|H|。 -/
theorem sum_ker_stdAddChar {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (a : ZMod M) :
    ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0), stdAddChar (a * y) =
      if a * (N : ZMod M) = 0 then ((univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0)).card : ℂ)
      else 0 := by
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hH
  by_cases ha : a * (N : ZMod M) = 0
  · simp only [ha, ↓reduceIte]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨c, rfl⟩ := (mem_ker_iff hNM y).mp (Finset.mem_filter.mp hy).2
    rw [← mul_assoc, ha, zero_mul, AddChar.map_zero_eq_one]
  · simp only [ha, ↓reduceIte]
    set y0 : ZMod M := (N : ZMod M)
    have hy0 : stdAddChar (a * y0) ≠ 1 := by
      intro h1
      apply ha
      rw [← AddChar.map_zero_eq_one (stdAddChar (N := M))] at h1
      exact ZMod.injective_stdAddChar h1
    have hshift : ∑ y ∈ H, stdAddChar (a * (y + y0)) = ∑ y ∈ H, stdAddChar (a * y) := by
      refine Finset.sum_equiv (Equiv.addRight y0) (fun y => ?_) (fun y _ => rfl)
      simp only [hH, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, map_add]
      have : ZMod.castHom hNM (ZMod N) y0 = 0 := by
        rw [map_natCast, ZMod.natCast_self]
      rw [this, add_zero]
    have hmul : ∑ y ∈ H, stdAddChar (a * (y + y0)) = stdAddChar (a * y0) * ∑ y ∈ H, stdAddChar (a * y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [mul_add, AddChar.map_add_eq_mul, mul_comm]
    have h0 : (stdAddChar (a * y0) - 1) * ∑ y ∈ H, stdAddChar (a * y) = 0 := by
      rw [sub_mul, ← hmul, hshift, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hy0
    · exact h

/-- p ∣ N、p ∣ M/N なら p² ∣ M、したがって p ∣ M/p。 -/
theorem p_dvd_div_p {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) : p ∣ M / p := by
  have hM : M = N * (M / N) := (Nat.mul_div_cancel' hNM).symm
  have hpp : p * p ∣ M := by rw [hM]; exact Nat.mul_dvd_mul hpN hpk
  exact Nat.dvd_div_of_mul_dvd hpp

/-- x = M/p（ℤ/M の中）で x² = 0。 -/
theorem sq_x_eq_zero {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) (hpk : p ∣ M / N) :
    ((M / p : ℕ) : ZMod M) * ((M / p : ℕ) : ZMod M) = 0 := by
  obtain ⟨r, hr⟩ := p_dvd_div_p hNM hpN hpk
  have hpM : p ∣ M := (hpN.trans hNM)
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨r, ?_⟩
  calc M / p * (M / p) = M / p * (p * r) := by rw [← hr]
    _ = M / p * p * r := by ring
    _ = M * r := by rw [Nat.div_mul_cancel hpM]

/-- x·N = 0（p ∣ N）。 -/
theorem x_mul_N {N M p : ℕ} [NeZero M] (hNM : N ∣ M) (hpN : p ∣ N) :
    ((M / p : ℕ) : ZMod M) * (N : ZMod M) = 0 := by
  have hpM : p ∣ M := (hpN.trans hNM)
  obtain ⟨c, hc⟩ := hpN
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  refine ⟨c, ?_⟩
  calc M / p * N = M / p * (p * c) := by rw [← hc]
    _ = M / p * p * c := by ring
    _ = M * c := by rw [Nat.div_mul_cancel hpM]

/-- (ξ − 1)·N = 0（ξ ≡ 1 mod M/N）なら ξ·x ≠ 0（p ∤ ξ）。 -/
theorem mul_x_ne_zero {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) (ξ : ZMod M) (hξ : (ξ - 1) * (N : ZMod M) = 0) :
    ξ * ((M / p : ℕ) : ZMod M) ≠ 0 := by
  intro h0
  have hpM : p ∣ M := (hpN.trans hNM)
  set v := ξ.val
  have hξv : ((v : ℕ) : ZMod M) = ξ := ZMod.natCast_zmod_val ξ
  -- p ∣ v
  have h1 : p ∣ v := by
    rw [← hξv, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
    have hpos : 0 < M / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) hp.pos
    have h0' : M / p * p ∣ M / p * v := by
      rw [Nat.div_mul_cancel hpM, mul_comm (M / p)]; exact h0
    exact Nat.dvd_of_mul_dvd_mul_left hpos h0'
  -- p ∣ v − 1（整数で）
  have h2 : (p : ℤ) ∣ (v : ℤ) - 1 := by
    have e : (((((v : ℤ) - 1) * (N : ℤ)) : ℤ) : ZMod M) = 0 := by
      push_cast; rw [hξv]; exact hξ
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at e
    have hM : (M : ℤ) = (N : ℤ) * ((M / N : ℕ) : ℤ) := by exact_mod_cast (Nat.mul_div_cancel' hNM).symm
    rw [hM, mul_comm ((v : ℤ) - 1)] at e
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have hk : ((M / N : ℕ) : ℤ) ∣ (v : ℤ) - 1 := (mul_dvd_mul_iff_left hN0).mp e
    exact (Int.natCast_dvd_natCast.mpr hpk).trans hk
  have h3 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (Int.natCast_dvd_natCast.mpr h1) h2
    simpa using this
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h3)

/-- **不存在（gcd(N, M/N) > 1 の段）**：素数 p が N と M/N の両方を割るなら、代数準同型 φ : A_N → A_M で、
(i) すべての S で φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合、を満たすものはない。
証明に使うのは s = N の D_N・E_N と、A_N の関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけ。 -/
theorem no_compatible_hom {N M p : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) (hp : p.Prime) (hpN : p ∣ N)
    (hpk : p ∣ M / N) :
    ¬ ∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) := by
  rintro ⟨φ, h2, hD, hE⟩
  obtain ⟨h, hh⟩ := exists_mulLeft_of_mem_span M (hD N)
  obtain ⟨g, hg, hgg⟩ := exists_convL_of_mem_span M (hE N)
  change (φ (dTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hh
  change (φ (eTop N) : Module.End ℂ (ZMod M → ℂ)) = _ at hgg
  -- φ(D_N) は H = ker(ℤ/M → ℤ/N) の指示関数の掛け算
  have hH : ∀ y, h y = dind N N (ZMod.castHom hNM (ZMod N) y) := by
    intro y
    have e := congrFun (h2 (dTop N) (fun _ => 1)) y
    rw [hh] at e
    simpa [PAG.Part201.pull_apply, dTop] using e
  -- φ(E_N) はべき等なので、m = 𝓕 g は 0 か 1
  have hidem : PAG.Part15.conv g g = g := by
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (eTop_mul_self N)
    simp only [map_mul, Subalgebra.coe_mul, hgg] at e
    have e2 := LinearMap.congr_fun e (Pi.single 0 1)
    simpa [PAG.Part15.convL_apply, conv_single] using e2
  set m := 𝓕 g with hm
  have hm01 : ∀ ξ, m ξ = 0 ∨ m ξ = 1 := by
    intro ξ
    have e := congrFun (congrArg 𝓕 hidem) ξ
    rw [PAG.Part16.dft_conv, Pi.mul_apply] at e
    have : m ξ * (m ξ - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  -- 関係 D_N E_N D_N = (1/N) D_N を φ で送り、δ₀ に当てる：H の上で g = (1/N)·δ₀
  have hδ : h * Pi.single 0 1 = Pi.single 0 1 := by
    funext z
    by_cases hz : z = 0
    · subst hz; simp [hH, PAG.Part251.dind_self_apply]
    · simp [hz]
  have hgH : ∀ y, ZMod.castHom hNM (ZMod N) y = 0 → g y = (N : ℂ)⁻¹ * (if y = 0 then 1 else 0) := by
    intro y hy
    have e := congrArg (fun S : shellAlg N => ((φ S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)))
      (dTop_eTop_dTop N)
    simp only [map_mul, map_smul, Subalgebra.coe_mul, Subalgebra.coe_smul, hh, hgg] at e
    have e2 := congrFun (LinearMap.congr_fun e (Pi.single 0 1)) y
    have hy1 : h y = 1 := by rw [hH, hy, PAG.Part251.dind_self_apply]; simp
    have key1 : ∀ F : ZMod M → ℂ, (LinearMap.mulLeft ℂ h * PAG.Part15.convL g * LinearMap.mulLeft ℂ h) F =
        h * PAG.Part15.conv g (h * F) := fun F => rfl
    have key2 : ∀ F : ZMod M → ℂ, ((N : ℂ)⁻¹ • LinearMap.mulLeft ℂ h) F = (N : ℂ)⁻¹ • (h * F) := fun F => rfl
    rw [key1, key2, hδ, conv_single, Pi.mul_apply, Pi.smul_apply, hy1, one_mul, smul_eq_mul] at e2
    rw [e2]
    by_cases hy0 : y = 0
    · subst hy0; simp
    · simp [hy0]
  -- フーリエの逆変換
  have hginv : ∀ y, g y = (M : ℂ)⁻¹ * ∑ ξ, stdAddChar (ξ * y) * m ξ := by
    intro y
    have e : 𝓕⁻ m = g := by rw [hm]; exact (ZMod.dft).symm_apply_apply g
    rw [← e, ZMod.invDFT_apply]
    simp [smul_eq_mul]
  set H := univ.filter (fun y : ZMod M => ZMod.castHom hNM (ZMod N) y = 0) with hHdef
  set C1 := univ.filter (fun ξ : ZMod M => (ξ - 1) * (N : ZMod M) = 0) with hC1def
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- 数え上げ：|H|·Σ_{ξ ≡ 1 (mod M/N)} m(ξ) = M/N
  have hS1 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (M : ℂ) * (N : ℂ)⁻¹ := by
    rw [Finset.sum_eq_single (0 : ZMod M)]
    · rw [hgH 0 (map_zero _)]; simp
    · intro y hyH hy0
      rw [hgH y (Finset.mem_filter.mp hyH).2]; simp [hy0]
    · intro h0
      have h0H : (0 : ZMod M) ∈ H := by
        rw [hHdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, map_zero _⟩
      exact absurd h0H h0
  have hS2 : ∑ y ∈ H, stdAddChar (-y) * ((M : ℂ) * g y) = (H.card : ℂ) * ∑ ξ ∈ C1, m ξ := by
    have step : ∀ y, stdAddChar (-y) * ((M : ℂ) * g y) = ∑ ξ, m ξ * stdAddChar ((ξ - 1) * y) := by
      intro y
      rw [hginv, ← mul_assoc (M : ℂ), mul_inv_cancel₀ hM, one_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [sub_mul, one_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun y _ => step y), Finset.sum_comm]
    have hinner : ∀ ξ, ∑ y ∈ H, m ξ * stdAddChar ((ξ - 1) * y) =
        m ξ * (if (ξ - 1) * (N : ZMod M) = 0 then (H.card : ℂ) else 0) := by
      intro ξ; rw [← Finset.mul_sum]; congr 1; exact sum_ker_stdAddChar hNM (ξ - 1)
    rw [Finset.sum_congr rfl (fun ξ _ => hinner ξ), hC1def, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ξ _
    split_ifs <;> ring
  have hcard : (H.card : ℂ) * N = M := by
    have := PAG.Part201.card_ker_cast (N := N) (N' := M) hNM
    exact this
  have hC1 : ∑ ξ ∈ C1, m ξ = 1 := by
    have e := hS2.symm.trans hS1
    have hHc : (H.card : ℂ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; exact hM hcard.symm
    have : (H.card : ℂ) * ∑ ξ ∈ C1, m ξ = (H.card : ℂ) * 1 := by
      rw [e, ← hcard]; field_simp
    exact mul_left_cancel₀ hHc this
  have hS : ∑ ξ ∈ C1, m ξ = ((C1.filter (fun ξ => m ξ = 1)).card : ℂ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter (fun ξ => m ξ = 1)]
    apply Finset.sum_congr rfl
    intro ξ _
    rcases hm01 ξ with h0 | h1
    · simp [h0]
    · simp [h1]
  have hone : (C1.filter (fun ξ => m ξ = 1)).card = 1 := by
    have := hS.symm.trans hC1
    exact_mod_cast this
  obtain ⟨ξ0, hξ0⟩ := Finset.card_eq_one.mp hone
  have hξ0mem : ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by rw [hξ0]; exact Finset.mem_singleton_self _
  -- もう 1 つの元 ξ1 = (1 + M/p)·ξ0
  set x : ZMod M := ((M / p : ℕ) : ZMod M) with hx
  have hx2 : x * x = 0 := sq_x_eq_zero hNM hpN hpk
  have hxN : x * (N : ZMod M) = 0 := x_mul_N hNM hpN
  let u : (ZMod M)ˣ := ⟨1 + x, 1 - x, by linear_combination (-1 : ZMod M) * hx2,
    by linear_combination (-1 : ZMod M) * hx2⟩
  have hξ1mem : (u : ZMod M) * ξ0 ∈ C1.filter (fun ξ => m ξ = 1) := by
    simp only [hC1def, Finset.mem_filter, Finset.mem_univ, true_and] at hξ0mem ⊢
    refine ⟨?_, ?_⟩
    · show ((1 + x) * ξ0 - 1) * (N : ZMod M) = 0
      linear_combination hξ0mem.1 + ξ0 * hxN
    · rw [← hξ0mem.2]
      exact dft_const_on_shells M hg _ _ (PAG.Part207.gcd_val_unit_mul M u ξ0)
  have hne : (u : ZMod M) * ξ0 ≠ ξ0 := by
    intro e
    have hξ0C : (ξ0 - 1) * (N : ZMod M) = 0 := by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hξ0mem).1).2
      exact this
    apply mul_x_ne_zero hNM hp hpN hpk ξ0 hξ0C
    have e' : (1 + x) * ξ0 = ξ0 := e
    linear_combination e'
  have : (u : ZMod M) * ξ0 ∈ ({ξ0} : Finset (ZMod M)) := hξ0 ▸ hξ1mem
  exact hne (Finset.mem_singleton.mp this)


/-! ### 二分法 -/

/-- **二分法**：N ∣ M のとき、(i)(ii) を満たす代数準同型 A_N → A_M があるのは、gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem exists_compatible_hom_iff {N M : ℕ} [NeZero N] [NeZero M] (hNM : N ∣ M) :
    (∃ φ : shellAlg N →ₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
          PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
      (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
        Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))) ↔
    Nat.Coprime N (M / N) := by
  constructor
  · intro hex
    by_contra hc
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hc
    exact no_compatible_hom hNM hp (hpd.trans (Nat.gcd_dvd_left _ _)) (hpd.trans (Nat.gcd_dvd_right _ _)) hex
  · intro hc
    rcases hNM with ⟨k, rfl⟩
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    rw [Nat.mul_div_cancel_left k hN0] at hc
    have : NeZero k := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
    exact exists_compatible_hom hc

end PAG.Part262

#print axioms PAG.Part262.shellLift_apply
#print axioms PAG.Part262.crtConj_shellLift
#print axioms PAG.Part262.castHom_crt_symm
#print axioms PAG.Part262.crtLin_pull
#print axioms PAG.Part262.shellLift_pull
#print axioms PAG.Part262.shellLift_dind
#print axioms PAG.Part262.shellLift_geps
#print axioms PAG.Part262.shellLift_injective
#print axioms PAG.Part262.exists_compatible_hom
#print axioms PAG.Part262.conv_single
#print axioms PAG.Part262.dTop_eTop_dTop
#print axioms PAG.Part262.eTop_mul_self
#print axioms PAG.Part262.exists_mulLeft_of_mem_span
#print axioms PAG.Part262.exists_convL_of_mem_span
#print axioms PAG.Part262.dft_const_on_shells
#print axioms PAG.Part262.pull_one
#print axioms PAG.Part262.mem_ker_iff
#print axioms PAG.Part262.sum_ker_stdAddChar
#print axioms PAG.Part262.p_dvd_div_p
#print axioms PAG.Part262.sq_x_eq_zero
#print axioms PAG.Part262.x_mul_N
#print axioms PAG.Part262.mul_x_ne_zero
#print axioms PAG.Part262.no_compatible_hom
#print axioms PAG.Part262.exists_compatible_hom_iff

```
# B. PAG262.out
```
'PAG.Part262.shellLift_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.crtConj_shellLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.castHom_crt_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.crtLin_pull' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.shellLift_pull' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.shellLift_dind' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.shellLift_geps' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.shellLift_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.exists_compatible_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.conv_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.dTop_eTop_dTop' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.eTop_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.exists_mulLeft_of_mem_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.exists_convL_of_mem_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.dft_const_on_shells' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.pull_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.mem_ker_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.sum_ker_stdAddChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.p_dvd_div_p' depends on axioms: [propext]
'PAG.Part262.sq_x_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.x_mul_N' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.mul_x_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.no_compatible_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'PAG.Part262.exists_compatible_hom_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

```
# C. 使った前の鎖の宣言（形式文の全文）
### PAG15（名前空間 PAG.Part15）::conv
```lean
def conv (f g : G → K) : G → K := fun x => ∑ y, f y * g (x - y)
```

### PAG15（名前空間 PAG.Part15）::convL
```lean
def convL : (G → K) →ₗ[K] (G → K) →ₗ[K] (G → K) :=
  LinearMap.mk₂ K conv
    (fun f₁ f₂ g => by funext x; simp [conv, add_mul, sum_add_distrib])
    (fun c f g => by funext x; simp [conv, mul_sum, mul_assoc])
    (fun f g₁ g₂ => by funext x; simp [conv, mul_add, sum_add_distrib])
    (fun c f g => by funext x; simp [conv, mul_sum, mul_left_comm])
```

### PAG15（名前空間 PAG.Part15）::conv_comm
```lean
theorem conv_comm (f g : G → K) : conv f g = conv g f
```

### PAG16（名前空間 PAG.Part16）::dft_conv
```lean
theorem dft_conv (f g : ZMod N → ℂ) : 𝓕 (PAG.Part15.conv f g) = 𝓕 f * 𝓕 g
```

### PAG201（名前空間 PAG.Part201）::pull
```lean
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom
```

### PAG201（名前空間 PAG.Part201）::card_ker_cast
```lean
theorem card_ker_cast {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') :
    ((Finset.univ.filter (fun z : ZMod N' => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).card : ℂ)
      * N = N'
```

### PAG205（名前空間 PAG.Part205）::dind
```lean
noncomputable def dind (N s : ℕ) : ZMod N → ℂ := fun ξ => if Nat.gcd N ξ.val = s then 1 else 0
```

### PAG205（名前空間 PAG.Part205）::geps
```lean
noncomputable def geps (N s : ℕ) [NeZero N] : ZMod N → ℂ := 𝓕⁻ (dind N s)
```

### PAG205（名前空間 PAG.Part205）::dft_geps
```lean
theorem dft_geps (N s : ℕ) [NeZero N] : 𝓕 (geps N s) = dind N s
```

### PAG205（名前空間 PAG.Part205）::geps_conv_geps
```lean
theorem geps_conv_geps (N s s' : ℕ) [NeZero N] :
    PAG.Part15.conv (geps N s) (geps N s') = if s = s' then geps N s else 0
```

### PAG207（名前空間 PAG.Part207）::gcd_val_unit_mul
```lean
theorem gcd_val_unit_mul (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (x : ZMod N) :
    Nat.gcd N ((a : ZMod N) * x).val = Nat.gcd N x.val
```

### PAG218（名前空間 PAG.Part218）::shellAlg
```lean
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))
```

### PAG232（名前空間 PAG.Part232）::crtLin
```lean
noncomputable def crtLin {a b : ℕ} (hab : Nat.Coprime a b) : (ZMod (a * b) → ℂ) ≃ₗ[ℂ] (ZMod a × ZMod b → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (ZMod.chineseRemainder hab).symm.toEquiv
```

### PAG232（名前空間 PAG.Part232）::crtConj
```lean
noncomputable def crtConj {a b : ℕ} (hab : Nat.Coprime a b) :
    Module.End ℂ (ZMod (a * b) → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  (crtLin hab).conjAlgEquiv ℂ
```

### PAG232（名前空間 PAG.Part232）::leftOp
```lean
noncomputable def leftOp {a : ℕ} (b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := S (fun x => F (x, p.2)) p.1
  map_add' F G := by
    funext p
    show S ((fun x => F (x, p.2)) + (fun x => G (x, p.2))) p.1 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show S (c • (fun x => F (x, p.2))) p.1 = _
    rw [map_smul]
    rfl
```

### PAG232（名前空間 PAG.Part232）::rightOp
```lean
noncomputable def rightOp (a : ℕ) {b : ℕ} (T : Module.End ℂ (ZMod b → ℂ)) : Module.End ℂ (ZMod a × ZMod b → ℂ) where
  toFun F p := T (fun y => F (p.1, y)) p.2
  map_add' F G := by
    funext p
    show T ((fun y => F (p.1, y)) + (fun y => G (p.1, y))) p.2 = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext p
    show T (c • (fun y => F (p.1, y))) p.2 = _
    rw [map_smul]
    rfl
```

### PAG232（名前空間 PAG.Part232）::leftHom
```lean
noncomputable def leftHom (a b : ℕ) : Module.End ℂ (ZMod a → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := leftOp b
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)
```

### PAG232（名前空間 PAG.Part232）::rightHom
```lean
noncomputable def rightHom (a b : ℕ) : Module.End ℂ (ZMod b → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod a × ZMod b → ℂ) :=
  AlgHom.ofLinearMap
    { toFun := rightOp a
      map_add' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl }
    (LinearMap.ext fun _ => funext fun _ => rfl)
    (fun _ _ => LinearMap.ext fun _ => funext fun _ => rfl)
```

### PAG232（名前空間 PAG.Part232）::leftHom_injective
```lean
theorem leftHom_injective (a b : ℕ) [NeZero b] : Function.Injective (leftHom a b)
```

### PAG232（名前空間 PAG.Part232）::sum_convL_geps
```lean
theorem sum_convL_geps (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, PAG.Part15.convL (geps N s) = 1
```

### PAG232（名前空間 PAG.Part232）::sum_mulLeft_dind
```lean
theorem sum_mulLeft_dind (N : ℕ) [NeZero N] : ∑ s ∈ N.divisors, LinearMap.mulLeft ℂ (dind N s) = 1
```

### PAG232（名前空間 PAG.Part232）::convL_geps_mem
```lean
theorem convL_geps_mem (N s : ℕ) [NeZero N] : PAG.Part15.convL (geps N s) ∈ shellAlg N
```

### PAG232（名前空間 PAG.Part232）::mulLeft_dind_mem
```lean
theorem mulLeft_dind_mem (N s : ℕ) [NeZero N] : LinearMap.mulLeft ℂ (dind N s) ∈ shellAlg N
```

### PAG232（名前空間 PAG.Part232）::shellAlgTensorEquiv
```lean
noncomputable def shellAlgTensorEquiv {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) :
    TensorProduct ℂ (shellAlg a) (shellAlg b) ≃ₐ[ℂ] shellAlg (a * b) :=
  ((AlgEquiv.ofInjective (tensLift a b) (tensLift_injective hab)).trans
    (Subalgebra.equivOfEq _ _ (range_tensLift hab))).trans
    (Subalgebra.equivMapOfInjective (shellAlg (a * b)) (crtConj hab).toAlgHom (crtConj hab).injective).symm
```

### PAG232（名前空間 PAG.Part232）::crtConj_shellAlgTensorEquiv_tmul
```lean
theorem crtConj_shellAlgTensorEquiv_tmul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b)
    (S : shellAlg a) (T : shellAlg b) :
    crtConj hab (shellAlgTensorEquiv hab (S ⊗ₜ[ℂ] T) : Module.End ℂ (ZMod (a * b) → ℂ)) =
      leftOp b (S : Module.End ℂ (ZMod a → ℂ)) * rightOp a (T : Module.End ℂ (ZMod b → ℂ))
```

### PAG232（名前空間 PAG.Part232）::shellAlgTensorEquiv_geps
```lean
theorem shellAlgTensorEquiv_geps {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ}
    (hsa : sa ∣ a) (hsb : sb ∣ b) :
    (shellAlgTensorEquiv hab (⟨_, convL_geps_mem a sa⟩ ⊗ₜ[ℂ] ⟨_, convL_geps_mem b sb⟩) :
      Module.End ℂ (ZMod (a * b) → ℂ)) = PAG.Part15.convL (geps (a * b) (sa * sb))
```

### PAG232（名前空間 PAG.Part232）::shellAlgTensorEquiv_dind
```lean
theorem shellAlgTensorEquiv_dind {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {sa sb : ℕ}
    (hsa : sa ∣ a) (hsb : sb ∣ b) :
    (shellAlgTensorEquiv hab (⟨_, mulLeft_dind_mem a sa⟩ ⊗ₜ[ℂ] ⟨_, mulLeft_dind_mem b sb⟩) :
      Module.End ℂ (ZMod (a * b) → ℂ)) = LinearMap.mulLeft ℂ (dind (a * b) (sa * sb))
```

### PAG232（名前空間 PAG.Part232）::dind_eq_zero_of_not_dvd
```lean
theorem dind_eq_zero_of_not_dvd {N s : ℕ} [NeZero N] (hs : ¬ s ∣ N) : dind N s = 0
```

### PAG232（名前空間 PAG.Part232）::geps_eq_zero_of_not_dvd
```lean
theorem geps_eq_zero_of_not_dvd {N s : ℕ} [NeZero N] (hs : ¬ s ∣ N) : geps N s = 0
```

### PAG232（名前空間 PAG.Part232）::crtLin_apply
```lean
theorem crtLin_apply {a b : ℕ} (hab : Nat.Coprime a b) (f : ZMod (a * b) → ℂ) (p : ZMod a × ZMod b) :
    crtLin hab f p = f ((ZMod.chineseRemainder hab).symm p)
```

### PAG243（名前空間 PAG.Part243）::geps_self
```lean
theorem geps_self (N : ℕ) [NeZero N] (x : ZMod N) : geps N N x = (N : ℂ)⁻¹
```

### PAG251（名前空間 PAG.Part251）::dind_self_apply
```lean
theorem dind_self_apply (N : ℕ) [NeZero N] (y : ZMod N) : dind N N y = if y = 0 then 1 else 0
```

### PAG251（名前空間 PAG.Part251）::rightOp_one'
```lean
theorem rightOp_one' (a : ℕ) {b : ℕ} : PAG.Part232.rightOp a (1 : Module.End ℂ (ZMod b → ℂ)) = 1
```

### PAG251（名前空間 PAG.Part251）::convL_geps_self_mul_mulLeft_dind_self
```lean
theorem convL_geps_self_mul_mulLeft_dind_self (N : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N N) * LinearMap.mulLeft ℂ (dind N N) * PAG.Part15.convL (geps N N) =
      (1 / (N : ℂ)) • PAG.Part15.convL (geps N N)
```

### PAG111（名前空間 PAG.Part111）::conv_single_gen
```lean
theorem conv_single_gen (g : G → ℂ) : conv (Pi.single 0 1) g = g
```

### PAG89（名前空間 PAG.Part89）::conv_assoc'
```lean
theorem conv_assoc' {N : ℕ} [NeZero N] (f g h : ZMod N → ℂ) : conv (conv f g) h = conv f (conv g h)
```

# D. ノート（全文）
# アーデル射影幾何 — Part 258（PAG 2.0）：方向βの前提 — N ∣ M で、引き戻しと両立し殻を混ぜない代数準同型 A_N → A_M があるのは gcd(N, M/N) = 1 のときに限る（存在の側は既知、不存在の側は文献が見つからなかった）

2026-11-14 夜。PAG262.lean（定理 24 個、定義 3 個）、step281.py（段階 2 の数値、13 組）。

- **問いの出所。** 著者側の申し送り補足7（2026-11-14）の決定（委任のもと）：次のパートは方向βの前提を問う。登録 `preregistration-part255-beta-premise.md` の 3 段階を、突き合わせの記録 `pag2_beta_registration_check.md` §3 の切り分けで修正して行った。着手前の文書は `pag2_part258_preregistration.md`（予想 §6、段階 1・2 の結果 §8、閉鎖条件 §9）。
- **問いと答えの範囲。** 幾何の言葉の問い（読み）：見方を変える（N を上げる）操作は、代数の側で 1 つの写像として実現できるか。Lean が答えるのは、登録の受容条件を次の形で読んだときの、写像の存在と不存在です。
  - (1) 代数準同型 φ : A_N →ₐ[ℂ] A_M（単位元を保つ）。
  - (2) 射影と両立：すべての S ∈ A_N で φ(S) π^* = π^* S（π^* は ℤ/M → ℤ/N に沿った引き戻し）。
  - (3) 殻を混ぜない（強い読み）：φ(D_s) は D_t の線形結合、φ(E_s) は E_t の線形結合。
  - この読み（とくに (3) を強い読みにしたこと）は構築者のもので、著者に確かめる事項です。
- **結論（Lean の文）。**
  1. **存在（gcd(N, M/N) = 1）。** M = N·b、gcd(N, b) = 1 なら、φ(S) = Θ(S ⊗ 1)（Θ は Part 228 の A_N ⊗ A_b ≅ A_{Nb}）が (1)〜(3) を満たします（`exists_compatible_hom`）。明示の形は φ(D_s) = Σ_{u ∣ b} D_{su}、φ(E_s) = Σ_{u ∣ b} E_{su}（`shellLift_dind`・`shellLift_geps`）。φ は単射です（`shellLift_injective`）。
  2. **不存在（素数 p が N と M/N の両方を割る）。** (1)〜(3) を満たす φ はありません（`no_compatible_hom`）。素数冪の段 p^e → p^{e+f}（e, f ≥ 1）はここに入ります。
  3. **二分法。** N ∣ M のとき、(1)〜(3) を満たす φ がある ⇔ gcd(N, M/N) = 1（`exists_compatible_hom_iff`）。
  - sorry 0、警告 0。`#print axioms` 24 行（定理と同数）は標準の公理の範囲です（23 行が [propext, Classical.choice, Quot.sound]、1 行が [propext]）。
- **不存在の証明の筋（Lean の文の中身）。** 使うのは A_N の D_N（{0} の指示関数の掛け算）・E_N（定数 1/N の畳み込み）と、関係 D_N E_N D_N = (1/N) D_N、E_N² = E_N だけです。
  - (2) と (3) から、φ(D_N) は核 H = ker(ℤ/M → ℤ/N) の指示関数の掛け算、φ(E_N) は ε の線形結合 g の畳み込みで、フーリエ変換 m = 𝓕g は双対殻の上で定数、値は 0 か 1。
  - 関係を φ で送って δ₀ に当てると、H の上で g = (1/N)·δ₀。H の上の指標の和で数えると、ξ ≡ 1 (mod M/N) の剰余類に m = 1 の点がちょうど 1 つ。
  - ところが u = 1 + M/p は ℤ/M の単数で（(M/p)² ≡ 0）、ξ ↦ uξ はその剰余類と双対殻を保ち、点を動かす（p ∤ ξ のため）。点が 2 つになり矛盾。
- **読み（解釈の言葉。Lean の文ではない）。** 「見方を変える操作が代数の写像として実現できるか」への答えは、互いに素な段（新しい素数を加える）では「できる（テンソル積の左の因子として）」、同じ素数の深さを上げる段では「(1)〜(3) の意味ではできない」です。したがって、N を整除の順に上げていく A_N の帰納系は、(1)〜(3) の写像では組めません。β（A_N の N → ∞ の極限の代数）を (1)〜(3) の写像の帰納極限として立てる道は、素数冪の段で閉じます。登録 §3 の言葉では「不存在の側」の判定です。ただし、(3) の弱い読み（像が A_M に入るだけ）、単位元を保たない写像、(2) を別の形にした写像は、この答えの外です。
- **公準 A1 との関係。** A1 は公準のままです。ここでの文は A_N についての代数の事実で、A1 とは関係しません。
- **位置づけ。** 存在の側は既知です（スキームの直積の Terwilliger 代数はテンソル積：Hanaki–Kim–Maekawa, Terwilliger algebras of direct and wreath products of association schemes, Theorem 3.1。鎖では Part 228。確信度：高）。不存在の側は、着手前の盲検の問いテストで文献が見つかりませんでした（確信度：中。見つからなかったというだけ）。議論は初等的です。ラベル（［再導出］か［新規候補（小さい）］か）は著者の判断事項です。

## 0. 内容

### 0.0 ハンドシェイク（CLAUDE.md §0）

- (a) 形式化済み：Part 214（PAG218）の A_N（`shellAlg`）、Part 201 の `geps`・`dind`、Part 228（PAG232）の A_a ⊗ A_b ≅ A_{ab}、Part 197 の引き戻し `pull`、Part 202 の関数のレベルの引き戻しの事実。
- (b) 著者の解釈の層：§1 の新しい置き方（素点たちは制限積の因子として並列に共存し、有限レベル商はその「見方」）。A1 は公準。
- (c) 未完の大域の問い：β（A_N の極限の代数）、Ẑ の上の定理 A、有限レベルの Bost–Connes（方向γの文献照合は未実施）。

### 0.1 4 点（着手前の文書 §1〜§4 から）

1. 幾何の言葉：見方を変える操作は代数の写像として実現できるか。
2. 既存分野の言葉への最善の翻訳：円分的なスキームの Terwilliger 代数 T(0) の、商 ℤ/M → ℤ/N に沿った代数準同型の存在。互いに素な段は直積の定理。
3. 残余：素数冪の段での存在問題（登録の残余を、内部照合で切り分けたもの）。
4. 対照群：F_q[t]/(t^e) → F_q[t]/(t^{e−1}) でも同じ理由で不存在、互いに素の類似では存在（盲検の手計算。私は計算していない）。したがって答えは ℚ に固有の算術ではなく、群・環の形から決まる（登録 §4 の判定：「β の前提の判定」としての価値は変わらないが、「アーデル射影幾何に固有の内容」としては数えない）。

### 0.2 定義（PAG262.lean）

| 記号 | Lean | 内容 |
|---|---|---|
| φ（互いに素） | `shellLift hab` | S ↦ Θ(S ⊗ 1)、A_a →ₐ A_{ab} |
| D_N | `dTop N` | {0} の指示関数の掛け算（A_N の元） |
| E_N | `eTop N` | 定数 1/N の畳み込み（A_N の元） |

### 0.3 ラベル（CLAUDE.md §7）

| 結果 | ラベル | 根拠 |
|---|---|---|
| 互いに素な段で写像がある | 既知 | Hanaki–Kim–Maekawa Theorem 3.1、鎖の Part 228 |
| gcd > 1 で写像はない、二分法 | 著者の判断事項（構築者の見立て：［再導出］か［新規候補（小さい）］） | 盲検で文献が見つからない（確信度 中）。議論は初等的 |
| 「見方を変える」「β の前提が閉じる」の読み | 著者の解釈の層と読み | — |

## 1. 検証表

| 主張 | Lean | 数値（step281） | 新規性 |
|---|---|---|---|
| 互いに素な段の写像と条件 2・3 | `shellLift`・`crtConj_shellLift`・`shellLift_pull`・`shellLift_dind`・`shellLift_geps`・`shellLift_injective`・`exists_compatible_hom` | (2,6)・(3,6)・(2,10)・(3,12)・(4,12) で CRT の写像が条件を満たす | 既知 |
| gcd > 1 で写像はない | `no_compatible_hom`（補助：`dTop_eTop_dTop`・`eTop_mul_self`・`exists_mulLeft_of_mem_span`・`exists_convL_of_mem_span`・`dft_const_on_shells`・`mem_ker_iff`・`sum_ker_stdAddChar`・`p_dvd_div_p`・`sq_x_eq_zero`・`x_mul_N`・`mul_x_ne_zero`・`conv_single`） | (2,4)・(2,8)・(3,9)・(4,8)・(6,12)・(2,12)・(6,18)・(9,27) で全数探索して 0 | 著者の判断事項 |
| 二分法 | `exists_compatible_hom_iff` | 13 組すべてで一致 | 著者の判断事項 |
| 単位元を保たない版 | Lean にしていない | 条件から自動的に単位元を保つ（数値） | — |
| 互いに素な組で CRT 以外の写像もある | Lean にしていない | (2,6)・(2,10)・(4,12) で割り当てが 2 つ | — |
| (3) の弱い読み、(2) を外したとき、F_q[t] | Lean にしていない | なし | — |

## 2. 数値照合（step281.py ＝ 着手前の段階 2 の `stage2.py`）

- (3) の強い読みでは、条件 2 から φ(D_s) が決まり、φ(E_s) は V（N 周期の関数）の双対殻の上で決まる。残りの双対殻の割り当てを全数で調べ、A_N の関係（語の基底での積の表）を像が満たすかを確かめた。
- 結果は上の表のとおり（13 組）。(2,4) の障害は手計算でも確かめた（A_2 = M_2(ℂ) で、階数 1 のべき等元の像の階数は 2 でなければならないが、φ(E_2) は階数 1 か 3）。
- 数値の確認は証明ではありません（Lean の二分法で置き換わった）。

## 3. Lean（PAG262.lean）

- import は PAG261。名前空間は `PAG.Part262`。
- 下書き：`scratch/t258/T1.lean`（存在）、`T2.lean`（不存在）、`T3.lean`（合わせたもの）。直したもの：
  - `AddSubmonoidClass.coe_finset_sum` はこの Mathlib では `coe_finsetSum`。AlgEquiv の `map_sum` で instance の探索が時間切れ（`synthInstance.maxHeartbeats` を上げた）。
  - `rw` の motive の型エラー（gcd の書き換えが `ZMod.val` の暗黙の法まで書き換えた）→ `rwa … at` に変えた。
  - `change` が時間切れ → 作用素の積の値を `rfl` の補題に分けた。
  - `set` で置いた Finset に、filter の形の補題が当たらない → 補題を明示の引数で当てた。
- 閉じる前の内部照合で、下書きの 3 つの宣言が前の鎖と同じ文・同じ内容だったので消した（§7）。
- sorry 0、警告 0、`#print axioms` 24 行。鎖全体（PAG.lean〜PAG262.lean）は theorem/lemma 3,574（Part 257 の後の 3,550 に 24 を足した数）。

## 4. 残る問い（本来の道）

- (3) の弱い読み（殻を混ぜてよい写像）や、(2) を別の形にした写像（たとえば引き戻しではなく押し出しとの両立）で、素数冪の段の写像があるか。β の前提を別の形で立て直すなら、ここから。
- 関数のレベルの帰納系（Part 197・202、極限 ℂ[ℚ/ℤ]）と、代数のレベルの関係。互いに素な段だけの帰納系（新しい素数を加える向き）は、テンソル積の帰納極限として組める見込み（Lean にしていない）。
- 方向γ（帰納系が T(0) の側に届く記述が文献にあるか）の文献照合は未実施。
- 次のパートは著者の選択を待ちます（Part 259 は始めていません）。

## 5. 文献の確認の記録

- 着手前の盲検の問いテスト（2026-11-14 22:4x〜、WebSearch・WebFetch 10 回、`prereg258/outputs/blind_output.md`）：
  - 開いたもの：Hanaki–Kim–Maekawa（直積・wreath 積の Terwilliger 代数、プレプリント）、Bastian–Humphries（arXiv 2606.19095、巡回群上のシューア環と AC な Terwilliger 代数）。
  - 商に沿った Terwilliger 代数の写像・帰納系を扱う文献は見つからなかった。Bost–Connes 系の有限レベルと Terwilliger 代数を結ぶ文献も見つからなかった。
- 私自身は文献を開いていません（盲検の申告のまま）。

## 6. 収束アラームの状況（CLAUDE.md §7、Part 258 の後）

- **兆候 4：10 パート連続**（Part 249〜258）。補足7 が予告していたとおり。価値は「前提の判定」（β の前提は (1)〜(3) の読みでは素数冪の段で閉じる）。§7 の規定どおり、次の作業を選ぶときに監査を提案する。
- 兆候 1 の内側版：下書きの 3 つの宣言が前の鎖と同じ内容だった（閉じる前の内部照合で見つけて消した）。そのうち 1 つ（`geps_self`）は機械的な候補選びでは拾えず、宣言の文を言葉で検索して見つけた。
- 第 2 の型（注入→回収）：登録 §5 の円環の検査。条件 2 は V の上で φ を決めるだけで、V の外の自由度が代数の関係を満たすかが中身だった。存在の側も不存在の側も、引き戻しを「写像」と呼ぶ円環ではない。
- §6 の表現：A1 は公準のまま。「導いた」「アプローチ」の表現は使っていない。

## 7. 内部照合（着手の前と閉じる前）

- **着手の前**（着手前の文書 §2）：Part 228 の `shellAlgTensorEquiv`・`leftHom`、Part 202 の `mem_geps_pull_iff`（関数のレベル）。商に沿った写像の宣言は見つからなかった。
- **閉じる前（1 回目）**：全宣言 4339 件を書き出し（`audit258/internal/Extract4.lean`）、PAG262 の 30 件に候補を上位 20 まで選び、`#dupcheck`・`#defeqcheck` を両向きに 1140 回（`Dup262_round1.out`）。一致：
  - 下書きの `dind_self_apply` ＝ Part 247（PAG251）の同名の定理（両向き）。
  - 下書きの `rightOp_one` ＝ Part 247 の `rightOp_one'`（両向き）。
  - `crtConj_shellLift` は Part 228 の `crtConj_shellAlgTensorEquiv_tmul` から直ちに出る（B。残した。docstring に記録）。
- **候補選びの外で、宣言の文を言葉で検索**（`geps N N`・`dind N N`・`Pi.single 0 1`）：下書きの `geps_self` ＝ Part 239（PAG243）の同名の定理と同じ内容（関数の等式と各点の形）。`conv_single` は Part 107（PAG111）の `conv_single_gen` の左右を入れ替えた形。`dTop_eTop_dTop` は Part 247 の `convL_geps_self_mul_mulLeft_dind_self`（E_N D_N E_N = (1/N) E_N）と対の式。
- 3 つ（`dind_self_apply`・`rightOp_one`・`geps_self`）を消して前の鎖のものを使い、`conv_single` を前の鎖の定理から示す形に書き直した。**2 回目**（4337 件、28 件、1060 回）の一致は、記録した B の 1 組だけ。
- 限界：候補選びは型に現れる定数の近さで上位 20 までで、`geps_self` の例のように拾えないものがある。言葉の検索も網羅ではない（確信度：中）。

## 8. 独立照合

（照合の後に書く）

# E. 着手前の文書から（§2〜§5、§8）
## 2. 既存分野の言葉への最善の翻訳

- **A_N の正体（鎖の定義）。** A_N = `shellAlg N`（Part 214 ＝ PAG218）＝ End(ℂ^{ℤ/N}) の中で D_s と E_s が生成する代数。D_s は空間の殻の指示関数 1_{gcd(N,x)=s} の掛け算、E_s は双対殻の射影（フーリエ側で 1_{gcd(N,ξ)=s} を掛ける。Part 201 の `geps`）。言い換えると、(ℤ/N)^× の作用の軌道でできるアソシエーションスキーム（円分的なスキーム）の、基点 0 での Terwilliger 代数 T(0)（辞書 `terwilliger-dictionary.md`）。
- **受容条件の形式化の候補（登録 §3 を、この文書で読みとして固める。著者に確かめる事項）。** π: ℤ/M → ℤ/N、π^*: ℂ^{ℤ/N} → ℂ^{ℤ/M}（引き戻し）。
  1. φ: A_N → A_M は ℂ 代数の準同型（単位元を保つ版と、保たない版の 2 通りを数値で見る）。
  2. 射影と両立：すべての T ∈ A_N で φ(T)∘π^* = π^*∘T。
  3. 殻構造と両立：**強い読み** φ(D_s^N) ∈ span{D_t^M}、φ(E_s^N) ∈ span{E_t^M}。**弱い読み** φ(D_s^N), φ(E_s^N) ∈ A_M だけ（殻を混ぜる写像も許す）。
- **条件 2 と強い読みの 3 から決まること（手計算、この文書を書く時点の見込み）。**
  - φ(D_s^N) は掛け算で、π^* と両立するには π^*(1_{gcd(N,·)=s}) の掛け算に決まる。これは M の空間の殻の和 Σ_{t ∣ M, gcd(N,t)=s} D_t^M（gcd(M, y) が gcd(N, y mod N) を決めるので）。
  - φ(E_s^N) はフーリエ側の掛け算で、π^* の像 V（N 周期の関数 ＝ フーリエの台が (M/N)ℤ/Mℤ にある関数）の上では E_s^N と同じでなければならない。V の上の双対殻は t = (M/N)·s（gcd(M, (M/N)j) = (M/N)·gcd(N, j)）。V の外の双対殻（M/N で割れない t）での値は自由。
  - 鎖の中の関連：Part 202（PAG206）の `mem_geps_pull_iff`（E^{Nt}_{ts} g = g ⇔ g は E^N_s f = f の f の引き戻し）、`dft_pull_apply`。これは関数のレベルの事実で、代数の写像の存在は言っていない。
- **互いに素な段（突き合わせ §3）。** M = N·b、gcd(N, b) = 1 なら、Part 228（PAG232）の `shellAlgTensorEquiv`（A_N ⊗ A_b ≅ A_{Nb}）と `leftHom`（T ↦ T ⊗ id）で、φ(T) = crtConj⁻¹(T ⊗ 1) が候補。条件 1 は満たす。条件 2・3 は手計算の見込み（補足7 §3：「D_t ⊗ 1 が A_{ab} の殻射影の和になるかは、殻の定義から自明ではない」。段階 2 で確かめる）。

## 3. 残余

素数冪の段 p^e → p^{e+1}（(2,4)・(2,8)・(3,9)）での写像の存在問題。強い読みでは、V の外の双対殻を E のどれに割り当てるか（または 0 にするか）の有限の選択で決まるので、段階 2 の数値で全数を調べられる。弱い読みでは候補が無限にあり、数値は「見つかった／自然な族の中にはない」までしか言えない。

## 4. 対照群テスト

- 関数体側（F_q[t] の素元の冪 P^e → P^{e+1}）でも同じ形の問いが立つ。答えが同じ理由（群 ℤ/p^{e+1} → ℤ/p^e の形）で決まるなら、ℚ に固有の算術ではない（登録 §4）。段階 2 では、ℤ/p^e と同じ単数の軌道の構造を持つ有限の環（F_q[t]/(t^e)）での比較を、できれば行う。
- 一般化素数では問いが立たない（環がない）。

## 5. 円環の検査（登録 §5）

- 引き戻しを「写像」と呼ぶ円環：条件 2 は φ(T) を V の上で決めるだけで、V の外では決めない。V の外の自由度が代数の関係を満たすかが問いの中身。
- 除去テスト：条件 2 を外すと、A_N → A_M の代数の写像は（A_N が単純な成分を持てば）埋め込みとしていくらでも作れる見込み。そのときは条件 2 が中身を運んでいる。

## 8. 段階 1・2 の結果（2026-11-14 23:0x）

### 8.1 段階 2（数値、`prereg258/stage2.py`・`stage2.log`。数値の確認は証明ではない）

- 強い読み（条件 3：φ(D_s) ∈ span{D^M}、φ(E_s) ∈ span{E^M}）のもとで、V の外の双対殻の割り当てをすべて調べた。
- **gcd(N, M/N) > 1 の組では、写像は 1 つもない**：(2,4)・(2,8)・(3,9)・(4,8)（素数冪）と (6,12)・(2,12)・(6,18)・(9,27)。落ちた理由はすべて積の関係（`mult`）。
- **gcd(N, M/N) = 1 の組では、写像がある**：(2,6)・(3,6)・(2,10)・(3,12)・(4,12)。φ(T) = CRT⁻¹(T ⊗ 1) が条件 1〜3（強い読み）をすべて満たし、像は A_M に入り、単位元を保つ。(2,6)・(2,10)・(4,12) では、条件を満たす割り当てがもう 1 つある（(2,6) では φ(E_1) = E_3 + E_2、φ(E_2) = E_6 + E_1）。
- 単位元を保たない版：条件 2 から φ(Σ D_s) = 恒等写像に決まるので、結局単位元を保つ版と同じになる（割り当てに「どこにも割り当てない」を入れた候補は、生成元の像の段階で落ちる）。
- 例 (2,4) の障害（手計算で確かめた）：A_2 = M_2(ℂ)（次元 4）。単位元を保つ準同型 M_2(ℂ) → End(ℂ^4) では、階数 1 のべき等元の像の階数は 2。φ(E_2) は条件から E^4_4（階数 1）か E^4_4 + E^4_1（階数 3）しかとれず、階数 2 にならない。

### 8.2 段階 1（盲検の問いテスト、`prereg258/outputs/blind_output.md`）

- **答え：(i)(ii)（＝条件 2 と強い読みの 3）を課すと、写像は gcd(N, M/N) = 1 のときに限り存在する**（盲検の手計算、確信度：高と申告）。数値の結果と一致する。
  - 存在：CRT で A_M = A_N ⊗ A_{M/N}、φ(T) = T ⊗ I（Hanaki–Kim–Maekawa, Terwilliger algebras of direct and wreath products of association schemes, Theorem 3.1。鎖では Part 228 の `shellAlgTensorEquiv`）。
  - 不存在：A_N の関係 D_N E_N D_N = (1/N) D_N を φ で送ると、φ(E_N) の台がフーリエ側で kℤ/Mℤ（k = M/N）の完全代表系でなければならない。p ∣ N かつ p ∣ k なら、p で割れない剰余類の点を含む双対殻が、その剰余類に 2 点以上を持つので不可能。
  - 単位元を保つかどうかで答えは変わらない（条件から自動的に単位的）。
  - 対照群 F_q[t]/(t^e) でも同じ理由で決まる（ℚ に固有の算術ではない、確信度：高と申告）。
- **文献：商に沿った Terwilliger 代数の写像を扱う文献は見つからなかった**（確信度：中。見つからなかったというだけ）。近いもの：Hanaki–Kim–Maekawa（直積・wreath 積）、Bastian–Humphries（arXiv 2606.19095、巡回群上のシューア環と AC な Terwilliger 代数、商に関する遺伝）。Bost–Connes 系の有限レベルと Terwilliger 代数を結ぶ文献も見つからなかった。

### 8.3 予想との照合

- 当たり：互いに素な組で存在（中〜高）、素数冪の組で不存在（中〜低）、商に沿った写像の文献は見つからない（中）、形式から決まる（中〜高）。
- 外れ：「単位元を保たない版では写像があるかもしれない（低）」は外れた（条件から自動的に単位的）。
- 予想になかったもの：素数冪だけでなく、gcd(N, M/N) > 1 なら一般に不存在という二分法。互いに素な組で、CRT の写像以外にも条件を満たす割り当てがあること。

### 8.4 登録 §7 の停止条件に照らして

- 段階 1 で「文献に答え」は見つからなかった（存在の側は直積の定理で既知、不存在の側は文献なし）。段階 2 で候補は「すべて落ちた」のではなく、互いに素な組で通った。したがって段階 3（Lean）に進む。
- 段階 3 の対象：(a) 互いに素なら写像がある（Part 228 から構成し、条件 2・3 を示す）。(b) gcd(N, M/N) > 1 なら写像はない（盲検の議論を Lean で）。(b) が Lean で通らなければ、通った範囲を明記し、残りは［観察］・手計算として分ける。
- ラベルの見込み：(a) は既知（直積の定理）。(b) は文献が見つからない簡単な事実で、［再導出］か［新規候補（小さい）］かは文献照合の結果と §7 の規則で決める（著者の判断事項）。


# F. 盲検の問いテストの出力（全文）
## 結論

(i) と (ii) を両方課すと、(N, M) の答えは **gcd(N, M/N) = 1 のときに限り存在する** という二分法で決まります。互いに素なら存在し、そうでなければ存在しません。(i) と (ii) からは φ(I) = I が自動的に従うので、単位元を保つかどうかで答えは変わりません。下の否定の議論はすべて手計算です。

以下 k = M/N、W = im π^*（周期 N の関数）とします。

---

### Q1

**答え**：存在するのは gcd(N, k) = 1 のときだけです。単位元を保つ版と保たない版で違いはありません。

**根拠（手計算）**
1. **D の像は (i) と (ii) で一意に決まる。** φ は準同型なので φ(D_s) は冪等元です。直交冪等元 D_t の線形結合で冪等なものは、部分和 Σ_{t∈U} D_t に限られます。(i) を f = 1 に適用すると U = {t ∣ M : gcd(N, t) = s} が強制されます。つまり φ(D_s) = D̃_s（π^{-1}(S_s) の指示関数）です。ここから φ(I) = Σ_s D̃_s = I_M となり、φ は自動的に単位的になります。
2. **E の像も部分的に決まる。** π^* E_s = E_{ks} π^* が成り立ち、t が k の倍数でないとき E_t π^* = 0 です。よって φ(E_s) = Σ_{t∈T_s} E_t と書けます。ここで T_s は M の約数の分割の各ブロックで、T_s ∩ {k s' : s' ∣ N} = {k s} を満たす必要があります。
3. **障害となる関係式。** A_N の中では D_N = e_{00}（S_N = {0} の指示関数）、E_N = J/N です。したがって D_N E_N D_N = (1/N) D_N が成り立ちます。これを φ で送ると、D̃_N は部分群 H = Nℤ/Mℤ の指示関数になります。H の上へ圧縮した核を ℤ/k 上でフーリエ比較すると、次と同値になります。
   - 「Ξ := ⋃_{t∈T_N} {ξ : gcd(M, ξ) = t} が、ℤ/M における kℤ/Mℤ の完全代表系である（各剰余類 mod k にちょうど 1 点）」
4. **gcd(N, k) &gt; 1 なら不可能。** 素数 p が p ∣ N かつ p ∣ k を満たすとします。Ξ は p 成分が単数になる剰余類 η mod k にも 1 点を持たなければなりません。その点が属する殻 t は v_p(t) = 0 です。CRT で分解すると、殻 t とその剰余類の交わりは p 成分だけで p^{v_p(N)} ≥ 2 点を持つので、完全代表系になりえません。
5. **gcd(N, k) = 1 なら存在する。** CRT により ℤ/M ≅ ℤ/N × ℤ/k、V_M = V_N ⊗ V_k となり、殻と周波数殻はどちらも積に分解します（D_{su} = D_s ⊗ D_u、E_{su} = E_s ⊗ E_u）。よって A_M = A_N ⊗ A_k です。これは Hanaki–Kim–Maekawa の Theorem 3.1（直積スキームの Terwilliger 代数はテンソル積）と一致します。π^* f = f ⊗ 1 なので、φ(T) = T ⊗ I_k が (i) と (ii) を満たす単位的準同型になります。

**補足（問いの外）**：(ii) を外して (i) だけを課す場合、非単位的な準同型は常に存在します。φ(T) = π^* T (π^*)^{-1} P_W ⊕ 0 とし、P_W = Σ_s E_{ks} とすれば、生成元の像 D̃_s P_W と E_{ks} はどちらも A_M に入ります。ただし D 側の (ii) は一般に破れます。(i) だけで単位的な準同型が存在するかどうかは確かめていません（不明）。

**確信度**：高。自分で導出した結果で、文献照合はできていません。

---

### Q2

**答え**
- gcd(N, k) = 1 のときは存在します（φ = T ⊗ I_k）。
- N = p^e、M = p^{e+1}（e ≥ 1）のときは存在しません。さらに一般に N = p^e、M = p^{e+f}（e, f ≥ 1）でも存在しません。T_N に加えられるのは殻 p^j（j &lt; f）だけで、その各剰余類 mod p^f には p^e ≥ 2 点が入るからです。

小さい例は次のとおりです。

| (N, M) | gcd(N, M/N) | 結果 |
|---|---|---|
| (2, 4) | 2 | なし |
| (2, 8) | 2 | なし |
| (3, 9) | 3 | なし |
| (2, 6) | 1 | あり |
| (3, 6) | 1 | あり |

(2, 4) は直接確かめられます。殻は {0}, {2}, {1, 3} で、Ξ は「0 を含む 2 元集合で、偶数類と奇数類から 1 点ずつ」でなければなりません。殻の和でそうなるものはありません。表現論で見ても同じ結論です。A_2 = M_2(ℂ) で、E_2 の階数は加群の次元のちょうど半分でなければなりません。一方 W^⊥（周波数 1, 3）の上では φ(E_2) は 0 か I にしかなれません。

**確信度**：高。

---

### Q3

**答え**：Terwilliger 代数のあいだで、商 ℤ/M → ℤ/N に沿った写像や帰納系の存在を扱う文献は見つかりませんでした。見つからなかった、というだけで、存在しないとは言えません。

近い文献は次のとおりです。
- Hanaki–Kim–Maekawa, "Terwilliger algebras of direct and wreath products of association schemes"（[プレプリント](https://soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf)）。
  - Theorem 3.1：直積の T はテンソル積。これが互いに素の場合の存在を与えます。
  - Theorem 4.1：wreath 積で、(Y, T) が thin または 1-class のときの中心的原始冪等元。
  - 掲載誌の J. Algebra 343 (2011) は Bastian–Humphries の引用によるもので、プレプリント本体には記載がありません。
  - 本文を確認した範囲では、商スキームや部分スキームが誘導する準同型は扱っていません。
- Bastian–Humphries, "Schur rings over cyclic groups having Almost Commutative Terwilliger algebras"（arXiv 2606.19095, 2026 年 6 月, https://arxiv.org/abs/2606.19095）。
  - C_{p^n} 上で単数群全体の軌道スキームは K_p ≀ … ≀ K_p（Corollary 3.6, Theorem 3.7）。
  - dim T の公式（Proposition 3.3）。
  - wedge 積と商 G → G/K に関する AC 性の遺伝（Proposition 5.6, Theorem 5.10）。
  - ここで扱われているのは AC 性の遺伝で、代数のあいだの写像ではありません。
- Bost–Connes 系の有限レベルと Terwilliger 代数を結びつける文献は見つかりませんでした。

**確信度**：中。存在しないことの確信ではなく、検索の範囲が限られているためです。

---

### Q4

**答え**：e ≥ 2 なら存在しません。ℤ/p^e のときと同じ理由で決まり、p が q に置き換わるだけです。

**根拠**：R_e = F_q[t]/(t^e) は鎖環（Frobenius 環）です。生成指標 ψ を使って R̂_e ≅ R_e と同一視すると、単数の軌道は空間側でも周波数側でも付値の殻になります。
- 核 K = t^{e-1} R_e の零化群は K^⊥ = t R_e です。
- Q1 と同じ関係式 D_top E_top D_top = (1/|R_{e-1}|) D_top から、「Ξ が R_e における t R_e の完全代表系である」ことが必要になります。
- T_top に追加できるのは付値 0 の殻（単数）だけです。その殻は各非零剰余類に q^{e-1} 点を持ちます。
- よって完全代表系になるのは e − 1 = 0 のときだけです。
- 互いに素の類似（F_q[t]/(fg) で gcd(f, g) = 1）では、CRT によりテンソル積となり存在します。

**確信度**：高（手計算）。

---

### 検索した語
1. Terwilliger algebra direct product of association schemes tensor product
2. Terwilliger algebra Schur ring cyclic group Z_n orbit scheme units
3. Terwilliger algebra quotient association scheme homomorphism inductive limit
4. Hanaki Kim Maekawa Terwilliger algebras of direct and wreath products of association schemes J. Algebra 2011
5. Bost-Connes system finite level Z/N association scheme Terwilliger algebra
6. Bastian Humphries Terwilliger algebra orbit Schur ring cyclic group p^n wreath product K_p
7. "Terwilliger algebra" profinite OR "inverse limit" OR "direct limit" association schemes Z/p^n tower

### 開いたページ
- https://arxiv.org/pdf/2606.19095
- https://arxiv.org/abs/2606.19095
- https://soar-ir.repo.nii.ac.jp/record/11832/files/Terwilliger_algebras_direct_wreath_products.pdf

検索結果に出たが開いていないページ：arXiv 2503.02837, 2305.19258, 0809.1052, 1109.1334, 2410.21600, 2101.09636。

# G. 数値照合 step281.log
```
(N,M)=(2,4)  dim A_N=4  dim A_M=10  gcd(N,M/N)=2 | 強い読み・単位的：候補 2、通った 0、落ちた理由 {'mult': 2} | 強い読み・非単位的：候補 3、通った 0、落ちた理由 {'mult': 2, 'gen': 1}
(N,M)=(2,8)  dim A_N=4  dim A_M=19  gcd(N,M/N)=2 | 強い読み・単位的：候補 4、通った 0、落ちた理由 {'mult': 4} | 強い読み・非単位的：候補 9、通った 0、落ちた理由 {'mult': 4, 'gen': 5}
(N,M)=(3,9)  dim A_N=5  dim A_M=12  gcd(N,M/N)=3 | 強い読み・単位的：候補 2、通った 0、落ちた理由 {'mult': 2} | 強い読み・非単位的：候補 3、通った 0、落ちた理由 {'mult': 2, 'gen': 1}
(N,M)=(4,8)  dim A_N=10  dim A_M=19  gcd(N,M/N)=2 | 強い読み・単位的：候補 3、通った 0、落ちた理由 {'mult': 3} | 強い読み・非単位的：候補 4、通った 0、落ちた理由 {'mult': 3, 'gen': 1}
(N,M)=(2,6)  dim A_N=4  dim A_M=20  gcd(N,M/N)=1 | 強い読み・単位的：候補 4、通った 2（例 {1: 1, 2: 2}）、落ちた理由 {'mult': 2} | 強い読み・非単位的：候補 9、通った 2（例 {1: 1, 2: 2}）、落ちた理由 {'mult': 2, 'gen': 5}
   互いに素：φ(T)=CRT⁻¹(T⊗1)：条件2 誤差 0.0e+00、条件3 D True・E True、像 ⊆ A_M True、単位元 True
(N,M)=(3,6)  dim A_N=5  dim A_M=20  gcd(N,M/N)=1 | 強い読み・単位的：候補 4、通った 1（例 {1: 1, 3: 3}）、落ちた理由 {'mult': 3} | 強い読み・非単位的：候補 9、通った 1（例 {1: 1, 3: 3}）、落ちた理由 {'mult': 3, 'gen': 5}
   互いに素：φ(T)=CRT⁻¹(T⊗1)：条件2 誤差 0.0e+00、条件3 D True・E True、像 ⊆ A_M True、単位元 True
(N,M)=(2,10)  dim A_N=4  dim A_M=20  gcd(N,M/N)=1 | 強い読み・単位的：候補 4、通った 2（例 {1: 1, 2: 2}）、落ちた理由 {'mult': 2} | 強い読み・非単位的：候補 9、通った 2（例 {1: 1, 2: 2}）、落ちた理由 {'mult': 2, 'gen': 5}
   互いに素：φ(T)=CRT⁻¹(T⊗1)：条件2 誤差 0.0e+00、条件3 D True・E True、像 ⊆ A_M True、単位元 True
(N,M)=(3,12)  dim A_N=5  dim A_M=50  gcd(N,M/N)=1 | 強い読み・単位的：候補 16、通った 1（例 {1: 1, 2: 1, 3: 3, 6: 3}）、落ちた理由 {'mult': 15} | 強い読み・非単位的：候補 81、通った 1（例 {1: 1, 2: 1, 3: 3, 6: 3}）、落ちた理由 {'mult': 15, 'gen': 65}
   互いに素：φ(T)=CRT⁻¹(T⊗1)：条件2 誤差 0.0e+00、条件3 D True・E True、像 ⊆ A_M True、単位元 True
追加（盲検の後に、二分法を確かめるため）：(6,12) gcd 2 候補 16 通った 0、(2,12) gcd 2 候補 16 通った 0、(6,18) gcd 3 候補 16 通った 0、(4,12) gcd 1 候補 27 通った 2、(9,27) gcd 3 候補 3 通った 0。

```
