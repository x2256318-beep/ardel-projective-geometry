/-
アーデル射影幾何 — Part 260（PAG264、短期層の小さいノート、2026-11-19）：角の写像 A_N → A_M（N ∣ M、単位元を保つとは限らない代数準同型。N < M では保たず、N = M では恒等）

問いの出所：方向 γ の立て直しの推薦案（`pag2_gamma_corner_preregistration.md` §4）。2026-11-19 09:37 に著者が採用した。
基礎文書の第 5 章（索引 5.2 の留保「代数版にはならない」）と第 6 章 6.3（Bost–Connes との接続）の材料。新しいパートではない。

記号：N, M ≥ 1（`NeZero`）、N ∣ M、π : ℤ/M → ℤ/N。
- A_N = `shellAlg N`。D^{(N)}_s = mulLeft(dind N s)、E^{(N)}_s = convL(geps N s)（水準を上付きで書く）。
- π^* = `pull`（Part 197（PAG201））。P = `oldP N t`（Part 202（PAG206）、M = N·t のときの旧部分への射影）。
- ε^{(M)}_u = geps M u（E^{(M)}_u の畳み込み核）。

定義：
- `fsum h`（h : N ∣ M）：繊維の和 π_* g(x) = Σ_{π y = x} g(y)。
- `cornerOp h S = (N/M)·π^* ∘ S ∘ π_*`（S ∈ End(ℂ^{ℤ/N})）。
  - 読み：ι = π^*/√(M/N) とおくと ι S ι^† に当たる。π_* が π^* の随伴であること（数え上げの内積）は Lean の外。
- `cornerHom h : shellAlg N →ₙₐ[ℂ] shellAlg M`：単位元を保つとは限らない代数準同型（型は単位元の保存を課さない。N < M では保たず（`cornerHom_one_ne_one`）、N = M では恒等（`cornerHom_self`））。

Lean の文：
1. 一般の S ∈ End(ℂ^{ℤ/N})：
   - π_*(π^* f) = (M/N)·f（`fsum_pull`）。
   - 引き戻しと両立 φ(S) π^* = π^* S（`cornerOp_pull`）。
   - 積（`cornerOp_mul`）、和・スカラー倍・0（`cornerOp_add`・`cornerOp_smul`・`cornerOp_zero`）。
   - φ(1)φ(S) = φ(S) = φ(S)φ(1)（`cornerOp_one_mul`・`cornerOp_mul_one`）。
   - 単射（`cornerOp_injective`）。
   - φ(1)(δ₀)(0) = N/M（`cornerOp_one_single`）。N < M なら φ(1) ≠ 1（`cornerOp_one_ne_one`）。N = M では φ(1) = 1（4 の恒等の法則）なので、N ∣ M のもとで φ(1) ≠ 1 ⟺ N < M（直ちに出る。単独の宣言はない）。
2. M = N·t の形：
   - π^*(π_* g) = t·P g（`pull_fsum`）。
   - φ(1) = P（`cornerOp_one_apply`）。
   - ε^{(Nt)}_{ts} ⋆ P g = ε^{(Nt)}_{ts} ⋆ g（`conv_geps_oldP`）。
   - φ(E^{(N)}_s) = E^{(Nt)}_{ts}（`cornerOp_geps_mul`）。
3. 一般の N ∣ M：
   - φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s（`cornerOp_one`）。
   - φ(E^{(N)}_s) = E^{(M)}_{(M/N)s}（`cornerOp_geps`）。
   - π^*(dind N s) = Σ_{u ∣ M, gcd(u, N) = s} dind M u（`pull_dind`）。
   - φ(D^{(N)}_s) = mulLeft(π^*(dind N s))·φ(1)（`cornerOp_dind`）。
   - φ は A_N を A_M に送る（`cornerOp_mem`）。gcd(N, M/N) は仮定にない。
   - まとめたものが `cornerHom`（値は `cornerHom_coe`）。
   - 像が φ(1) の角に入ること（⊆）は、`cornerOp_mem`・`cornerOp_one_mem`・`cornerOp_one_mul`・`cornerOp_mul_one` から直ちに出る（単独の宣言はない）。
4. 一意性と合成：
   - (a) すべての S ∈ A_N と f で φ(S)(π^* f) = π^*(S f)、(b) φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
   - (a)(b) を満たす、単位元の保存を課さない代数準同型 A_N → A_M（`→ₙₐ` の中で）は、ちょうど 1 つ（`existsUnique_corner`）。
   - 一意性の証明は φ(S) = φ(S)φ(1) と (a)(b) だけを使う短い議論で、引き戻しとの両立だけで決まるという文ではない。
   - 独立照合の手計算の反例（Lean にしていない）：(b) を外すと一意でない（(N, M) = (1,2) で φ'(c) = c·1 も (a) を満たす）。(a) を外しても、積を保つことを外しても一意でない（どちらも (2,4) の例。(1,2) では A_1 = ℂ なので (b) だけで決まる）。
   - 繊維の和の合成（`fsum_trans`）。
   - N ∣ M ∣ L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}（`cornerOp_comp`・`cornerHom_comp`）。引き戻しの合成は Part 259（PAG263）の `pull_pull`。
   - 単射（`cornerHom_injective`）。N < M なら cornerHom(1) ≠ 1（`cornerHom_one_ne_one`）。
   - 恒等の法則（2026-11-19 午後に追加）：N → N の繊維の和は恒等（`fsum_self`）、φ_{N,N} = id（`cornerOp_self`・`cornerHom_self`。引き戻しの恒等は Part 259（PAG263）の `pull_self`）。
   - 合成の法則と恒等の法則が揃ったので、(A_N, φ_{N,M}) は正の整数の整除の順序（N ∣ M）の上で、帰納系の 2 法則を満たす。Mathlib の `DirectedSystem` としての束ねと、極限の対象は Lean にしていない。
5. D 側の証人：(N, M) = (2, 4) で、φ(D^{(2)}_2) は D^{(4)}_u の線形結合でない（`cornerOp_dind_not_mem_span`）。
   - Part 258（PAG262）の殻を混ぜない条件（強い読み：φ(D_s) は D_t の、φ(E_s) は E_t の線形結合）の D 側を満たさない。E 側は 3 の φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} から満たす（直ちに出る。単独の宣言はない）。
   - この現象は素数冪の段に固有ではない。N ∣ M、N < M なら、すべての s ∣ N で φ(D^{(N)}_s) は D^{(M)}_u の span に入らない。
     - 数値：M ≤ 30 の N < M の 81 組。
     - 手計算：(1,2)・(2,6)、独立照合。
     - Lean にあるのは (2,4)、s = 2 だけ。

範囲（Lean にしていないもの）：
- 像が角全体であること（φ(1) A_M φ(1) ⊆ φ(A_N) の側）。
  - 数値：M ≤ 30 で N ∣ M の 111 組（N = M の 30 組を含み、その 30 組は `cornerHom_self` から直ちに出る。自明でないのは N < M の 81 組）。
  - 手計算：構築側と盲検が一致。三重正則性（文献）からの短い帰結の見込み。
- 帰納系の `DirectedSystem` としての束ねと、その極限 A_∞（有限次元の代数の和集合。完備化は解像度が落ちる側の操作と読む）。
- Bost–Connes の ρ との対応（数値と手計算）。
- 随伴を保つこと φ(S^*) = φ(S)^*（独立照合の照合者による、行列の形からの手計算）。
- 対照群 F_p[t]/(t^e) → F_p[t]/(t^{e'})（数値。ℤ/p^e の段に当たる場合だけを試した）。

位置づけ（ラベル）：
- ［既知］：E 側の像 φ(E^{(N)}_s) = E^{(M)}_{(M/N)s} と φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E^{(M)}_s。
  - Bose–Mesner 代数の商スキームの古典的事実（べき等元による角。Zieschang 2005、Kodalen 2019 §2.5）の作用素版。
  - 関数のレベルは Part 202（PAG206）。
- ［再導出（小さい）］：A_N を A_M に送ること、非単位的であること（N < M）、単射、一意性、合成、恒等の法則、D 側の証人。
  - 初等的な議論。
  - T(0) 版の文献は、盲検の問いテスト（2026-11-19）では見つからなかった（確信度：低〜中。MathSciNet・zbMATH は未実施）。
- 新規候補はない。対照群は、ℤ/p^e の段に当たる場合（F_p[t]/(t^e) → F_p[t]/(t^{e'})。関数体そのものではない）に限って同じ文が成り立つ（数値）。互いに素な段は試していない。盲検の手計算では、使うのは平行移動スキームの形式（商とフーリエ双対）だけ。ℚ に固有の算術の内容は、試した範囲では見つかっていない。
- A1 とは関係しない。

内部照合：
- 着手前（言葉の検索）：商に沿った非単位的な写像 A_N → A_M の宣言は、鎖になかった（網羅ではない）。
  - Part 202（PAG206）の `oldP` 系を使った：φ(1) = P、`oldP_eq_sum`（P = Σ E）、`geps_conv_pull`、`dft_oldP`。
  - Part 201（PAG205）の `dft_geps` も使った。
- 閉じる前（機械的）：全宣言 4470 件。PAG264 の対象は 46 件で、定理 41（自動生成の congr_simp を含む）と定義 5。
  - 候補は上位 20。定理は両向きに、定義は 1 回で照合し、41·20·2 + 5·20 = 1740 回。
  - 一致と出たのは `cornerOp_apply` と Part 197（PAG201）の `pull_smul` の 1 組だけ。どちらも定義を展開すると等しくなる式で、中身の重複ではない。
  - 候補の上位を言葉で確かめて、下書きの次の 2 つを消した。
    - `pull_trans`：Part 259（PAG263）の `pull_pull` と向きが逆の同じ文（A）。
    - `apply_single_two_of_mem_span`：Part 258（PAG262）の `exists_mulLeft_of_mem_span` から直ちに出る（B）。
  - 単射の証明は Part 259（PAG263）の `pull_injective'` を使う形に直した。
- 2 回目：全宣言 4468 件、対象 44 件（定理 39・定義 5）、39·20·2 + 5·20 = 1660 回。上の定義の展開の 1 組だけ。
- 3 回目（午後、恒等の法則の 3 つ）：全宣言 4471 件、対象 3 件、候補上位 20、3·20·2 = 120 回。一致なし。
- 宣言は定理 40・定義 5（午後に 3 つを足した）。自動生成の宣言は数えない。
- 「見つからなかった」は「重複はない」ではない。

照合（記録は `records/audit264/`）：
- 独立照合（形式文と定義だけ）：偽・空虚な文はなかった。除去テストの反例を文面に反映した。
- 直した文面の再照合で、7 点の指摘を受けて直した：(1) 非単位的の言い方、(2) 「帰納系をなす」を外し恒等の法則を Lean の外と書いた、(3) M = N·t の形、(4) D 側の量化と根拠、(5) 三重正則性を「見込み」に、(6) ι S ι^† は読み、(7) 条件の記号 (a)(b)。ほかに水準の明示・件数の内訳・対照群の範囲・PAG 番号を直した。
- 午後に恒等の法則を Lean に入れたので、(2) の「恒等の法則は Lean の外」は置き換えた。
- 統合照合（恒等の法則の 3 定理と、再照合の後の直しの尾をまとめて 1 回）：
  - 足した 3 定理は意図どおりで、宣言名・記号の取り違えはなかった。
  - 散文のずれ 11 点を直した：N = M の文、件数、(2) の置き換えの注記、対照群の結論、反例の組、span の対象、正の整数、S ∈ A_N、⊆ の注記、7 点の列挙、随伴の根拠。
  - 統合照合の後のこの直しは、主張を狭めるか明確にするもの（強める直しはない）。補足8の停止の規約の範囲として、尾の台帳は空とする。
-/
import PAG263

open Complex Finset

namespace PAG.Part264

open PAG.Part201 PAG.Part205 PAG.Part206 PAG.Part218 PAG.Part232

section general

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- 繊維の和 π_* g(x) = Σ_{π y = x} g(y)（π : ℤ/M → ℤ/N、N ∣ M）。 -/
noncomputable def fsum (h : N ∣ M) (g : ZMod M → ℂ) : ZMod N → ℂ :=
  fun x => ∑ y ∈ univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x), g y

omit [NeZero N] in
theorem fsum_add (h : N ∣ M) (g g' : ZMod M → ℂ) : fsum h (g + g') = fsum h g + fsum h g' := by
  funext x; simp only [fsum, Pi.add_apply, sum_add_distrib]

omit [NeZero N] in
theorem fsum_smul (h : N ∣ M) (c : ℂ) (g : ZMod M → ℂ) : fsum h (c • g) = c • fsum h g := by
  funext x; simp only [fsum, Pi.smul_apply, smul_eq_mul, mul_sum]

/-- 引き戻し（線形写像）。 -/
noncomputable def pullLin (h : N ∣ M) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod M → ℂ) where
  toFun := pull h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 繊維の和（線形写像）。 -/
noncomputable def fsumLin (h : N ∣ M) : (ZMod M → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := fsum h
  map_add' := fsum_add h
  map_smul' := fsum_smul h

/-- 繊維の大きさは M/N。 -/
theorem card_fiber (h : N ∣ M) (x : ZMod N) :
    ((univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x)).card : ℂ) = (M : ℂ) / N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨y0, hy0⟩ := ZMod.ringHom_surjective (ZMod.castHom h (ZMod N)) x
  have e : univ.filter (fun y : ZMod M => ZMod.castHom h (ZMod N) y = x) =
      (univ.filter (fun z : ZMod M => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).map
        (addRightEmbedding y0) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_map, addRightEmbedding_apply,
      RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    constructor
    · intro hy
      exact ⟨y - y0, by rw [map_sub, hy, hy0, sub_self], sub_add_cancel y y0⟩
    · rintro ⟨z, hz, rfl⟩
      rw [map_add, hz, zero_add, hy0]
  rw [e, card_map, eq_div_iff hN]
  exact card_ker_cast h

/-- **1a.** π_*(π^* f) = (M/N)·f。 -/
theorem fsum_pull (h : N ∣ M) (f : ZMod N → ℂ) : fsum h (pull h f) = ((M : ℂ) / N) • f := by
  funext x
  simp only [fsum, pull_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_congr rfl (fun y hy => by rw [(mem_filter.mp hy).2]), sum_const, nsmul_eq_mul, card_fiber]

/-- 角の写像 φ(S) = (N/M)·π^* ∘ S ∘ π_*（= ι S ι^†、ι = π^*/√(M/N)）。 -/
noncomputable def cornerOp (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) : Module.End ℂ (ZMod M → ℂ) :=
  ((N : ℂ) / M) • (pullLin h ∘ₗ S ∘ₗ fsumLin h)

omit [NeZero N] in
theorem cornerOp_apply (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (g : ZMod M → ℂ) :
    cornerOp h S g = ((N : ℂ) / M) • pull h (S (fsum h g)) := rfl

theorem scal_cancel (N M : ℕ) [NeZero N] [NeZero M] : ((N : ℂ) / M) * ((M : ℂ) / N) = 1 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  field_simp

/-- **1b. 引き戻しと両立**：φ(S) π^* = π^* S。 -/
theorem cornerOp_pull (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) (f : ZMod N → ℂ) :
    cornerOp h S (pull h f) = pull h (S f) := by
  rw [cornerOp_apply, fsum_pull, map_smul, pull_smul, smul_smul, scal_cancel, one_smul]

/-- **1c. 積を保つ**：φ(ST) = φ(S)φ(T)。 -/
theorem cornerOp_mul (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S * T) = cornerOp h S * cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, fsum_smul, fsum_pull,
    smul_smul, scal_cancel, one_smul, Module.End.mul_apply]

omit [NeZero N] in
theorem cornerOp_add (h : N ∣ M) (S T : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (S + T) = cornerOp h S + cornerOp h T := by
  apply LinearMap.ext; intro g
  rw [LinearMap.add_apply, cornerOp_apply, cornerOp_apply, cornerOp_apply, LinearMap.add_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]

omit [NeZero N] in
theorem cornerOp_smul (h : N ∣ M) (c : ℂ) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h (c • S) = c • cornerOp h S := by
  apply LinearMap.ext; intro g
  rw [LinearMap.smul_apply, cornerOp_apply, cornerOp_apply, LinearMap.smul_apply, pull_smul, smul_comm]

omit [NeZero N] in
theorem cornerOp_zero (h : N ∣ M) : cornerOp h 0 = 0 := by
  simpa using cornerOp_smul h 0 0

/-- **1d.** 像は角に入る：φ(1) φ(S) = φ(S) = φ(S) φ(1)。 -/
theorem cornerOp_one_mul (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h 1 * cornerOp h S = cornerOp h S := by
  rw [← cornerOp_mul, one_mul]

theorem cornerOp_mul_one (h : N ∣ M) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h S * cornerOp h 1 = cornerOp h S := by
  rw [← cornerOp_mul, mul_one]

/-- **1e.** φ は単射。 -/
theorem cornerOp_injective (h : N ∣ M) : Function.Injective (cornerOp h) := by
  intro S T hST
  apply LinearMap.ext; intro f
  have e := congrArg (fun X : Module.End ℂ (ZMod M → ℂ) => X (pull h f)) hST
  simp only [cornerOp_pull] at e
  exact PAG.Part263.pull_injective' h e

omit [NeZero N] in
/-- 1 点の関数の繊維の和。 -/
theorem fsum_single (h : N ∣ M) (y0 : ZMod M) (c : ℂ) (x : ZMod N) :
    fsum h (Pi.single y0 c) x = if ZMod.castHom h (ZMod N) y0 = x then c else 0 := by
  simp only [fsum]
  rw [sum_pi_single']
  simp only [mem_filter, mem_univ, true_and]

omit [NeZero N] in
/-- **1f.** φ(1)(δ₀)(0) = N/M（N < M なら φ(1) ≠ 1：単位元を保たない）。 -/
theorem cornerOp_one_single (h : N ∣ M) :
    cornerOp h 1 (Pi.single 0 1) 0 = (N : ℂ) / M := by
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, Module.End.one_apply, fsum_single, map_zero,
    ite_eq_left rfl, smul_eq_mul, mul_one]

omit [NeZero N] in
theorem cornerOp_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerOp h 1 ≠ 1 := by
  intro e
  have e2 := cornerOp_one_single h
  rw [e, Module.End.one_apply, Pi.single_eq_same] at e2
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  rw [eq_div_iff hM, one_mul] at e2
  exact absurd (Nat.cast_injective e2) (Nat.ne_of_lt hlt).symm

end general

/-! ### 2. 生成元の像（M = N·t の形） -/

section gens

variable {N t : ℕ} [NeZero N] [NeZero t]

/-- π^*(π_* g) = t·P g（P は Part 202 の旧部分への射影 `oldP`）。 -/
theorem pull_fsum (g : ZMod (N * t) → ℂ) :
    pull (dvd_mul_right N t) (fsum (dvd_mul_right N t) g) = (t : ℂ) • oldP N t g := by
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  funext x
  rw [pull_apply, Pi.smul_apply, oldP, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ht, one_mul]
  have hre : (∑ y : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) y * g (x - y)) =
      ∑ z : ZMod (N * t), PAG.Part203.rk (N := N * t) N 1 (fun _ => (1 : ℂ)) (x - z) * g z :=
    (Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun z => by simp [Equiv.subLeft_apply])).symm
  simp only [PAG.Part15.conv]
  rw [hre, fsum, sum_filter]
  refine sum_congr rfl (fun z _ => ?_)
  have key : N ∣ (x - z).val ↔ ZMod.castHom (dvd_mul_right N t) (ZMod N) z =
      ZMod.castHom (dvd_mul_right N t) (ZMod N) x := by
    rw [← ZMod.natCast_eq_zero_iff, ← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := dvd_mul_right N t),
      map_sub, sub_eq_zero, eq_comm]
  simp only [PAG.Part203.rk]
  by_cases hz : N ∣ (x - z).val
  · rw [ite_eq_left hz, ite_eq_left (key.mp hz), one_mul]
  · rw [ite_eq_right hz, ite_eq_right (fun e => hz (key.mpr e)), zero_mul]

/-- **2a.** φ(1) = P（`oldP`）。 -/
theorem cornerOp_one_apply (g : ZMod (N * t) → ℂ) :
    cornerOp (dvd_mul_right N t) 1 g = oldP N t g := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  rw [cornerOp_apply, Module.End.one_apply, pull_fsum, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

/-- P(E 側の殻 ts) は動かない：ε_{ts} ⋆ P g = ε_{ts} ⋆ g。 -/
theorem conv_geps_oldP (s : ℕ) (g : ZMod (N * t) → ℂ) :
    PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) = PAG.Part15.conv (geps (N * t) (t * s)) g := by
  apply (ZMod.dft (N := N * t) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, PAG.Part16.dft_conv, Pi.mul_apply, Pi.mul_apply, dft_oldP]
  by_cases htξ : t ∣ ξ.val
  · rw [ite_eq_left htξ]
  · rw [ite_eq_right htξ, dft_geps]
    have hd : dind (N * t) (t * s) ξ = 0 := by
      simp only [dind]
      rw [ite_eq_right (fun h => htξ ((dvd_mul_right t s).trans
        (by rw [← h]; exact Nat.gcd_dvd_right (N * t) ξ.val)))]
    rw [hd, zero_mul, zero_mul]

/-- **2b.** φ(E_s) = E_{ts}。 -/
theorem cornerOp_geps_mul (s : ℕ) :
    cornerOp (dvd_mul_right N t) (PAG.Part15.convL (geps N s)) =
      PAG.Part15.convL (geps (N * t) (t * s)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne t)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply]
  show ((N : ℂ) / ((N * t : ℕ) : ℂ)) • pull (dvd_mul_right N t)
      (PAG.Part15.conv (geps N s) (fsum (dvd_mul_right N t) g)) = PAG.Part15.conv (geps (N * t) (t * s)) g
  rw [← geps_conv_pull, pull_fsum]
  have hcs : PAG.Part15.conv (geps (N * t) (t * s)) ((t : ℂ) • oldP N t g) =
      (t : ℂ) • PAG.Part15.conv (geps (N * t) (t * s)) (oldP N t g) := by
    rw [PAG.Part15.conv_comm, conv_smul_left, PAG.Part15.conv_comm]
  rw [hcs, conv_geps_oldP, smul_smul]
  have : (N : ℂ) / ((N * t : ℕ) : ℂ) * t = 1 := by push_cast; field_simp
  rw [this, one_smul]

end gens

/-! ### 3. 生成元の像（一般の N ∣ M）と、A_N を A_M に送ること -/

section mem

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- φ(1) = Σ_{s ∣ M, (M/N) ∣ s} E_s。 -/
theorem cornerOp_one (h : N ∣ M) :
    cornerOp h 1 = ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  apply LinearMap.ext; intro g
  rw [cornerOp_one_apply, oldP_eq_sum, LinearMap.sum_apply]
  rfl

/-- **3a.** φ(E_s) = E_{(M/N)s}。 -/
theorem cornerOp_geps (h : N ∣ M) (s : ℕ) :
    cornerOp h (PAG.Part15.convL (geps N s)) = PAG.Part15.convL (geps M (M / N * s)) := by
  obtain ⟨t, rfl⟩ := h
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  rw [Nat.mul_div_cancel_left t hN0]
  exact cornerOp_geps_mul s

omit [NeZero N] in
/-- π^*(1_{D_s}) = Σ_{t ∣ M, gcd(t, N) = s} 1_{D_t}。 -/
theorem pull_dind (h : N ∣ M) (s : ℕ) :
    pull h (dind N s) = ∑ u ∈ M.divisors.filter (fun u => Nat.gcd u N = s), dind M u := by
  funext y
  rw [pull_apply, Finset.sum_apply]
  simp only [dind]
  rw [sum_ite_eq]
  have hg : Nat.gcd N (ZMod.castHom h (ZMod N) y).val = Nat.gcd (Nat.gcd M y.val) N := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, Nat.gcd_comm N, ← Nat.gcd_rec,
      Nat.gcd_comm N, Nat.gcd_comm M, Nat.gcd_assoc, Nat.gcd_eq_right h]
  have hmem : Nat.gcd M y.val ∈ M.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, NeZero.ne M⟩
  rw [hg]
  by_cases hs : Nat.gcd (Nat.gcd M y.val) N = s
  · rw [ite_eq_left hs, ite_eq_left (show Nat.gcd M y.val ∈ M.divisors.filter (fun u => Nat.gcd u N = s) from
      mem_filter.mpr ⟨hmem, hs⟩)]
  · rw [ite_eq_right hs, ite_eq_right (show Nat.gcd M y.val ∉ M.divisors.filter (fun u => Nat.gcd u N = s) from
      fun hm => hs (mem_filter.mp hm).2)]

omit [NeZero M] in
theorem mulLeft_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod M → ℂ) :
    LinearMap.mulLeft ℂ (∑ i ∈ s, f i) = ∑ i ∈ s, LinearMap.mulLeft ℂ (f i) := by
  apply LinearMap.ext; intro g
  rw [LinearMap.mulLeft_apply, LinearMap.sum_apply, Finset.sum_mul]
  rfl

omit [NeZero N] in
theorem mulLeft_pull_dind_mem (h : N ∣ M) (s : ℕ) :
    LinearMap.mulLeft ℂ (pull h (dind N s)) ∈ shellAlg M := by
  rw [pull_dind, mulLeft_sum]
  exact Subalgebra.sum_mem _ (fun u _ => mulLeft_dind_mem M u)

omit [NeZero N] in
/-- **3b.** φ(D_s) = (π^*1_{D_s})·φ(1)（D 側の像は殻の掛け算と φ(1) の積）。 -/
theorem cornerOp_dind (h : N ∣ M) (s : ℕ) :
    cornerOp h (LinearMap.mulLeft ℂ (dind N s)) =
      LinearMap.mulLeft ℂ (pull h (dind N s)) * cornerOp h 1 := by
  apply LinearMap.ext; intro g
  rw [Module.End.mul_apply, cornerOp_apply, cornerOp_apply, Module.End.one_apply, LinearMap.mulLeft_apply,
    LinearMap.mulLeft_apply]
  funext y
  simp only [pull_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

theorem cornerOp_one_mem (h : N ∣ M) : cornerOp h 1 ∈ shellAlg M := by
  rw [cornerOp_one]
  exact Subalgebra.sum_mem _ (fun s _ => convL_geps_mem M s)

/-- **3c.** φ は A_N を A_M に送る（gcd(N, M/N) によらない）。 -/
theorem cornerOp_mem (h : N ∣ M) {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) :
    cornerOp h S ∈ shellAlg M := by
  unfold shellAlg at hS
  induction hS using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [cornerOp_geps]; exact convL_geps_mem M _
    · rw [cornerOp_dind]; exact Subalgebra.mul_mem _ (mulLeft_pull_dind_mem h s) (cornerOp_one_mem h)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, cornerOp_smul]
    exact Subalgebra.smul_mem _ (cornerOp_one_mem h) r
  | add x y _ _ hx hy => rw [cornerOp_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy => rw [cornerOp_mul]; exact Subalgebra.mul_mem _ hx hy

/-- **3d. 角の写像** A_N → A_M（単位元を保つとは限らない代数準同型、φ(S) = (N/M)·π^* ∘ S ∘ π_*。N < M では単位元を保たず（`cornerHom_one_ne_one`）、N = M では恒等（`cornerHom_self`））。 -/
noncomputable def cornerHom (h : N ∣ M) : shellAlg N →ₙₐ[ℂ] shellAlg M where
  toFun S := ⟨cornerOp h S, cornerOp_mem h S.2⟩
  map_smul' c S := Subtype.ext (show cornerOp h (c • (S : Module.End ℂ (ZMod N → ℂ))) = c • cornerOp h S from
    cornerOp_smul h c S)
  map_zero' := Subtype.ext (cornerOp_zero h)
  map_add' S T := Subtype.ext (cornerOp_add h S T)
  map_mul' S T := Subtype.ext (cornerOp_mul h S T)

theorem cornerHom_coe (h : N ∣ M) (S : shellAlg N) :
    ((cornerHom h S : shellAlg M) : Module.End ℂ (ZMod M → ℂ)) = cornerOp h S := rfl

end mem

/-! ### 4. 一意性と合成 -/

section uniq

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- **4a. 一意性**：引き戻しと両立し、φ(1) = Σ_{(M/N) ∣ s} E_s を満たす、単位元の保存を課さない代数準同型（`→ₙₐ`）は、ちょうど 1 つ（形式文は ∃!。それが φ = `cornerHom h` であることは証明の中で示す）。 -/
theorem existsUnique_corner (h : N ∣ M) :
    ∃! φ : shellAlg N →ₙₐ[ℂ] shellAlg M,
      (∀ (S : shellAlg N) (f : ZMod N → ℂ),
        (φ S : Module.End ℂ (ZMod M → ℂ)) (pull h f) = pull h ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
      (φ 1 : Module.End ℂ (ZMod M → ℂ)) =
        ∑ s ∈ M.divisors.filter (fun s => M / N ∣ s), PAG.Part15.convL (geps M s) := by
  refine ⟨cornerHom h, ⟨fun S f => cornerOp_pull h S f, ?_⟩, ?_⟩
  · rw [← cornerOp_one]; rfl
  · rintro ψ ⟨hpull, hone⟩
    apply NonUnitalAlgHom.ext; intro S
    apply Subtype.ext
    apply LinearMap.ext; intro g
    have e1 : ψ S = ψ S * ψ 1 := by rw [← map_mul, mul_one]
    rw [cornerHom_coe, e1, Subalgebra.coe_mul, Module.End.mul_apply, hone, ← cornerOp_one,
      cornerOp_apply, Module.End.one_apply, ← pull_smul, hpull, map_smul, pull_smul, cornerOp_apply]

omit [NeZero N] in
theorem fsum_trans {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (g : ZMod L → ℂ) :
    fsum (h1.trans h2) g = fsum h1 (fsum h2 g) := by
  funext x
  simp only [fsum]
  rw [← Finset.sum_fiberwise_of_maps_to (g := ZMod.castHom h2 (ZMod M))
    (t := univ.filter (fun y : ZMod M => ZMod.castHom h1 (ZMod N) y = x))]
  · refine sum_congr rfl (fun y hy => ?_)
    apply sum_congr _ (fun _ _ => rfl)
    ext z
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    constructor
    · rintro ⟨_, hz⟩; exact hz
    · intro hz
      refine ⟨?_, hz⟩
      rw [← ZMod.castHom_comp h1 h2, RingHom.comp_apply, hz, hy]
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    rw [← RingHom.comp_apply, ZMod.castHom_comp h1 h2, hz]

omit [NeZero N] in
/-- **4b. 合成**：φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem cornerOp_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) (S : Module.End ℂ (ZMod N → ℂ)) :
    cornerOp h2 (cornerOp h1 S) = cornerOp (h1.trans h2) S := by
  have hM : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, cornerOp_apply, cornerOp_apply, pull_smul, smul_smul, PAG.Part263.pull_pull h1 h2, fsum_trans h1 h2]
  congr 1
  field_simp

theorem cornerHom_comp {L : ℕ} [NeZero L] (h1 : N ∣ M) (h2 : M ∣ L) :
    (cornerHom h2).comp (cornerHom h1) = cornerHom (h1.trans h2) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_comp h1 h2 S

/-- 恒等の法則の補助：N → N の繊維の和は恒等。 -/
theorem fsum_self (g : ZMod N → ℂ) : fsum (dvd_refl N) g = g := by
  funext x
  simp [fsum, Finset.sum_filter]

/-- **4e. 恒等の法則**：φ_{N,N} = id（引き戻しの恒等は Part 259 の `pull_self`）。 -/
theorem cornerOp_self (S : Module.End ℂ (ZMod N → ℂ)) : cornerOp (dvd_refl N) S = S := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply LinearMap.ext; intro g
  rw [cornerOp_apply, fsum_self, PAG.Part263.pull_self, div_self hN, one_smul]

theorem cornerHom_self : cornerHom (dvd_refl N) = NonUnitalAlgHom.id ℂ (shellAlg N) := by
  apply NonUnitalAlgHom.ext; intro S
  apply Subtype.ext
  exact cornerOp_self (S : Module.End ℂ (ZMod N → ℂ))

/-- **4c.** φ は単射。 -/
theorem cornerHom_injective (h : N ∣ M) : Function.Injective (cornerHom h) :=
  fun _ _ hST => Subtype.ext (cornerOp_injective h (congrArg Subtype.val hST))

/-- **4d.** N < M なら φ は単位元を保たない。 -/
theorem cornerHom_one_ne_one (h : N ∣ M) (hlt : N < M) : cornerHom h 1 ≠ 1 :=
  fun e => cornerOp_one_ne_one h hlt (congrArg Subtype.val e)

end uniq

/-! ### 5. D 側は殻の span に入らない（(N, M) = (2, 4) の証人） -/

/-- **5.** (N, M) = (2, 4)：φ(D_2) は D_t の線形結合でない（Part 258 の強い読みの D 側を満たさない）。 -/
theorem cornerOp_dind_not_mem_span :
    cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) ∉
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind 4 u)) := by
  intro hmem
  obtain ⟨m, hm⟩ := PAG.Part262.exists_mulLeft_of_mem_span 4 hmem
  have e : cornerOp (show 2 ∣ 4 by norm_num) (LinearMap.mulLeft ℂ (dind 2 2)) (Pi.single 0 1) 2 = 0 := by
    rw [hm, LinearMap.mulLeft_apply, Pi.mul_apply, Pi.single_eq_of_ne (by decide), mul_zero]
  rw [cornerOp_apply, Pi.smul_apply, pull_apply, LinearMap.mulLeft_apply, Pi.mul_apply, fsum_single] at e
  have hc : ZMod.castHom (show 2 ∣ 4 by norm_num) (ZMod 2) (2 : ZMod 4) = 0 := by
    rw [map_ofNat]; rfl
  rw [hc, map_zero, ite_eq_left rfl] at e
  simp [dind] at e


end PAG.Part264

#print axioms PAG.Part264.fsum_add
#print axioms PAG.Part264.fsum_smul
#print axioms PAG.Part264.card_fiber
#print axioms PAG.Part264.fsum_pull
#print axioms PAG.Part264.cornerOp_apply
#print axioms PAG.Part264.scal_cancel
#print axioms PAG.Part264.cornerOp_pull
#print axioms PAG.Part264.cornerOp_mul
#print axioms PAG.Part264.cornerOp_add
#print axioms PAG.Part264.cornerOp_smul
#print axioms PAG.Part264.cornerOp_zero
#print axioms PAG.Part264.cornerOp_one_mul
#print axioms PAG.Part264.cornerOp_mul_one
#print axioms PAG.Part264.cornerOp_injective
#print axioms PAG.Part264.fsum_single
#print axioms PAG.Part264.cornerOp_one_single
#print axioms PAG.Part264.cornerOp_one_ne_one
#print axioms PAG.Part264.pull_fsum
#print axioms PAG.Part264.cornerOp_one_apply
#print axioms PAG.Part264.conv_geps_oldP
#print axioms PAG.Part264.cornerOp_geps_mul
#print axioms PAG.Part264.cornerOp_one
#print axioms PAG.Part264.cornerOp_geps
#print axioms PAG.Part264.pull_dind
#print axioms PAG.Part264.mulLeft_sum
#print axioms PAG.Part264.mulLeft_pull_dind_mem
#print axioms PAG.Part264.cornerOp_dind
#print axioms PAG.Part264.cornerOp_one_mem
#print axioms PAG.Part264.cornerOp_mem
#print axioms PAG.Part264.cornerHom_coe
#print axioms PAG.Part264.existsUnique_corner
#print axioms PAG.Part264.fsum_trans
#print axioms PAG.Part264.cornerOp_comp
#print axioms PAG.Part264.cornerHom_comp
#print axioms PAG.Part264.fsum_self
#print axioms PAG.Part264.cornerOp_self
#print axioms PAG.Part264.cornerHom_self
#print axioms PAG.Part264.cornerHom_injective
#print axioms PAG.Part264.cornerHom_one_ne_one
#print axioms PAG.Part264.cornerOp_dind_not_mem_span
