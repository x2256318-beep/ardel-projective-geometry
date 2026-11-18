/-
アーデル射影幾何 — Part 259（PAG 2.0）：互いに素な段の写像の一意性と、帰納系の添字

問いの出所：基礎文書の骨格（著者側、2026-11-15）の第5章と、方向ラウンドの項目 (b) の R1
（互いに素な段だけの帰納系を第5章の材料として確定できるか）。R1 の査定（`pag2_R1_assessment.md`、
数値と手計算）の主張を Lean にした。著者の指示（2026-11-15 07:27「Lean」）。

記号：A_N = `shellAlg N`、D_s = mulLeft(dind N s)、E_s = convL(geps N s)、π^* = `pull`。
Part 258（PAG262）の条件 (i)(ii)（`Compat`）：(i) φ(S) π^* = π^* S、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合。
(iii)（`CompatF` で足す）：φ(𝓕 S 𝓕⁻¹) = 𝓕 φ(S) 𝓕⁻¹（`fC` は Part 242 の `fourierConj` を A_N に制限したもの）。

内容：
1. 互いに素な段の順序 `UDvd`（N ∣ M かつ gcd(N, M/N) = 1。古典的な「ユニタリ約数」の関係 N ∥ M。
   E. Cohen, Math. Z. 74 (1960) 66–80）：N > 0 で反射的（`udvd_refl`）、推移的（`udvd_trans`）。Part 216 の層
   `InLayer` で c = d = N とした場合と同じ（`udvd_iff_inLayer`、N > 0）。素数 p について p と p² の共通の上界がなく
   （`not_directed_udvd`）、したがって ℕ の上で有向でない（`not_isDirected_udvd`）。
2. 生成元 D_s・E_s で一致する A_N からの代数準同型は等しい（`shellAlg_hom_ext`）。(i)(ii) の D の側から φ(D_s) は
   一意に決まる（`compat_dind_unique`。文は N ∣ M だけを仮定する。Part 258 の不存在は (ii) の E の側も仮定する文なので、
   gcd(N, M/N) ≠ 1 で (i) と D の側だけを満たす写像があるかは、Lean にも Part 258 にもない（照合 T の指摘で直した）。
3. 一意性：(i)(ii)(iii) を満たす写像は高々 1 つ（`compatF_unique`）。これは φ(D_s) の一意性を (iii) で E の側へ
   運ぶだけの、ほぼ即座の帰結である（(ii) の E の側も互いに素も使わない）。同じ理由で (ii) の E の側は (i)、(ii) の
   D の側、(iii) から出る（`compatF_of_dind`）。内容があるのは存在の側：`shellLift`（φ(S) = S ⊗ 1）がフーリエと
   両立すること（`shellLift_fC`）。gcd(a, b) = 1 なら (i)(ii)(iii) を満たすのは `shellLift` だけ
   （`compatF_iff_eq_shellLift`）。N ∣ M のとき、(i)(ii)(iii) を満たす写像がちょうど 1 つある ⇔ gcd(N, M/N) = 1
   （`existsUnique_compatF_iff`）。互いに素でないときに成り立たないのは、(i)(ii) を満たす写像が 1 つもないから
   （Part 258）で、複数あるからではない。
4. (i)(ii)(iii) は合成で保たれ（`compatF_comp`）、恒等写像は満たす（`compatF_id`）。互いに素な段の標準の写像
   `canon` は `shellLift` に等しく（`canon_eq_shellLift`）、φ_{N,N} = id（`canon_self`）、φ_{M,L} ∘ φ_{N,M} = φ_{N,L}
   （`canon_comp`）。
5. (iii) を外すと一意でない場合がある（a = 2 の例）：gcd(2, b) = 1、1 < b のとき、A_2 の自己同型（対合、
   `twist2_twist2`・`twist2_bijective`）ψ(S) = χ S χ⁻¹（χ(x) = (−1)^x、`twist2`。D_s を固定し E_1 と E_2 を入れ替える）
   を使った φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))（`twLift`、Θ は Part 228 の `shellAlgTensorEquiv`）は (i)(ii) を
   満たし（`compat_twLift`）、`shellLift` と異なる（`twLift_ne_shellLift`）。したがって (i)(ii) を満たす A_2 → A_{2b}
   は一意でない（`not_existsUnique_compat`）。Lean が示すのはこの場合だけ。R1 の査定の数値（9 組）では、a が奇数なら
   (i)(ii) だけで一意で、(iii) が効くのは a が偶数のときだけと見られる（Lean にしていない）。
6. 有向な部分系の例：素数の有限集合 S の積 N_S（無平方数）の段は、包含の順で `canon` により帰納系をなし
   （`DirectedSystem` のインスタンス）、ℂ 加群としての帰納極限 `sqLim` に各 A_{N_S} は単射で入る
   （`sqLim_of_injective`。遷移写像の単射性 `compat_injective`（仮定は `Compat`、証明は (i) だけを使う）からほぼ自動的に出る）。この系は、極大な有向部分系
   （各素数の指数を 1 つに固定したもの）のうち指数がすべて 1 の場合にすぎず、A_{p^k}（k ≥ 2）を含まない。

Lean にしていないこと：一意でない写像の個数（数値の観察では a が偶数なら 2^{d(b)−1}、奇数なら 1）、a が 2 以外の
偶数の場合の捩れ、a が奇数での (i)(ii) だけによる一意性。`sqLim` の代数の構造と、それが制限テンソル積 ⊗'_p A_p に
同型であること。他の有向な部分系。どの有向な部分系も整除の順序で共終でないこと（初等的）。照合 B が手計算で示した
(iii) の言い換え（𝓕⁻¹ π^* 𝓕 は双対側の部分群の埋め込み ι_* なので、(i)(iii) から φ(S) ι_* = ι_* S。逆向きも
成り立つ見込み。確信度：中）。
-/
import PAG262

open Complex Finset
open PAG.Part205 PAG.Part218 PAG.Part232 PAG.Part246 PAG.Part262
open ZMod (stdAddChar)
open scoped ZMod

namespace PAG.Part263

/-! ### 1. 互いに素な段の順序 -/

/-- 互いに素な段：N ∣ M かつ gcd(N, M/N) = 1。 -/
def UDvd (N M : ℕ) : Prop := N ∣ M ∧ Nat.Coprime N (M / N)

theorem udvd_refl {N : ℕ} (hN : 0 < N) : UDvd N N :=
  ⟨dvd_rfl, by rw [Nat.div_self hN]; exact Nat.coprime_one_right N⟩

theorem udvd_trans {N M L : ℕ} (h1 : UDvd N M) (h2 : UDvd M L) : UDvd N L := by
  obtain ⟨⟨a, rfl⟩, ha⟩ := h1
  obtain ⟨⟨b, rfl⟩, hb⟩ := h2
  refine ⟨⟨a * b, by ring⟩, ?_⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp at ha
  rw [Nat.mul_div_cancel_left a hN] at ha
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    have : N = 1 := by simpa using ha
    subst this; simp
  rw [Nat.mul_div_cancel_left b (Nat.mul_pos hN ha0)] at hb
  rw [mul_assoc, Nat.mul_div_cancel_left _ hN]
  exact Nat.Coprime.mul_right ha (Nat.Coprime.coprime_dvd_left (dvd_mul_right N a) hb)

/-- 内部照合（2026-11-15）：互いに素な段は、Part 216（PAG220）の層 `InLayer`（n = d·e、e は c と互いに素）で
c = d = N とした場合と同じ（N > 0）。 -/
theorem udvd_iff_inLayer {N M : ℕ} (hN : 0 < N) : UDvd N M ↔ PAG.Part220.InLayer N N M := by
  constructor
  · rintro ⟨⟨e, rfl⟩, h⟩
    rw [Nat.mul_div_cancel_left e hN] at h
    exact ⟨e, rfl, h.symm⟩
  · rintro ⟨e, rfl, h⟩
    refine ⟨dvd_mul_right N e, ?_⟩
    rw [Nat.mul_div_cancel_left e hN]
    exact h.symm

/-- p と p² の両方の上に来る段はない（p は素数）。 -/
theorem not_udvd_and_udvd_sq {p M : ℕ} (hp : p.Prime) : ¬ (UDvd p M ∧ UDvd (p ^ 2) M) := by
  rintro ⟨⟨_, h1⟩, ⟨⟨k, rfl⟩, _⟩⟩
  have : p ^ 2 * k / p = p * k := by
    rw [pow_two, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  rw [this] at h1
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h1 (dvd_mul_right p k))

/-- **有向でない**：互いに素な段の順序には、p と p² の共通の上界がない。 -/
theorem not_directed_udvd {p : ℕ} (hp : p.Prime) : ¬ ∃ M, UDvd p M ∧ UDvd (p ^ 2) M :=
  fun ⟨_, h⟩ => not_udvd_and_udvd_sq hp h

/-- **有向でない**（照合 B の指摘で追加）：ℕ の上の UDvd は有向でない（p = 2 の場合）。 -/
theorem not_isDirected_udvd : ¬ IsDirected ℕ UDvd := by
  intro h
  obtain ⟨M, h1, h2⟩ := h.directed 2 (2 ^ 2)
  exact not_udvd_and_udvd_sq Nat.prime_two ⟨h1, h2⟩

/-! ### 2. 生成元での一致と、φ(D_s) の一意性 -/

variable {N M L : ℕ} [NeZero N] [NeZero M] [NeZero L]

/-- 生成元 D_s・E_s で一致する、A_N からの代数準同型は等しい。 -/
theorem shellAlg_hom_ext {B : Type} [Semiring B] [Algebra ℂ B] {φ ψ : shellAlg N →ₐ[ℂ] B}
    (hD : ∀ s, φ ⟨_, mulLeft_dind_mem N s⟩ = ψ ⟨_, mulLeft_dind_mem N s⟩)
    (hE : ∀ s, φ ⟨_, convL_geps_mem N s⟩ = ψ ⟨_, convL_geps_mem N s⟩) : φ = ψ := by
  have key : shellAlg N ≤ (AlgHom.equalizer φ ψ).map (shellAlg N).val := by
    apply Algebra.adjoin_le
    rintro x (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact Subalgebra.mem_map.mpr ⟨⟨_, convL_geps_mem N s⟩, (AlgHom.mem_equalizer _ _ _).mpr (hE s), rfl⟩
    · exact Subalgebra.mem_map.mpr ⟨⟨_, mulLeft_dind_mem N s⟩, (AlgHom.mem_equalizer _ _ _).mpr (hD s), rfl⟩
  ext S
  obtain ⟨T, hT, hTS⟩ := Subalgebra.mem_map.mp (key S.2)
  have hT' : T = S := Subtype.ext hTS
  rw [← hT']
  exact (AlgHom.mem_equalizer φ ψ T).mp hT

omit [NeZero N] [NeZero M] [NeZero L] in
/-- 引き戻しの合成。
内部照合（2026-11-15）：還元の合成は Part 192（PAG196）の `castHom_castHom`。それを引き戻しに言い直したもの。 -/
theorem pull_pull (hNM : N ∣ M) (hML : M ∣ L) (f : ZMod N → ℂ) :
    PAG.Part201.pull hML (PAG.Part201.pull hNM f) = PAG.Part201.pull (hNM.trans hML) f := by
  funext x
  simp only [PAG.Part201.pull, Function.comp_apply]
  congr 1
  exact PAG.Part196.castHom_castHom hNM hML (hNM.trans hML) x

omit [NeZero N] in
theorem pull_self (f : ZMod N → ℂ) : PAG.Part201.pull (dvd_refl N) f = f := by
  funext x
  simp only [PAG.Part201.pull, Function.comp_apply]
  congr 1
  exact RingHom.congr_fun (ZMod.castHom_self) x

omit [NeZero N] [NeZero M] in
theorem pull_one (hNM : N ∣ M) : PAG.Part201.pull hNM (1 : ZMod N → ℂ) = 1 := rfl

/-- **φ(D_s) は (i) と (ii) の D の側から一意に決まる**（文は N ∣ M だけを仮定する。gcd(N, M/N) ≠ 1 でこの前提を
満たす写像があるかは未確認）。 -/
theorem compat_dind_unique (hNM : N ∣ M) {φ ψ : shellAlg N →ₐ[ℂ] shellAlg M}
    (hφ1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (hψ1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (ψ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (hφ2 : ∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (hψ2 : ∀ s : ℕ, (ψ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (s : ℕ) : φ ⟨_, mulLeft_dind_mem N s⟩ = ψ ⟨_, mulLeft_dind_mem N s⟩ := by
  obtain ⟨g, hg⟩ := exists_mulLeft_of_mem_span M (hφ2 s)
  obtain ⟨g', hg'⟩ := exists_mulLeft_of_mem_span M (hψ2 s)
  have h1 := hφ1 ⟨_, mulLeft_dind_mem N s⟩ 1
  have h2 := hψ1 ⟨_, mulLeft_dind_mem N s⟩ 1
  rw [hg, pull_one, LinearMap.mulLeft_apply, mul_one] at h1
  rw [hg', pull_one, LinearMap.mulLeft_apply, mul_one] at h2
  apply Subtype.ext
  rw [hg, hg', h1, h2]

/-! ### 3. フーリエとの両立 (iii) と一意性 -/

/-- A_N のフーリエ共役 S ↦ 𝓕 S 𝓕⁻¹（Part 242 の `fourierConj` を A_N に制限したもの）。 -/
noncomputable def fC (N : ℕ) [NeZero N] : shellAlg N ≃ₐ[ℂ] shellAlg N :=
  ((fourierConj N).subalgebraMap (shellAlg N)).trans
    (Subalgebra.equivOfEq _ _ (map_fourierConj_shellAlg N))

theorem fC_coe (S : shellAlg N) :
    (fC N S : Module.End ℂ (ZMod N → ℂ)) = fourierConj N (S : Module.End ℂ (ZMod N → ℂ)) := rfl

theorem fC_dind (s : ℕ) : fC N ⟨_, mulLeft_dind_mem N s⟩ = ⟨_, convL_geps_mem N s⟩ :=
  Subtype.ext (fourierConj_mulLeft_dind N s)

theorem fC_geps (s : ℕ) : fC N ⟨_, convL_geps_mem N s⟩ = ⟨_, mulLeft_dind_mem N s⟩ :=
  Subtype.ext (fourierConj_convL_geps N s)

/-- Part 258 の条件：(i) 引き戻しと両立、(ii) φ(D_s) は D_t の、φ(E_s) は E_t の線形結合。 -/
def Compat (hNM : N ∣ M) (φ : shellAlg N →ₐ[ℂ] shellAlg M) : Prop :=
  (∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f)) ∧
    (∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) ∧
    (∀ s : ℕ, (φ ⟨_, convL_geps_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)))

/-- (i)(ii) に (iii) フーリエとの両立 φ(𝓕 S 𝓕⁻¹) = 𝓕 φ(S) 𝓕⁻¹ を足した条件。 -/
def CompatF (hNM : N ∣ M) (φ : shellAlg N →ₐ[ℂ] shellAlg M) : Prop :=
  Compat hNM φ ∧ ∀ S : shellAlg N, φ (fC N S) = fC M (φ S)

/-- フーリエ共役は D_t の張る空間を E_t の張る空間に移す（補助）。 -/
theorem fourierConj_mem_spanE {T : Module.End ℂ (ZMod M → ℂ)}
    (hT : T ∈ Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    fourierConj M T ∈ Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
  have h : (Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))).map
      (fourierConj M).toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext t
    exact fourierConj_mulLeft_dind M t
  rw [← h]
  exact Submodule.mem_map_of_mem hT

/-- **(ii) の E の側は余分**（照合 B の指摘で追加）：(i)、(ii) の D の側、(iii) から CompatF が出る。 -/
theorem compatF_of_dind (hNM : N ∣ M) {φ : shellAlg N →ₐ[ℂ] shellAlg M}
    (h1 : ∀ (S : shellAlg N) (f : ZMod N → ℂ),
      (φ S : Module.End ℂ (ZMod M → ℂ)) (PAG.Part201.pull hNM f) =
        PAG.Part201.pull hNM ((S : Module.End ℂ (ZMod N → ℂ)) f))
    (h2 : ∀ s : ℕ, (φ ⟨_, mulLeft_dind_mem N s⟩ : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)))
    (h3 : ∀ S : shellAlg N, φ (fC N S) = fC M (φ S)) : CompatF hNM φ := by
  refine ⟨⟨h1, h2, fun s => ?_⟩, h3⟩
  rw [← fC_dind, h3, fC_coe]
  exact fourierConj_mem_spanE (h2 s)

/-- **一意性**：(i)(ii)(iii) を満たす代数準同型は高々 1 つ（N ∣ M）。 -/
theorem compatF_unique (hNM : N ∣ M) {φ ψ : shellAlg N →ₐ[ℂ] shellAlg M}
    (hφ : CompatF hNM φ) (hψ : CompatF hNM ψ) : φ = ψ := by
  have hD := compat_dind_unique hNM hφ.1.1 hψ.1.1 hφ.1.2.1 hψ.1.2.1
  apply shellAlg_hom_ext hD
  intro s
  rw [← fC_dind, hφ.2, hψ.2, hD]

theorem dsub_eq_zero {s : ℕ} (hs : ¬ s ∣ N) : (⟨_, mulLeft_dind_mem N s⟩ : shellAlg N) = 0 := by
  apply Subtype.ext
  show LinearMap.mulLeft ℂ (dind N s) = 0
  rw [dind_eq_zero_of_not_dvd hs]; exact LinearMap.mulLeft_zero_eq_zero ℂ _

theorem esub_eq_zero {s : ℕ} (hs : ¬ s ∣ N) : (⟨_, convL_geps_mem N s⟩ : shellAlg N) = 0 := by
  apply Subtype.ext
  show PAG.Part15.convL (geps N s) = 0
  rw [geps_eq_zero_of_not_dvd hs, map_zero]

section lift
variable {a b : ℕ} [NeZero a] [NeZero b]

set_option synthInstance.maxHeartbeats 200000 in
/-- `shellLift`（φ(S) = S ⊗ 1）はフーリエと両立する。 -/
theorem shellLift_fC (hab : a.Coprime b) (S : shellAlg a) :
    shellLift hab (fC a S) = fC (a * b) (shellLift hab S) := by
  have h : (shellLift hab).comp (fC a).toAlgHom = (fC (a * b)).toAlgHom.comp (shellLift hab) := by
    apply shellAlg_hom_ext
    · intro s
      show shellLift hab (fC a _) = fC (a * b) (shellLift hab _)
      by_cases hs : s ∣ a
      · rw [fC_dind]
        apply Subtype.ext
        rw [fC_coe, shellLift_geps hab hs, shellLift_dind hab hs, map_sum]
        exact Finset.sum_congr rfl fun u _ => (fourierConj_mulLeft_dind _ _).symm
      · rw [dsub_eq_zero hs, map_zero, map_zero, map_zero]
    · intro s
      show shellLift hab (fC a _) = fC (a * b) (shellLift hab _)
      by_cases hs : s ∣ a
      · rw [fC_geps]
        apply Subtype.ext
        rw [fC_coe, shellLift_geps hab hs, shellLift_dind hab hs, map_sum]
        exact Finset.sum_congr rfl fun u _ => (fourierConj_convL_geps _ _).symm
      · rw [esub_eq_zero hs, map_zero, map_zero, map_zero]
  exact congrArg (fun g : shellAlg a →ₐ[ℂ] shellAlg (a * b) => g S) h

/-- `shellLift` は (i)(ii)(iii) を満たす。 -/
theorem compatF_shellLift (hab : a.Coprime b) : CompatF (dvd_mul_right a b) (shellLift hab) := by
  obtain ⟨-, h2, h3⟩ : Compat (dvd_mul_right a b) (shellLift hab) := by
    refine ⟨shellLift_pull hab, fun s => ?_, fun s => ?_⟩
    · by_cases hs : s ∣ a
      · rw [shellLift_dind hab hs]
        exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
      · rw [dsub_eq_zero hs, map_zero]; exact Submodule.zero_mem _
    · by_cases hs : s ∣ a
      · rw [shellLift_geps hab hs]
        exact Submodule.sum_mem _ fun u _ => Submodule.subset_span ⟨s * u, rfl⟩
      · rw [esub_eq_zero hs, map_zero]; exact Submodule.zero_mem _
  exact ⟨⟨shellLift_pull hab, h2, h3⟩, shellLift_fC hab⟩

/-- (i)(ii)(iii) を満たす A_a → A_{ab} は `shellLift` だけ（gcd(a, b) = 1）。 -/
theorem compatF_iff_eq_shellLift (hab : a.Coprime b) (φ : shellAlg a →ₐ[ℂ] shellAlg (a * b)) :
    CompatF (dvd_mul_right a b) φ ↔ φ = shellLift hab :=
  ⟨fun h => compatF_unique _ h (compatF_shellLift hab), fun h => h ▸ compatF_shellLift hab⟩

end lift

/-- **一意な存在の二分法**：N ∣ M のとき、(i)(ii)(iii) を満たす代数準同型 A_N → A_M が
ちょうど 1 つあるのは gcd(N, M/N) = 1 のとき、かつそのときに限る。 -/
theorem existsUnique_compatF_iff (hNM : N ∣ M) :
    (∃! φ : shellAlg N →ₐ[ℂ] shellAlg M, CompatF hNM φ) ↔ Nat.Coprime N (M / N) := by
  constructor
  · rintro ⟨φ, hφ, -⟩
    exact (exists_compatible_hom_iff hNM).mp ⟨φ, hφ.1⟩
  · intro hc
    rcases hNM with ⟨k, rfl⟩
    have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    rw [Nat.mul_div_cancel_left k hN0] at hc
    have : NeZero k := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
    exact ⟨shellLift hc, compatF_shellLift hc, fun ψ hψ => compatF_unique _ hψ (compatF_shellLift hc)⟩

/-! ### 4. 合成との両立と、標準の写像の系 -/

/-- ψ が D の生成元を D_t の張る空間に送るなら、その空間の元も送る。 -/
theorem map_mem_spanD (ψ : shellAlg M →ₐ[ℂ] shellAlg L)
    (hψ : ∀ t : ℕ, (ψ ⟨_, mulLeft_dind_mem M t⟩ : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind L u)))
    {X : shellAlg M} (hX : (X : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t))) :
    (ψ X : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => LinearMap.mulLeft ℂ (dind L u)) := by
  set G : Set (shellAlg M) := Set.range fun t : ℕ => (⟨_, mulLeft_dind_mem M t⟩ : shellAlg M)
  set lin : shellAlg M →ₗ[ℂ] Module.End ℂ (ZMod L → ℂ) :=
    (shellAlg L).val.toLinearMap ∘ₗ ψ.toLinearMap
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ (Set.range fun u : ℕ =>
      LinearMap.mulLeft ℂ (dind L u))).comap lin := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hψ t
  have hmap : (Submodule.span ℂ G).map (shellAlg M).val.toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => LinearMap.mulLeft ℂ (dind M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [← hmap] at hX
  obtain ⟨Y, hY, hYX⟩ := Submodule.mem_map.mp hX
  have : Y = X := Subtype.ext hYX
  subst this
  exact hle hY

theorem map_mem_spanE (ψ : shellAlg M →ₐ[ℂ] shellAlg L)
    (hψ : ∀ t : ℕ, (ψ ⟨_, convL_geps_mem M t⟩ : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps L u)))
    {X : shellAlg M} (hX : (X : Module.End ℂ (ZMod M → ℂ)) ∈
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t))) :
    (ψ X : Module.End ℂ (ZMod L → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps L u)) := by
  set G : Set (shellAlg M) := Set.range fun t : ℕ => (⟨_, convL_geps_mem M t⟩ : shellAlg M)
  set lin : shellAlg M →ₗ[ℂ] Module.End ℂ (ZMod L → ℂ) :=
    (shellAlg L).val.toLinearMap ∘ₗ ψ.toLinearMap
  have hle : Submodule.span ℂ G ≤ (Submodule.span ℂ (Set.range fun u : ℕ =>
      PAG.Part15.convL (geps L u))).comap lin := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hψ t
  have hmap : (Submodule.span ℂ G).map (shellAlg M).val.toLinearMap =
      Submodule.span ℂ (Set.range fun t : ℕ => PAG.Part15.convL (geps M t)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [← hmap] at hX
  obtain ⟨Y, hY, hYX⟩ := Submodule.mem_map.mp hX
  have : Y = X := Subtype.ext hYX
  subst this
  exact hle hY

/-- **合成**：(i)(ii)(iii) は合成で保たれる。 -/
theorem compatF_comp (hNM : N ∣ M) (hML : M ∣ L) {φ : shellAlg N →ₐ[ℂ] shellAlg M}
    {ψ : shellAlg M →ₐ[ℂ] shellAlg L} (hφ : CompatF hNM φ) (hψ : CompatF hML ψ) :
    CompatF (hNM.trans hML) (ψ.comp φ) := by
  refine ⟨⟨fun S f => ?_, fun s => ?_, fun s => ?_⟩, fun S => ?_⟩
  · rw [AlgHom.comp_apply, ← pull_pull hNM hML, hψ.1.1, hφ.1.1, pull_pull]
  · exact map_mem_spanD ψ hψ.1.2.1 (hφ.1.2.1 s)
  · exact map_mem_spanE ψ hψ.1.2.2 (hφ.1.2.2 s)
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, hφ.2, hψ.2]

/-- 恒等写像は (i)(ii)(iii) を満たす。 -/
theorem compatF_id : CompatF (dvd_refl N) (AlgHom.id ℂ (shellAlg N)) :=
  ⟨⟨fun S f => by rw [AlgHom.id_apply, pull_self, pull_self],
    fun s => Submodule.subset_span ⟨s, rfl⟩, fun s => Submodule.subset_span ⟨s, rfl⟩⟩,
    fun S => rfl⟩

/-- 互いに素な段の標準の写像（(i)(ii)(iii) を満たす唯一の写像）。 -/
noncomputable def canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : shellAlg N →ₐ[ℂ] shellAlg M :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose

theorem compatF_canon (hNM : N ∣ M) (hc : Nat.Coprime N (M / N)) : CompatF hNM (canon hNM hc) :=
  ((existsUnique_compatF_iff hNM).mpr hc).exists.choose_spec

/-- 標準の写像は `shellLift`。 -/
theorem canon_eq_shellLift {a b : ℕ} [NeZero a] [NeZero b] (hab : a.Coprime b)
    (hc : Nat.Coprime a (a * b / a)) : canon (dvd_mul_right a b) hc = shellLift hab :=
  compatF_unique _ (compatF_canon _ hc) (compatF_shellLift hab)

theorem canon_self (hc : Nat.Coprime N (N / N)) : canon (dvd_refl N) hc = AlgHom.id ℂ (shellAlg N) :=
  compatF_unique _ (compatF_canon _ hc) compatF_id

/-- **帰納系**：互いに素な段 N → M → L で φ_{M,L} ∘ φ_{N,M} = φ_{N,L}。 -/
theorem canon_comp (h1 : UDvd N M) (h2 : UDvd M L) :
    (canon h2.1 h2.2).comp (canon h1.1 h1.2) = canon (udvd_trans h1 h2).1 (udvd_trans h1 h2).2 :=
  compatF_unique _ (compatF_comp h1.1 h2.1 (compatF_canon _ _) (compatF_canon _ _)) (compatF_canon _ _)

/-! ### 5. (iii) を外すと一意でない（a = 2） -/

/-- E_s E_t = [s = t] E_s（A_N の中で）。 -/
theorem esub_mul_esub (s t : ℕ) :
    (⟨_, convL_geps_mem N s⟩ : shellAlg N) * ⟨_, convL_geps_mem N t⟩ =
      if s = t then ⟨_, convL_geps_mem N s⟩ else 0 := by
  apply Subtype.ext
  apply LinearMap.ext; intro f
  show PAG.Part15.conv (geps N s) (PAG.Part15.conv (geps N t) f) = _
  rw [← PAG.Part89.conv_assoc', geps_conv_geps]
  split_ifs
  · rfl
  · show PAG.Part15.conv 0 f = 0
    funext x; simp [PAG.Part15.conv]

/-- E_N は定数を保つ。 -/
theorem conv_geps_self_const (c : ℂ) :
    PAG.Part15.conv (geps N N) (fun _ => c) = fun _ => c := by
  funext x
  unfold PAG.Part15.conv
  simp only [PAG.Part243.geps_self]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp

/-- ℤ/2 の指標 χ(x) = (−1)^x。 -/
noncomputable def chi2 : ZMod 2 → ℂ := fun x => if x = 0 then 1 else -1

theorem chi2_mul_self (x : ZMod 2) : chi2 x * chi2 x = 1 := by
  unfold chi2; split_ifs <;> norm_num

/-- χ を掛ける作用素（χ² = 1 なので自分自身が逆）。 -/
noncomputable def chiMul : (ZMod 2 → ℂ) ≃ₗ[ℂ] (ZMod 2 → ℂ) where
  toFun h := chi2 * h
  map_add' f g := mul_add _ _ _
  map_smul' c f := mul_smul_comm c chi2 f
  invFun h := chi2 * h
  left_inv h := by funext x; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
  right_inv h := by funext x; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]

/-- χ による共役 T ↦ χ T χ⁻¹。 -/
noncomputable def chiConj : Module.End ℂ (ZMod 2 → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod 2 → ℂ) :=
  LinearEquiv.conjAlgEquiv ℂ chiMul

theorem chiConj_apply (T : Module.End ℂ (ZMod 2 → ℂ)) (h : ZMod 2 → ℂ) :
    chiConj T h = chi2 * T (chi2 * h) := rfl

theorem chiConj_mulLeft (g : ZMod 2 → ℂ) : chiConj (LinearMap.mulLeft ℂ g) = LinearMap.mulLeft ℂ g := by
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply]
  simp only [Pi.mul_apply, LinearMap.mulLeft_apply]
  linear_combination (g x * h x) * chi2_mul_self x

/-- E_1 = 1 − E_2（N = 2）。 -/
theorem convL_geps_two_one :
    PAG.Part15.convL (geps 2 1) = 1 - PAG.Part15.convL (geps 2 2) := by
  have h := sum_convL_geps 2
  rw [Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by norm_num)] at h
  rw [← h]; abel

theorem sum_zmod2 (g : ZMod 2 → ℂ) : ∑ x, g x = g 0 + g 1 := Fin.sum_univ_two g

/-- χ E_2 χ⁻¹ = E_1。 -/
theorem chiConj_geps_two : chiConj (PAG.Part15.convL (geps 2 2)) = PAG.Part15.convL (geps 2 1) := by
  rw [convL_geps_two_one]
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply]
  simp only [Pi.mul_apply, LinearMap.sub_apply, Module.End.one_apply, Pi.sub_apply,
    PAG.Part15.convL_apply, PAG.Part15.conv, PAG.Part243.geps_self, sum_zmod2]
  have e1 : (0 : ZMod 2) - 1 = 1 := rfl
  have e2 : (1 : ZMod 2) - 1 = 0 := rfl
  have e3 : (1 : ZMod 2) - 0 = 1 := rfl
  have e4 : (0 : ZMod 2) - 0 = 0 := rfl
  have e5 : (1 : ZMod 2) ≠ 0 := by decide
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl <;>
    simp only [chi2, e1, e2, e3, e4, e5, ↓reduceIte] <;> ring

/-- χ の共役は対合。 -/
theorem chiConj_chiConj (T : Module.End ℂ (ZMod 2 → ℂ)) : chiConj (chiConj T) = T := by
  apply LinearMap.ext; intro h; funext x
  rw [chiConj_apply, chiConj_apply]
  have hc : chi2 * (chi2 * h) = h := by
    funext y; simp only [Pi.mul_apply]; rw [← mul_assoc, chi2_mul_self, one_mul]
  simp only [Pi.mul_apply]
  rw [hc, ← mul_assoc, chi2_mul_self, one_mul]

theorem chiConj_geps_one : chiConj (PAG.Part15.convL (geps 2 1)) = PAG.Part15.convL (geps 2 2) := by
  rw [← chiConj_geps_two, chiConj_chiConj]

theorem map_chiConj_le : (shellAlg 2).map (chiConj : Module.End ℂ (ZMod 2 → ℂ) →ₐ[ℂ] _) ≤ shellAlg 2 := by
  rw [shellAlg_eq_adjoin, AlgHom.map_adjoin]
  apply Algebra.adjoin_le
  rintro _ ⟨T, (⟨s, rfl⟩ | ⟨s, rfl⟩), rfl⟩
  · show chiConj (PAG.Part15.convL (geps 2 s)) ∈ shellAlg 2
    by_cases h1 : s = 1
    · subst h1; rw [chiConj_geps_one]; exact convL_geps_mem 2 2
    by_cases h2 : s = 2
    · subst h2; rw [chiConj_geps_two]; exact convL_geps_mem 2 1
    have hs : ¬ s ∣ 2 := by
      intro hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> contradiction
    rw [geps_eq_zero_of_not_dvd hs, map_zero, map_zero]; exact Subalgebra.zero_mem _
  · show chiConj (LinearMap.mulLeft ℂ (dind 2 s)) ∈ shellAlg 2
    rw [chiConj_mulLeft]; exact mulLeft_dind_mem 2 s

/-- A_2 の自己同型 ψ(S) = χ S χ⁻¹：D_s を固定し、E_1 と E_2 を入れ替える。 -/
noncomputable def twist2 : shellAlg 2 →ₐ[ℂ] shellAlg 2 :=
  ((chiConj : Module.End ℂ (ZMod 2 → ℂ) →ₐ[ℂ] _).comp (shellAlg 2).val).codRestrict (shellAlg 2)
    (fun S => map_chiConj_le (Subalgebra.mem_map.mpr ⟨S, S.2, rfl⟩))

theorem twist2_coe (S : shellAlg 2) :
    (twist2 S : Module.End ℂ (ZMod 2 → ℂ)) = chiConj (S : Module.End ℂ (ZMod 2 → ℂ)) := rfl

/-- ψ は対合（照合 B の指摘で追加。したがって A_2 の自己同型）。 -/
theorem twist2_twist2 (S : shellAlg 2) : twist2 (twist2 S) = S :=
  Subtype.ext (chiConj_chiConj _)

theorem twist2_bijective : Function.Bijective twist2 :=
  Function.Involutive.bijective twist2_twist2

theorem twist2_dind (s : ℕ) : twist2 ⟨_, mulLeft_dind_mem 2 s⟩ = ⟨_, mulLeft_dind_mem 2 s⟩ :=
  Subtype.ext (chiConj_mulLeft _)

theorem twist2_geps_one : twist2 ⟨_, convL_geps_mem 2 1⟩ = ⟨_, convL_geps_mem 2 2⟩ :=
  Subtype.ext chiConj_geps_one

theorem twist2_geps_two : twist2 ⟨_, convL_geps_mem 2 2⟩ = ⟨_, convL_geps_mem 2 1⟩ :=
  Subtype.ext chiConj_geps_two

section twistLift
variable {b : ℕ} [NeZero b]

theorem eTop_const (c : ℂ) :
    (eTop b : Module.End ℂ (ZMod b → ℂ)) (fun _ => c) = fun _ => c :=
  conv_geps_self_const c

theorem one_sub_eTop_const (c : ℂ) :
    ((1 - eTop b : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) (fun _ => c) = 0 := by
  rw [Subalgebra.coe_sub, Subalgebra.coe_one, LinearMap.sub_apply, Module.End.one_apply, eTop_const, sub_self]

theorem one_sub_eTop_eq : (1 - eTop b : shellAlg b) = 1 + (-1 : ℂ) • eTop b :=
  Subtype.ext (by
    rw [Subalgebra.coe_sub, Subalgebra.coe_add, Subalgebra.coe_one, Subalgebra.coe_smul, neg_one_smul,
      sub_eq_add_neg])

/-- 線形写像 S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)。 -/
noncomputable def twTensLin : shellAlg 2 →ₗ[ℂ] TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
  (TensorProduct.mk ℂ (shellAlg 2) (shellAlg b)).flip (eTop b) +
    ((TensorProduct.mk ℂ (shellAlg 2) (shellAlg b)).flip (1 - eTop b)) ∘ₗ twist2.toLinearMap

theorem twTensLin_apply (S : shellAlg 2) :
    (twTensLin S : TensorProduct ℂ (shellAlg 2) (shellAlg b)) =
      S ⊗ₜ[ℂ] eTop b + twist2 S ⊗ₜ[ℂ] (1 - eTop b) := rfl

/-- 代数準同型 A_2 → A_2 ⊗ A_b、S ↦ S ⊗ E_b + ψ(S) ⊗ (1 − E_b)。 -/
noncomputable def twTens : shellAlg 2 →ₐ[ℂ] TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
  AlgHom.ofLinearMap twTensLin
    (by
      rw [twTensLin_apply, map_one, ← TensorProduct.tmul_add,
        show eTop b + (1 - eTop b) = 1 by abel]
      rfl)
    (fun S T => by
      have he : eTop b * eTop b = eTop b := eTop_mul_self b
      have he' : (eTop b : Module.End ℂ (ZMod b → ℂ)) * eTop b = eTop b := congrArg Subtype.val he
      have h1 : (1 - eTop b) * eTop b = 0 := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, sub_mul, one_mul, he', sub_self,
          ZeroMemClass.coe_zero])
      have h2 : eTop b * (1 - eTop b) = 0 := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, mul_sub, mul_one, he', sub_self,
          ZeroMemClass.coe_zero])
      have h3 : (1 - eTop b) * (1 - eTop b) = 1 - eTop b := Subtype.ext (by
        rw [Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one, sub_mul, one_mul, mul_sub, mul_one, he',
          sub_self, sub_zero])
      simp only [twTensLin_apply, map_mul, add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        he, h1, h2, h3, TensorProduct.tmul_zero, add_zero, zero_add])

theorem twTens_apply (S : shellAlg 2) :
    (twTens S : TensorProduct ℂ (shellAlg 2) (shellAlg b)) =
      S ⊗ₜ[ℂ] eTop b + twist2 S ⊗ₜ[ℂ] (1 - eTop b) := rfl

/-- **捩れた写像** A_2 → A_{2b}：φ'(S) = Θ(S ⊗ E_b + ψ(S) ⊗ (1 − E_b))。 -/
noncomputable def twLift (hab : Nat.Coprime 2 b) : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) :=
  (shellAlgTensorEquiv hab).toAlgHom.comp twTens

theorem twLift_apply (hab : Nat.Coprime 2 b) (S : shellAlg 2) :
    twLift hab S = shellAlgTensorEquiv hab (twTens S) := rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- φ' は引き戻しと両立する（条件 (i)）。 -/
theorem twLift_pull (hab : Nat.Coprime 2 b) (S : shellAlg 2) (f : ZMod 2 → ℂ) :
    (twLift hab S : Module.End ℂ (ZMod (2 * b) → ℂ)) (PAG.Part201.pull (dvd_mul_right 2 b) f) =
      PAG.Part201.pull (dvd_mul_right 2 b) ((S : Module.End ℂ (ZMod 2 → ℂ)) f) := by
  apply (crtLin hab).injective
  have h1 : ∀ (T : Module.End ℂ (ZMod (2 * b) → ℂ)) (g : ZMod (2 * b) → ℂ),
      crtLin hab (T g) = crtConj hab T (crtLin hab g) := by
    intro T g; rw [crtConj_apply, LinearEquiv.symm_apply_apply]
  rw [h1, twLift_apply, crtConj_shellAlgTensorEquiv, twTens_apply, map_add, tensLift_tmul, tensLift_tmul]
  funext p
  simp only [LinearMap.add_apply, Module.End.mul_apply, leftOp_apply, rightOp_apply, crtLin_pull,
    Pi.add_apply]
  rw [show (fun x : ZMod 2 => (eTop b : Module.End ℂ (ZMod b → ℂ)) (fun _ => f x) p.2) = f from
      funext fun x => congrFun (eTop_const (f x)) p.2,
    show (fun x : ZMod 2 => ((1 - eTop b : shellAlg b) : Module.End ℂ (ZMod b → ℂ)) (fun _ => f x) p.2) = 0 from
      funext fun x => congrFun (one_sub_eTop_const (f x)) p.2,
    map_zero, Pi.zero_apply, add_zero]

set_option synthInstance.maxHeartbeats 200000 in
/-- φ'(D_s) = φ(D_s)（`shellLift` と D の側で一致）。 -/
theorem twLift_dind (hab : Nat.Coprime 2 b) (s : ℕ) :
    twLift hab ⟨_, mulLeft_dind_mem 2 s⟩ = shellLift hab ⟨_, mulLeft_dind_mem 2 s⟩ := by
  rw [twLift_apply, twTens_apply, twist2_dind, ← TensorProduct.tmul_add,
    show eTop b + (1 - eTop b) = 1 by abel, shellLift_apply]

theorem twist2_geps (s : ℕ) : ∃ t, twist2 ⟨_, convL_geps_mem 2 s⟩ = ⟨_, convL_geps_mem 2 t⟩ := by
  by_cases h1 : s = 1
  · subst h1; exact ⟨2, twist2_geps_one⟩
  by_cases h2 : s = 2
  · subst h2; exact ⟨1, twist2_geps_two⟩
  have hs : ¬ s ∣ 2 := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h <;> contradiction
  refine ⟨0, ?_⟩
  rw [esub_eq_zero hs, map_zero, esub_eq_zero (by norm_num : ¬ (0 : ℕ) ∣ 2)]

set_option synthInstance.maxHeartbeats 200000 in
theorem tensor_eTop_mem_spanE (hab : Nat.Coprime 2 b) (t : ℕ) :
    (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 t⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
      Module.End ℂ (ZMod (2 * b) → ℂ)) ∈
      Submodule.span ℂ (Set.range fun u : ℕ => PAG.Part15.convL (geps (2 * b) u)) := by
  by_cases ht : t ∣ 2
  · rw [eTop, shellAlgTensorEquiv_geps hab ht dvd_rfl]
    exact Submodule.subset_span ⟨t * b, rfl⟩
  · rw [esub_eq_zero ht, TensorProduct.zero_tmul, map_zero]
    exact Submodule.zero_mem _

set_option synthInstance.maxHeartbeats 200000 in
/-- φ' は Part 258 の条件 (i)(ii) を満たす。 -/
theorem compat_twLift (hab : Nat.Coprime 2 b) : Compat (dvd_mul_right 2 b) (twLift hab) := by
  have hL := (compatF_shellLift hab).1
  refine ⟨twLift_pull hab, fun s => ?_, fun s => ?_⟩
  · rw [twLift_dind]; exact hL.2.1 s
  · obtain ⟨t, ht⟩ := twist2_geps s
    have e : (twLift hab ⟨_, convL_geps_mem 2 s⟩ : Module.End ℂ (ZMod (2 * b) → ℂ)) =
        (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 s⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
          Module.End ℂ (ZMod (2 * b) → ℂ)) +
          (shellLift hab ⟨_, convL_geps_mem 2 t⟩ : Module.End ℂ (ZMod (2 * b) → ℂ)) -
          (shellAlgTensorEquiv hab ((⟨_, convL_geps_mem 2 t⟩ : shellAlg 2) ⊗ₜ[ℂ] eTop b) :
            Module.End ℂ (ZMod (2 * b) → ℂ)) := by
      rw [twLift_apply, twTens_apply, ht, shellLift_apply, one_sub_eTop_eq, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, map_add, map_add, map_smul, Subalgebra.coe_add, Subalgebra.coe_add,
        Subalgebra.coe_smul, neg_one_smul]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (tensor_eTop_mem_spanE hab s) (hL.2.2 t))
      (tensor_eTop_mem_spanE hab t)

theorem convL_geps_one_ne_zero (M : ℕ) [NeZero M] : PAG.Part15.convL (geps M 1) ≠ 0 := by
  intro h
  have h2 := congrArg (fourierConj M) h
  rw [fourierConj_convL_geps, map_zero] at h2
  have h3 := congrFun (LinearMap.congr_fun h2 1) 1
  rw [LinearMap.mulLeft_apply, LinearMap.zero_apply, Pi.mul_apply, Pi.one_apply, mul_one,
    Pi.zero_apply] at h3
  have hg : Nat.gcd M (1 : ZMod M).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.gcd_comm, ← Nat.gcd_rec]
    exact Nat.gcd_one_right M
  simp [dind, hg] at h3

set_option synthInstance.maxHeartbeats 200000 in
/-- **φ' ≠ `shellLift`**（1 < b）。 -/
theorem twLift_ne_shellLift (hab : Nat.Coprime 2 b) (hb : 1 < b) : twLift hab ≠ shellLift hab := by
  intro heq
  set z : TensorProduct ℂ (shellAlg 2) (shellAlg b) :=
    (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) ⊗ₜ[ℂ] (⟨_, convL_geps_mem b 1⟩ : shellAlg b)
  have h1 : twTens (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) =
      (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) ⊗ₜ[ℂ] (1 : shellAlg b) := by
    apply (shellAlgTensorEquiv hab).injective
    have := congrArg (fun g : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b) => g ⟨_, convL_geps_mem 2 1⟩) heq
    simpa only [twLift_apply, shellLift_apply] using this
  have hz0 : twTens (⟨_, convL_geps_mem 2 1⟩ : shellAlg 2) * z = 0 := by
    have hb1 : (b : ℕ) ≠ 1 := hb.ne'
    have hebe : eTop b * (⟨_, convL_geps_mem b 1⟩ : shellAlg b) = 0 := by
      rw [eTop, esub_mul_esub, ite_eq_right_iff.mpr (fun h => absurd h hb1)]
    have h21 : (⟨_, convL_geps_mem 2 2⟩ : shellAlg 2) * ⟨_, convL_geps_mem 2 1⟩ = 0 := by
      rw [esub_mul_esub, ite_eq_right_iff.mpr (fun h => absurd h (by norm_num))]
    rw [twTens_apply, twist2_geps_one, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, hebe, h21, TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero]
  have hz : z = 0 := by
    rw [h1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, esub_mul_esub] at hz0
    simpa only [↓reduceIte] using hz0
  have hΘ := congrArg (fun w => (shellAlgTensorEquiv hab w : Module.End ℂ (ZMod (2 * b) → ℂ))) hz
  simp only [z, shellAlgTensorEquiv_geps hab (one_dvd 2) (one_dvd b), mul_one, map_zero,
    ZeroMemClass.coe_zero] at hΘ
  exact convL_geps_one_ne_zero (2 * b) hΘ

/-- **(iii) を外すと一意でない場合がある（a = 2 の例）**：gcd(2, b) = 1、1 < b のとき、Part 258 の条件 (i)(ii) だけを
課すと、それを満たす A_2 → A_{2b} は一意でない（`shellLift` と φ'。2 つあることは `compat_twLift`・`compatF_shellLift`・
`twLift_ne_shellLift` による）。 -/
theorem not_existsUnique_compat (hab : Nat.Coprime 2 b) (hb : 1 < b) :
    ¬ ∃! φ : shellAlg 2 →ₐ[ℂ] shellAlg (2 * b), Compat (dvd_mul_right 2 b) φ := by
  rintro ⟨φ, -, hu⟩
  exact twLift_ne_shellLift hab hb ((hu _ (compat_twLift hab)).trans (hu _ (compatF_shellLift hab).1).symm)

end twistLift

/-! ### 6. 無平方数の段の帰納系と、その極限（有向な部分系） -/

/-- 引き戻しは単射（N ∣ M）。
内部照合（2026-11-15）：Part 202（PAG206）の `pull_injective`（M = N·t の形）から直ちに出る（Lean で確認）。 -/
theorem pull_injective' (hNM : N ∣ M) : Function.Injective (PAG.Part201.pull hNM) := by
  obtain ⟨t, rfl⟩ := hNM
  have : NeZero t := ⟨by rintro rfl; exact NeZero.ne (N * 0) (by simp)⟩
  exact PAG.Part206.pull_injective N t

/-- (i)(ii)（`Compat`）を満たす写像は単射（証明は (i) だけを使う）。 -/
theorem compat_injective (hNM : N ∣ M) {φ : shellAlg N →ₐ[ℂ] shellAlg M} (hφ : Compat hNM φ) :
    Function.Injective φ := by
  intro S T h
  apply Subtype.ext
  apply LinearMap.ext
  intro f
  apply pull_injective' hNM
  rw [← hφ.1, ← hφ.1, h]

/-- 素数の有限集合 S の積 N_S = ∏_{p ∈ S} p（無平方数）。 -/
def primeProd (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

theorem primeProd_pos (S : Finset Nat.Primes) : 0 < primeProd S :=
  Finset.prod_pos fun p _ => p.2.pos

instance (S : Finset Nat.Primes) : NeZero (primeProd S) := ⟨(primeProd_pos S).ne'⟩

theorem primeProd_udvd {S T : Finset Nat.Primes} (h : S ⊆ T) : UDvd (primeProd S) (primeProd T) := by
  have hmul : primeProd T = primeProd (T \ S) * primeProd S := by
    unfold primeProd; rw [Finset.prod_sdiff h]
  refine ⟨⟨primeProd (T \ S), by rw [hmul, mul_comm]⟩, ?_⟩
  rw [hmul, Nat.mul_div_cancel _ (primeProd_pos S)]
  unfold primeProd
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  rw [Nat.coprime_primes p.2 q.2]
  intro hpq
  have : p = q := Subtype.ext hpq
  subst this
  exact (Finset.mem_sdiff.mp hq).2 hp

/-- 無平方数の段の標準の写像 A_{N_S} → A_{N_T}（S ⊆ T）。 -/
noncomputable def sqMap (S T : Finset Nat.Primes) (h : S ≤ T) :
    shellAlg (primeProd S) →ₐ[ℂ] shellAlg (primeProd T) :=
  canon (primeProd_udvd h).1 (primeProd_udvd h).2

/-- **帰納系**：無平方数の段（素数の有限集合の包含）の上で、標準の写像は帰納系をなす。 -/
instance : DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h : shellAlg (primeProd S) → shellAlg (primeProd T))) where
  map_self S x := by
    show sqMap S S le_rfl x = x
    rw [sqMap, canon_self]; rfl
  map_map {U T S} hST hTU x := by
    show sqMap T U hTU (sqMap S T hST x) = sqMap S U (hST.trans hTU) x
    rw [← AlgHom.comp_apply, sqMap, sqMap, sqMap,
      canon_comp (primeProd_udvd hST) (primeProd_udvd hTU)]

/-- 無平方数の段の帰納極限（ℂ 加群として）。 -/
abbrev sqLim : Type :=
  Module.DirectLimit (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h).toLinearMap)

instance : DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => ((sqMap S T h).toLinearMap : shellAlg (primeProd S) → shellAlg (primeProd T))) :=
  inferInstanceAs (DirectedSystem (fun S : Finset Nat.Primes => shellAlg (primeProd S))
    (fun S T h => (sqMap S T h : shellAlg (primeProd S) → shellAlg (primeProd T))))

/-- 各段 A_{N_S} は極限に単射で入る。 -/
theorem sqLim_of_injective (S : Finset Nat.Primes) :
    Function.Injective (Module.DirectLimit.of ℂ (Finset Nat.Primes)
      (fun S : Finset Nat.Primes => shellAlg (primeProd S)) (fun S T h => (sqMap S T h).toLinearMap) S) := by
  intro x y hxy
  obtain ⟨T, hST, hT⟩ := Module.DirectLimit.exists_eq_of_of_eq hxy
  exact compat_injective (primeProd_udvd hST).1 (compatF_canon _ (primeProd_udvd hST).2).1 hT

end PAG.Part263

#print axioms PAG.Part263.udvd_refl
#print axioms PAG.Part263.udvd_trans
#print axioms PAG.Part263.udvd_iff_inLayer
#print axioms PAG.Part263.not_udvd_and_udvd_sq
#print axioms PAG.Part263.not_directed_udvd
#print axioms PAG.Part263.not_isDirected_udvd
#print axioms PAG.Part263.shellAlg_hom_ext
#print axioms PAG.Part263.pull_pull
#print axioms PAG.Part263.pull_self
#print axioms PAG.Part263.pull_one
#print axioms PAG.Part263.compat_dind_unique
#print axioms PAG.Part263.fC_coe
#print axioms PAG.Part263.fC_dind
#print axioms PAG.Part263.fC_geps
#print axioms PAG.Part263.fourierConj_mem_spanE
#print axioms PAG.Part263.compatF_of_dind
#print axioms PAG.Part263.compatF_unique
#print axioms PAG.Part263.dsub_eq_zero
#print axioms PAG.Part263.esub_eq_zero
#print axioms PAG.Part263.shellLift_fC
#print axioms PAG.Part263.compatF_shellLift
#print axioms PAG.Part263.compatF_iff_eq_shellLift
#print axioms PAG.Part263.existsUnique_compatF_iff
#print axioms PAG.Part263.map_mem_spanD
#print axioms PAG.Part263.map_mem_spanE
#print axioms PAG.Part263.compatF_comp
#print axioms PAG.Part263.compatF_id
#print axioms PAG.Part263.compatF_canon
#print axioms PAG.Part263.canon_eq_shellLift
#print axioms PAG.Part263.canon_self
#print axioms PAG.Part263.canon_comp
#print axioms PAG.Part263.esub_mul_esub
#print axioms PAG.Part263.conv_geps_self_const
#print axioms PAG.Part263.chi2_mul_self
#print axioms PAG.Part263.chiConj_apply
#print axioms PAG.Part263.chiConj_mulLeft
#print axioms PAG.Part263.convL_geps_two_one
#print axioms PAG.Part263.sum_zmod2
#print axioms PAG.Part263.chiConj_geps_two
#print axioms PAG.Part263.chiConj_chiConj
#print axioms PAG.Part263.chiConj_geps_one
#print axioms PAG.Part263.map_chiConj_le
#print axioms PAG.Part263.twist2_coe
#print axioms PAG.Part263.twist2_twist2
#print axioms PAG.Part263.twist2_bijective
#print axioms PAG.Part263.twist2_dind
#print axioms PAG.Part263.twist2_geps_one
#print axioms PAG.Part263.twist2_geps_two
#print axioms PAG.Part263.eTop_const
#print axioms PAG.Part263.one_sub_eTop_const
#print axioms PAG.Part263.one_sub_eTop_eq
#print axioms PAG.Part263.twTensLin_apply
#print axioms PAG.Part263.twTens_apply
#print axioms PAG.Part263.twLift_apply
#print axioms PAG.Part263.twLift_pull
#print axioms PAG.Part263.twLift_dind
#print axioms PAG.Part263.twist2_geps
#print axioms PAG.Part263.tensor_eTop_mem_spanE
#print axioms PAG.Part263.compat_twLift
#print axioms PAG.Part263.convL_geps_one_ne_zero
#print axioms PAG.Part263.twLift_ne_shellLift
#print axioms PAG.Part263.not_existsUnique_compat
#print axioms PAG.Part263.pull_injective'
#print axioms PAG.Part263.compat_injective
#print axioms PAG.Part263.primeProd_pos
#print axioms PAG.Part263.primeProd_udvd
#print axioms PAG.Part263.sqLim_of_injective
