/-
  PAG 2.0 Part 246（2026-11-06）— E_s を 1 つ足した代数 B_s = ⟨D_u, E_N, E_s⟩：|S′| ≤ 2 なら A_N、2 点の証拠で E_1 ∉ B_s
  A_N = ⟨D_s, E_s⟩（Part 214 の shellAlg）、⟨D_u, E_N⟩（Part 240 の oneEAlg N N。Part 241 で dim = d(N)² + |S′|）、
  S′ = {t ∣ N : φ(N/t) ≠ 1}（Part 241 の devSet）、P = 殻の平均（shellAvg）、B_s = ⟨D_u, E_N, E_s⟩（addEAlg）。
  1. ⟨D_u, E_N⟩ ≤ B_s ≤ A_N、B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩（addEAlg_eq_sup）、B_N = ⟨D_u, E_N⟩（addEAlg_self）
  2. B_s = ⟨D_u, E_N⟩ ⇔ E_s ∈ ⟨D_u, E_N⟩ ⇔（s ∣ N で）s ∉ S′ ∨ (s = 1 ∧ N ∈ {1, 4} ∪ 素数)（addEAlg_eq_oneEAlg_iff_all）。
     Σ_{t ∣ N} E_t = 1 を使い、|S′| ≤ 2、s ∈ S′ なら B_s = A_N（addEAlg_eq_shellAlg_of_card_le_two）。
     |S′| ≤ 2 ⇔ d(N) ≤ 3 + [2 ∣ N]（card_devSet_le_two_iff）
  3. 判定法：U_s^⊥ = {f : P f = 0、どの u でも E_s(1_{D_u}·f) = 0} の上で、B_s の元は殻ごとのスカラー
     X f = Σ_{t ∈ S′} b_t·1_{D_t}·f として働く（exists_apply_of_mem_addEAlg）。f が 1 つの殻に載れば X f = c·f
  4. 2 点の証拠：素数 r ∣ s ∣ N（r ≠ 2 か 4 ∣ N）と、r と異なる素数 q ∣ N があるとき、m = j·N/r（j ∈ {1, 2}）、
     f = δ_1 − δ_{1+m}。1 + m は単数なので P f = 0、ε_s は N/s の倍数の平行移動で不変なので E_s f = 0。
     E_1 ∈ B_s なら E_1 f = c·f で、フーリエ変換すると k = q で c = 0、k = 1 で矛盾。よって E_1 ∉ B_s、B_s ≠ A_N
     （convL_geps_one_not_mem_addEAlg、addEAlg_ne_shellAlg）。N が平方因子なしなら、s ∈ S′ で s ∉ {1, 2} の
     すべてで B_s ≠ A_N（addEAlg_ne_shellAlg_of_squarefree）
  5. フーリエ双対：𝓕 B_s 𝓕⁻¹ = ⟨E_u, D_N, D_s⟩（map_fourierConj_addEAlg）、次元が等しい、A_N との一致も同値、
     4 と同じ仮定で D_1 ∉ ⟨E_u, D_N, D_s⟩
  数値だけ（step269、Lean の証明ではない）：N ≤ 60 で、s ∈ S′ なら B_s = A_N ⇔ |S′| ≤ 2 ∨（N が平方因子なし ∧ s ∈ {1, 2}）。
  平方因子なしで s ∈ {1, 2} のときの B_s = A_N（十分性）と、平方因子ありの s = 1・素冪・2 ∥ N の s = 2 での
  B_s ≠ A_N は Lean にしていない
-/
import PAG249

namespace PAG.Part250

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244 PAG.Part245 PAG.Part246 PAG.Part247 PAG.Part248 PAG.Part249
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. E_s を 1 つ足した代数 B_s = ⟨D_u, E_N, E_s⟩ -/

/-- D_u（u ∈ ℕ）と E_N、E_s が生成する部分代数 B_s = ⟨D_u, E_N, E_s⟩。 -/
noncomputable def addEAlg (N s : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : ℕ => LinearMap.mulLeft ℂ (dind N u)) ∪
    {PAG.Part15.convL (geps N N), PAG.Part15.convL (geps N s)})

/-- **1a.** E_s ∈ B_s。 -/
theorem convL_geps_mem_addEAlg (N s : ℕ) [NeZero N] : PAG.Part15.convL (geps N s) ∈ addEAlg N s :=
  Algebra.subset_adjoin (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- **1b.** ⟨D_u, E_N⟩ ≤ B_s。 -/
theorem oneEAlg_le_addEAlg (N s : ℕ) [NeZero N] : oneEAlg N N ≤ addEAlg N s :=
  Algebra.adjoin_mono (Set.union_subset_union_right _ (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))

/-- **1c.** ⟨D_u, E_s⟩ ≤ B_s。 -/
theorem oneEAlg_le_addEAlg' (N s : ℕ) [NeZero N] : oneEAlg N s ≤ addEAlg N s :=
  Algebra.adjoin_mono (Set.union_subset_union_right _
    (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- **1d.** B_s ≤ A_N。 -/
theorem addEAlg_le (N s : ℕ) [NeZero N] : addEAlg N s ≤ shellAlg N := by
  apply Algebra.adjoin_le
  rintro X (⟨u, rfl⟩ | rfl | rfl)
  · exact PAG.Part232.mulLeft_dind_mem N u
  · exact PAG.Part232.convL_geps_mem N N
  · exact PAG.Part232.convL_geps_mem N s

/-- **1e.** B_N = ⟨D_u, E_N⟩。 -/
theorem addEAlg_self (N : ℕ) [NeZero N] : addEAlg N N = oneEAlg N N := by
  rw [addEAlg, oneEAlg, Set.pair_eq_singleton]

/-- **1f.** B_s = ⟨D_u, E_N⟩ ⊔ ⟨D_u, E_s⟩。 -/
theorem addEAlg_eq_sup (N s : ℕ) [NeZero N] : addEAlg N s = oneEAlg N N ⊔ oneEAlg N s := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro X (⟨u, rfl⟩ | rfl | rfl)
    · exact Algebra.mem_sup_left (Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩))
    · exact Algebra.mem_sup_left (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _)))
    · exact Algebra.mem_sup_right (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _)))
  · exact sup_le (oneEAlg_le_addEAlg N s) (oneEAlg_le_addEAlg' N s)

/-! ### 2. 簡単な場合：E_s ∈ ⟨D_u, E_N⟩ なら何も増えない、|S′| ≤ 2 なら B_s = A_N -/

/-- **2a.** s ∤ N なら 1_{D_s} = 0。 -/
theorem dind_of_not_dvd {N s : ℕ} (hs : ¬ s ∣ N) : dind N s = 0 := by
  funext ξ
  show (if Nat.gcd N ξ.val = s then (1 : ℂ) else 0) = 0
  refine ite_eq_right (fun h => hs ?_)
  rw [← h]
  exact Nat.gcd_dvd_left N ξ.val

/-- **2b.** s ∤ N なら E_s = 0。 -/
theorem convL_geps_of_not_dvd {N s : ℕ} [NeZero N] (hs : ¬ s ∣ N) : PAG.Part15.convL (geps N s) = 0 := by
  have h : geps N s = 0 := by
    rw [geps, dind_of_not_dvd hs, map_zero]
  rw [h, map_zero]

/-- **2c.** s ∉ S′ なら E_s ∈ ⟨D_u, E_N⟩（s ∣ N なら φ(N/s) = 1、s ∤ N なら E_s = 0）。 -/
theorem convL_geps_mem_oneEAlg_of_not_mem {N s : ℕ} [NeZero N] (hs : s ∉ devSet N) :
    PAG.Part15.convL (geps N s) ∈ oneEAlg N N := by
  by_cases hd : s ∣ N
  · apply convL_geps_mem_oneEAlg hd
    by_contra h
    exact hs (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, NeZero.ne N⟩, h⟩)
  · rw [convL_geps_of_not_dvd hd]
    exact Subalgebra.zero_mem _

/-- **2d.** B_s = ⟨D_u, E_N⟩ ⇔ E_s ∈ ⟨D_u, E_N⟩。 -/
theorem addEAlg_eq_oneEAlg_iff (N s : ℕ) [NeZero N] :
    addEAlg N s = oneEAlg N N ↔ PAG.Part15.convL (geps N s) ∈ oneEAlg N N := by
  constructor
  · intro h
    rw [← h]
    exact convL_geps_mem_addEAlg N s
  · intro h
    refine le_antisymm ?_ (oneEAlg_le_addEAlg N s)
    apply Algebra.adjoin_le
    rintro X (⟨u, rfl⟩ | rfl | rfl)
    · exact Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))
    · exact h

/-- **2e.** s ∉ S′ なら B_s = ⟨D_u, E_N⟩。 -/
theorem addEAlg_eq_oneEAlg {N s : ℕ} [NeZero N] (hs : s ∉ devSet N) : addEAlg N s = oneEAlg N N :=
  (addEAlg_eq_oneEAlg_iff N s).mpr (convL_geps_mem_oneEAlg_of_not_mem hs)

/-- **2f.** s ∣ N のとき B_s = ⟨D_u, E_N⟩ ⇔ s ∉ S′ ∨ (s = 1 ∧ (N = 1 ∨ N = 4 ∨ N は素数))（Part 243 の 5g から）。 -/
theorem addEAlg_eq_oneEAlg_iff_all {N s : ℕ} [NeZero N] (hs : s ∣ N) :
    addEAlg N s = oneEAlg N N ↔ s ∉ devSet N ∨ (s = 1 ∧ (N = 1 ∨ N = 4 ∨ N.Prime)) := by
  rw [addEAlg_eq_oneEAlg_iff, convL_geps_mem_oneEAlg_iff_all hs]
  have hmem : s ∉ devSet N ↔ Nat.totient (N / s) = 1 := by
    constructor
    · intro h
      by_contra h'
      exact h (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hs, NeZero.ne N⟩, h'⟩)
    · intro h h'
      exact (Finset.mem_filter.mp h').2 h
  rw [hmem]
  constructor
  · rintro (⟨-, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · by_cases h1 : s = 1
      · subst h1
        right
        refine ⟨rfl, ?_⟩
        rw [Nat.div_one, Nat.totient_eq_one_iff] at h
        rcases h with h | h
        · exact Or.inl h
        · right; right
          rw [h]
          exact Nat.prime_two
      · exact Or.inl ⟨h1, h⟩
    · exact Or.inr h

/-- **2g.** Σ_{t ∣ N} E_t = 1。 -/
theorem sum_convL_geps (N : ℕ) [NeZero N] : ∑ t ∈ N.divisors, PAG.Part15.convL (geps N t) = 1 := by
  apply LinearMap.ext
  intro f
  rw [LinearMap.sum_apply, Module.End.one_apply]
  exact sum_geps_conv N f

/-- **2h.** B_s = A_N ⇔ すべての t ∣ N で E_t ∈ B_s。 -/
theorem addEAlg_eq_shellAlg_iff (N s : ℕ) [NeZero N] :
    addEAlg N s = shellAlg N ↔ ∀ t ∈ N.divisors, PAG.Part15.convL (geps N t) ∈ addEAlg N s := by
  constructor
  · intro h t _
    rw [h]
    exact PAG.Part232.convL_geps_mem N t
  · intro h
    refine le_antisymm (addEAlg_le N s) ?_
    rw [PAG.Part232.shellAlg_eq_adjoin]
    apply Algebra.adjoin_le
    rintro X (⟨t, rfl⟩ | ⟨u, rfl⟩)
    · by_cases ht : t ∣ N
      · exact h t (Nat.mem_divisors.mpr ⟨ht, NeZero.ne N⟩)
      · show PAG.Part15.convL (geps N t) ∈ addEAlg N s
        rw [convL_geps_of_not_dvd ht]
        exact Subalgebra.zero_mem _
    · exact Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩)

/-- **2i.** E_t = 1 − Σ_{u ∣ N, u ≠ t} E_u（t ∣ N）。 -/
theorem convL_geps_eq_one_sub {N t : ℕ} [NeZero N] (ht : t ∈ N.divisors) :
    PAG.Part15.convL (geps N t) = 1 - ∑ u ∈ N.divisors.erase t, PAG.Part15.convL (geps N u) := by
  rw [Finset.sum_erase_eq_sub ht, sum_convL_geps, sub_sub_cancel]

/-- **2j.** |S′| ≤ 2、s ∈ S′ なら B_s = A_N（S′ の残りの t は E_t = 1 − Σ_{u ≠ t} E_u で入る）。 -/
theorem addEAlg_eq_shellAlg_of_card_le_two {N s : ℕ} [NeZero N] (hcard : (devSet N).card ≤ 2)
    (hs : s ∈ devSet N) : addEAlg N s = shellAlg N := by
  have hE : ∀ u, u ∉ devSet N ∨ u = s → PAG.Part15.convL (geps N u) ∈ addEAlg N s := by
    rintro u (hu | rfl)
    · exact oneEAlg_le_addEAlg N s (convL_geps_mem_oneEAlg_of_not_mem hu)
    · exact convL_geps_mem_addEAlg N u
  rw [addEAlg_eq_shellAlg_iff]
  intro t ht
  by_cases h1 : t ∉ devSet N ∨ t = s
  · exact hE t h1
  · push Not at h1
    obtain ⟨htS, hts⟩ := h1
    rw [convL_geps_eq_one_sub ht]
    refine sub_mem (one_mem _) (sum_mem (fun u hu => hE u ?_))
    obtain ⟨hut, -⟩ := Finset.mem_erase.mp hu
    by_contra hcon
    push Not at hcon
    obtain ⟨huS, hus⟩ := hcon
    have hsub : ({s, t, u} : Finset ℕ) ⊆ devSet N := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hs
      · exact htS
      · exact huS
    have h3 : ({s, t, u} : Finset ℕ).card = 3 :=
      Finset.card_eq_three.mpr ⟨s, t, u, fun e => hts e.symm, fun e => hus e.symm, fun e => hut e.symm, rfl⟩
    have := Finset.card_le_card hsub
    omega

/-- **2k.** |S′| ≤ 2 ⇔ d(N) ≤ 3 + [2 ∣ N]（Part 241 の #S′ + 1 + [2 ∣ N] = d(N) から）。 -/
theorem card_devSet_le_two_iff (N : ℕ) [NeZero N] :
    (devSet N).card ≤ 2 ↔ N.divisors.card ≤ 3 + if 2 ∣ N then 1 else 0 := by
  have h := card_devSet N
  split_ifs at h ⊢ <;> omega

/-! ### 3. 判定法：B_s の元は U_s^⊥ = {f : P f = 0、どの u でも E_s(1_{D_u}·f) = 0} の上で殻ごとのスカラー -/

/-- **3a.** f ∈ U_s^⊥ なら 1_{D_t}·f ∈ U_s^⊥。 -/
theorem uperp_dind_mul {N s : ℕ} [NeZero N] {f : ZMod N → ℂ} (hf : shellAvg N f = 0)
    (hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * f) = 0) (t : ℕ) :
    shellAvg N (dind N t * f) = 0 ∧ ∀ u, PAG.Part15.convL (geps N s) (dind N u * (dind N t * f)) = 0 := by
  refine ⟨by rw [shellAvg_dind_mul, hf, mul_zero], fun u => ?_⟩
  rw [← mul_assoc, dind_mul]
  split_ifs with h
  · exact hE u
  · rw [zero_mul, map_zero]

/-- **3b.** どの u でも E_s(1_{D_u}·f) = 0 なら E_s f = 0（f = Σ_{u ∣ N} 1_{D_u}·f）。 -/
theorem convL_geps_eq_zero_of_uperp {N s : ℕ} [NeZero N] {f : ZMod N → ℂ}
    (hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * f) = 0) : PAG.Part15.convL (geps N s) f = 0 := by
  have e : f = ∑ u ∈ N.divisors, dind N u * f := by
    rw [← Finset.sum_mul, sum_dind, one_mul]
  rw [e, map_sum]
  exact Finset.sum_eq_zero (fun u _ => hE u)

/-- **3c.** 判定法：X ∈ B_s なら、ある b : S′ → ℂ があって、P f = 0 かつどの u でも E_s(1_{D_u}·f) = 0 の
どの f にも X f = Σ_{t ∈ S′} b_t·1_{D_t}·f（D_u・E_N は Part 243 の 2d、E_s は U_s^⊥ を 0 に送る）。 -/
theorem exists_apply_of_mem_addEAlg {N s : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)}
    (hX : X ∈ addEAlg N s) :
    ∃ b : devSet N → ℂ, ∀ f : ZMod N → ℂ, shellAvg N f = 0 →
      (∀ u, PAG.Part15.convL (geps N s) (dind N u * f) = 0) → X f = ∑ t : devSet N, b t • (dind N t * f) := by
  have hO : ∀ Y ∈ oneEAlg N N, ∃ b : devSet N → ℂ, ∀ f : ZMod N → ℂ, shellAvg N f = 0 →
      (∀ u, PAG.Part15.convL (geps N s) (dind N u * f) = 0) → Y f = ∑ t : devSet N, b t • (dind N t * f) := by
    intro Y hY
    obtain ⟨b, hb⟩ := exists_apply_of_mem_oneEAlg hY
    exact ⟨b, fun f hf _ => hb f hf⟩
  have key : ∀ (b : devSet N → ℂ) (t : devSet N) (g : ZMod N → ℂ),
      ∑ t' : devSet N, b t' • (dind N t' * (dind N t * g)) = b t • (dind N t * g) := by
    intro b t g
    rw [Finset.sum_eq_single t]
    · rw [← mul_assoc, dind_mul, ite_eq_left rfl]
    · intro t' _ ht'
      rw [← mul_assoc, dind_mul, ite_eq_right (fun h => ht' (Subtype.ext h)), zero_mul, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  unfold addEAlg at hX
  induction hX using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨u, rfl⟩ | rfl | rfl
    · exact hO _ (Algebra.subset_adjoin (Or.inl ⟨u, rfl⟩))
    · exact hO _ (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _)))
    · refine ⟨0, fun f _ hE => ?_⟩
      rw [convL_geps_eq_zero_of_uperp hE]
      simp
  | algebraMap r => exact hO _ (Subalgebra.algebraMap_mem _ r)
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b + b', fun f hf hE => ?_⟩
    rw [LinearMap.add_apply, hb f hf hE, hb' f hf hE, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Pi.add_apply, add_smul]
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨b', hb'⟩ := hy
    refine ⟨b * b', fun f hf hE => ?_⟩
    rw [Module.End.mul_apply, hb' f hf hE, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    obtain ⟨h1, h2⟩ := uperp_dind_mul hf hE t
    rw [map_smul, hb _ h1 h2, key b t f, smul_smul, Pi.mul_apply, mul_comm (b' t)]

/-- **3d.** X ∈ B_s、f ∈ U_s^⊥ で f が 1 つの殻 D_a に載っている（1_{D_a}·f = f）なら、ある c で X f = c·f。 -/
theorem exists_apply_eq_smul_of_mem_addEAlg {N s : ℕ} [NeZero N] {X : Module.End ℂ (ZMod N → ℂ)}
    (hX : X ∈ addEAlg N s) {f : ZMod N → ℂ} (hf : shellAvg N f = 0)
    (hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * f) = 0) {a : ℕ} (ha : dind N a * f = f) :
    ∃ c : ℂ, X f = c • f := by
  obtain ⟨b, hb⟩ := exists_apply_of_mem_addEAlg hX
  refine ⟨∑ t : devSet N, if (t : ℕ) = a then b t else 0, ?_⟩
  rw [hb f hf hE, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  by_cases ht : (t : ℕ) = a
  · rw [ite_eq_left ht, ht, ha]
  · rw [ite_eq_right ht, zero_smul, ← ha, ← mul_assoc, dind_mul, ite_eq_right ht, zero_mul, smul_zero]

/-! ### 4. 2 点の証拠 f = δ_1 − δ_b：E_1 ∉ B_s -/

/-- 2 点の関数 δ_1 − δ_b。 -/
noncomputable def twoPt (N : ℕ) (b : ZMod N) : ZMod N → ℂ := Pi.single (1 : ZMod N) (1 : ℂ) - Pi.single b (1 : ℂ)

/-- **4a.** b が単数なら P(δ_1 − δ_b) = 0（1 と b は同じ殻）。 -/
theorem shellAvg_twoPt {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b) : shellAvg N (twoPt N b) = 0 := by
  funext x
  rw [shellAvg_apply, Pi.zero_apply]
  have h : ∑ y, dind N (Nat.gcd N x.val) y * twoPt N b y = 0 := by
    simp only [twoPt, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sum_mul_single]
    have hr := dind_radial N (Nat.gcd N x.val) hb.unit 1
    rw [IsUnit.unit_spec, mul_one] at hr
    rw [hr, sub_self]
  rw [h, zero_div]

/-- **4b.** b が単数なら 1_{D_1}·(δ_1 − δ_b) = δ_1 − δ_b（単数の殻に載っている）。 -/
theorem dind_one_mul_twoPt {N : ℕ} [NeZero N] {b : ZMod N} (hb : IsUnit b) :
    dind N 1 * twoPt N b = twoPt N b := by
  have h1 : dind N 1 (1 : ZMod N) = 1 := by
    have := dind_self N 1 (one_dvd N)
    rwa [Nat.cast_one] at this
  have hb1 : dind N 1 b = 1 := by
    have hr := dind_radial N 1 hb.unit 1
    rw [IsUnit.unit_spec, mul_one] at hr
    rw [hr, h1]
  have key : ∀ a : ZMod N, dind N 1 a = 1 →
      ∀ y, dind N 1 y * (Pi.single a (1 : ℂ) : ZMod N → ℂ) y = (Pi.single a (1 : ℂ) : ZMod N → ℂ) y := by
    intro a ha y
    by_cases hy : y = a
    · subst hy
      rw [ha, one_mul]
    · rw [Pi.single_eq_of_ne hy, mul_zero]
  funext y
  rw [Pi.mul_apply, twoPt, Pi.sub_apply, mul_sub, key 1 h1 y, key b hb1 y]

/-- **4c.** (g ⋆ δ_a)(x) = g(x − a)。 -/
theorem conv_single {N : ℕ} [NeZero N] (g : ZMod N → ℂ) (a x : ZMod N) :
    PAG.Part15.conv g (Pi.single a (1 : ℂ)) x = g (x - a) := by
  show ∑ y, g y * (Pi.single a (1 : ℂ) : ZMod N → ℂ) (x - y) = g (x - a)
  rw [Finset.sum_eq_single (x - a)]
  · rw [sub_sub_cancel, Pi.single_eq_same, mul_one]
  · intro y _ hy
    have h' : x - y ≠ a := by
      intro h
      apply hy
      rw [← h, sub_sub_cancel]
    rw [Pi.single_eq_of_ne h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **4d.** ε_s は N/s の倍数だけの平行移動で不変：(N/s) ∣ m なら ε_s(w + m) = ε_s(w)（s ∣ N。N·ε_s(u) = c_{N/s}(u)
と c_q(u) が u mod q だけで決まることから）。 -/
theorem geps_add_of_dvd {N s : ℕ} [NeZero N] (hs : s ∣ N) {m : ℕ} (hm : N / s ∣ m) (w : ZMod N) :
    geps N s (w + (m : ZMod N)) = geps N s w := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  apply mul_left_cancel₀ hN
  have e1 : w + (m : ZMod N) = ((w.val + m : ℕ) : ZMod N) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  have e2 : w = ((w.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val w).symm
  rw [e1, natCast_mul_geps_eq_ramSum hs]
  conv_rhs => rw [e2]
  rw [natCast_mul_geps_eq_ramSum hs]
  obtain ⟨k, rfl⟩ := hm
  rw [← ramSum_mod (w.val + N / s * k), Nat.add_mul_mod_self_left, ramSum_mod]

/-- **4e.** (N/s) ∣ m なら E_s(δ_1 − δ_{1+m}) = 0（s ∣ N）。 -/
theorem convL_geps_twoPt {N s m : ℕ} [NeZero N] (hs : s ∣ N) (hm : N / s ∣ m) :
    PAG.Part15.convL (geps N s) (twoPt N (1 + (m : ZMod N))) = 0 := by
  funext x
  rw [twoPt, map_sub, Pi.sub_apply, Pi.zero_apply, PAG.Part15.convL_apply, PAG.Part15.convL_apply,
    conv_single, conv_single, sub_eq_zero]
  have e : x - (1 + (m : ZMod N)) + (m : ZMod N) = x - 1 := by ring
  rw [← e, geps_add_of_dvd hs hm]

/-- **4f.** 𝓕δ_a(k) = e(−a·k)。 -/
theorem dft_single {N : ℕ} [NeZero N] (a k : ZMod N) :
    𝓕 (Pi.single a (1 : ℂ)) k = stdAddChar (-(a * k)) := by
  rw [ZMod.dft_apply, Fintype.sum_eq_single a (fun j hj => by rw [Pi.single_eq_of_ne hj, smul_zero]),
    Pi.single_eq_same, smul_eq_mul, mul_one]

/-- **4g.** (b − 1)·k ≠ 0 なら 𝓕(δ_1 − δ_b)(k) ≠ 0。 -/
theorem dft_twoPt_ne_zero {N : ℕ} [NeZero N] {b k : ZMod N} (h : (b - 1) * k ≠ 0) : 𝓕 (twoPt N b) k ≠ 0 := by
  rw [twoPt, map_sub, Pi.sub_apply, dft_single, dft_single, sub_ne_zero]
  intro e
  apply h
  have e2 := ZMod.injective_stdAddChar e
  rw [one_mul, neg_inj] at e2
  rw [sub_mul, one_mul, ← e2, sub_self]

/-- **4h.** 証拠からの結論：s ∣ N、(N/s) ∣ m、1 + m は単数、q ∣ N（q ≠ 1）、m ≢ 0、m·q ≢ 0（mod N）なら E_1 ∉ B_s。
f = δ_1 − δ_{1+m} は U_s^⊥ に入り単数の殻に載るので、E_1 ∈ B_s なら E_1 f = c·f（3d）。フーリエ変換すると
1_{D_1}·𝓕f = c·𝓕f で、k = q（D_1 の外）で c = 0、k = 1 で 𝓕f(1) = 0 となり矛盾。 -/
theorem convL_geps_one_not_mem_addEAlg_of_witness {N s m q : ℕ} [NeZero N] (hs : s ∣ N) (hm : N / s ∣ m)
    (hu : IsUnit (1 + (m : ZMod N))) (hq : q ∣ N) (hq1 : q ≠ 1) (hm0 : (m : ZMod N) ≠ 0)
    (hmq : ((m * q : ℕ) : ZMod N) ≠ 0) : PAG.Part15.convL (geps N 1) ∉ addEAlg N s := by
  intro hX
  have hP : shellAvg N (twoPt N (1 + (m : ZMod N))) = 0 := shellAvg_twoPt hu
  have hsupp := dind_one_mul_twoPt hu
  have hE0 := convL_geps_twoPt hs hm
  have hE : ∀ u, PAG.Part15.convL (geps N s) (dind N u * twoPt N (1 + (m : ZMod N))) = 0 := by
    intro u
    have e : dind N u * twoPt N (1 + (m : ZMod N)) = if u = 1 then twoPt N (1 + (m : ZMod N)) else 0 := by
      conv_lhs => rw [← hsupp]
      rw [← mul_assoc, dind_mul]
      split_ifs with h
      · rw [h, hsupp]
      · rw [zero_mul]
    rw [e]
    split_ifs
    · exact hE0
    · exact map_zero _
  obtain ⟨c, hc⟩ := exists_apply_eq_smul_of_mem_addEAlg hX hP hE hsupp
  rw [PAG.Part15.convL_apply] at hc
  have hF : dind N 1 * 𝓕 (twoPt N (1 + (m : ZMod N))) = c • 𝓕 (twoPt N (1 + (m : ZMod N))) := by
    rw [← dft_conv_geps, hc, map_smul]
  have h1 := congrFun hF (q : ZMod N)
  have h2 := congrFun hF 1
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have hdq : dind N 1 (q : ZMod N) = 0 := by
    have hg : Nat.gcd N (q : ZMod N).val ≠ 1 := by
      rw [gcd_natCast_self N q hq]
      exact hq1
    exact ite_eq_right hg
  have hd1 : dind N 1 (1 : ZMod N) = 1 := by
    have := dind_self N 1 (one_dvd N)
    rwa [Nat.cast_one] at this
  rw [hdq, zero_mul] at h1
  rw [hd1, one_mul] at h2
  have hFq : 𝓕 (twoPt N (1 + (m : ZMod N))) (q : ZMod N) ≠ 0 := dft_twoPt_ne_zero (by
    rw [add_sub_cancel_left, ← Nat.cast_mul]
    exact hmq)
  have hF1 : 𝓕 (twoPt N (1 + (m : ZMod N))) 1 ≠ 0 := dft_twoPt_ne_zero (by
    rw [add_sub_cancel_left, mul_one]
    exact hm0)
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hFq
  rw [hc0, zero_mul] at h2
  exact hF1 h2

/-- **4i.** 素数 r ∣ N（r ≠ 2 か 4 ∣ N）には、r ∤ j かつ gcd(1 + j·N/r, N) = 1 となる j がある
（r ∤ 1 + N/r なら j = 1、そうでなければ j = 2）。 -/
theorem exists_witness_coeff {N r : ℕ} (hr : r.Prime) (hrN : r ∣ N) (hr2 : r ≠ 2 ∨ 4 ∣ N) :
    ∃ j : ℕ, ¬ r ∣ j ∧ Nat.Coprime (1 + j * (N / r)) N := by
  have hNr : N = r * (N / r) := (Nat.mul_div_cancel' hrN).symm
  have hcop : ∀ j, ¬ r ∣ 1 + j * (N / r) → Nat.Coprime (1 + j * (N / r)) N := by
    intro j hj
    apply Nat.coprime_of_dvd
    intro p hp hp1 hpN
    by_cases hpr : p = r
    · rw [hpr] at hp1
      exact hj hp1
    · have hpNr : p ∣ N / r := by
        rw [hNr] at hpN
        rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hr).mp h) hpr
        · exact h
      have h2 : p ∣ j * (N / r) := dvd_mul_of_dvd_right hpNr j
      have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [add_comm] at hp1)
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  by_cases h1 : r ∣ 1 + N / r
  · refine ⟨2, ?_, hcop 2 ?_⟩
    · intro h2
      have hr2' : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
      rcases hr2 with h | h
      · exact h hr2'
      · rw [hr2'] at h1
        have h4 : 2 ∣ N / 2 := Nat.dvd_div_of_mul_dvd (by norm_num; exact h)
        omega
    · intro h2
      have h3 : r ∣ 2 * (1 + N / r) := dvd_mul_of_dvd_right h1 2
      have h4 : r ∣ 2 * (1 + N / r) - (1 + 2 * (N / r)) := Nat.dvd_sub h3 h2
      have h5 : 2 * (1 + N / r) - (1 + 2 * (N / r)) = 1 := by omega
      rw [h5] at h4
      exact hr.one_lt.ne' (Nat.dvd_one.mp h4)
  · refine ⟨1, fun h => hr.one_lt.ne' (Nat.dvd_one.mp h), hcop 1 ?_⟩
    rwa [one_mul]

/-- **4j.** 主定理：素数 r ∣ s ∣ N（r ≠ 2 か 4 ∣ N）と、r と異なる素数 q ∣ N があれば E_1 ∉ B_s。
証拠は m = j·N/r（4i の j）、f = δ_1 − δ_{1+m}。 -/
theorem convL_geps_one_not_mem_addEAlg {N s r q : ℕ} [NeZero N] (hs : s ∣ N) (hr : r.Prime) (hrs : r ∣ s)
    (hr2 : r ≠ 2 ∨ 4 ∣ N) (hq : q.Prime) (hqN : q ∣ N) (hqr : q ≠ r) :
    PAG.Part15.convL (geps N 1) ∉ addEAlg N s := by
  have hN : N ≠ 0 := NeZero.ne N
  have hrN : r ∣ N := dvd_trans hrs hs
  obtain ⟨j, hj, hcop⟩ := exists_witness_coeff hr hrN hr2
  have hNr : N = r * (N / r) := (Nat.mul_div_cancel' hrN).symm
  have hNr0 : 0 < N / r := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hrN) hr.pos
  have hsr : N / s ∣ N / r := by
    obtain ⟨s', rfl⟩ := hrs
    have e : N / r = s' * (N / (r * s')) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hs]
      rw [mul_assoc, Nat.mul_div_cancel_left _ hr.pos]
    rw [e]
    exact dvd_mul_left _ _
  have hm : N / s ∣ j * (N / r) := dvd_mul_of_dvd_right hsr j
  have hu : IsUnit (1 + ((j * (N / r) : ℕ) : ZMod N)) := by
    have e : (1 + ((j * (N / r) : ℕ) : ZMod N)) = ((1 + j * (N / r) : ℕ) : ZMod N) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [e]
    exact (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hrj : ∀ k, ¬ r ∣ k → ¬ N ∣ j * (N / r) * k := by
    intro k hk h
    have h' : r * (N / r) ∣ j * k * (N / r) := by
      rw [← hNr]
      have e : j * k * (N / r) = j * (N / r) * k := by ring
      rw [e]
      exact h
    rcases (Nat.Prime.dvd_mul hr).mp (Nat.dvd_of_mul_dvd_mul_right hNr0 h') with h1 | h1
    · exact hj h1
    · exact hk h1
  have hm0 : ((j * (N / r) : ℕ) : ZMod N) ≠ 0 := by
    intro h
    apply hrj 1 (fun h1 => hr.one_lt.ne' (Nat.dvd_one.mp h1))
    rw [mul_one]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h
  have hmq : ((j * (N / r) * q : ℕ) : ZMod N) ≠ 0 := by
    intro h
    exact hrj q (fun h1 => hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp h1).symm)
      ((ZMod.natCast_eq_zero_iff _ _).mp h)
  exact convL_geps_one_not_mem_addEAlg_of_witness hs hm hu hqN hq.one_lt.ne' hm0 hmq

/-- **4k.** 同じ仮定で B_s ≠ A_N。 -/
theorem addEAlg_ne_shellAlg {N s r q : ℕ} [NeZero N] (hs : s ∣ N) (hr : r.Prime) (hrs : r ∣ s)
    (hr2 : r ≠ 2 ∨ 4 ∣ N) (hq : q.Prime) (hqN : q ∣ N) (hqr : q ≠ r) : addEAlg N s ≠ shellAlg N := by
  intro h
  apply convL_geps_one_not_mem_addEAlg hs hr hrs hr2 hq hqN hqr
  rw [h]
  exact PAG.Part232.convL_geps_mem N 1

/-- **4l.** N が平方因子をもたず、s ∈ S′、s ≠ 1、s ≠ 2 なら B_s ≠ A_N（s の奇素因数 r と、N/r の最小素因数 q で 4k）。 -/
theorem addEAlg_ne_shellAlg_of_squarefree {N s : ℕ} [NeZero N] (hsq : Squarefree N) (hs : s ∈ devSet N)
    (hs1 : s ≠ 1) (hs2 : s ≠ 2) : addEAlg N s ≠ shellAlg N := by
  obtain ⟨hsd, hφ⟩ := Finset.mem_filter.mp hs
  have hsN : s ∣ N := Nat.dvd_of_mem_divisors hsd
  have hN : N ≠ 0 := NeZero.ne N
  have hsq_s : Squarefree s := Squarefree.squarefree_of_dvd hsN hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hN (Nat.eq_zero_of_zero_dvd hsN)
  obtain ⟨r, hr, hrs, hr2⟩ : ∃ r, r.Prime ∧ r ∣ s ∧ r ≠ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k, hk⟩ : ∃ k, s = 2 ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hs0 (fun hd hdvd => hcon _ hd hdvd)⟩
    rcases k with _ | _ | k
    · exact hs1 (by rw [hk, pow_zero])
    · exact hs2 (by rw [hk, pow_one])
    · exact (Nat.squarefree_iff_prime_squarefree.mp hsq_s) 2 Nat.prime_two ⟨2 ^ k, by rw [hk]; ring⟩
  have hrN : r ∣ N := dvd_trans hrs hsN
  have hNr1 : N / r ≠ 1 := by
    intro h
    have hNr : N = r := by
      have := Nat.div_mul_cancel hrN
      rw [h, one_mul] at this
      exact this.symm
    have hsr : s = r := by
      have hsr' : s ∣ r := by
        rw [← hNr]
        exact hsN
      rcases (Nat.dvd_prime hr).mp hsr' with h' | h'
      · exact absurd h' hs1
      · exact h'
    apply hφ
    rw [hsr, ← hNr, Nat.div_self (Nat.pos_of_ne_zero hN), Nat.totient_one]
  have hq := Nat.minFac_prime hNr1
  have hqd : (N / r).minFac ∣ N / r := Nat.minFac_dvd _
  have hqN : (N / r).minFac ∣ N := dvd_trans hqd (Nat.div_dvd_of_dvd hrN)
  have hqr : (N / r).minFac ≠ r := by
    intro h
    rw [h] at hqd
    have hrr : r * r ∣ N := by
      have := mul_dvd_mul_left r hqd
      rwa [Nat.mul_div_cancel' hrN] at this
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq) r hr hrr
  exact addEAlg_ne_shellAlg hsN hr hrs (Or.inl hr2) hq hqN hqr

/-! ### 5. フーリエ双対 ⟨E_u, D_N, D_s⟩ -/

/-- E_u（u ∈ ℕ）と D_N、D_s が生成する部分代数 ⟨E_u, D_N, D_s⟩（B_s のフーリエ双対）。 -/
noncomputable def dualAddEAlg (N s : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun u : ℕ => PAG.Part15.convL (geps N u)) ∪
    {LinearMap.mulLeft ℂ (dind N N), LinearMap.mulLeft ℂ (dind N s)})

/-- **5a.** 𝓕 B_s 𝓕⁻¹ = ⟨E_u, D_N, D_s⟩。 -/
theorem map_fourierConj_addEAlg (N s : ℕ) [NeZero N] :
    (addEAlg N s).map (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) =
      dualAddEAlg N s := by
  rw [addEAlg, dualAddEAlg, AlgHom.map_adjoin, Set.image_union, Set.image_pair, ← Set.range_comp]
  have h1 : (⇑(fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)) ∘
      fun u : ℕ => LinearMap.mulLeft ℂ (dind N u)) = fun u => PAG.Part15.convL (geps N u) := by
    funext u
    exact fourierConj_mulLeft_dind N u
  have h2 : ∀ t, (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ))
      (PAG.Part15.convL (geps N t)) = LinearMap.mulLeft ℂ (dind N t) := fun t => fourierConj_convL_geps N t
  rw [h1, h2, h2]

/-- **5b.** dim ⟨E_u, D_N, D_s⟩ = dim B_s。 -/
theorem finrank_dualAddEAlg (N s : ℕ) [NeZero N] :
    Module.finrank ℂ (dualAddEAlg N s) = Module.finrank ℂ (addEAlg N s) := by
  rw [← map_fourierConj_addEAlg]
  exact ((fourierConj N).subalgebraMap (addEAlg N s)).toLinearEquiv.finrank_eq.symm

/-- **5c.** ⟨E_u, D_N, D_s⟩ = A_N ⇔ B_s = A_N。 -/
theorem dualAddEAlg_eq_shellAlg_iff (N s : ℕ) [NeZero N] :
    dualAddEAlg N s = shellAlg N ↔ addEAlg N s = shellAlg N := by
  rw [← map_fourierConj_addEAlg]
  conv_lhs => rw [← map_fourierConj_shellAlg]
  exact (Subalgebra.map_injective
    (f := (fourierConj N : Module.End ℂ (ZMod N → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ)))
    (fourierConj N).injective).eq_iff

/-- **5d.** 4j と同じ仮定で D_1 ∉ ⟨E_u, D_N, D_s⟩。 -/
theorem mulLeft_dind_one_not_mem_dualAddEAlg {N s r q : ℕ} [NeZero N] (hs : s ∣ N) (hr : r.Prime) (hrs : r ∣ s)
    (hr2 : r ≠ 2 ∨ 4 ∣ N) (hq : q.Prime) (hqN : q ∣ N) (hqr : q ≠ r) :
    LinearMap.mulLeft ℂ (dind N 1) ∉ dualAddEAlg N s := by
  rw [← map_fourierConj_addEAlg, ← fourierConj_convL_geps N 1]
  intro h
  obtain ⟨Y, hY, hYX⟩ := Subalgebra.mem_map.mp h
  have hYX' : fourierConj N Y = fourierConj N (PAG.Part15.convL (geps N 1)) := hYX
  rw [(fourierConj N).injective hYX'] at hY
  exact convL_geps_one_not_mem_addEAlg hs hr hrs hr2 hq hqN hqr hY

end PAG.Part250

#print axioms PAG.Part250.addEAlg
#print axioms PAG.Part250.convL_geps_mem_addEAlg
#print axioms PAG.Part250.oneEAlg_le_addEAlg
#print axioms PAG.Part250.oneEAlg_le_addEAlg'
#print axioms PAG.Part250.addEAlg_le
#print axioms PAG.Part250.addEAlg_self
#print axioms PAG.Part250.addEAlg_eq_sup
#print axioms PAG.Part250.dind_of_not_dvd
#print axioms PAG.Part250.convL_geps_of_not_dvd
#print axioms PAG.Part250.convL_geps_mem_oneEAlg_of_not_mem
#print axioms PAG.Part250.addEAlg_eq_oneEAlg_iff
#print axioms PAG.Part250.addEAlg_eq_oneEAlg
#print axioms PAG.Part250.addEAlg_eq_oneEAlg_iff_all
#print axioms PAG.Part250.sum_convL_geps
#print axioms PAG.Part250.addEAlg_eq_shellAlg_iff
#print axioms PAG.Part250.convL_geps_eq_one_sub
#print axioms PAG.Part250.addEAlg_eq_shellAlg_of_card_le_two
#print axioms PAG.Part250.card_devSet_le_two_iff
#print axioms PAG.Part250.uperp_dind_mul
#print axioms PAG.Part250.convL_geps_eq_zero_of_uperp
#print axioms PAG.Part250.exists_apply_of_mem_addEAlg
#print axioms PAG.Part250.exists_apply_eq_smul_of_mem_addEAlg
#print axioms PAG.Part250.twoPt
#print axioms PAG.Part250.shellAvg_twoPt
#print axioms PAG.Part250.dind_one_mul_twoPt
#print axioms PAG.Part250.conv_single
#print axioms PAG.Part250.geps_add_of_dvd
#print axioms PAG.Part250.convL_geps_twoPt
#print axioms PAG.Part250.dft_single
#print axioms PAG.Part250.dft_twoPt_ne_zero
#print axioms PAG.Part250.convL_geps_one_not_mem_addEAlg_of_witness
#print axioms PAG.Part250.exists_witness_coeff
#print axioms PAG.Part250.convL_geps_one_not_mem_addEAlg
#print axioms PAG.Part250.addEAlg_ne_shellAlg
#print axioms PAG.Part250.addEAlg_ne_shellAlg_of_squarefree
#print axioms PAG.Part250.dualAddEAlg
#print axioms PAG.Part250.map_fourierConj_addEAlg
#print axioms PAG.Part250.finrank_dualAddEAlg
#print axioms PAG.Part250.dualAddEAlg_eq_shellAlg_iff
#print axioms PAG.Part250.mulLeft_dind_one_not_mem_dualAddEAlg
