/-
  PAG 2.0 Part 211（2026-10-25）— ブロックの中の双対基底と、ブロックへの直交射影（直交分解）
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。u, v, w は L の約数
  k_u = |u, χ⟩_N（Part 210 の kblock）、G = (⟨k_u, k_u′⟩)（Part 209 の blockGram）、H = G⁻¹（Part 210 の blockGramInv）
  k^∨_u = Part 208 の双対ベクトル kdual（g_{s₀/e, χ̄′} の和で定義）、G_v = g_{N/(vc), χ̄′}（Part 210 の gblock）
  0. 一意性：すべてのケットとの内積が等しいベクトルは等しい
  1. 主定理：k^∨_u = Σ_{u′} conj(H(u, u′))·k_{u′}（双対ベクトルはブロックの中のケットで書ける）
  2. 系：座標 ⟨k^∨_u, f⟩ = Σ_{u′} H(u, u′)·⟨k_{u′}, f⟩、双対ベクトルはブロックの張る空間に入る、
     双対ベクトルのグラム行列 ⟨k^∨_u, k^∨_w⟩ = H(u, w)、大きさ ‖k^∨_u‖² = (N/|B_u|²)·Σ_{v ∣ L, u ∣ v} μ(v/u)²|χ(v/u)|²/φ(vc)、
     Part 208 の定義のブロックの記号での形 k^∨_u = Σ_{v ∣ L, u ∣ v} conj(B_u⁻¹μ(v/u)χ̄(v/u)·N/φ(vc))·G_v、
     ブロックの張る空間 span{k_u} = span{G_v}
  3. ブロックのケットが直交する条件：(u ≠ u′ ⇒ ⟨k_u, k_u′⟩ = 0) ⇔ rad(N/c) ∣ c。そのときブロックは正規直交で k^∨_u = k_u
  4. ブロックへの直交射影 P f = Σ_u ⟨k^∨_u, f⟩·k_u：f − P f はブロックと直交、ほかのブロックで 0、P k_w = k_w、P² = P、
     自己共役、違うブロックの射影は直交。直交分解 f = Σ_{(c, χ)} P_{c,χ} f
-/
import PAG214

namespace PAG.Part215

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** u ∣ N ≠ 0 なら N/u ≠ 0。 -/
theorem div_ne_zero_of_dvd {N u : ℕ} (hN : N ≠ 0) (hu : u ∣ N) : N / u ≠ 0 := by
  intro h0
  have := Nat.mul_div_cancel' hu
  rw [h0, mul_zero] at this
  exact hN this.symm

/-- **0b.** ⟨a, b⟩ = conj⟨b, a⟩。 -/
theorem inner_conj_symm {N : ℕ} [NeZero N] (a b : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (a x) * b x = starRingEnd ℂ (∑ x, starRingEnd ℂ (b x) * a x) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- **0c. 一意性**：すべてのケットとの内積が等しい 2 つのベクトルは等しい。 -/
theorem eq_of_inner_ketFam_eq (N : ℕ) [NeZero N] (D E : ZMod N → ℂ)
    (h : ∀ j : KetIdx N,
      ∑ x, starRingEnd ℂ (D x) * ketFam N j x = ∑ x, starRingEnd ℂ (E x) * ketFam N j x) :
    D = E := by
  classical
  let _ := Fintype.ofFinite (KetIdx N)
  have hall : ∀ f : ZMod N → ℂ, ∑ x, starRingEnd ℂ (D x) * f x = ∑ x, starRingEnd ℂ (E x) * f x := by
    intro f
    rw [← (ketBasis N).sum_repr f, inner_sum_smul_right, inner_sum_smul_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ketBasis_apply, h j]
  funext y
  have e1 : ∀ F : ZMod N → ℂ,
      ∑ x, starRingEnd ℂ (F x) * (fun x => if x = y then (1 : ℂ) else 0) x = starRingEnd ℂ (F y) := by
    intro F
    rw [Finset.sum_eq_single y]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  have hy := hall (fun x => if x = y then 1 else 0)
  rw [e1, e1] at hy
  exact (starRingEnd ℂ).injective hy

/-- **0d.** 約数の算術：c ∣ N、N/c = U·m·k（U, c > 0、N/c ≠ 0）なら N/c/U/m = k、N/k = U·m·c、N/(U·m·c) = k。 -/
theorem div_shell_aux {N c U m k : ℕ} (hcN : c ∣ N) (hU : 0 < U) (hc : 0 < c) (hk : N / c = U * m * k)
    (hL0 : N / c ≠ 0) : N / c / U / m = k ∧ N / k = U * m * c ∧ N / (U * m * c) = k := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero, zero_mul] at hk; exact hL0 hk)
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hk; exact hL0 hk)
  have hNc : N = U * m * k * c := by
    rw [← hk]
    exact (Nat.div_mul_cancel hcN).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hk, show U * m * k = U * (m * k) by ring, Nat.mul_div_cancel_left _ hU, Nat.mul_div_cancel_left k hm0]
  · apply Nat.div_eq_of_eq_mul_left hk0
    rw [hNc]
    ring
  · apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos (Nat.mul_pos hU hm0) hc)
    rw [hNc]
    ring

/-- ブロック (c, χ) の番号 u に対応するケットの番号 (u, c, χ)。 -/
def blockIdx (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (u : (N / c).divisors) : KetIdx N :=
  ⟨⟨u, Nat.mem_divisors.mpr ⟨(block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).1, NeZero.ne N⟩⟩,
    ⟨c, Nat.mem_divisors.mpr ⟨(block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).2,
      div_ne_zero_of_dvd (NeZero.ne N) (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).1⟩⟩, ⟨χ, hχ⟩⟩

/-- **0e.** 番号 (u, c, χ) のケットはブロックのケット k_u。 -/
theorem ketFam_blockIdx (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive)
    (u : (N / c).divisors) : ketFam N (blockIdx N c hcN χ hχ u) = kblock N c χ u :=
  (kblock_of_dvd N c χ (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).1
    (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).2).symm

/-- **0f.** 番号 (u, c, χ) の双対ベクトルは kdual N u c χ。 -/
theorem kdualI_blockIdx (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) : kdualI N (blockIdx N c hcN χ hχ u) = kdual N u c χ :=
  rfl

/-- **0g.** ブロックのケットどうしの内積はグラム行列の成分。 -/
theorem inner_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (u u' : (N / c).divisors) :
    ∑ x, starRingEnd ℂ (kblock N c χ u x) * kblock N c χ u' x = blockGram N c hcN χ u u' := by
  rw [kblock_of_dvd N c χ (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).1
      (block_dvd hcN (Nat.dvd_of_mem_divisors u.2)).2,
    kblock_of_dvd N c χ (block_dvd hcN (Nat.dvd_of_mem_divisors u'.2)).1
      (block_dvd hcN (Nat.dvd_of_mem_divisors u'.2)).2]
  rfl

/-- **0h.** H·G = 1（χ 原始的）。 -/
theorem blockGramInv_mul_blockGram (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : blockGramInv N c χ * blockGram N c hcN χ = 1 :=
  mul_eq_one_comm.mp (blockGram_mul_blockGramInv N c hcN χ hχ)

/-- **0i.** H の成分：H(u, u′) = B_u⁻¹·A_χ⁻¹(u, u′)·N/conj(B_{u′})。 -/
theorem blockGramInv_apply (N c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (u u' : (N / c).divisors) :
    blockGramInv N c χ u u' =
      (kcoef (N / u) c χ)⁻¹ * blockAinv (N / c) c χ u u' * ((N : ℂ) / starRingEnd ℂ (kcoef (N / u') c χ)) := by
  simp only [blockGramInv, Matrix.mul_diagonal, Matrix.diagonal_mul]

/-! ### 1. ブロックの中の双対基底 -/

/-- ブロックの中の双対ベクトル：Σ_{u′} conj(H(u, u′))·k_{u′}。 -/
noncomputable def kdualB (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (u : (N / c).divisors) :
    ZMod N → ℂ :=
  ∑ u' : (N / c).divisors, starRingEnd ℂ (blockGramInv N c χ u u') • kblock N c χ u'

/-- **1a.** ⟨Σ_{u′} conj(H(u, u′))·k_{u′}, k_w⟩ = [u = w]（同じブロック、χ 原始的）。 -/
theorem inner_kdualB_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u w : (N / c).divisors) :
    ∑ x, starRingEnd ℂ (kdualB N c χ u x) * kblock N c χ w x = if u = w then 1 else 0 := by
  unfold kdualB
  rw [inner_sum_smul_left]
  simp only [Complex.conj_conj, inner_kblock N c hcN χ]
  have e := congrFun (congrFun (blockGramInv_mul_blockGram N c hcN χ hχ) u) w
  rw [Matrix.mul_apply, Matrix.one_apply] at e
  exact e

/-- **1b.** ほかのブロックのケットとは直交：ketClass j ≠ (c, χ) なら ⟨Σ_{u′} conj(H(u, u′))·k_{u′}, k_j⟩ = 0。 -/
theorem inner_kdualB_ketFam_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) (j : KetIdx N) (hne : ketClass j ≠ ⟨c, χ⟩) :
    ∑ x, starRingEnd ℂ (kdualB N c χ u x) * ketFam N j x = 0 := by
  unfold kdualB
  rw [inner_sum_smul_left]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [← ketFam_blockIdx N c hcN χ hχ w,
    inner_ketFam_of_ketClass_ne N (blockIdx N c hcN χ hχ w) j (fun e => hne e.symm), mul_zero]

open Classical in
/-- **1c.** 番号の形：⟨Σ_{u′} conj(H(u, u′))·k_{u′}, k_j⟩ = [(u, c, χ) = j]。 -/
theorem inner_kdualB_ketFam (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) (j : KetIdx N) :
    ∑ x, starRingEnd ℂ (kdualB N c χ u x) * ketFam N j x = if blockIdx N c hcN χ hχ u = j then 1 else 0 := by
  obtain ⟨⟨u', hu'⟩, ⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := j
  by_cases hcc : c = c'
  · subst hcc
    by_cases hχχ : χ = χ'
    · subst hχχ
      have hu'L : u' ∈ (N / c).divisors := ((mem_block_iff N u' c (NeZero.ne N)).mp ⟨hu', hc'⟩).2
      have e : ketFam N ⟨⟨u', hu'⟩, ⟨c, hc'⟩, ⟨χ, hχ'⟩⟩ =
          kblock N c χ ((⟨u', hu'L⟩ : (N / c).divisors) : ℕ) :=
        (kblock_of_dvd N c χ (Nat.dvd_of_mem_divisors hu') (Nat.dvd_of_mem_divisors hc')).symm
      rw [e, inner_kdualB_kblock N c hcN χ hχ u ⟨u', hu'L⟩]
      by_cases huu : u = ⟨u', hu'L⟩
      · subst huu
        rw [ite_eq_left rfl, ite_eq_left (show blockIdx N c hcN χ hχ ⟨u', hu'L⟩ =
          ⟨⟨u', hu'⟩, ⟨c, hc'⟩, ⟨χ, hχ'⟩⟩ from rfl)]
      · rw [ite_eq_right huu, ite_eq_right]
        intro hb
        exact huu (Subtype.ext (congrArg (fun i : KetIdx N => (i.1 : ℕ)) hb))
    · rw [inner_kdualB_ketFam_of_ne N c hcN χ hχ u _ ?_, ite_eq_right]
      · intro hb
        have hcl := congrArg ketClass hb
        exact hχχ (eq_of_heq (Sigma.mk.inj_iff.mp hcl).2)
      · intro hcl
        exact hχχ (eq_of_heq (Sigma.mk.inj_iff.mp hcl).2).symm
  · rw [inner_kdualB_ketFam_of_ne N c hcN χ hχ u _ ?_, ite_eq_right]
    · intro hb
      exact hcc (congrArg (fun i : KetIdx N => (i.2.1 : ℕ)) hb)
    · intro hcl
      exact hcc (congrArg Sigma.fst hcl).symm

/-- **1d. 主定理**：Part 208 の双対ベクトルは、ブロックのケットとグラム行列の逆行列で書ける：
k^∨_u = Σ_{u′} conj(G⁻¹(u, u′))·k_{u′}（χ 原始的）。 -/
theorem kdual_eq_kdualB (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) :
    kdual N u c χ = kdualB N c χ u := by
  apply eq_of_inner_ketFam_eq N
  intro j
  rw [← kdualI_blockIdx N c hcN χ hχ u, inner_kdualI_ketFam, inner_kdualB_ketFam N c hcN χ hχ u j]

/-! ### 2. 系 -/

/-- **2a. 座標**：⟨k^∨_u, f⟩ = Σ_{u′} G⁻¹(u, u′)·⟨k_{u′}, f⟩。 -/
theorem inner_kdual_eq_sum (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * f x =
      ∑ u' : (N / c).divisors, blockGramInv N c χ u u' * ∑ x, starRingEnd ℂ (kblock N c χ u' x) * f x := by
  rw [kdual_eq_kdualB N c hcN χ hχ u]
  unfold kdualB
  rw [inner_sum_smul_left]
  simp only [Complex.conj_conj]

/-- **2b.** ケット基底での座標：(ketBasis N).repr f (u, c, χ) = Σ_{u′} G⁻¹(u, u′)·⟨k_{u′}, f⟩。 -/
theorem ketBasis_repr_blockIdx (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) (f : ZMod N → ℂ) :
    (ketBasis N).repr f (blockIdx N c hcN χ hχ u) =
      ∑ u' : (N / c).divisors, blockGramInv N c χ u u' * ∑ x, starRingEnd ℂ (kblock N c χ u' x) * f x := by
  rw [ketBasis_repr, kdualI_blockIdx, inner_kdual_eq_sum N c hcN χ hχ u f]

/-- **2c.** 双対ベクトルはブロックの張る空間に入る。 -/
theorem kdual_mem_span (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) :
    kdual N u c χ ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w) := by
  rw [kdual_eq_kdualB N c hcN χ hχ u]
  exact Submodule.sum_mem _ (fun w _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩))

/-- **2d. 双対ベクトルのグラム行列**：⟨k^∨_u, k^∨_w⟩ = G⁻¹(u, w)。 -/
theorem inner_kdual_kdual (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u w : (N / c).divisors) :
    ∑ x, starRingEnd ℂ (kdual N u c χ x) * kdual N w c χ x = blockGramInv N c χ u w := by
  have hw : ∀ u' : (N / c).divisors,
      ∑ x, starRingEnd ℂ (kblock N c χ u' x) * kdual N w c χ x = if w = u' then 1 else 0 := by
    intro u'
    rw [inner_conj_symm, kdual_eq_kdualB N c hcN χ hχ w, inner_kdualB_kblock N c hcN χ hχ w u']
    split_ifs <;> simp
  rw [inner_kdual_eq_sum N c hcN χ hχ u]
  simp only [hw, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **2e. 双対ベクトルの大きさ**：‖k^∨_u‖² = (N/|B_u|²)·Σ_{v ∣ L, u ∣ v} μ(v/u)²·|χ(v/u)|²/φ(vc)。 -/
theorem normSq_kdual (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : (N / c).divisors) :
    ((∑ x, Complex.normSq (kdual N u c χ x) : ℝ) : ℂ) =
      (N : ℂ) / (Complex.normSq (kcoef (N / u) c χ) : ℂ) *
        ∑ v ∈ (N / c).divisors.filter (fun v => (u : ℕ) ∣ v),
          (ArithmeticFunction.moebius (v / u) : ℂ) ^ 2 * (Complex.normSq (χ ((v / u : ℕ) : ZMod c)) : ℂ) /
            (Nat.totient (v * c) : ℂ) := by
  obtain ⟨h1, h2⟩ := block_dvd hcN (Nat.dvd_of_mem_divisors u.2)
  have hB : kcoef (N / u) c χ ≠ 0 :=
    kcoef_ne_zero (N / u) c (div_ne_zero_of_dvd (NeZero.ne N) h1) h2 χ hχ
  have hBc : starRingEnd ℂ (kcoef (N / u) c χ) ≠ 0 := (map_ne_zero _).mpr hB
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hn : ((∑ x, Complex.normSq (kdual N u c χ x) : ℝ) : ℂ) =
      ∑ x, starRingEnd ℂ (kdual N u c χ x) * kdual N u c χ x := by
    push_cast
    exact Finset.sum_congr rfl (fun x _ => Complex.normSq_eq_conj_mul_self)
  have hfilt : (N / c).divisors.filter (fun v => (u : ℕ) ∣ v ∧ (u : ℕ) ∣ v) =
      (N / c).divisors.filter (fun v => (u : ℕ) ∣ v) := by
    simp only [and_self]
  rw [hn, inner_kdual_kdual N c hcN χ hχ u u, blockGramInv_apply, blockAinv_apply, hfilt,
    Complex.normSq_eq_conj_mul_self]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  have hφ : (Nat.totient (v * c) : ℂ) ≠ 0 := by
    have hv0 : 0 < v := Nat.pos_of_mem_divisors (Finset.mem_filter.mp ‹v ∈ _›).1
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hv0 (Nat.pos_of_ne_zero (NeZero.ne c)))).ne'
  have hχv : χ⁻¹ ((v / u : ℕ) : ZMod c) * χ ((v / u : ℕ) : ZMod c) =
      (Complex.normSq (χ ((v / u : ℕ) : ZMod c)) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self, ← MulChar.star_apply', starRingEnd_apply]
  rw [← hχv]
  field_simp

/-- **2f.** Part 208 の定義をブロックの記号で書いたもの：
k^∨_u = Σ_{v ∣ L, u ∣ v} conj(B_u⁻¹·μ(v/u)χ̄(v/u)·N/φ(vc))·G_v（G_v は u の倍数の番号だけが現れる）。 -/
theorem kdual_eq_sum_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (u : (N / c).divisors) :
    kdual N u c χ = ∑ v ∈ (N / c).divisors.filter (fun v => (u : ℕ) ∣ v),
      starRingEnd ℂ ((kcoef (N / u) c χ)⁻¹ * ((ArithmeticFunction.moebius (v / u) : ℂ) * χ⁻¹ ((v / u : ℕ) : ZMod c)) *
        ((N : ℂ) / (Nat.totient (v * c) : ℂ))) • gblock N c χ v := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  have huL : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
  have hu0 : 0 < (u : ℕ) := Nat.pos_of_mem_divisors u.2
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hdiv : N / (u : ℕ) / c = N / c / u := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
  unfold kdual
  rw [hdiv, ← sum_divisors_filter_dvd (N / c) u hL0 huL]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hvL : v ∣ N / c := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hv).1
  have huv : (u : ℕ) ∣ v := (Finset.mem_filter.mp hv).2
  obtain ⟨k, hk⟩ := hvL
  obtain ⟨m, rfl⟩ := huv
  have hm : (u : ℕ) * m / u = m := Nat.mul_div_cancel_left m hu0
  obtain ⟨hq, hn, hs⟩ := div_shell_aux hcN hu0 hc0 hk hL0
  rw [hm, hq, hn]
  unfold gblock
  rw [hs]

/-- **2g. ブロックの張る空間**：span{k_u : u ∣ L} = span{G_v : v ∣ L}（χ 原始的）。 -/
theorem span_kblock_eq_span_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    Submodule.span ℂ (Set.range fun u : (N / c).divisors => kblock N c χ u) =
      Submodule.span ℂ (Set.range fun v : (N / c).divisors => gblock N c χ v) := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    change kblock N c χ u ∈ Submodule.span ℂ _
    rw [kblock_eq_sum N c hcN χ hχ u (Nat.dvd_of_mem_divisors u.2)]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun v hv => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨v, ?_⟩, rfl⟩)))
    exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hv) (Nat.dvd_of_mem_divisors u.2), hL0⟩
  · rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    change gblock N c χ v ∈ Submodule.span ℂ _
    rw [gblock_eq_sum N c hcN χ hχ v (Nat.dvd_of_mem_divisors v.2)]
    refine Submodule.sum_mem _ (fun w hw => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨w, ?_⟩, rfl⟩))
    exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors hw) (Nat.dvd_of_mem_divisors v.2), hL0⟩

/-! ### 3. ブロックのケットが直交する条件 -/

/-- **3a.** rad(L) ∣ c で x ∣ L、x ≠ 1 なら χ(x) = 0。 -/
theorem chi_eq_zero_of_rad {L c x : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ L → p ∣ c) (hx : x ∣ L) (hx1 : x ≠ 1) : χ (x : ZMod c) = 0 := by
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd hx1
  apply MulChar.map_nonunit
  intro hu
  rw [ZMod.isUnit_iff_coprime] at hu
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpx hu)
    (hrad p hp (dvd_trans hpx hx)))

/-- **3b.** rad(L) ∣ c なら A_χ は対角：A_χ(u, u′) = [u = u′]·φ(uc)（χ は法 c のどの指標でもよい）。 -/
theorem blockA_of_rad (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c)
    (hrad : ∀ p : ℕ, p.Prime → p ∣ L → p ∣ c) (u u' : L.divisors) :
    blockA L c χ u u' = if u = u' then (Nat.totient ((u : ℕ) * c) : ℂ) else 0 := by
  have huL : (u : ℕ) ∣ L := Nat.dvd_of_mem_divisors u.2
  have hu'L : (u' : ℕ) ∣ L := Nat.dvd_of_mem_divisors u'.2
  have hu0 : (u : ℕ) ≠ 0 := (Nat.pos_of_mem_divisors u.2).ne'
  simp only [blockA, Matrix.of_apply]
  have hterm : ∀ v ∈ (Nat.gcd (u : ℕ) u').divisors, v ≠ (u : ℕ) ∨ v ≠ (u' : ℕ) →
      χ (((u : ℕ) / v : ℕ) : ZMod c) * χ⁻¹ (((u' : ℕ) / v : ℕ) : ZMod c) * (Nat.totient (v * c) : ℂ) = 0 := by
    intro v hv hne
    have hvg : v ∣ Nat.gcd (u : ℕ) u' := Nat.dvd_of_mem_divisors hv
    have hvu : v ∣ (u : ℕ) := dvd_trans hvg (Nat.gcd_dvd_left _ _)
    have hvu' : v ∣ (u' : ℕ) := dvd_trans hvg (Nat.gcd_dvd_right _ _)
    rcases hne with h | h
    · have h1 : (u : ℕ) / v ≠ 1 := fun e => h (by rw [← Nat.div_mul_cancel hvu, e, one_mul])
      rw [chi_eq_zero_of_rad χ hrad (dvd_trans (Nat.div_dvd_of_dvd hvu) huL) h1, zero_mul, zero_mul]
    · have h1 : (u' : ℕ) / v ≠ 1 := fun e => h (by rw [← Nat.div_mul_cancel hvu', e, one_mul])
      rw [chi_eq_zero_of_rad χ⁻¹ hrad (dvd_trans (Nat.div_dvd_of_dvd hvu') hu'L) h1, mul_zero, zero_mul]
  by_cases huu : u = u'
  · subst huu
    rw [ite_eq_left rfl, Finset.sum_eq_single (u : ℕ)]
    · rw [Nat.div_self (Nat.pos_of_ne_zero hu0), Nat.cast_one, map_one, map_one, one_mul, one_mul]
    · intro v hv hne
      exact hterm v hv (Or.inl hne)
    · intro h
      rw [Nat.gcd_self] at h
      exact absurd (Nat.mem_divisors_self _ hu0) h
  · rw [ite_eq_right huu]
    refine Finset.sum_eq_zero (fun v hv => hterm v hv ?_)
    by_cases h1 : v = (u : ℕ)
    · right
      intro h2
      exact huu (Subtype.ext (h1.symm.trans h2))
    · left
      exact h1

/-- **3c. ブロックのケットが直交する条件**：(u ≠ u′ ⇒ ⟨k_u, k_u′⟩ = 0) ⇔ rad(N/c) ∣ c（χ 原始的）。 -/
theorem blockGram_offDiag_iff (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (∀ u u' : (N / c).divisors, u ≠ u' → blockGram N c hcN χ u u' = 0) ↔
      ∀ p : ℕ, p.Prime → p ∣ N / c → p ∣ c := by
  have hL0 : N / c ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) hcN
  constructor
  · intro H p hp hpL
    by_contra hpc
    have hpmem : p ∈ (N / c).divisors := Nat.mem_divisors.mpr ⟨hpL, hL0⟩
    have h1mem : 1 ∈ (N / c).divisors := Nat.mem_divisors.mpr ⟨one_dvd _, hL0⟩
    have hne : (⟨p, hpmem⟩ : (N / c).divisors) ≠ ⟨1, h1mem⟩ :=
      fun e => hp.one_lt.ne' (congrArg Subtype.val e)
    have hG := H _ _ hne
    rw [blockGram_eq N c hcN χ hχ] at hG
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, blockA, Matrix.of_apply] at hG
    rw [Nat.gcd_one_right, Nat.divisors_one, Finset.sum_singleton, Nat.div_one, Nat.div_one, one_mul,
      Nat.cast_one, map_one, mul_one] at hG
    obtain ⟨hp1, hp2⟩ := block_dvd hcN hpL
    obtain ⟨h11, h12⟩ := block_dvd hcN (one_dvd (N / c))
    have hBp : kcoef (N / p) c χ ≠ 0 :=
      kcoef_ne_zero (N / p) c (div_ne_zero_of_dvd (NeZero.ne N) hp1) hp2 χ hχ
    have hB1 : kcoef (N / 1) c χ ≠ 0 :=
      kcoef_ne_zero (N / 1) c (div_ne_zero_of_dvd (NeZero.ne N) h11) h12 χ hχ
    have hχp : χ (p : ZMod c) ≠ 0 :=
      ((ZMod.isUnit_iff_coprime p c).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpc)).map χ |>.ne_zero
    have hφ : (Nat.totient c : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne c))).ne'
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    exact mul_ne_zero (mul_ne_zero (div_ne_zero ((map_ne_zero _).mpr hBp) hNC) (mul_ne_zero hχp hφ)) hB1 hG
  · intro hrad u u' hne
    rw [blockGram_eq N c hcN χ hχ]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [blockA_of_rad (N / c) c χ hrad u u', ite_eq_right hne, mul_zero, zero_mul]

/-- **3d.** rad(N/c) ∣ c ならブロックのケットは正規直交：G = 1。 -/
theorem blockGram_eq_one_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hrad : ∀ p : ℕ, p.Prime → p ∣ N / c → p ∣ c) : blockGram N c hcN χ = 1 := by
  ext u u'
  by_cases huu : u = u'
  · subst huu
    rw [Matrix.one_apply_eq]
    obtain ⟨h1, h2⟩ := block_dvd hcN (Nat.dvd_of_mem_divisors u.2)
    have hs0 : N / u / c ∣ N / c := by
      have e : N / u / c = N / c / u := by
        rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
      rw [e]
      exact Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors u.2)
    have hk := (normSq_gket_eq_one_iff (u : ℕ) (N / u) N (Nat.mul_div_cancel' h1) c h2 χ).mpr
      (fun p hp hps => hrad p hp (dvd_trans hps hs0))
    rw [← inner_kblock N c hcN χ u u, kblock_of_dvd N c χ h1 h2]
    have e2 : ∑ x, starRingEnd ℂ (gket (u : ℕ) (N / u) N (Nat.mul_div_cancel' h1) c h2 χ x) *
        gket (u : ℕ) (N / u) N (Nat.mul_div_cancel' h1) c h2 χ x =
        ((∑ x, Complex.normSq (gket (u : ℕ) (N / u) N (Nat.mul_div_cancel' h1) c h2 χ x) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun x _ => Complex.normSq_eq_conj_mul_self.symm)
    rw [e2, hk, Complex.ofReal_one]
  · rw [Matrix.one_apply_ne huu]
    exact (blockGram_offDiag_iff N c hcN χ hχ).mpr hrad u u' huu

/-- **3e.** rad(N/c) ∣ c なら双対ベクトルはケット自身：k^∨_u = k_u。 -/
theorem kdual_eq_kblock_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hrad : ∀ p : ℕ, p.Prime → p ∣ N / c → p ∣ c) (u : (N / c).divisors) :
    kdual N u c χ = kblock N c χ u := by
  have hH : blockGramInv N c χ = 1 := by
    have e := blockGram_mul_blockGramInv N c hcN χ hχ
    rwa [blockGram_eq_one_of_rad N c hcN χ hχ hrad, one_mul] at e
  rw [kdual_eq_kdualB N c hcN χ hχ u]
  unfold kdualB
  rw [hH, Finset.sum_eq_single u]
  · rw [Matrix.one_apply_eq, map_one, one_smul]
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), map_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-! ### 4. ブロックへの直交射影と直交分解 -/

/-- ブロック (c, χ) への射影：P f = Σ_{u ∣ N/c} ⟨k^∨_u, f⟩·k_u（ケット基底の展開のうち、ブロックの部分）。 -/
noncomputable def blockProj (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    ZMod N → ℂ :=
  ∑ u : (N / c).divisors, (∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) • kblock N c χ u

/-- **4a.** P f はブロックの張る空間に入る。 -/
theorem blockProj_mem_span (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    blockProj N c χ f ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w) :=
  Submodule.sum_mem _ (fun w _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩))

/-- **4b.** f − P f はブロックのケットと直交：⟨k_w, P f⟩ = ⟨k_w, f⟩。 -/
theorem inner_kblock_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (w : (N / c).divisors) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (kblock N c χ w x) * blockProj N c χ f x =
      ∑ x, starRingEnd ℂ (kblock N c χ w x) * f x := by
  unfold blockProj
  rw [inner_sum_smul_right]
  simp only [inner_kblock N c hcN χ, inner_kdual_eq_sum N c hcN χ hχ, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hGH : ∀ u' : (N / c).divisors,
      ∑ u : (N / c).divisors, blockGramInv N c χ u u' * (∑ x, starRingEnd ℂ (kblock N c χ u' x) * f x) *
        blockGram N c hcN χ w u =
      (if w = u' then 1 else 0) * ∑ x, starRingEnd ℂ (kblock N c χ u' x) * f x := by
    intro u'
    have e := congrFun (congrFun (blockGram_mul_blockGramInv N c hcN χ hχ) w) u'
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    rw [← e, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  simp only [hGH, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- **4c.** ほかのブロックのケットとは直交：ketClass j ≠ (c, χ) なら ⟨k_j, P f⟩ = 0。 -/
theorem inner_ketFam_blockProj_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) (j : KetIdx N) (hne : ketClass j ≠ ⟨c, χ⟩) :
    ∑ x, starRingEnd ℂ (ketFam N j x) * blockProj N c χ f x = 0 := by
  unfold blockProj
  rw [inner_sum_smul_right]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [← ketFam_blockIdx N c hcN χ hχ w, inner_ketFam_of_ketClass_ne N j (blockIdx N c hcN χ hχ w) hne, mul_zero]

/-- **4d.** P k_w = k_w（同じブロックのケット）。 -/
theorem blockProj_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (w : (N / c).divisors) : blockProj N c χ (kblock N c χ w) = kblock N c χ w := by
  have h : ∀ u : (N / c).divisors,
      ∑ x, starRingEnd ℂ (kdual N u c χ x) * kblock N c χ w x = if u = w then 1 else 0 := by
    intro u
    rw [kdual_eq_kdualB N c hcN χ hχ u, inner_kdualB_kblock N c hcN χ hχ u w]
  unfold blockProj
  simp only [h, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp

/-- **4e.** P k_j = 0（ほかのブロックのケット）。 -/
theorem blockProj_ketFam_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (j : KetIdx N) (hne : ketClass j ≠ ⟨c, χ⟩) : blockProj N c χ (ketFam N j) = 0 := by
  unfold blockProj
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [kdual_eq_kdualB N c hcN χ hχ u, inner_kdualB_ketFam_of_ne N c hcN χ hχ u j hne, zero_smul]

/-- **4f.** P は冪等：P (P f) = P f。 -/
theorem blockProj_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) : blockProj N c χ (blockProj N c χ f) = blockProj N c χ f := by
  have h : ∀ u : (N / c).divisors,
      ∑ x, starRingEnd ℂ (kdual N u c χ x) * blockProj N c χ f x = ∑ x, starRingEnd ℂ (kdual N u c χ x) * f x := by
    intro u
    have hk : ∀ w : (N / c).divisors,
        ∑ x, starRingEnd ℂ (kdual N u c χ x) * kblock N c χ w x = if u = w then 1 else 0 := fun w => by
      rw [kdual_eq_kdualB N c hcN χ hχ u, inner_kdualB_kblock N c hcN χ hχ u w]
    unfold blockProj
    rw [inner_sum_smul_right]
    simp only [hk, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  calc blockProj N c χ (blockProj N c χ f)
      = ∑ u : (N / c).divisors, (∑ x, starRingEnd ℂ (kdual N u c χ x) * blockProj N c χ f x) •
          kblock N c χ u := rfl
    _ = ∑ u : (N / c).divisors, (∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) • kblock N c χ u := by
        simp only [h]
    _ = blockProj N c χ f := rfl

/-- **4g.** ブロックの張る空間のベクトル p = Σ_u d_u·k_u について ⟨p, P f⟩ = ⟨p, f⟩。 -/
theorem inner_span_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (d : (N / c).divisors → ℂ) (f : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ ((∑ u : (N / c).divisors, d u • kblock N c χ u) x) * blockProj N c χ f x =
      ∑ x, starRingEnd ℂ ((∑ u : (N / c).divisors, d u • kblock N c χ u) x) * f x := by
  rw [inner_sum_smul_left, inner_sum_smul_left]
  simp only [inner_kblock_blockProj N c hcN χ hχ]

/-- **4h.** P は自己共役：⟨P f, g⟩ = ⟨f, P g⟩。 -/
theorem inner_blockProj_comm (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (blockProj N c χ f x) * g x = ∑ x, starRingEnd ℂ (f x) * blockProj N c χ g x := by
  have h1 : ∑ x, starRingEnd ℂ (blockProj N c χ f x) * blockProj N c χ g x =
      ∑ x, starRingEnd ℂ (blockProj N c χ f x) * g x :=
    inner_span_blockProj N c hcN χ hχ (fun u => ∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) g
  have h2 : ∑ x, starRingEnd ℂ (blockProj N c χ g x) * blockProj N c χ f x =
      ∑ x, starRingEnd ℂ (blockProj N c χ g x) * f x :=
    inner_span_blockProj N c hcN χ hχ (fun u => ∑ x, starRingEnd ℂ (kdual N u c χ x) * g x) f
  rw [← h1, inner_conj_symm f (blockProj N c χ g), ← h2, ← inner_conj_symm]

/-- **4i.** 違うブロックへの射影は直交：(c, χ) ≠ (c′, χ′) なら ⟨P_{c,χ} f, P_{c′,χ′} g⟩ = 0。 -/
theorem inner_blockProj_of_ne (N c c' : ℕ) [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    (χ : DirichletCharacter ℂ c) (χ' : DirichletCharacter ℂ c') (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    (hne : (⟨c, χ⟩ : Σ c : ℕ, DirichletCharacter ℂ c) ≠ ⟨c', χ'⟩) (f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (blockProj N c χ f x) * blockProj N c' χ' g x = 0 := by
  rw [show blockProj N c χ f = ∑ u : (N / c).divisors, (∑ x, starRingEnd ℂ (kdual N u c χ x) * f x) •
    kblock N c χ u from rfl, inner_sum_smul_left]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [← ketFam_blockIdx N c hcN χ hχ u,
    inner_ketFam_blockProj_of_ne N c' hc'N χ' hχ' g (blockIdx N c hcN χ hχ u) hne, mul_zero]

/-- ブロックの番号：(c, χ)（c ∣ N、χ は法 c の原始指標）。 -/
abbrev BlockIdx (N : ℕ) : Type :=
  Σ c : N.divisors, {χ : DirichletCharacter ℂ c // χ.IsPrimitive}

/-- 番号 b = (c, χ) のブロックへの射影。 -/
noncomputable def blockProjI (N : ℕ) [NeZero N] (b : BlockIdx N) (f : ZMod N → ℂ) : ZMod N → ℂ :=
  @blockProj N b.1 _ ⟨(Nat.pos_of_mem_divisors b.1.2).ne'⟩ b.2.1 f

/-- (ブロック (c, χ), ブロックの中の番号 u) とケットの番号 (u, c, χ) の対応。 -/
def blockEquiv (N : ℕ) [NeZero N] : (Σ b : BlockIdx N, (N / (b.1 : ℕ)).divisors) ≃ KetIdx N where
  toFun p := blockIdx N p.1.1 (Nat.dvd_of_mem_divisors p.1.1.2) p.1.2.1 p.1.2.2 p.2
  invFun i := ⟨⟨⟨i.2.1, ((mem_block_iff N i.1 i.2.1 (NeZero.ne N)).mp ⟨i.1.2, i.2.1.2⟩).1⟩, i.2.2⟩,
    ⟨i.1, ((mem_block_iff N i.1 i.2.1 (NeZero.ne N)).mp ⟨i.1.2, i.2.1.2⟩).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **4j. 直交分解**：f = Σ_{(c, χ)} P_{c,χ} f（ブロックの番号の Fintype はどれでもよい）。 -/
theorem sum_blockProjI (N : ℕ) [NeZero N] [Fintype (BlockIdx N)] (f : ZMod N → ℂ) :
    f = ∑ b : BlockIdx N, blockProjI N b f := by
  classical
  let _ : Fintype (KetIdx N) := Fintype.ofEquiv _ (blockEquiv N)
  conv_lhs => rw [eq_sum_kdualI N f]
  rw [← Equiv.sum_comp (blockEquiv N), Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have : NeZero (b.1 : ℕ) := ⟨(Nat.pos_of_mem_divisors b.1.2).ne'⟩
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [show blockEquiv N ⟨b, u⟩ = blockIdx N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 u from rfl,
    kdualI_blockIdx, ketFam_blockIdx]

end PAG.Part215

#print axioms PAG.Part215.div_ne_zero_of_dvd
#print axioms PAG.Part215.inner_conj_symm
#print axioms PAG.Part215.eq_of_inner_ketFam_eq
#print axioms PAG.Part215.div_shell_aux
#print axioms PAG.Part215.blockIdx
#print axioms PAG.Part215.ketFam_blockIdx
#print axioms PAG.Part215.kdualI_blockIdx
#print axioms PAG.Part215.inner_kblock
#print axioms PAG.Part215.blockGramInv_mul_blockGram
#print axioms PAG.Part215.blockGramInv_apply
#print axioms PAG.Part215.kdualB
#print axioms PAG.Part215.inner_kdualB_kblock
#print axioms PAG.Part215.inner_kdualB_ketFam_of_ne
#print axioms PAG.Part215.inner_kdualB_ketFam
#print axioms PAG.Part215.kdual_eq_kdualB
#print axioms PAG.Part215.inner_kdual_eq_sum
#print axioms PAG.Part215.ketBasis_repr_blockIdx
#print axioms PAG.Part215.kdual_mem_span
#print axioms PAG.Part215.inner_kdual_kdual
#print axioms PAG.Part215.normSq_kdual
#print axioms PAG.Part215.kdual_eq_sum_gblock
#print axioms PAG.Part215.span_kblock_eq_span_gblock
#print axioms PAG.Part215.chi_eq_zero_of_rad
#print axioms PAG.Part215.blockA_of_rad
#print axioms PAG.Part215.blockGram_offDiag_iff
#print axioms PAG.Part215.blockGram_eq_one_of_rad
#print axioms PAG.Part215.kdual_eq_kblock_of_rad
#print axioms PAG.Part215.blockProj
#print axioms PAG.Part215.blockProj_mem_span
#print axioms PAG.Part215.inner_kblock_blockProj
#print axioms PAG.Part215.inner_ketFam_blockProj_of_ne
#print axioms PAG.Part215.blockProj_kblock
#print axioms PAG.Part215.blockProj_ketFam_of_ne
#print axioms PAG.Part215.blockProj_blockProj
#print axioms PAG.Part215.inner_span_blockProj
#print axioms PAG.Part215.inner_blockProj_comm
#print axioms PAG.Part215.inner_blockProj_of_ne
#print axioms PAG.Part215.BlockIdx
#print axioms PAG.Part215.blockProjI
#print axioms PAG.Part215.blockEquiv
#print axioms PAG.Part215.sum_blockProjI
