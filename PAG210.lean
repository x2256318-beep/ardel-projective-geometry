/-
  PAG 2.0 Part 206（2026-10-24）— 畳み込み代数の構造（Part 204 の基底での構造定数）
  g_{s,ψ}（ψ は法 n の指標、s·n = N）、ε_s = g_{s,1}。k = |u, χ⟩_N（χ は法 c の原始指標、s₀ = M/c、B = kcoef）
  1. 構造定数：g_{s,ψ} ⋆ g_{s,ψ′} = g_{s,ψψ′}、s ≠ s′ なら g_{s,ψ} ⋆ g_{s′,ψ′} = 0、単位元 Σ_s g_{s,1} = δ₀
     （(ℂ^{ℤ/N}, ⋆) は、殻ごとの (ℤ/(N/s))ˣ の指標群の群環の直和）
  2. 殻ごとの分解：f ⋆ g = Σ_{s ∣ N} (ε_s ⋆ f) ⋆ (ε_s ⋆ g)
  3. ケットの作用：t ∣ u なら k ⋆ g_{s₀t,ψ} = B·χ̄(t)·g_{s₀t, χ̄′_t·ψ}、ほかの殻では 0（指標のずらし）
  4. 2 つのケットの畳み込みの統一公式：
     k₁ ⋆ k₂ = Σ_s B₁χ̄₁(s/s₁)·B₂χ̄₂(s/s₂)·g_{s, χ̄₁′χ̄₂′}（s ∣ N、s₁ ∣ s、s/s₁ ∣ u₁、s₂ ∣ s、s/s₂ ∣ u₂）
  5. 定理 B の一般形：k ⋆ |u, χ̄⟩ = χ(−1)·(s₀²c/φ(M))·Σ_{s₀ ∣ s, s/s₀ ∣ u, (s/s₀, c) = 1} ε_s。
     (R) なら Σ は ε_{s₀} だけで、Part 201 の thmB_geps と同じ式
-/
import PAG209

namespace PAG.Part210

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- 法 c の指標を法 m に持ち上げる（c ∣ m でなければ 1）。 -/
noncomputable def liftc {c : ℕ} (χ : DirichletCharacter ℂ c) (m : ℕ) : DirichletCharacter ℂ m :=
  if h : c ∣ m then χ.changeLevel h else 1

/-- **0a.** c ∣ m なら liftc χ m = χ を法 m へ持ち上げたもの。 -/
theorem liftc_of_dvd {c m : ℕ} (χ : DirichletCharacter ℂ c) (h : c ∣ m) : liftc χ m = χ.changeLevel h := by
  unfold liftc
  exact dite_eq_left h

/-- **0b.** 法の自然数が等しければ、持ち上げた指標の基底ベクトルも等しい。 -/
theorem gbas_congr (s N : ℕ) [NeZero N] {n₁ n₂ c : ℕ} (e : n₁ = n₂) (h₁ : c ∣ n₁) (h₂ : c ∣ n₂)
    (χ : DirichletCharacter ℂ c) : gbas s n₁ N (χ.changeLevel h₁) = gbas s n₂ N (χ.changeLevel h₂) := by
  subst e
  rfl

/-- **0c.** f ⋆ 0 = 0。 -/
theorem conv_zero_right {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : PAG.Part15.conv f 0 = 0 := by
  funext x
  simp [PAG.Part15.conv]

/-- **0d.** 0 ⋆ g = 0。 -/
theorem conv_zero_left {N : ℕ} [NeZero N] (g : ZMod N → ℂ) : PAG.Part15.conv 0 g = 0 := by
  funext x
  simp [PAG.Part15.conv]

/-- **0e.** s₀ ∣ s、s/s₀ ∣ u なら s·((u/(s/s₀))c) = N、N/s = (u/(s/s₀))c。 -/
theorem shell_quot {u M N c s : ℕ} [NeZero N] (h : u * M = N) (hc : c ∣ M) (hs0 : M / c ∣ s)
    (hsu : s / (M / c) ∣ u) :
    s * (u / (s / (M / c)) * c) = N ∧ N / s = u / (s / (M / c)) * c := by
  have hst := shell_eq h hc hsu
  rw [Nat.mul_div_cancel' hs0] at hst
  have hs_pos : 0 < s := Nat.pos_of_ne_zero (fun h0 => by
    rw [h0, zero_mul] at hst; exact NeZero.ne N hst.symm)
  exact ⟨hst, Nat.div_eq_of_eq_mul_left hs_pos (by rw [← hst]; ring)⟩

/-! ### 1. 構造定数 -/

/-- **1a.** g_{s,ψ} ⋆ g_{s,ψ′} = g_{s,ψψ′}。 -/
theorem conv_gbas_same (s n N : ℕ) [NeZero N] (ψ ψ' : DirichletCharacter ℂ n) :
    PAG.Part15.conv (gbas s n N ψ) (gbas s n N ψ') = gbas s n N (ψ * ψ') := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, dft_gbas_apply, dft_gbas_apply, dft_gbas_apply]
  split_ifs
  · rw [MulChar.mul_apply]
  · rw [zero_mul]

/-- **1b.** s ≠ s′ なら g_{s,ψ} ⋆ g_{s′,ψ′} = 0。 -/
theorem conv_gbas_ne (s n s' n' N : ℕ) [NeZero N] (h : s * n = N) (h' : s' * n' = N) (hne : s ≠ s')
    (ψ : DirichletCharacter ℂ n) (ψ' : DirichletCharacter ℂ n') :
    PAG.Part15.conv (gbas s n N ψ) (gbas s' n' N ψ') = 0 := by
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  rw [PAG.Part16.dft_conv, Pi.mul_apply, map_zero, Pi.zero_apply, ← dind_mul_dft_gbas s n N h ψ,
    ← dind_mul_dft_gbas s' n' N h' ψ', Pi.mul_apply, Pi.mul_apply]
  by_cases hk : Nat.gcd N ξ.val = s
  · have h0 : dind N s' ξ = 0 := by
      simp only [dind]; rw [ite_eq_right (fun e => hne (hk.symm.trans e))]
    rw [h0, zero_mul, mul_zero]
  · have h0 : dind N s ξ = 0 := by simp only [dind]; rw [ite_eq_right hk]
    rw [h0, zero_mul, zero_mul]

/-- **1c. 単位元**：Σ_{s ∣ N} g_{s,1} = δ₀。 -/
theorem sum_gbas_one (N : ℕ) [NeZero N] :
    ∑ s ∈ N.divisors, gbas s (N / s) N 1 = Pi.single (0 : ZMod N) (1 : ℂ) := by
  rw [← sum_geps N]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  exact gbas_one s (N / s) N (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hs))

/-! ### 2. 殻ごとの分解 -/

/-- **2.** f ⋆ g = Σ_{s ∣ N} (ε_s ⋆ f) ⋆ (ε_s ⋆ g)。 -/
theorem conv_eq_sum_shells {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    PAG.Part15.conv f g = ∑ s ∈ N.divisors,
      PAG.Part15.conv (PAG.Part15.conv (geps N s) f) (PAG.Part15.conv (geps N s) g) := by
  conv_lhs => rw [← sum_geps_conv N (PAG.Part15.conv f g)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  apply (ZMod.dft (N := N) (E := ℂ)).injective
  funext ξ
  simp only [PAG.Part16.dft_conv, Pi.mul_apply, dft_geps]
  have hd : dind N s ξ * dind N s ξ = dind N s ξ := by
    simp only [dind]; split_ifs <;> simp
  linear_combination (-(𝓕 f ξ * 𝓕 g ξ)) * hd

/-! ### 3. ケットの作用 -/

/-- **3a. ケットの作用**：t ∣ u なら k ⋆ g_{s₀t,ψ} = B·χ̄(t)·g_{s₀t, χ̄′_t·ψ}（ψ は法 (u/t)c の指標）。 -/
theorem conv_gket_gbas (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (t : ℕ) (ht : t ∣ u)
    (ψ : DirichletCharacter ℂ (u / t * c)) :
    PAG.Part15.conv (gket u M N h c hc χ) (gbas (M / c * t) (u / t * c) N ψ) =
      (kcoef M c χ * χ⁻¹ (t : ZMod c)) •
        gbas (M / c * t) (u / t * c) N ((χ⁻¹).changeLevel (dvd_mul_left c (u / t)) * ψ) := by
  have hst := shell_eq h hc ht
  rw [← geps_conv_gbas (M / c * t) (u / t * c) N hst ψ, ← PAG.Part89.conv_assoc',
    PAG.Part15.conv_comm (gket u M N h c hc χ) (geps N (M / c * t)),
    geps_conv_gket_comp u M N h c hc χ hχ t ht, conv_smul_left, conv_gbas_same]

/-- **3b.** s がどの s₀t（t ∣ u）とも違えば k ⋆ g_{s,ψ} = 0。 -/
theorem conv_gket_gbas_eq_zero (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (s n : ℕ) (hsn : s * n = N)
    (hs : ∀ t : ℕ, t ∣ u → s ≠ M / c * t) (ψ : DirichletCharacter ℂ n) :
    PAG.Part15.conv (gket u M N h c hc χ) (gbas s n N ψ) = 0 := by
  rw [← geps_conv_gbas s n N hsn ψ, ← PAG.Part89.conv_assoc',
    PAG.Part15.conv_comm (gket u M N h c hc χ) (geps N s),
    geps_conv_gket_eq_zero u M N h c hc χ hχ s (fun t ht _ => hs t ht), conv_zero_left]

/-! ### 4. 2 つのケットの畳み込み -/

/-- **4a. 成分の正規形**：s₀ ∣ s、s/s₀ ∣ u なら ε_s ⋆ k = B·χ̄(s/s₀)·g_{s, χ̄′}（χ̄′ は χ⁻¹ を法 N/s へ持ち上げたもの）。 -/
theorem geps_conv_gket_canon (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (s : ℕ) (hs0 : M / c ∣ s) (hsu : s / (M / c) ∣ u) :
    PAG.Part15.conv (geps N s) (gket u M N h c hc χ) =
      (kcoef M c χ * χ⁻¹ ((s / (M / c) : ℕ) : ZMod c)) • gbas s (N / s) N (liftc χ⁻¹ (N / s)) := by
  obtain ⟨_, hn⟩ := shell_quot h hc hs0 hsu
  have hcN : c ∣ N / s := by rw [hn]; exact dvd_mul_left c _
  have e := geps_conv_gket_comp u M N h c hc χ hχ (s / (M / c)) hsu
  rw [Nat.mul_div_cancel' hs0] at e
  rw [e, gbas_congr s N hn.symm (dvd_mul_left c _) hcN χ⁻¹, liftc_of_dvd χ⁻¹ hcN]

/-- **4b. 2 つのケットの畳み込みの統一公式**：
k₁ ⋆ k₂ = Σ_s B₁χ̄₁(s/s₁)·B₂χ̄₂(s/s₂)·g_{s, χ̄₁′χ̄₂′}（s ∣ N、s₁ ∣ s、s/s₁ ∣ u₁、s₂ ∣ s、s/s₂ ∣ u₂）。 -/
theorem conv_gket_gket (u₁ M₁ u₂ M₂ N : ℕ) [NeZero N] (h₁ : u₁ * M₁ = N) (h₂ : u₂ * M₂ = N)
    (c₁ c₂ : ℕ) [NeZero c₁] [NeZero c₂] (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (χ₁ : DirichletCharacter ℂ c₁) (χ₂ : DirichletCharacter ℂ c₂) (hχ₁ : χ₁.IsPrimitive)
    (hχ₂ : χ₂.IsPrimitive) :
    PAG.Part15.conv (gket u₁ M₁ N h₁ c₁ hc₁ χ₁) (gket u₂ M₂ N h₂ c₂ hc₂ χ₂) =
      ∑ s ∈ N.divisors.filter
          (fun s => M₁ / c₁ ∣ s ∧ s / (M₁ / c₁) ∣ u₁ ∧ M₂ / c₂ ∣ s ∧ s / (M₂ / c₂) ∣ u₂),
        (kcoef M₁ c₁ χ₁ * χ₁⁻¹ ((s / (M₁ / c₁) : ℕ) : ZMod c₁) *
          (kcoef M₂ c₂ χ₂ * χ₂⁻¹ ((s / (M₂ / c₂) : ℕ) : ZMod c₂))) •
          gbas s (N / s) N (liftc χ₁⁻¹ (N / s) * liftc χ₂⁻¹ (N / s)) := by
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have hs1 : 0 < M₁ / c₁ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₁)) hc₁)
    (Nat.pos_of_ne_zero (NeZero.ne c₁))
  have hs2 : 0 < M₂ / c₂ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M₂)) hc₂)
    (Nat.pos_of_ne_zero (NeZero.ne c₂))
  rw [conv_eq_sum_shells, ← Finset.sum_filter_of_ne
    (p := fun s => M₁ / c₁ ∣ s ∧ s / (M₁ / c₁) ∣ u₁ ∧ M₂ / c₂ ∣ s ∧ s / (M₂ / c₂) ∣ u₂)]
  · refine Finset.sum_congr rfl (fun s hs => ?_)
    obtain ⟨_, h1, h1u, h2, h2u⟩ := Finset.mem_filter.mp hs
    rw [geps_conv_gket_canon u₁ M₁ N h₁ c₁ hc₁ χ₁ hχ₁ s h1 h1u,
      geps_conv_gket_canon u₂ M₂ N h₂ c₂ hc₂ χ₂ hχ₂ s h2 h2u, PAG.Part15.conv_smul_smul, conv_gbas_same]
  · intro s _ hne
    by_contra hP
    apply hne
    by_cases hA : M₁ / c₁ ∣ s ∧ s / (M₁ / c₁) ∣ u₁
    · have hB : ¬ (M₂ / c₂ ∣ s ∧ s / (M₂ / c₂) ∣ u₂) := fun hB => hP ⟨hA.1, hA.2, hB.1, hB.2⟩
      rw [geps_conv_gket_eq_zero u₂ M₂ N h₂ c₂ hc₂ χ₂ hχ₂ s (fun t ht _ e => hB ⟨Dvd.intro t e.symm,
        by rw [e, Nat.mul_div_cancel_left t hs2]; exact ht⟩), conv_zero_right]
    · rw [geps_conv_gket_eq_zero u₁ M₁ N h₁ c₁ hc₁ χ₁ hχ₁ s (fun t ht _ e => hA ⟨Dvd.intro t e.symm,
        by rw [e, Nat.mul_div_cancel_left t hs1]; exact ht⟩), conv_zero_left]

/-! ### 5. 定理 B の一般形 -/

/-- **5a.** B(χ)·B(χ̄) = χ(−1)·s₀²c/φ(M)。 -/
theorem kcoef_mul_kcoef_inv (M c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    kcoef M c χ * kcoef M c χ⁻¹ = χ (-1) * (((M / c : ℕ) : ℂ) ^ 2 * c / Nat.totient M) := by
  have hsq : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) =
      (Nat.totient M : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    push_cast
    rfl
  have hm : χ⁻¹ (-1) * χ (-1) = 1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply isUnit_one.neg]
  unfold kcoef
  rw [inv_inv, Complex.ofReal_inv]
  calc ((Real.sqrt (Nat.totient M) : ℝ) : ℂ)⁻¹ * ((M / c : ℕ) : ℂ) * χ⁻¹ (-1) * gaussSum χ stdAddChar *
        (((Real.sqrt (Nat.totient M) : ℝ) : ℂ)⁻¹ * ((M / c : ℕ) : ℂ) * χ (-1) * gaussSum χ⁻¹ stdAddChar)
      = (((Real.sqrt (Nat.totient M) : ℝ) : ℂ) * ((Real.sqrt (Nat.totient M) : ℝ) : ℂ))⁻¹ *
          ((M / c : ℕ) : ℂ) ^ 2 * (χ⁻¹ (-1) * χ (-1)) *
          (gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar) := by ring
    _ = χ (-1) * (((M / c : ℕ) : ℂ) ^ 2 * c / Nat.totient M) := by
        rw [hsq, hm, PAG.Part16.gauss_mul_gauss_inv_eq hχ]
        ring

/-- **5b. 定理 B の一般形**：k ⋆ |u, χ̄⟩ = χ(−1)·(s₀²c/φ(M))·Σ_{s₀ ∣ s, s/s₀ ∣ u, (s/s₀, c) = 1} ε_s。 -/
theorem conv_gket_inv (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (gket u M N h c hc χ) (gket u M N h c hc (χ⁻¹ : DirichletCharacter ℂ c)) =
      (χ (-1) * (((M / c : ℕ) : ℂ) ^ 2 * c / Nat.totient M)) •
        ∑ s ∈ N.divisors.filter (fun s => M / c ∣ s ∧ s / (M / c) ∣ u ∧ (s / (M / c)).Coprime c), geps N s := by
  have hM := neZero_of_mul h
  have hK := kcoef_mul_kcoef_inv M c χ hχ
  rw [conv_gket_gket u M u M N h h c c hc hc χ χ⁻¹ hχ (PAG.Part16.isPrimitive_inv hχ), Finset.smul_sum,
    Finset.filter_congr (p := fun s => M / c ∣ s ∧ s / (M / c) ∣ u ∧ M / c ∣ s ∧ s / (M / c) ∣ u)
      (q := fun s => M / c ∣ s ∧ s / (M / c) ∣ u)
      (fun s _ => ⟨fun ⟨a, b, _, _⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b, a, b⟩⟩)]
  have hfilt : N.divisors.filter (fun s => M / c ∣ s ∧ s / (M / c) ∣ u ∧ (s / (M / c)).Coprime c) =
      (N.divisors.filter (fun s => M / c ∣ s ∧ s / (M / c) ∣ u)).filter
        (fun s => (s / (M / c)).Coprime c) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun s _ => and_assoc.symm)
  rw [hfilt]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨_, hA, hB⟩ := Finset.mem_filter.mp hs
  obtain ⟨hsn, hq⟩ := shell_quot h hc hA hB
  have hcN : c ∣ N / s := by rw [hq]; exact dvd_mul_left c _
  have hsN : s * (N / s) = N := by rw [hq]; exact hsn
  have hlift : liftc χ⁻¹ (N / s) * liftc χ⁻¹⁻¹ (N / s) = 1 := by
    rw [liftc_of_dvd _ hcN, liftc_of_dvd _ hcN, ← map_mul, mul_inv_cancel, map_one]
  rw [hlift, gbas_one s (N / s) N hsN, inv_inv]
  by_cases hC : (s / (M / c)).Coprime c
  · have hu : χ⁻¹ ((s / (M / c) : ℕ) : ZMod c) * χ ((s / (M / c) : ℕ) : ZMod c) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hC)]
    rw [ite_eq_left hC, ← hK]
    congr 1
    linear_combination (kcoef M c χ * kcoef M c χ⁻¹) * hu
  · have hnu : ¬ IsUnit ((s / (M / c) : ℕ) : ZMod c) := fun hu => hC ((ZMod.isUnit_iff_coprime _ _).mp hu)
    rw [ite_eq_right hC, MulChar.map_nonunit χ⁻¹ hnu]
    simp

/-- **5c.** (R)（u の素因数がすべて c を割る）なら k ⋆ |u, χ̄⟩ = χ(−1)·(s₀²c/φ(M))·ε_{s₀}（Part 201 の thmB_geps と同じ式）。 -/
theorem conv_gket_inv_rad (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c) :
    PAG.Part15.conv (gket u M N h c hc χ) (gket u M N h c hc (χ⁻¹ : DirichletCharacter ℂ c)) =
      (χ (-1) * (((M / c : ℕ) : ℂ) ^ 2 * c / Nat.totient M)) • geps N (M / c) := by
  have hM := neZero_of_mul h
  have hs0 : 0 < M / c := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hc)
    (Nat.pos_of_ne_zero (NeZero.ne c))
  have hset : N.divisors.filter (fun s => M / c ∣ s ∧ s / (M / c) ∣ u ∧ (s / (M / c)).Coprime c) =
      {M / c} := by
    ext s
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hA, hB, hC⟩
      have ht1 : s / (M / c) = 1 := by
        by_contra hne
        obtain ⟨q, hq, hqt⟩ := Nat.exists_prime_and_dvd hne
        have hqc : q ∣ c := hrad q hq (hqt.trans hB)
        have hq1 := Nat.dvd_gcd hqt hqc
        rw [Nat.Coprime.gcd_eq_one hC] at hq1
        exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
      rw [← Nat.mul_div_cancel' hA, ht1, mul_one]
    · rintro rfl
      refine ⟨Nat.mem_divisors.mpr ⟨?_, NeZero.ne N⟩, dvd_refl _, ?_, ?_⟩
      · exact ⟨u * c, by rw [← h, show M / c * (u * c) = u * (M / c * c) by ring, Nat.div_mul_cancel hc]⟩
      · rw [Nat.div_self hs0]; exact one_dvd u
      · rw [Nat.div_self hs0]; exact Nat.coprime_one_left c
  rw [conv_gket_inv u M N h c hc χ hχ, hset, Finset.sum_singleton]

end PAG.Part210

#print axioms PAG.Part210.liftc_of_dvd
#print axioms PAG.Part210.gbas_congr
#print axioms PAG.Part210.conv_zero_right
#print axioms PAG.Part210.conv_zero_left
#print axioms PAG.Part210.shell_quot
#print axioms PAG.Part210.conv_gbas_same
#print axioms PAG.Part210.conv_gbas_ne
#print axioms PAG.Part210.sum_gbas_one
#print axioms PAG.Part210.conv_eq_sum_shells
#print axioms PAG.Part210.conv_gket_gbas
#print axioms PAG.Part210.conv_gket_gbas_eq_zero
#print axioms PAG.Part210.geps_conv_gket_canon
#print axioms PAG.Part210.conv_gket_gket
#print axioms PAG.Part210.kcoef_mul_kcoef_inv
#print axioms PAG.Part210.conv_gket_inv
#print axioms PAG.Part210.conv_gket_inv_rad
