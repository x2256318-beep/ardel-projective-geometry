/-
  PAG 2.0 Part 197（2026-10-24）— ℤ/N のケットの帰納系と、ハール正規化の定理 A（Ẑ の見方）
  N ∣ N′ の引き戻し π^* f = f ∘ (mod N)（`pull`）について
  1. conv_pull：π^*f ⋆ π^*g = (N′/N)·π^*(f ⋆ g)（核の大きさ N′/N、`card_ker_cast`）
  2. gket_pull：π^*|u, χ⟩_N = √(φ(Mt)/φ(M))·|u, χ⟩_{Nt}（M = N/u）。
     totient_mul_of_primes：t の素因数がすべて M を割るなら φ(Mt) = φ(M)·t。
     このとき π^*|u, χ⟩_N = √t·|u, χ⟩_{Nt}（Part 102 の π^*|w,χ⟩_K = √p|w,χ⟩_{K+1} の一般化）
  3. ハール正規化（全体の測度 1）：zket = √N·|u, χ⟩_N、hconv f g = (1/N)·f ⋆ g。
     zket_pull：t の素因数が M を割るなら π^* zket_N = zket_{Nt}。hconv_pull：π^* と hconv は可換。
     zket_apply：M と c の素因数が同じなら zket(x) = √(uc/φ(c))·[u ∣ x]·χ(x/u)（N によらない式）
  4. thmA_haar：hconv(zket A, zket B) = φ(uc)^(−1/2)·J̃·zket Ψ、J̃ = (τ(A)τ(B)/τ(Ψ))/√(c·c/d)。
     定数は N によらない（Ẑ 上の定理 A）。norm_zket：(1/N)·Σ|zket|² = 1
-/
import PAG200

namespace PAG.Part201

open Complex Finset PAG.Part199 PAG.Part200
open ZMod (stdAddChar)

/-! ### 1. 引き戻しと畳み込み -/

/-- 引き戻し π^* f = f ∘ (mod N)（N ∣ N′）。 -/
noncomputable def pull {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) : ZMod N' → ℂ :=
  f ∘ (ZMod.castHom h (ZMod N)).toAddMonoidHom

theorem pull_apply {N N' : ℕ} (h : N ∣ N') (f : ZMod N → ℂ) (x : ZMod N') :
    pull h f x = f (ZMod.castHom h (ZMod N) x) := rfl

theorem pull_smul {N N' : ℕ} (h : N ∣ N') (a : ℂ) (f : ZMod N → ℂ) : pull h (a • f) = a • pull h f := rfl

/-- 還元 ZMod N′ → ZMod N の核の大きさ：|ker|·N = N′。 -/
theorem card_ker_cast {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') :
    ((Finset.univ.filter (fun z : ZMod N' => (ZMod.castHom h (ZMod N)).toAddMonoidHom z = 0)).card : ℂ)
      * N = N' := by
  have e := PAG.Part17.sum_comp_surj (ZMod.castHom h (ZMod N)).toAddMonoidHom (ZMod.ringHom_surjective _)
    (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at e
  exact e.symm

/-- **1. 引き戻しと畳み込み**：π^*f ⋆ π^*g = (N′/N)·π^*(f ⋆ g)。 -/
theorem conv_pull {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') (f g : ZMod N → ℂ) :
    PAG.Part15.conv (pull h f) (pull h g) = ((N' : ℂ) / N) • pull h (PAG.Part15.conv f g) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold pull
  rw [PAG.Part17.conv_pullback _ (ZMod.ringHom_surjective _)]
  congr 1
  rw [eq_div_iff hN, card_ker_cast h]

/-! ### 2. ケットの引き戻し -/

/-- t の素因数がすべて M を割るなら φ(Mt) = φ(M)·t。 -/
theorem totient_mul_of_primes (M : ℕ) : ∀ t : ℕ, (∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) →
    Nat.totient (M * t) = Nat.totient M * t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t IH =>
  intro ht
  rcases Nat.lt_or_ge t 2 with h2 | h2
  · interval_cases t <;> simp
  · have hp := Nat.minFac_prime (by omega : t ≠ 1)
    obtain ⟨t', ht'⟩ := Nat.minFac_dvd t
    have hpos : 0 < t' := by
      rcases Nat.eq_zero_or_pos t' with h0 | h0
      · rw [h0, mul_zero] at ht'; omega
      · exact h0
    have hlt : t' < t := by
      have := hp.two_le
      rw [ht']; nlinarith
    have hpM : t.minFac ∣ M := ht _ hp (Nat.minFac_dvd t)
    have ht'M : ∀ q : ℕ, q.Prime → q ∣ t' → q ∣ M :=
      fun q hq hqt => ht q hq (hqt.trans (Dvd.intro_left _ ht'.symm))
    rw [ht', show M * (t.minFac * t') = t.minFac * (M * t') by ring,
      Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpM t'), IH t' hlt ht'M]
    ring

/-- c ∣ M、M の素因数がすべて c を割るなら φ(M)·c = φ(c)·M。 -/
theorem totient_ratio {c M : ℕ} (hc : c ∣ M) (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) :
    Nat.totient M * c = Nat.totient c * M := by
  have h1 := totient_mul_of_primes c (M / c) (fun q hq hqt => hrad q hq (hqt.trans (Nat.div_dvd_of_dvd hc)))
  rw [Nat.mul_div_cancel' hc] at h1
  rw [h1, mul_assoc, Nat.div_mul_cancel hc]

/-- **2. ケットの引き戻し**：π^*|u, χ⟩_N = √(φ(Mt)/φ(M))·|u, χ⟩_{Nt}。 -/
theorem gket_pull (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) :
    pull (dvd_mul_right N t) (gket u M N h c hc χ)
      = ((Real.sqrt (Nat.totient (M * t)) / Real.sqrt (Nat.totient M) : ℝ) : ℂ) •
        gket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ := by
  have hMZ := neZero_of_mul h
  have hu := pos_of_mul h
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  have hMt0 : M * t ≠ 0 := mul_ne_zero (NeZero.ne M) (NeZero.ne t)
  have hφMt : (0 : ℝ) < Real.sqrt (Nat.totient (M * t)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hMt0))
  have hv : ∀ y : ZMod (N * t), (ZMod.castHom (dvd_mul_right N t) (ZMod N) y).val = y.val % N := by
    intro y
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  funext x
  rw [pull_apply, Pi.smul_apply, smul_eq_mul, gket_apply, gket_apply, hv]
  have hdvd : u ∣ x.val % N ↔ u ∣ x.val := Nat.dvd_mod_iff (Dvd.intro _ h)
  by_cases hx : u ∣ x.val
  · obtain ⟨q, hq⟩ := hx
    have e1 : x.val % N = u * (q % M) := by rw [hq, ← h, Nat.mul_mod_mul_left]
    have e2 : ((q % M : ℕ) : ZMod c) = (q : ZMod c) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hc]
    rw [ite_eq_left (hdvd.mpr ⟨q, hq⟩), ite_eq_left ⟨q, hq⟩, e1, Nat.mul_div_cancel_left _ hu, hq,
      Nat.mul_div_cancel_left _ hu, e2]
    have a1 : ((Real.sqrt (Nat.totient M) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφM.ne'
    have a2 : ((Real.sqrt (Nat.totient (M * t)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφMt.ne'
    push_cast
    field_simp
  · rw [ite_eq_right (fun hd => hx (hdvd.mp hd)), ite_eq_right hx, mul_zero]

/-- **2'. 素因数が増えない引き戻し**：t の素因数がすべて M を割るなら π^*|u, χ⟩_N = √t·|u, χ⟩_{Nt}。 -/
theorem gket_pull_same (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) (ht : ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) :
    pull (dvd_mul_right N t) (gket u M N h c hc χ)
      = ((Real.sqrt t : ℝ) : ℂ) •
        gket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ := by
  have hMZ := neZero_of_mul h
  have hφM : (0 : ℝ) < Real.sqrt (Nat.totient M) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M)))
  rw [gket_pull, totient_mul_of_primes M t ht, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _),
    mul_div_cancel_left₀ _ hφM.ne']

/-! ### 3. ハール正規化 -/

/-- ハール正規化したケット zket = √N·|u, χ⟩_N（全体の測度を 1 にしたときの単位ベクトル）。 -/
noncomputable def zket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M) (χ : ZMod c → ℂ) :
    ZMod N → ℂ :=
  ((Real.sqrt N : ℝ) : ℂ) • gket u M N h c hc χ

/-- ハール正規化した畳み込み (1/N)·f ⋆ g。 -/
noncomputable def hconv {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ZMod N → ℂ :=
  ((N : ℂ)⁻¹) • PAG.Part15.conv f g

/-- **3a.** t の素因数がすべて M を割るなら π^* zket_N = zket_{Nt}。 -/
theorem zket_pull (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : ZMod c → ℂ) (ht : ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) :
    pull (dvd_mul_right N t) (zket u M N h c hc χ)
      = zket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ := by
  unfold zket
  rw [pull_smul, gket_pull_same u M N t h c hc χ ht, smul_smul, ← Complex.ofReal_mul,
    ← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul]

/-- **3b.** 引き戻しとハール正規化の畳み込みは可換：hconv(π^*f, π^*g) = π^* hconv(f, g)。 -/
theorem hconv_pull {N N' : ℕ} [NeZero N] [NeZero N'] (h : N ∣ N') (f g : ZMod N → ℂ) :
    hconv (pull h f) (pull h g) = pull h (hconv f g) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN' : (N' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N')
  unfold hconv
  rw [conv_pull h f g, smul_smul, pull_smul]
  congr 1
  field_simp

/-- **3c. N によらない値の式**：M と c の素因数が同じなら zket(x) = √(uc/φ(c))·[u ∣ x]·χ(x/u)。 -/
theorem zket_apply (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M) (χ : ZMod c → ℂ)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) (x : ZMod N) :
    zket u M N h c hc χ x =
      if u ∣ x.val then ((Real.sqrt ((u * c : ℕ) / (Nat.totient c : ℝ)) : ℝ) : ℂ) * χ ((x.val / u : ℕ) : ZMod c)
      else 0 := by
  have hMZ := neZero_of_mul h
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hc0 : c ≠ 0 := fun h0 => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ hc))
  have hφM : (Nat.totient M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))).ne'
  have hφc : (Nat.totient c : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hc0)).ne'
  have hr := totient_ratio hc hrad
  unfold zket
  rw [Pi.smul_apply, smul_eq_mul, gket_apply]
  by_cases hx : u ∣ x.val
  · rw [ite_eq_left hx, ite_eq_left hx, ← mul_assoc]
    congr 1
    -- √N·(√φ(M))⁻¹ = √(uc/φ(c))
    have e : (N : ℝ) / (Nat.totient M : ℝ) = (u * c : ℕ) / (Nat.totient c : ℝ) := by
      rw [div_eq_div_iff hφM hφc, ← h]
      have hr' : (Nat.totient M : ℝ) * c = (Nat.totient c : ℝ) * M := by exact_mod_cast hr
      push_cast
      linear_combination (-(u : ℝ)) * hr'
    rw [← e, Real.sqrt_div (Nat.cast_nonneg _), div_eq_mul_inv]
    push_cast
    ring
  · rw [ite_eq_right hx, ite_eq_right hx, mul_zero]

/-! ### 4. ハール正規化の定理 A -/

/-- 定理 A の位相の部分 J̃ = (τ(A)τ(B)/τ(Ψ))/√(c·c/d)。 -/
noncomputable def jt (c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) : ℂ :=
  gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar /
    ((Real.sqrt ((c * (c / d) : ℕ) : ℝ) : ℝ) : ℂ)

theorem thmAConst_eq (N u c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) :
    thmAConst N u c d A B Ψ = ((Real.sqrt ((N : ℝ) / (Nat.totient (u * c) : ℝ)) : ℝ) : ℂ) * jt c d A B Ψ := by
  unfold thmAConst jt
  ring

/-- **4. ハール正規化の定理 A（Ẑ 上の定理 A）**：thmA_general の仮定のもとで
(1/N)·zket(A) ⋆ zket(B) = φ(uc)^(−1/2)·J̃·zket(Ψ)。定数は N によらない。 -/
theorem thmA_haar (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N) (hc : c ∣ M)
    (hdc : d ∣ c) (h' : u' * M' = N) (hd : d ∣ M') (hu' : u' = u * (c / d))
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ N → q ∣ d)
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) (hΨ : Ψ.IsPrimitive) (hprod : A * B = Ψ.changeLevel hdc) :
    hconv (zket u M N h c hc A) (zket u M N h c hc B)
      = ((((Real.sqrt (Nat.totient (u * c)))⁻¹ : ℝ) : ℂ) * jt c d A B Ψ) • zket u' M' N h' d hd Ψ := by
  have H := thmA_general N u M c d u' M' h hc hdc h' hd hu' hprimes A B Ψ hA hB hΨ hprod
  unfold ThmA at H
  have hu0 : u ≠ 0 := (pos_of_mul h).ne'
  have hc0 : c ≠ 0 := NeZero.ne c
  have hφ : (0 : ℝ) < Real.sqrt (Nat.totient (u * c)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hu0 hc0)))
  have hN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  unfold hconv zket
  rw [PAG.Part15.conv_smul_smul, H, smul_smul, smul_smul, smul_smul, thmAConst_eq,
    Real.sqrt_div (Nat.cast_nonneg _)]
  congr 1
  have a1 : ((Real.sqrt (Nat.totient (u * c)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have a2 : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have a3 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hsqC : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = N := by exact_mod_cast hsq
  push_cast
  field_simp
  linear_combination (jt c d A B Ψ) * hsqC

/-- **4'. ハール正規化のノルム**：M を割るすべての素数が c を割るなら (1/N)·Σ|zket|² = 1。 -/
theorem norm_zket (u M N : ℕ) [NeZero N] [NeZero M] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) :
    (N : ℝ)⁻¹ * ∑ x, Complex.normSq (zket u M N h c hc χ x) = 1 := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold zket
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [← Finset.mul_sum, norm_gket u M N h c hc χ hrad, mul_one, inv_mul_cancel₀ hN]

/-- **4''. 帰納系との両立**：t の素因数がすべて M を割るなら、レベル Nt のハール正規化の畳み込みは
レベル N のものの引き戻し。 -/
theorem hconv_zket_pull (u M N t : ℕ) [NeZero N] [NeZero t] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ₁ χ₂ : ZMod c → ℂ) (ht : ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M) :
    hconv (zket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ₁)
        (zket u (M * t) (N * t) (by rw [← h, mul_assoc]) c (hc.trans (dvd_mul_right M t)) χ₂)
      = pull (dvd_mul_right N t) (hconv (zket u M N h c hc χ₁) (zket u M N h c hc χ₂)) := by
  rw [← zket_pull u M N t h c hc χ₁ ht, ← zket_pull u M N t h c hc χ₂ ht, hconv_pull]

end PAG.Part201

#print axioms PAG.Part201.pull_apply
#print axioms PAG.Part201.pull_smul
#print axioms PAG.Part201.card_ker_cast
#print axioms PAG.Part201.conv_pull
#print axioms PAG.Part201.totient_mul_of_primes
#print axioms PAG.Part201.totient_ratio
#print axioms PAG.Part201.gket_pull
#print axioms PAG.Part201.gket_pull_same
#print axioms PAG.Part201.zket_pull
#print axioms PAG.Part201.hconv_pull
#print axioms PAG.Part201.zket_apply
#print axioms PAG.Part201.thmAConst_eq
#print axioms PAG.Part201.thmA_haar
#print axioms PAG.Part201.norm_zket
#print axioms PAG.Part201.hconv_zket_pull
