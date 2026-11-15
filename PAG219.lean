/-
  PAG 2.0 Part 215（2026-10-28）— ブロックの既約性：殻の射影で閉じた部分空間と gcd(c, N/c)
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。v, w は L の約数
  V_{c,χ} = span{k_u}（def blockSpan）、P = P_{c,χ}（Part 211 の blockProj）
  G_v = g_{N/(vc), χ̄′}（Part 210 の gblock。双対殻 N/(vc) の基底ベクトル）、
  H_w = 𝓕 G′_w（G′ はブロック (c, χ̄) の G、台は空間の殻 D_{N/(wc)}、Part 213）
  E_s = ε_s ⋆（双対殻の射影）、D_s = 1_{D_s}·（空間の殻の射影）
  ShellInvariant W：すべての s で E_s W ⊆ W、D_s W ⊆ W（Part 214 の代数 A = shellAlg の元で閉じることと同値）
  BlockIrreducible：殻の射影で閉じたブロックの部分空間は 0 かブロック全体
  0. 準備：V_{c,χ} の元は P で動かない、G_v・H_w は V_{c,χ} に入る、G_v ≠ 0、G_1 = g_{N/c, χ̄}
  1. かなめの式：⟨G_1, H_w⟩ = conj(τ(χ̄))/N·conj(χ(N/(wc)))·φ(wc)。gcd(N/(wc), c) = 1 なら 0 でない
  2. 主定理（⇐）：gcd(c, N/c) = 1 ならブロックは既約（0 でない f → ある H_w → G_1 → すべての H_w′）
  3. 主定理（⇒）：素数 p が c と N/c を割るなら、W_p = {f ∈ V_{c,χ} : p ∣ x で f(x) = 0} は殻の射影で閉じ、
     0 でもブロック全体でもない（台の補題：p ∣ c なら G_v(x) ≠ 0 ⇒ (p ∣ x ⇔ p ∣ v)）
  4. まとめ：ブロックが既約 ⇔ gcd(c, N/c) = 1。殻で閉じる ⇔ A のすべての元で閉じる。
     シューア型：gcd(c, N/c) = 1 なら、E_s・D_s・P と可換な線形写像はブロックの上でスカラー
  5. 推移性：V_{c,χ} の 0 でない任意の f を任意の g に写す A の元がある ⇔ gcd(c, N/c) = 1
     （p が c と N/c を割るなら、A のどの元も G_1 を G_p に写さない）
-/
import PAG218

namespace PAG.Part219

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- ブロック (c, χ) の張る空間 V_{c,χ} = span{k_u : u ∣ N/c}。 -/
noncomputable def blockSpan (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) : Submodule ℂ (ZMod N → ℂ) :=
  Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w)

/-- **0a.** V_{c,χ} の元は P で動かない。 -/
theorem blockProj_of_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) : blockProj N c χ f = f := by
  unfold blockSpan at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact blockProj_kblock N c hcN χ hχ w
  | zero =>
    rw [← blockProjL_apply, map_zero]
  | add x y _ _ hx hy =>
    rw [← blockProjL_apply, map_add, blockProjL_apply, blockProjL_apply, hx, hy]
  | smul r x _ hx =>
    rw [← blockProjL_apply, map_smul, blockProjL_apply, hx]

/-- **0b.** G_v は V_{c,χ} に入る（v ∣ N/c）。 -/
theorem gblock_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v : ℕ} (hv : v ∣ N / c) : gblock N c χ v ∈ blockSpan N c χ := by
  rw [← blockProj_gblock N c hcN χ hχ hv]
  exact blockProj_mem_span N c χ _

/-- **0c.** P H_w = H_w（H_w = 𝓕 G′_w、w ∣ N/c）。 -/
theorem blockProj_dft_gblock_inv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c) :
    blockProj N c χ (𝓕 (gblock N c χ⁻¹ w)) = 𝓕 (gblock N c χ⁻¹ w) := by
  have e := blockProj_dft_gblock N c hcN χ⁻¹ (PAG.Part16.isPrimitive_inv hχ) hw
  rwa [inv_inv] at e

/-- **0d.** H_w は V_{c,χ} に入る。 -/
theorem dft_gblock_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c) : 𝓕 (gblock N c χ⁻¹ w) ∈ blockSpan N c χ := by
  rw [← blockProj_dft_gblock_inv N c hcN χ hχ hw]
  exact blockProj_mem_span N c χ _

/-- **0e.** G_v ≠ 0（v ∣ N/c）。 -/
theorem gblock_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {v : ℕ}
    (hv : v ∣ N / c) : gblock N c χ v ≠ 0 := by
  intro h0
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hφ : (Nat.totient (v * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hv hL0) hc0)).ne'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have e := inner_gblock N c hcN χ hv hv
  rw [ite_eq_left rfl, h0] at e
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero] at e
  exact div_ne_zero hφ hN e.symm

/-- **0f.** G_1 = g_{N/c, χ̄}（法 c の原始指標 χ̄ の基底ベクトル）。 -/
theorem gblock_one (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) : gblock N c χ 1 = gbas (N / c) c N χ⁻¹ := by
  unfold gblock
  rw [liftc_of_dvd χ⁻¹ (dvd_mul_left c 1),
    gbas_congr (N / (1 * c)) N (one_mul c) (dvd_mul_left c 1) (dvd_refl c) χ⁻¹,
    DirichletCharacter.changeLevel_self, one_mul]

/-- **0g.** ψ(m) ≠ 0（ψ は法 c の指標）なら、c を割る素数 p は m を割らない。 -/
theorem not_dvd_of_chi_ne_zero {c : ℕ} (ψ : DirichletCharacter ℂ c) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c)
    {m : ℕ} (hm : ψ (m : ZMod c) ≠ 0) : ¬ p ∣ m := by
  intro hpm
  apply hm
  apply MulChar.map_nonunit
  intro hu
  have hcop := (ZMod.isUnit_iff_coprime m c).mp hu
  have hq := Nat.dvd_gcd hpm hpc
  rw [Nat.Coprime.gcd_eq_one hcop] at hq
  exact hp.one_lt.ne' (Nat.dvd_one.mp hq)

/-! ### 1. かなめの式 -/

/-- **1a.** Σ_{y ∈ ℤ/(wc)} χ′(y)·conj(χ(y mod c)) = φ(wc)（χ′ は χ を法 wc へ持ち上げたもの）。 -/
theorem sum_changeLevel_mul_conj {c : ℕ} [NeZero c] (χ : DirichletCharacter ℂ c) (m : ℕ) [NeZero m]
    (hdvd : c ∣ m) :
    ∑ y : ZMod m, χ.changeLevel hdvd y * starRingEnd ℂ (χ ((y.val : ℕ) : ZMod c)) = Nat.totient m := by
  rw [← card_isUnit m, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : IsUnit y
  · rw [ite_eq_left hy]
    obtain ⟨u, rfl⟩ := hy
    have hcop : Nat.Coprime (u : ZMod m).val c :=
      Nat.Coprime.coprime_dvd_right hdvd (ZMod.val_coe_unit_coprime u)
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val, Complex.mul_conj,
      normSq_chi_natCast χ _ hcop, Complex.ofReal_one]
  · rw [ite_eq_right hy, MulChar.map_nonunit _ hy, zero_mul]

/-- **1b. かなめの式**：⟨G_1, H_w⟩ = conj(τ(χ̄))/N·conj(χ(N/(wc)))·φ(wc)（H_w = 𝓕 G′_w、w ∣ N/c、χ 原始的）。 -/
theorem inner_gblock_one_dft (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c) :
    ∑ x, starRingEnd ℂ (gblock N c χ 1 x) * 𝓕 (gblock N c χ⁻¹ w) x =
      starRingEnd ℂ (gaussSum χ⁻¹ stdAddChar) / N * starRingEnd ℂ (χ ((N / (w * c) : ℕ) : ZMod c)) *
        Nat.totient (w * c) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hw hL0
  have hwc : NeZero (w * c) := ⟨(Nat.mul_pos hw0 hc0).ne'⟩
  have hsh : N / (w * c) * (w * c) = N := gblock_shell hcN hw
  have hc1 : N / c * c = N := Nat.div_mul_cancel hcN
  have hdvd : c ∣ w * c := dvd_mul_left c w
  have hH : 𝓕 (gblock N c χ⁻¹ w) =
      PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) := by
    unfold gblock
    rw [inv_inv, liftc_of_dvd χ hdvd, dft_gbas (N / (w * c)) (w * c) N hsh]
  rw [gblock_one N c χ, hH]
  rw [show (∑ x, starRingEnd ℂ (gbas (N / c) c N χ⁻¹ x) *
      PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) x) =
      ∑ x, PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) x *
        starRingEnd ℂ (gbas (N / c) c N χ⁻¹ x) from Finset.sum_congr rfl (fun x _ => mul_comm _ _)]
  rw [PAG.Part17.sum_push_mul _ (memb_injective _ _ N hsh)]
  have hterm : ∀ y : ZMod (w * c), χ.changeLevel hdvd y *
      starRingEnd ℂ (gbas (N / c) c N χ⁻¹ (memb (N / (w * c)) (w * c) N hsh y)) =
      starRingEnd ℂ (gaussSum χ⁻¹ stdAddChar) / N * starRingEnd ℂ (χ ((N / (w * c) : ℕ) : ZMod c)) *
        (χ.changeLevel hdvd y * starRingEnd ℂ (χ ((y.val : ℕ) : ZMod c))) := by
    intro y
    rw [gbas_of_isPrimitive_apply (N / c) c N hc1 χ⁻¹ (PAG.Part16.isPrimitive_inv hχ), inv_inv, memb_val,
      Nat.cast_mul]
    simp only [map_mul, map_div₀, Complex.conj_natCast]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, sum_changeLevel_mul_conj χ (w * c) hdvd]

/-- **1c.** gcd(N/(wc), c) = 1 なら ⟨G_1, H_w⟩ ≠ 0。 -/
theorem inner_gblock_one_dft_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c)
    (hcop : Nat.Coprime (N / (w * c)) c) :
    ∑ x, starRingEnd ℂ (gblock N c χ 1 x) * 𝓕 (gblock N c χ⁻¹ w) x ≠ 0 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hτ : gaussSum χ⁻¹ stdAddChar ≠ 0 := PAG.Part16.gaussSum_ne_zero (PAG.Part16.isPrimitive_inv hχ)
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hχs : χ ((N / (w * c) : ℕ) : ZMod c) ≠ 0 := chi_natCast_ne_zero χ _ hcop
  have hφ : (Nat.totient (w * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hw hL0) hc0)).ne'
  rw [inner_gblock_one_dft N c hcN χ hχ hw]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero ((map_ne_zero _).mpr hτ) hN) ((map_ne_zero _).mpr hχs)) hφ

/-- **1d.** 逆向きの内積：⟨H_w, G_1⟩ = conj ⟨G_1, H_w⟩ も、gcd(N/(wc), c) = 1 なら 0 でない。 -/
theorem inner_dft_gblock_one_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N)
    (χ : DirichletCharacter ℂ c) (hχ : χ.IsPrimitive) {w : ℕ} (hw : w ∣ N / c)
    (hcop : Nat.Coprime (N / (w * c)) c) :
    ∑ x, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w) x) * gblock N c χ 1 x ≠ 0 := by
  rw [PAG.Part215.inner_conj_symm]
  exact (map_ne_zero _).mpr (inner_gblock_one_dft_ne_zero N c hcN χ hχ hw hcop)

/-! ### 2. gcd(c, N/c) = 1 ならブロックは既約 -/

/-- 殻の射影 E_s = ε_s ⋆、D_s = 1_{D_s}· で閉じた部分空間。 -/
def ShellInvariant {N : ℕ} [NeZero N] (W : Submodule ℂ (ZMod N → ℂ)) : Prop :=
  ∀ s : ℕ, ∀ f ∈ W, PAG.Part15.conv (geps N s) f ∈ W ∧ dind N s * f ∈ W

/-- ブロック (c, χ) が既約：殻の射影で閉じた V_{c,χ} の部分空間は 0 か V_{c,χ} 全体。 -/
def BlockIrreducible (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) : Prop :=
  ∀ W : Submodule ℂ (ZMod N → ℂ), ShellInvariant W → W ≤ blockSpan N c χ → W = ⊥ ∨ W = blockSpan N c χ

/-- **2a.** w ∣ N/c、gcd(c, N/c) = 1 なら gcd(N/(wc), c) = 1。 -/
theorem coprime_shell (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (hcop : Nat.Coprime c (N / c))
    {w : ℕ} (hw : w ∣ N / c) : Nat.Coprime (N / (w * c)) c := by
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hsh : N / (w * c) * (w * c) = N := gblock_shell hcN hw
  have h : N / c = w * (N / (w * c)) := Nat.div_eq_of_eq_mul_left hc0 (hsh.symm.trans (by ring))
  have hdvd : N / (w * c) ∣ N / c := ⟨w, by rw [h]; ring⟩
  exact Nat.Coprime.coprime_dvd_left hdvd hcop.symm

/-- **2b. 主定理（⇐）**：gcd(c, N/c) = 1 ならブロック (c, χ) は既約（χ 原始的）。 -/
theorem blockIrreducible_of_coprime (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hcop : Nat.Coprime c (N / c)) : BlockIrreducible N c χ := by
  intro W hW hWb
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  right
  refine le_antisymm hWb ?_
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hφ : ∀ w : ℕ, w ∣ N / c → (Nat.totient (w * c) : ℂ) ≠ 0 := fun w hw => by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hw hL0) hc0)).ne'
  -- 0 でない f ∈ W
  obtain ⟨f, hfW, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hPf := blockProj_of_mem N c hcN χ hχ (hWb hfW)
  -- ある w で ⟨H_w, f⟩ ≠ 0
  have hex : ∃ w ∈ (N / c).divisors, ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w) k) * f k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf0
    rw [← hPf, blockProj_eq_sum_dft_gblock N c hcN χ hχ f]
    exact Finset.sum_eq_zero (fun w hw => by rw [hall w hw, mul_zero, zero_smul])
  obtain ⟨w, hw, hfw⟩ := hex
  have hw' : w ∣ N / c := Nat.dvd_of_mem_divisors hw
  -- H_w ∈ W（D_{N/(wc)} を当てる）
  have hHw : 𝓕 (gblock N c χ⁻¹ w) ∈ W := by
    have h1 := (hW (N / (w * c)) f hfW).2
    rw [← hPf, dind_mul_blockProj_dft_gblock N c hcN χ hχ hw' f] at h1
    exact (W.smul_mem_iff (mul_ne_zero (inv_ne_zero (hφ w hw')) hfw)).mp h1
  -- G_1 ∈ W（E_{N/c} を当てる）
  have hG1 : gblock N c χ 1 ∈ W := by
    have h2 := (hW (N / (1 * c)) _ hHw).1
    rw [← blockProj_dft_gblock_inv N c hcN χ hχ hw', geps_conv_blockProj_gblock N c hcN χ hχ (one_dvd _) _] at h2
    refine (W.smul_mem_iff ?_).mp h2
    exact mul_ne_zero (div_ne_zero hN (hφ 1 (one_dvd _)))
      (inner_gblock_one_dft_ne_zero N c hcN χ hχ hw' (coprime_shell N c hcN hcop hw'))
  -- すべての H_{w′} ∈ W（D_{N/(w′c)} を G_1 に当てる）
  have hH : ∀ w' ∈ (N / c).divisors, 𝓕 (gblock N c χ⁻¹ w') ∈ W := by
    intro w' hw''
    have hw2 : w' ∣ N / c := Nat.dvd_of_mem_divisors hw''
    have h3 := (hW (N / (w' * c)) _ hG1).2
    rw [← blockProj_gblock N c hcN χ hχ (one_dvd _), dind_mul_blockProj_dft_gblock N c hcN χ hχ hw2 _] at h3
    refine (W.smul_mem_iff ?_).mp h3
    exact mul_ne_zero (inv_ne_zero (hφ w' hw2))
      (inner_dft_gblock_one_ne_zero N c hcN χ hχ hw2 (coprime_shell N c hcN hcop hw2))
  -- V_{c,χ} = span{H_w} ⊆ W
  intro g hg
  rw [← blockProj_of_mem N c hcN χ hχ hg, blockProj_eq_sum_dft_gblock N c hcN χ hχ g]
  exact Submodule.sum_mem _ (fun w' hw' => Submodule.smul_mem _ _ (hH w' hw'))

/-! ### 3. 素数 p が c と N/c を割れば既約でない -/

/-- **3a. 台の補題**：素数 p が c を割り v ∣ N/c なら、G_v(x) ≠ 0 ⇒ (p ∣ x ⇔ p ∣ v)。 -/
theorem gblock_support (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) {v : ℕ} (hv : v ∣ N / c) (x : ZMod N)
    (hx : gblock N c χ v x ≠ 0) : p ∣ x.val ↔ p ∣ v := by
  rw [gblock_eq_sum N c hcN χ hχ v hv, Finset.sum_apply] at hx
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  rw [Pi.smul_apply, smul_eq_mul] at hne
  have hwv : w ∣ v := Nat.dvd_of_mem_divisors hw
  have hp1 : ¬ p ∣ v / w :=
    not_dvd_of_chi_ne_zero χ⁻¹ hp hpc (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne)))
  have hk := right_ne_zero_of_mul hne
  obtain ⟨h1, h2⟩ := block_dvd hcN (dvd_trans hwv hv)
  rw [kblock_of_dvd N c χ h1 h2, gket_apply] at hk
  by_cases hwx : w ∣ x.val
  · rw [ite_eq_left hwx] at hk
    have hp2 : ¬ p ∣ x.val / w := not_dvd_of_chi_ne_zero χ hp hpc (right_ne_zero_of_mul hk)
    have ex : p ∣ x.val ↔ p ∣ w := by
      conv_lhs => rw [← Nat.mul_div_cancel' hwx]
      rw [hp.dvd_mul]
      exact or_iff_left hp2
    have ev : p ∣ v ↔ p ∣ w := by
      conv_lhs => rw [← Nat.mul_div_cancel' hwv]
      rw [hp.dvd_mul]
      exact or_iff_left hp1
    exact ex.trans ev.symm
  · rw [ite_eq_right hwx] at hk
    exact absurd rfl hk

/-- p 成分 W_p = {f ∈ V_{c,χ} : p ∣ x なら f(x) = 0}。 -/
noncomputable def pPart (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (p : ℕ) :
    Submodule ℂ (ZMod N → ℂ) where
  carrier := {f | f ∈ blockSpan N c χ ∧ ∀ x : ZMod N, p ∣ x.val → f x = 0}
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun x hx => by
    rw [Pi.add_apply, ha.2 x hx, hb.2 x hx, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun r {f} hf => ⟨Submodule.smul_mem _ r hf.1, fun x hx => by
    rw [Pi.smul_apply, hf.2 x hx, smul_zero]⟩

/-- **3b.** W_p の元の判定。 -/
theorem mem_pPart (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (p : ℕ) (f : ZMod N → ℂ) :
    f ∈ pPart N c χ p ↔ f ∈ blockSpan N c χ ∧ ∀ x : ZMod N, p ∣ x.val → f x = 0 := Iff.rfl

/-- **3c.** p ∣ c なら W_p は殻の射影で閉じる。 -/
theorem pPart_shellInvariant (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) : ShellInvariant (pPart N c χ p) := by
  intro s f hf
  obtain ⟨hfb, hfz⟩ := (mem_pPart N c χ p f).mp hf
  have hPf := blockProj_of_mem N c hcN χ hχ hfb
  constructor
  · by_cases hs : ∃ v ∈ (N / c).divisors, s = N / (v * c)
    · obtain ⟨v, hv, rfl⟩ := hs
      have hv' : v ∣ N / c := Nat.dvd_of_mem_divisors hv
      rw [← hPf, geps_conv_blockProj_gblock N c hcN χ hχ hv' f]
      by_cases hpv : p ∣ v
      · have h0 : ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x = 0 := by
          refine Finset.sum_eq_zero (fun x _ => ?_)
          by_cases hpx : p ∣ x.val
          · rw [hfz x hpx, mul_zero]
          · have hg0 : gblock N c χ v x = 0 := by
              by_contra hne
              exact hpx ((gblock_support N c hcN χ hχ hp hpc hv' x hne).mpr hpv)
            rw [hg0, map_zero, zero_mul]
        rw [h0, mul_zero, zero_smul]
        exact zero_mem _
      · refine Submodule.smul_mem _ _ ((mem_pPart N c χ p _).mpr ⟨gblock_mem N c hcN χ hχ hv', fun x hpx => ?_⟩)
        by_contra hne
        exact hpv ((gblock_support N c hcN χ hχ hp hpc hv' x hne).mp hpx)
    · push Not at hs
      rw [← hPf, geps_conv_blockProj_eq_zero N c hcN χ hχ s hs f]
      exact zero_mem _
  · refine (mem_pPart N c χ p _).mpr ⟨?_, fun x hx => by rw [Pi.mul_apply, hfz x hx, mul_zero]⟩
    rw [← hPf, dind_mul_blockProj N c hcN χ hχ s f]
    exact blockProj_mem_span N c χ _

/-- **3d.** G_1 ∈ W_p。 -/
theorem gblock_one_mem_pPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) : gblock N c χ 1 ∈ pPart N c χ p :=
  (mem_pPart N c χ p _).mpr ⟨gblock_mem N c hcN χ hχ (one_dvd _), fun x hpx => by
    by_contra hne
    exact hp.not_dvd_one ((gblock_support N c hcN χ hχ hp hpc (one_dvd _) x hne).mp hpx)⟩

/-- **3e.** p ∣ N/c なら G_p ∉ W_p。 -/
theorem gblock_not_mem_pPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hpL : p ∣ N / c) :
    gblock N c χ p ∉ pPart N c χ p := by
  intro hGp
  apply gblock_ne_zero N c hcN χ hpL
  funext x
  show gblock N c χ p x = 0
  by_contra hne
  by_cases hpx : p ∣ x.val
  · exact hne (((mem_pPart N c χ p _).mp hGp).2 x hpx)
  · exact hpx ((gblock_support N c hcN χ hχ hp hpc hpL x hne).mpr (dvd_refl p))

/-- **3f.** W_p ≠ 0。 -/
theorem pPart_ne_bot (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) : pPart N c χ p ≠ ⊥ := by
  intro h
  have hG1 := gblock_one_mem_pPart N c hcN χ hχ hp hpc
  rw [h, Submodule.mem_bot] at hG1
  exact gblock_ne_zero N c hcN χ (one_dvd _) hG1

/-- **3g.** p ∣ N/c なら W_p ≠ V_{c,χ}。 -/
theorem pPart_ne_top (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hpL : p ∣ N / c) :
    pPart N c χ p ≠ blockSpan N c χ := by
  intro h
  apply gblock_not_mem_pPart N c hcN χ hχ hp hpc hpL
  rw [h]
  exact gblock_mem N c hcN χ hχ hpL

/-- **3h. 主定理（⇒ の対偶）**：素数 p が c と N/c を割るならブロック (c, χ) は既約でない。 -/
theorem not_blockIrreducible_of_dvd (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hpL : p ∣ N / c) :
    ¬ BlockIrreducible N c χ := by
  intro hirr
  rcases hirr (pPart N c χ p) (pPart_shellInvariant N c hcN χ hχ hp hpc)
      (fun f hf => ((mem_pPart N c χ p f).mp hf).1) with h | h
  · exact pPart_ne_bot N c hcN χ hχ hp hpc h
  · exact pPart_ne_top N c hcN χ hχ hp hpc hpL h

/-! ### 4. まとめ -/

/-- **4a. 既約性の判定**：ブロック (c, χ) が既約 ⇔ gcd(c, N/c) = 1（χ 原始的）。 -/
theorem blockIrreducible_iff (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : BlockIrreducible N c χ ↔ Nat.Coprime c (N / c) := by
  constructor
  · intro hirr
    by_contra hnc
    obtain ⟨p, hp, hpc, hpL⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    exact not_blockIrreducible_of_dvd N c hcN χ hχ hp hpc hpL hirr
  · exact blockIrreducible_of_coprime N c hcN χ hχ

/-- **4b.** 殻の射影で閉じる ⇔ 代数 A（Part 214 の shellAlg）のすべての元で閉じる。 -/
theorem shellInvariant_iff (N : ℕ) [NeZero N] (W : Submodule ℂ (ZMod N → ℂ)) :
    ShellInvariant W ↔ ∀ T ∈ shellAlg N, ∀ f ∈ W, T f ∈ W := by
  constructor
  · intro hW T hT
    unfold shellAlg at hT
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      intro f hf
      rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · exact (hW s f hf).1
      · exact (hW s f hf).2
    | algebraMap r =>
      intro f hf
      rw [Module.algebraMap_end_apply]
      exact W.smul_mem r hf
    | add x y _ _ hx hy =>
      intro f hf
      rw [LinearMap.add_apply]
      exact W.add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy =>
      intro f hf
      rw [Module.End.mul_apply]
      exact hx _ (hy f hf)
  · intro hA s f hf
    refine ⟨hA (PAG.Part15.convL (geps N s)) ?_ f hf, hA (LinearMap.mulLeft ℂ (dind N s)) ?_ f hf⟩
    · unfold shellAlg
      exact Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
    · unfold shellAlg
      exact Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)

/-- **4c. シューア型**：gcd(c, N/c) = 1 なら、E_s・D_s・P とすべて可換な線形写像 T は V_{c,χ} の上でスカラー。 -/
theorem commute_scalar_of_coprime (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hcop : Nat.Coprime c (N / c)) (T : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ) (f : ZMod N → ℂ), T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ) (f : ZMod N → ℂ), T (dind N s * f) = dind N s * T f)
    (hTP : ∀ f : ZMod N → ℂ, T (blockProj N c χ f) = blockProj N c χ (T f)) :
    ∃ μ : ℂ, ∀ f ∈ blockSpan N c χ, T f = μ • f := by
  set μ : ℂ := (N : ℂ) / (Nat.totient (1 * c) : ℂ) *
    ∑ x, starRingEnd ℂ (gblock N c χ 1 x) * T (gblock N c χ 1) x with hμ
  have hTG : T (gblock N c χ 1) = μ • gblock N c χ 1 := by
    have h1 : PAG.Part15.conv (geps N (N / (1 * c))) (gblock N c χ 1) = gblock N c χ 1 := by
      rw [geps_conv_gblock N c hcN χ (one_dvd _) (N / (1 * c)), ite_eq_left rfl]
    have h2 : blockProj N c χ (gblock N c χ 1) = gblock N c χ 1 := blockProj_gblock N c hcN χ hχ (one_dvd _)
    calc T (gblock N c χ 1)
        = T (PAG.Part15.conv (geps N (N / (1 * c))) (blockProj N c χ (gblock N c χ 1))) := by rw [h2, h1]
      _ = PAG.Part15.conv (geps N (N / (1 * c))) (blockProj N c χ (T (gblock N c χ 1))) := by rw [hTE, hTP]
      _ = μ • gblock N c χ 1 := geps_conv_blockProj_gblock N c hcN χ hχ (one_dvd _) _
  refine ⟨μ, ?_⟩
  let W : Submodule ℂ (ZMod N → ℂ) :=
    { carrier := {f | f ∈ blockSpan N c χ ∧ T f = μ • f}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [map_add, ha.2, hb.2, smul_add]⟩
      zero_mem' := ⟨zero_mem _, by rw [map_zero, smul_zero]⟩
      smul_mem' := fun r {f} hf => ⟨Submodule.smul_mem _ r hf.1, by rw [map_smul, hf.2, smul_comm]⟩ }
  have hWinv : ShellInvariant W := by
    intro s f hf
    obtain ⟨hfb, hfT⟩ := hf
    have hPf := blockProj_of_mem N c hcN χ hχ hfb
    constructor
    · refine ⟨?_, ?_⟩
      · rw [← hPf, geps_conv_blockProj N c hcN χ hχ s f]
        exact blockProj_mem_span N c χ _
      · rw [hTE, hfT, ← PAG.Part15.convL_apply, map_smul, PAG.Part15.convL_apply]
    · refine ⟨?_, ?_⟩
      · rw [← hPf, dind_mul_blockProj N c hcN χ hχ s f]
        exact blockProj_mem_span N c χ _
      · rw [hTD, hfT, mul_smul_comm]
  rcases blockIrreducible_of_coprime N c hcN χ hχ hcop W hWinv (fun f hf => hf.1) with h | h
  · exfalso
    have hG : gblock N c χ 1 ∈ W := ⟨gblock_mem N c hcN χ hχ (one_dvd _), hTG⟩
    rw [h, Submodule.mem_bot] at hG
    exact gblock_ne_zero N c hcN χ (one_dvd _) hG
  · intro f hf
    rw [← h] at hf
    exact hf.2

/-! ### 5. 推移性：A の元で写せるか -/

/-- **5a.** gcd(c, N/c) = 1 なら、V_{c,χ} の 0 でない f を V_{c,χ} の任意の g に写す A の元がある。 -/
theorem exists_shellAlg_apply_eq (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hcop : Nat.Coprime c (N / c)) {f g : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ)
    (hg : g ∈ blockSpan N c χ) (hf0 : f ≠ 0) : ∃ T ∈ shellAlg N, T f = g := by
  let W : Submodule ℂ (ZMod N → ℂ) := (Subalgebra.toSubmodule (shellAlg N)).map (LinearMap.applyₗ f)
  have hmem : ∀ h, h ∈ W ↔ ∃ T ∈ shellAlg N, T f = h := by
    intro h
    simp only [W, Submodule.mem_map, Subalgebra.mem_toSubmodule, LinearMap.applyₗ_apply_apply]
  have hWinv : ShellInvariant W := by
    intro s h hh
    obtain ⟨T, hT, rfl⟩ := (hmem h).mp hh
    constructor
    · refine (hmem _).mpr ⟨PAG.Part15.convL (geps N s) * T, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hT
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
    · refine (hmem _).mpr ⟨LinearMap.mulLeft ℂ (dind N s) * T, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hT
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
  have hWb : W ≤ blockSpan N c χ := by
    intro h hh
    obtain ⟨T, hT, rfl⟩ := (hmem h).mp hh
    rw [← blockProj_of_mem N c hcN χ hχ hf, shellAlg_comm_blockProj N c hcN χ hχ hT]
    exact blockProj_mem_span N c χ _
  have hfW : f ∈ W := (hmem f).mpr ⟨1, Subalgebra.one_mem _, rfl⟩
  rcases blockIrreducible_of_coprime N c hcN χ hχ hcop W hWinv hWb with h | h
  · exfalso
    rw [h, Submodule.mem_bot] at hfW
    exact hf0 hfW
  · rw [← h] at hg
    exact (hmem g).mp hg

/-- **5b.** 素数 p が c と N/c を割るなら、A のどの元も G_1 を G_p に写さない。 -/
theorem shellAlg_apply_ne_of_dvd (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {p : ℕ} (hp : p.Prime) (hpc : p ∣ c) (hpL : p ∣ N / c)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N) : T (gblock N c χ 1) ≠ gblock N c χ p := by
  intro e
  have hinv := (shellInvariant_iff N (pPart N c χ p)).mp (pPart_shellInvariant N c hcN χ hχ hp hpc)
  have hGp := hinv T hT _ (gblock_one_mem_pPart N c hcN χ hχ hp hpc)
  rw [e] at hGp
  exact gblock_not_mem_pPart N c hcN χ hχ hp hpc hpL hGp

/-- **5c. 推移性の判定**：V_{c,χ} の 0 でない任意の f を V_{c,χ} の任意の g に写す A の元がある ⇔ gcd(c, N/c) = 1。 -/
theorem transitive_iff (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    (∀ f ∈ blockSpan N c χ, ∀ g ∈ blockSpan N c χ, f ≠ 0 → ∃ T ∈ shellAlg N, T f = g) ↔
      Nat.Coprime c (N / c) := by
  constructor
  · intro htr
    by_contra hnc
    obtain ⟨p, hp, hpc, hpL⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    obtain ⟨T, hT, e⟩ := htr _ (gblock_mem N c hcN χ hχ (one_dvd _)) _ (gblock_mem N c hcN χ hχ hpL)
      (gblock_ne_zero N c hcN χ (one_dvd _))
    exact shellAlg_apply_ne_of_dvd N c hcN χ hχ hp hpc hpL hT e
  · intro hcop f hf g hg hf0
    exact exists_shellAlg_apply_eq N c hcN χ hχ hcop hf hg hf0

end PAG.Part219

#print axioms PAG.Part219.blockSpan
#print axioms PAG.Part219.blockProj_of_mem
#print axioms PAG.Part219.gblock_mem
#print axioms PAG.Part219.blockProj_dft_gblock_inv
#print axioms PAG.Part219.dft_gblock_mem
#print axioms PAG.Part219.gblock_ne_zero
#print axioms PAG.Part219.gblock_one
#print axioms PAG.Part219.not_dvd_of_chi_ne_zero
#print axioms PAG.Part219.sum_changeLevel_mul_conj
#print axioms PAG.Part219.inner_gblock_one_dft
#print axioms PAG.Part219.inner_gblock_one_dft_ne_zero
#print axioms PAG.Part219.inner_dft_gblock_one_ne_zero
#print axioms PAG.Part219.ShellInvariant
#print axioms PAG.Part219.BlockIrreducible
#print axioms PAG.Part219.coprime_shell
#print axioms PAG.Part219.blockIrreducible_of_coprime
#print axioms PAG.Part219.gblock_support
#print axioms PAG.Part219.pPart
#print axioms PAG.Part219.mem_pPart
#print axioms PAG.Part219.pPart_shellInvariant
#print axioms PAG.Part219.gblock_one_mem_pPart
#print axioms PAG.Part219.gblock_not_mem_pPart
#print axioms PAG.Part219.pPart_ne_bot
#print axioms PAG.Part219.pPart_ne_top
#print axioms PAG.Part219.not_blockIrreducible_of_dvd
#print axioms PAG.Part219.blockIrreducible_iff
#print axioms PAG.Part219.shellInvariant_iff
#print axioms PAG.Part219.commute_scalar_of_coprime
#print axioms PAG.Part219.exists_shellAlg_apply_eq
#print axioms PAG.Part219.shellAlg_apply_ne_of_dvd
#print axioms PAG.Part219.transitive_iff
