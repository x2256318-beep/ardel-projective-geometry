/-
  PAG 2.0 Part 221（2026-10-29）— 可換子の代数としての構造
  A = ⟨E_s, D_s⟩、A′ = 空間全体の可換子（Part 220 の fullComm）、dilComm = A′ ∩ (U_a と可換)（Part 220）
  ブロック b = (c, χ)、V_b、P_b、層の射影 Q_d = ι_d·（Part 217）、m(c) = 法 c の原始指標の数
  0. V の上で可換で V を保つ写像は、V の上で関数を掛ける作用素（φ = Σ_d μ_d·ι_d）。
     そのような 2 つの写像は V の上で可換。各ブロックを保つ A′ の 2 つの元は可換
  1. 単数倍とも可換な変換は各ブロックを保つので、dilComm は可換
  2. すべての c ∣ N で m(c) ≤ 1 なら、同じ導手のブロックは 1 つだけなので A′ の元は各ブロックを保ち、A′ は可換
  3. 法 c に原始指標 χ ≠ χ′ があれば、X = (ねじり Θ の延長)、Y = (恒等写像の延長) = P_χ は A′ の元で
     XY − YX = X ≠ 0。まとめ：A′ が可換 ⇔ すべての c ∣ N で m(c) ≤ 1
  4. 原始指標の数：m(1) = 1、m(p) = p − 2、m(4) = 1、m(6) = 0、m(8) = 2、m(9) = 4、m(12) = 1。
     すべての c ∣ N で m(c) ≤ 1 ⇔ N ∣ 12。よって A′ が可換 ⇔ N ∣ 12
  5. ブロックに制限した可換子（Part 217 の blockComm）：Q_dQ_{d′} = [d = d′]Q_d、Σ_d Q_d = 1、各元は V の上で
     関数を掛ける作用素で、可換。積で閉じた部分代数（def blockCommAlg）で、ℂ^D と代数として同型
     （a ↦ Σ_d a_d·Q_d、def layerAlgHom・blockCommAlgEquiv）
-/
import PAG224

namespace PAG.Part225

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 関数を掛ける作用素 -/

/-- **0a.** V の上で E_s・D_s と可換で V を保つ T は、V の上で関数 φ = Σ_{d ∈ D} μ_d(T)·ι_d を掛ける作用素
（Part 217 の `commute_eq_sum_layerInd`）。 -/
theorem exists_mul_of_commute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ,
      T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ), ∀ f ∈ blockSpan N c χ, T (dind N s * f) = dind N s * T f)
    (hTV : ∀ f ∈ blockSpan N c χ, T f ∈ blockSpan N c χ) :
    ∃ φ : ZMod N → ℂ, ∀ f ∈ blockSpan N c χ, T f = φ * f := by
  refine ⟨∑ d ∈ layerIdx c (N / c), ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
      ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x) • layerInd N c d, fun f hf => ?_⟩
  rw [commute_eq_sum_layerInd N c hcN χ hχ T hTE hTD hTV f hf, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [smul_mul_assoc]

/-- **0b.** A′ の元 T, T′ がどちらも V を保つなら、V の上で T(T′ f) = T′(T f)。 -/
theorem commute_on_blockSpan (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) (hT' : T' ∈ fullComm N)
    (hTV : ∀ f ∈ blockSpan N c χ, T f ∈ blockSpan N c χ) (hT'V : ∀ f ∈ blockSpan N c χ, T' f ∈ blockSpan N c χ)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) : T (T' f) = T' (T f) := by
  obtain ⟨φ, hφ⟩ := exists_mul_of_commute N c hcN χ hχ T (fun s g _ => ((mem_fullComm N T).mp hT s g).1)
    (fun s g _ => ((mem_fullComm N T).mp hT s g).2) hTV
  obtain ⟨φ', hφ'⟩ := exists_mul_of_commute N c hcN χ hχ T' (fun s g _ => ((mem_fullComm N T').mp hT' s g).1)
    (fun s g _ => ((mem_fullComm N T').mp hT' s g).2) hT'V
  rw [hφ _ (hT'V f hf), hφ' f hf, hφ' _ (hTV f hf), hφ f hf, mul_left_comm]

/-- **0c.** A′ の 2 つの元がどちらも各ブロックを保つなら、可換。 -/
theorem commute_of_preserves (N : ℕ) [NeZero N] {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N)
    (hT' : T' ∈ fullComm N)
    (hTb : ∀ b : BlockIdx N, ∀ f ∈ blockSpan N b.1 b.2.1, T f ∈ blockSpan N b.1 b.2.1)
    (hT'b : ∀ b : BlockIdx N, ∀ f ∈ blockSpan N b.1 b.2.1, T' f ∈ blockSpan N b.1 b.2.1) : Commute T T' := by
  classical
  apply LinearMap.ext
  intro g
  rw [Module.End.mul_apply, Module.End.mul_apply, ← sum_blockProj N g]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact commute_on_blockSpan N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 hT hT' (hTb b) (hT'b b)
    (blockProjL_mem N b.1 b.2.1 g)

/-! ### 1. 単数倍とも可換な変換は可換 -/

/-- **1a.** 単数倍 U_a とすべて可換な T は各ブロックを保つ（T は P_b と可換：Part 214 の `comm_blockProj`）。 -/
theorem dilCommute_preserves (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ dilCommute N)
    (b : BlockIdx N) {f : ZMod N → ℂ} (hf : f ∈ blockSpan N b.1 b.2.1) : T f ∈ blockSpan N b.1 b.2.1 := by
  rw [← blockProj_of_mem N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 hf,
    comm_blockProj N b.1 (Nat.dvd_of_mem_divisors b.1.2) b.2.1 b.2.2 T ((mem_dilCommute N T).mp hT) f]
  exact blockProjL_mem N b.1 b.2.1 _

/-- **1b. 単数倍とも可換な変換は可換**：T, T′ ∈ dilComm なら TT′ = T′T（Part 214 の読み取り）。 -/
theorem dilComm_commute (N : ℕ) [NeZero N] {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ dilComm N)
    (hT' : T' ∈ dilComm N) : Commute T T' :=
  commute_of_preserves N ((mem_dilComm N T).mp hT).1 ((mem_dilComm N T').mp hT').1
    (fun b _ hf => dilCommute_preserves N ((mem_dilComm N T).mp hT).2 b hf)
    (fun b _ hf => dilCommute_preserves N ((mem_dilComm N T').mp hT').2 b hf)

/-! ### 2. 各導手の原始指標が 1 つ以下なら A′ は可換 -/

/-- **2a.** すべての c ∣ N で m(c) ≤ 1 なら、導手の等しいブロックの番号は等しい。 -/
theorem blockIdx_eq_of_card_le_one (N : ℕ)
    (h : ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1)
    {b b' : BlockIdx N} (hc : (b.1 : ℕ) = b'.1) : b = b' := by
  obtain ⟨⟨c, hc1⟩, χ⟩ := b
  obtain ⟨⟨c', hc1'⟩, χ'⟩ := b'
  have hcc : c = c' := hc
  subst hcc
  have : Subsingleton {χ : DirichletCharacter ℂ c // χ.IsPrimitive} :=
    Finite.card_le_one_iff_subsingleton.mp (h c hc1)
  have e : χ = χ' := Subsingleton.elim χ χ'
  subst e
  rfl

/-- **2b.** すべての c ∣ N で m(c) ≤ 1 なら、A′ の元は各ブロックを保つ（ほかのブロックへの成分は、導手が違うので 0）。 -/
theorem fullComm_preserves_of_card_le_one (N : ℕ) [NeZero N]
    (h : ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) (b : BlockIdx N) {f : ZMod N → ℂ}
    (hf : f ∈ blockSpan N b.1 b.2.1) : T f ∈ blockSpan N b.1 b.2.1 := by
  classical
  have e : T f = blockProj N b.1 b.2.1 (T f) := by
    conv_lhs => rw [← sum_blockProj N (T f)]
    rw [Finset.sum_eq_single b]
    · intro b' _ hb'
      have hcc : (b.1 : ℕ) ≠ b'.1 := fun hc => hb' (blockIdx_eq_of_card_le_one N h hc).symm
      have hm := commBlock_mem N b b' hT
      rw [blockHom_eq_bot_of_ne N b.1 b'.1 (Nat.dvd_of_mem_divisors b.1.2) (Nat.dvd_of_mem_divisors b'.1.2)
        b.2.1 b'.2.1 b.2.2 b'.2.2 hcc, Submodule.mem_bot] at hm
      have h1 : (commBlock N b b' T ⟨f, hf⟩ : ZMod N → ℂ) = 0 := by rw [hm]; rfl
      exact (commBlock_apply N b b' T ⟨f, hf⟩).symm.trans h1
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  rw [e]
  exact blockProjL_mem N b.1 b.2.1 _

/-- **2c.** すべての c ∣ N で m(c) ≤ 1 なら A′ は可換。 -/
theorem fullComm_commute_of_card_le_one (N : ℕ) [NeZero N]
    (h : ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1)
    {T T' : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ fullComm N) (hT' : T' ∈ fullComm N) : Commute T T' :=
  commute_of_preserves N hT hT' (fun b _ hf => fullComm_preserves_of_card_le_one N h hT b hf)
    (fun b _ hf => fullComm_preserves_of_card_le_one N h hT' b hf)

/-! ### 3. 同じ導手に原始指標が 2 つあれば A′ は可換でない -/

/-- **3a.** V の恒等写像はブロックに制限した可換子に入る。 -/
theorem id_mem_blockComm (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) :
    (LinearMap.id : Module.End ℂ (blockSpan N c χ)) ∈ blockComm N c χ := by
  rw [mem_blockComm]
  intro s f hf
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **3b.** V の恒等写像は A 準同型。 -/
theorem id_mem_blockHom (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) :
    (LinearMap.id : blockSpan N c χ →ₗ[ℂ] blockSpan N c χ) ∈ blockHom N c c χ χ := by
  rw [mem_blockHom]
  intro s f hf
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- **3c.** 法 c の原始指標 χ ≠ χ′ について、X = (ねじり Θ : V_χ → V_χ′ の延長)、Y = (V_χ の恒等写像の延長) = P_χ は
A′ の元で、可換でない（XY = X、YX = 0、X ≠ 0）。 -/
theorem not_commute_of_ne (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ χ' : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) (hne : χ ≠ χ') :
    blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id) ∈ fullComm N ∧
      blockHomExt N c c χ χ LinearMap.id ∈ fullComm N ∧
      ¬ Commute (blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id))
        (blockHomExt N c c χ χ LinearMap.id) := by
  refine ⟨blockHomExt_mem_fullComm N c c hcN χ χ' hχ
      (twistV_comp_mem_blockHom N c hcN χ χ' hχ hχ' (id_mem_blockComm N c χ)),
    blockHomExt_mem_fullComm N c c hcN χ χ hχ (id_mem_blockHom N c χ), fun hcomm => ?_⟩
  have hg : gblock N c χ 1 ∈ blockSpan N c χ := gblock_mem N c hcN χ hχ (one_dvd _)
  have hg0 : gblock N c χ 1 ≠ 0 := gblock_ne_zero N c hcN χ (one_dvd _)
  have hne' : (⟨c, χ'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) ≠ ⟨c, χ⟩ :=
    fun e => hne (eq_of_heq (Sigma.mk.inj e).2).symm
  have hY : ∀ f, blockHomExt N c c χ χ LinearMap.id f = blockProj N c χ f := fun _ => rfl
  have hX : ∀ f, blockHomExt N c c χ χ' (twistV N c hcN χ χ' ∘ₗ LinearMap.id) f =
      twistFn N c χ χ' * blockProj N c χ f := fun _ => rfl
  have e := LinearMap.congr_fun hcomm.eq (gblock N c χ 1)
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  simp only [hX, hY] at e
  rw [blockProj_of_mem N c hcN χ hχ hg, blockProj_of_mem N c hcN χ hχ hg,
    blockProj_eq_zero_of_mem N c c hcN hcN χ' χ hχ' hχ hne' (twistFn_mul_mem N c hcN χ χ' hg)] at e
  apply hg0
  rw [← twistFn_mul_twistFn N c hcN χ χ' hg, e, mul_zero]

/-- **3d.** A′ が可換なら、すべての c ∣ N で m(c) ≤ 1。 -/
theorem card_le_one_of_fullComm_commute (N : ℕ) [NeZero N]
    (h : ∀ T ∈ fullComm N, ∀ T' ∈ fullComm N, Commute T T') :
    ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1 := by
  intro c hc
  by_contra hlt
  have hlt' : 1 < Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} := Nat.lt_of_not_le hlt
  have : NeZero c := ⟨(Nat.pos_of_mem_divisors hc).ne'⟩
  obtain ⟨⟨χ, hχ⟩, ⟨χ', hχ'⟩, hne⟩ := (Finite.one_lt_card_iff_nontrivial.mp hlt').exists_pair_ne
  have hne' : χ ≠ χ' := fun e => hne (Subtype.ext e)
  obtain ⟨hX, hY, hXY⟩ := not_commute_of_ne N c (Nat.dvd_of_mem_divisors hc) χ χ' hχ hχ' hne'
  exact hXY (h _ hX _ hY)

/-- **3e. A′ が可換になる条件**：A′ が可換 ⇔ すべての c ∣ N で m(c) ≤ 1。 -/
theorem fullComm_commute_iff (N : ℕ) [NeZero N] :
    (∀ T ∈ fullComm N, ∀ T' ∈ fullComm N, Commute T T') ↔
      ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1 :=
  ⟨card_le_one_of_fullComm_commute N, fun h _ hT _ hT' => fullComm_commute_of_card_le_one N h hT hT'⟩

/-! ### 4. 原始指標の数と N ∣ 12 -/

/-- **4a.** m(1) = 1。 -/
theorem card_primitive_one : Nat.card {χ : DirichletCharacter ℂ 1 // χ.IsPrimitive} = 1 := by
  have h := sum_card_primitive 1
  rw [Nat.divisors_one, Finset.sum_singleton, Nat.totient_one] at h
  exact h

/-- **4b.** 素数 p で m(p) = p − 2。 -/
theorem card_primitive_prime {p : ℕ} (hp : p.Prime) :
    Nat.card {χ : DirichletCharacter ℂ p // χ.IsPrimitive} = p - 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h := sum_card_primitive p
  rw [Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne, card_primitive_one, Nat.totient_prime hp] at h
  have := hp.two_le
  omega

/-- **4c.** m(4) = 1。 -/
theorem card_primitive_four : Nat.card {χ : DirichletCharacter ℂ 4 // χ.IsPrimitive} = 1 := by
  have h := sum_card_primitive 4
  rw [show Nat.divisors 4 = {1, 2, 4} by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, card_primitive_one, card_primitive_prime Nat.prime_two,
    show Nat.totient 4 = 2 by decide] at h
  omega

/-- **4d.** m(6) = 0。 -/
theorem card_primitive_six : Nat.card {χ : DirichletCharacter ℂ 6 // χ.IsPrimitive} = 0 := by
  have h := sum_card_primitive 6
  rw [show Nat.divisors 6 = {1, 2, 3, 6} by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, card_primitive_one, card_primitive_prime Nat.prime_two,
    card_primitive_prime Nat.prime_three, show Nat.totient 6 = 2 by decide] at h
  omega

/-- **4e.** m(8) = 2。 -/
theorem card_primitive_eight : Nat.card {χ : DirichletCharacter ℂ 8 // χ.IsPrimitive} = 2 := by
  have h := sum_card_primitive 8
  rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, card_primitive_one, card_primitive_prime Nat.prime_two,
    card_primitive_four, show Nat.totient 8 = 4 by decide] at h
  omega

/-- **4f.** m(9) = 4。 -/
theorem card_primitive_nine : Nat.card {χ : DirichletCharacter ℂ 9 // χ.IsPrimitive} = 4 := by
  have h := sum_card_primitive 9
  rw [show Nat.divisors 9 = {1, 3, 9} by decide, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, card_primitive_one, card_primitive_prime Nat.prime_three,
    show Nat.totient 9 = 6 by decide] at h
  omega

/-- **4g.** m(12) = 1。 -/
theorem card_primitive_twelve : Nat.card {χ : DirichletCharacter ℂ 12 // χ.IsPrimitive} = 1 := by
  have h := sum_card_primitive 12
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, card_primitive_one, card_primitive_prime Nat.prime_two,
    card_primitive_prime Nat.prime_three, card_primitive_four, card_primitive_six,
    show Nat.totient 12 = 4 by decide] at h
  omega

/-- **4h.** N ∣ 12 なら、すべての c ∣ N で m(c) ≤ 1。 -/
theorem card_primitive_le_one_of_dvd {N : ℕ} (hN : N ∣ 12) :
    ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1 := by
  intro c hc
  have hc12 : c ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨(Nat.dvd_of_mem_divisors hc).trans hN, by norm_num⟩
  rw [show Nat.divisors 12 = {1, 2, 3, 4, 6, 12} by decide] at hc12
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc12
  rcases hc12 with rfl | rfl | rfl | rfl | rfl | rfl
  · have := card_primitive_one; omega
  · have := card_primitive_prime Nat.prime_two; omega
  · have := card_primitive_prime Nat.prime_three; omega
  · have := card_primitive_four; omega
  · have := card_primitive_six; omega
  · have := card_primitive_twelve; omega

/-- **4i.** すべての c ∣ N で m(c) ≤ 1 なら N ∣ 12（素因数は 2・3 だけ、8 ∤ N、9 ∤ N）。 -/
theorem dvd_twelve_of_card_primitive_le_one {N : ℕ} [NeZero N]
    (h : ∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1) : N ∣ 12 := by
  have hN : N ≠ 0 := NeZero.ne N
  have hp : ∀ p ∈ N.primeFactors, p = 2 ∨ p = 3 := by
    intro p hpN
    have hpp := Nat.prime_of_mem_primeFactors hpN
    have h1 := h p (Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hpN, hN⟩)
    rw [card_primitive_prime hpp] at h1
    have h2 := hpp.two_le
    omega
  have h8 : ¬ 2 ^ 3 ∣ N := fun h8 => by
    have h1 := h 8 (Nat.mem_divisors.mpr ⟨by simpa using h8, hN⟩)
    rw [card_primitive_eight] at h1
    omega
  have h9 : ¬ 3 ^ 2 ∣ N := fun h9 => by
    have h1 := h 9 (Nat.mem_divisors.mpr ⟨by simpa using h9, hN⟩)
    rw [card_primitive_nine] at h1
    omega
  have hsub : N.factorization.support ⊆ {2, 3} := by
    intro p hpN
    rw [Nat.support_factorization] at hpN
    rcases hp p hpN with rfl | rfl <;> simp
  have hfac := Nat.prod_factorization_pow_eq_self hN
  rw [Finsupp.prod_of_support_subset N.factorization hsub (fun p k => p ^ k) (fun _ _ => pow_zero _),
    Finset.prod_pair (by norm_num)] at hfac
  have ha : N.factorization 2 ≤ 2 := by
    by_contra ha
    have ha3 : 3 ≤ N.factorization 2 := by omega
    exact h8 ((pow_dvd_pow 2 ha3).trans (Nat.ordProj_dvd N 2))
  have hb : N.factorization 3 ≤ 1 := by
    by_contra hb
    have hb2 : 2 ≤ N.factorization 3 := by omega
    exact h9 ((pow_dvd_pow 3 hb2).trans (Nat.ordProj_dvd N 3))
  rw [← hfac, show (12 : ℕ) = 2 ^ 2 * 3 ^ 1 by norm_num]
  exact Nat.mul_dvd_mul (pow_dvd_pow 2 ha) (pow_dvd_pow 3 hb)

/-- **4j.** すべての c ∣ N で m(c) ≤ 1 ⇔ N ∣ 12。 -/
theorem card_primitive_le_one_iff (N : ℕ) [NeZero N] :
    (∀ c ∈ N.divisors, Nat.card {χ : DirichletCharacter ℂ c // χ.IsPrimitive} ≤ 1) ↔ N ∣ 12 :=
  ⟨dvd_twelve_of_card_primitive_le_one, card_primitive_le_one_of_dvd⟩

/-- **4k. A′ が可換 ⇔ N ∣ 12**（step243 の (4) で数値だけだった読み取り）。 -/
theorem fullComm_commute_iff_dvd_twelve (N : ℕ) [NeZero N] :
    (∀ T ∈ fullComm N, ∀ T' ∈ fullComm N, Commute T T') ↔ N ∣ 12 :=
  (fullComm_commute_iff N).trans (card_primitive_le_one_iff N)

/-! ### 5. ブロックに制限した可換子は ℂ^D と代数として同型 -/

/-- **5a.** Q_dQ_{d′} = [d = d′]·Q_d。 -/
theorem layerProjV_mul (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (d d' : layerIdx c (N / c)) :
    layerProjV N c hcN χ d * layerProjV N c hcN χ d' = if d = d' then layerProjV N c hcN χ d else 0 := by
  have hd := ((mem_layerIdx c (N / c) d).mp d.2).2
  have hd' := ((mem_layerIdx c (N / c) d').mp d'.2).2
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Module.End.mul_apply, layerProjV_apply, layerProjV_apply]
  by_cases hdd : d = d'
  · subst hdd
    rw [ite_eq_left rfl, layerProjV_apply]
    funext x
    simp only [Pi.mul_apply, layerInd]
    split_ifs <;> simp
  · rw [ite_eq_right hdd, LinearMap.zero_apply, Submodule.coe_zero]
    funext x
    simp only [Pi.mul_apply, layerInd, Pi.zero_apply]
    split_ifs with h1 h2 <;> first | exact absurd (Subtype.ext (layer_unique hd hd' h1 h2)) hdd | simp

/-- **5b.** Σ_d Q_d = 1（V の上）。 -/
theorem sum_layerProjV (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    ∑ d : layerIdx c (N / c), layerProjV N c hcN χ d = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [LinearMap.sum_apply, Submodule.coe_sum, Module.End.one_apply]
  simp only [layerProjV_apply]
  exact (Finset.sum_coe_sort (layerIdx c (N / c)) (fun d => layerInd N c d * (f : ZMod N → ℂ))).trans
    (sum_layerInd_mul N c hcN χ f.2)

/-- **5c.** ブロックに制限した可換子の元は、V の上で関数 φ = Σ_d μ_d·ι_d を掛ける作用素。 -/
theorem blockComm_exists_mul (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {S : Module.End ℂ (blockSpan N c χ)} (hS : S ∈ blockComm N c χ) :
    ∃ φ : ZMod N → ℂ, ∀ f : blockSpan N c χ, (S f : ZMod N → ℂ) = φ * f := by
  refine ⟨∑ d ∈ layerIdx c (N / c), ((N : ℂ) / (Nat.totient (d * c) : ℂ) *
      ∑ x, starRingEnd ℂ (gblock N c χ d x) * blockExt N c χ S (gblock N c χ d) x) • layerInd N c d,
    fun f => ?_⟩
  rw [blockComm_apply N c hcN χ hχ hS f, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [smul_mul_assoc]

/-- **5d. ブロックに制限した可換子は可換**。 -/
theorem blockComm_commute (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {S S' : Module.End ℂ (blockSpan N c χ)} (hS : S ∈ blockComm N c χ)
    (hS' : S' ∈ blockComm N c χ) : Commute S S' := by
  obtain ⟨φ, hφ⟩ := blockComm_exists_mul N c hcN χ hχ hS
  obtain ⟨φ', hφ'⟩ := blockComm_exists_mul N c hcN χ hχ hS'
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rw [Module.End.mul_apply, Module.End.mul_apply, hφ, hφ', hφ', hφ, mul_left_comm]

/-- **5e.** ブロックに制限した可換子は積で閉じる。 -/
theorem blockComm_mul_mem (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {S S' : Module.End ℂ (blockSpan N c χ)} (hS : S ∈ blockComm N c χ)
    (hS' : S' ∈ blockComm N c χ) : S * S' ∈ blockComm N c χ := by
  have hinv := blockSpan_shellInvariant N c hcN χ hχ
  rw [mem_blockComm]
  intro s f hf
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e1 : S' ⟨PAG.Part15.conv (geps N s) f, h⟩ =
        ⟨PAG.Part15.conv (geps N s) (S' ⟨f, hf⟩ : ZMod N → ℂ), (hinv s _ (S' ⟨f, hf⟩).2).1⟩ :=
      Subtype.ext (((mem_blockComm N c χ S').mp hS' s f hf).1 h)
    rw [Module.End.mul_apply, Module.End.mul_apply, e1]
    exact ((mem_blockComm N c χ S).mp hS s _ (S' ⟨f, hf⟩).2).1 _
  · have e1 : S' ⟨dind N s * f, h⟩ =
        ⟨dind N s * (S' ⟨f, hf⟩ : ZMod N → ℂ), (hinv s _ (S' ⟨f, hf⟩).2).2⟩ :=
      Subtype.ext (((mem_blockComm N c χ S').mp hS' s f hf).2 h)
    rw [Module.End.mul_apply, Module.End.mul_apply, e1]
    exact ((mem_blockComm N c χ S).mp hS s _ (S' ⟨f, hf⟩).2).2 _

/-- ブロックに制限した可換子の部分代数。 -/
noncomputable def blockCommAlg (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : Subalgebra ℂ (Module.End ℂ (blockSpan N c χ)) :=
  (blockComm N c χ).toSubalgebra (id_mem_blockComm N c χ) (fun _ _ hS hS' => blockComm_mul_mem N c hcN χ hχ hS hS')

/-- **5f.** 判定（元は blockComm と同じ）。 -/
theorem mem_blockCommAlg (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (S : Module.End ℂ (blockSpan N c χ)) :
    S ∈ blockCommAlg N c hcN χ hχ ↔ S ∈ blockComm N c χ := Iff.rfl

/-- ℂ^D → (ブロックに制限した可換子)：a ↦ Σ_d a_d·Q_d（代数の準同型）。 -/
noncomputable def layerAlgHom (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : (layerIdx c (N / c) → ℂ) →ₐ[ℂ] blockCommAlg N c hcN χ hχ :=
  AlgHom.ofLinearMap
    { toFun := fun a => ⟨∑ d, a d • layerProjV N c hcN χ d,
        (mem_blockCommAlg N c hcN χ hχ _).mpr (Submodule.sum_mem _ (fun d _ =>
          Submodule.smul_mem _ _ (layerProjV_mem_blockComm N c hcN χ hχ d)))⟩
      map_add' := fun a b => by
        apply Subtype.ext
        show ∑ d, (a + b) d • layerProjV N c hcN χ d =
          ∑ d, a d • layerProjV N c hcN χ d + ∑ d, b d • layerProjV N c hcN χ d
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        apply Subtype.ext
        show ∑ d, (r • a) d • layerProjV N c hcN χ d = r • ∑ d, a d • layerProjV N c hcN χ d
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] }
    (by
      apply Subtype.ext
      show ∑ d, (1 : layerIdx c (N / c) → ℂ) d • layerProjV N c hcN χ d = 1
      simp only [Pi.one_apply, one_smul]
      exact sum_layerProjV N c hcN χ)
    (fun a b => by
      apply Subtype.ext
      show ∑ d, (a * b) d • layerProjV N c hcN χ d =
        (∑ d, a d • layerProjV N c hcN χ d) * ∑ d, b d • layerProjV N c hcN χ d
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.mul_sum]
      simp only [smul_mul_smul_comm, layerProjV_mul, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq]
      simp)

/-- **5g.** (layerAlgHom a) = Σ_d a_d·Q_d。 -/
theorem layerAlgHom_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (a : layerIdx c (N / c) → ℂ) :
    (layerAlgHom N c hcN χ hχ a : Module.End ℂ (blockSpan N c χ)) = ∑ d, a d • layerProjV N c hcN χ d := rfl

/-- **5h.** a ↦ Σ_d a_d·Q_d は全単射（Q_d は一次独立で、可換子を張る：Part 217）。 -/
theorem layerAlgHom_bijective (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : Function.Bijective (layerAlgHom N c hcN χ hχ) := by
  constructor
  · intro a b hab
    have h := congrArg (fun S : blockCommAlg N c hcN χ hχ => (S : Module.End ℂ (blockSpan N c χ))) hab
    simp only [layerAlgHom_apply] at h
    funext d
    exact Fintype.linearIndependent_iffₛ.mp (layerProjV_linearIndependent N c hcN χ hχ) a b h d
  · intro S
    have hS : (S : Module.End ℂ (blockSpan N c χ)) ∈ Submodule.span ℂ (Set.range (layerProjV N c hcN χ)) := by
      rw [← blockComm_eq_span N c hcN χ hχ]
      exact S.2
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hS
    exact ⟨a, Subtype.ext ha⟩

/-- **5i. 代数の同型** ℂ^D ≅ (ブロックに制限した可換子)。 -/
noncomputable def blockCommAlgEquiv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : (layerIdx c (N / c) → ℂ) ≃ₐ[ℂ] blockCommAlg N c hcN χ hχ :=
  AlgEquiv.ofBijective (layerAlgHom N c hcN χ hχ) (layerAlgHom_bijective N c hcN χ hχ)

end PAG.Part225

#print axioms PAG.Part225.exists_mul_of_commute
#print axioms PAG.Part225.commute_on_blockSpan
#print axioms PAG.Part225.commute_of_preserves
#print axioms PAG.Part225.dilCommute_preserves
#print axioms PAG.Part225.dilComm_commute
#print axioms PAG.Part225.blockIdx_eq_of_card_le_one
#print axioms PAG.Part225.fullComm_preserves_of_card_le_one
#print axioms PAG.Part225.fullComm_commute_of_card_le_one
#print axioms PAG.Part225.id_mem_blockComm
#print axioms PAG.Part225.id_mem_blockHom
#print axioms PAG.Part225.not_commute_of_ne
#print axioms PAG.Part225.card_le_one_of_fullComm_commute
#print axioms PAG.Part225.fullComm_commute_iff
#print axioms PAG.Part225.card_primitive_one
#print axioms PAG.Part225.card_primitive_prime
#print axioms PAG.Part225.card_primitive_four
#print axioms PAG.Part225.card_primitive_six
#print axioms PAG.Part225.card_primitive_eight
#print axioms PAG.Part225.card_primitive_nine
#print axioms PAG.Part225.card_primitive_twelve
#print axioms PAG.Part225.card_primitive_le_one_of_dvd
#print axioms PAG.Part225.dvd_twelve_of_card_primitive_le_one
#print axioms PAG.Part225.card_primitive_le_one_iff
#print axioms PAG.Part225.fullComm_commute_iff_dvd_twelve
#print axioms PAG.Part225.layerProjV_mul
#print axioms PAG.Part225.sum_layerProjV
#print axioms PAG.Part225.blockComm_exists_mul
#print axioms PAG.Part225.blockComm_commute
#print axioms PAG.Part225.blockComm_mul_mem
#print axioms PAG.Part225.blockCommAlg
#print axioms PAG.Part225.mem_blockCommAlg
#print axioms PAG.Part225.layerAlgHom
#print axioms PAG.Part225.layerAlgHom_apply
#print axioms PAG.Part225.layerAlgHom_bijective
#print axioms PAG.Part225.blockCommAlgEquiv
