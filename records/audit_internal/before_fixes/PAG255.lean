/-
  PAG 2.0 Part 251（2026-11-12）— Part 249 の射影極限の側：素数の類は、両立する系の群 unitSys × ℝ で稠密な部分群を生成する
  （unitSys は lim (ℤ/N)^× の具体モデル。Ẑ^× との同一視、極限としての普遍性は Lean にしていない）
  問いの出所：著者の指示（「Part 249 の射影極限の側から進めてください」）。
  Part 249 は有限レベル (ℤ/N)^× × ℝ ごとの稠密性を示し、射影極限への読み替えは「既知の事実による推論、Lean ではない」
  としていた（独立照合 B の指摘）。このパートはその読み替えを Lean にする。
  1. p^(K!) の安定性：N ≤ K なら p^(K!) ≡ p^(N!) (mod N)（N = p^a·M′ と分けると、p^a の側で 0、M′ の側で 1。
     p^(N!) mod N は冪等元だが、冪等性 e² ≡ e そのものは文にしていない）。
     w_p(N) = 1 + p^(N!)·(p − 1) は N と互いに素で、p ∤ N なら w_p(N) ≡ p (mod N)
  2. 両立する系の群 unitSys（射影極限の具体モデル）：レベル N ≥ 1 ごとの単数の、自然な写像で両立する系の全体（積の部分群。各レベルは離散位相）。
     素数 p の類 κ_p = (w_p(N)⁻¹ mod N)_N は両立する系で、p ∤ N なら p⁻¹、p^a ∣ N なら法 p^a で 1
     （Part 249 の独立照合で指摘された「p 成分を 1 とおく」を定義にしたもの）
  3. 稠密性：L を割らない素数の類 (κ_p, −log p) が生成する unitSys × ℝ の部分群は稠密（L = 1 ですべての素数）。
     ℝ は Multiplicative ℝ として積の群に入れた。稠密性は κ_p の p 成分の取り方によらない
  4. 一意性：p ∤ N のレベルで p⁻¹、p の冪のレベルで 1 となる両立する系は κ_p だけ
  どれも既知（C_ℚ ≅ Ẑ^× × ℝ_{>0} のもとで、素数イデールの類が生成する部分群の稠密性）。構造定理 C_ℚ ≅ Ẑ^× × ℝ_{>0}
  そのものと、unitSys ≅ Ẑ^×（Mathlib の Ẑ との同一視）は Lean にしていない
-/
import PAG254
import Mathlib.FieldTheory.Finite.Basic

namespace PAG.Part255

open PAG.Part253 Nat

/-! ### 1. p^(N!) の安定性と、素数の類の代表 w_p(N) -/

/-- 補題：N = p^a·M′、N ≤ K なら p^a ∣ p^(K!)。 -/
theorem pow_dvd_pow_factorial {p a M' N K : ℕ} (hp : p.Prime) (hN : N = p ^ a * M') (hN0 : 0 < N)
    (hK : N ≤ K) : p ^ a ∣ p ^ K ! := by
  apply pow_dvd_pow
  have hM' : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · rw [h, mul_zero] at hN; omega
    · exact h
  have h1 : a < p ^ a := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ a ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_right _ hM'
  have h3 : K ≤ K ! := Nat.self_le_factorial K
  omega

/-- 補題：N = p^a·M′、p ∤ M′、N ≤ K なら p^(K!) ≡ 1 (mod M′)（Euler の定理と φ(M′) ∣ K!）。 -/
theorem pow_factorial_modEq_one {p a M' N K : ℕ} (hp : p.Prime) (hN : N = p ^ a * M') (hpM : ¬ p ∣ M')
    (hN0 : 0 < N) (hK : N ≤ K) : p ^ K ! ≡ 1 [MOD M'] := by
  have hM' : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · rw [h, mul_zero] at hN; omega
    · exact h
  have hcop : p.Coprime M' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have h1 : p ^ φ M' ≡ 1 [MOD M'] := Nat.ModEq.pow_totient hcop
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have h2 : M' ≤ N := by rw [hN]; exact Nat.le_mul_of_pos_left _ hpa
  have h3 : φ M' ∣ K ! :=
    Nat.dvd_factorial (Nat.totient_pos.mpr hM') (le_trans (Nat.totient_le M') (le_trans h2 hK))
  obtain ⟨c, hc⟩ := h3
  rw [hc, pow_mul]
  have := h1.pow c
  rwa [one_pow] at this

/-- **1a. p^(K!) の安定性**：p が素数、0 < N ≤ K なら p^(K!) ≡ p^(N!) (mod N)。 -/
theorem pow_factorial_modEq {p N K : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hK : N ≤ K) :
    p ^ K ! ≡ p ^ N ! [MOD N] := by
  obtain ⟨a, M', hpM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' p hp.ne_one
  have hcop : (p ^ a).Coprime M' := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  have key : p ^ K ! ≡ p ^ N ! [MOD p ^ a * M'] := by
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · have h1 := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow_factorial hp hN hN0 hK)
      have h2 := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow_factorial hp hN hN0 le_rfl)
      exact h1.trans h2.symm
    · have h1 := pow_factorial_modEq_one hp hN hpM hN0 hK
      have h2 := pow_factorial_modEq_one hp hN hpM hN0 le_rfl
      exact h1.trans h2.symm
  rw [← hN] at key
  exact key

/-- w_p(N) = 1 + p^(N!)·(p − 1)。 -/
def wNat (p N : ℕ) : ℕ := 1 + p ^ N ! * (p - 1)

/-- **1b.** w_p(N) は N と互いに素（p の側では w ≡ 1、M′ の側では w ≡ p）。 -/
theorem wNat_coprime {p N : ℕ} (hp : p.Prime) (hN0 : 0 < N) : (wNat p N).Coprime N := by
  obtain ⟨a, M', hpM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0.ne' p hp.ne_one
  have hpM' : p.Coprime M' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have hp1 : 1 ≤ p := hp.pos
  have key : (wNat p N).Coprime (p ^ a * M') := by
    apply Nat.Coprime.mul_right
    · -- w と p は互いに素
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      unfold wNat at hdvd
      have h1 : p ∣ p ^ N ! * (p - 1) :=
        Dvd.dvd.mul_right (dvd_pow_self p (Nat.factorial_pos N).ne') _
      have h2 : p ∣ 1 := (Nat.dvd_add_left h1).mp hdvd
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · -- w ≡ p (mod M′)
      have h1 := pow_factorial_modEq_one hp hN hpM hN0 le_rfl
      have h2 : wNat p N ≡ p [MOD M'] := by
        have h3 : 1 + p ^ N ! * (p - 1) ≡ 1 + 1 * (p - 1) [MOD M'] :=
          Nat.ModEq.add_left 1 (h1.mul_right (p - 1))
        have h4 : 1 + 1 * (p - 1) = p := by omega
        rw [h4] at h3
        exact h3
      have h5 : Nat.gcd (wNat p N) M' = Nat.gcd p M' := h2.gcd_eq
      exact h5.trans hpM'
  rw [← hN] at key
  exact key

/-- **1c.** 0 < N ≤ K なら w_p(K) ≡ w_p(N) (mod N)。 -/
theorem wNat_cast_eq {p N K : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hK : N ≤ K) :
    ((wNat p K : ℕ) : ZMod N) = ((wNat p N : ℕ) : ZMod N) := by
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.add_left 1 ((pow_factorial_modEq hp hN0 hK).mul_right (p - 1))

/-- **1d.** p ∤ N なら w_p(N) ≡ p (mod N)。 -/
theorem wNat_cast_of_coprime {p N : ℕ} (hp : p.Prime) (hN0 : 0 < N) (hpN : p.Coprime N) :
    ((wNat p N : ℕ) : ZMod N) = (p : ZMod N) := by
  rw [ZMod.natCast_eq_natCast_iff]
  have h1 : p ^ φ N ≡ 1 [MOD N] := Nat.ModEq.pow_totient hpN
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.totient_pos.mpr hN0) (Nat.totient_le N)
  have h2 : p ^ N ! ≡ 1 [MOD N] := by
    rw [hc, pow_mul]
    have := h1.pow c
    rwa [one_pow] at this
  have h3 : 1 + p ^ N ! * (p - 1) ≡ 1 + 1 * (p - 1) [MOD N] :=
    Nat.ModEq.add_left 1 (h2.mul_right (p - 1))
  have h4 : 1 + 1 * (p - 1) = p := by have := hp.pos; omega
  rw [h4] at h3
  exact h3

/-- 補題：kUnit は剰余だけで決まる。 -/
theorem kUnit_congr {N : ℕ} {m n : ℕ} (hm : m.Coprime N) (hn : n.Coprime N)
    (h : (m : ZMod N) = (n : ZMod N)) : kUnit m hm = kUnit n hn := by
  unfold kUnit
  congr 1
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime]
  exact h

/-! ### 2. 射影極限と素数の類 κ_p -/

/-- 各レベルの単数群 (ℤ/N)^× には離散位相を入れる（射影極限の位相は、その積位相の制限）。 -/
instance instTopUnitsLevel (N : ℕ+) : TopologicalSpace (ZMod (N : ℕ))ˣ := ⊥

instance instDiscreteUnitsLevel (N : ℕ+) : DiscreteTopology (ZMod (N : ℕ))ˣ := ⟨rfl⟩

/-- 射影極限：レベル N ≥ 1 ごとの単数の、自然な写像で両立する系の全体。 -/
def unitSys : Subgroup (∀ N : ℕ+, (ZMod (N : ℕ))ˣ) where
  carrier := {a | ∀ (N M : ℕ+) (h : (N : ℕ) ∣ (M : ℕ)), ZMod.unitsMap h (a M) = a N}
  mul_mem' := by
    intro a b ha hb N M h
    rw [Pi.mul_apply, map_mul, ha N M h, hb N M h, Pi.mul_apply]
  one_mem' := by
    intro N M h
    rw [Pi.one_apply, map_one, Pi.one_apply]
  inv_mem' := by
    intro a ha N M h
    rw [Pi.inv_apply, map_inv, ha N M h, Pi.inv_apply]

/-- 素数 p の類のレベル N での成分。 -/
def primeCls (p : ℕ) (hp : p.Prime) (N : ℕ+) : (ZMod (N : ℕ))ˣ :=
  kUnit (wNat p N) (wNat_coprime hp N.pos)

/-- **2a.** p ∤ N なら κ_p のレベル N の成分は Part 249 の k_p = p⁻¹。 -/
theorem primeCls_of_coprime (p : ℕ) (hp : p.Prime) (N : ℕ+) (hpN : p.Coprime N) :
    primeCls p hp N = kUnit p hpN :=
  kUnit_congr _ _ (wNat_cast_of_coprime hp N.pos hpN)

/-- **2b.** κ_p は両立する系（unitSys の元）。 -/
theorem primeCls_mem (p : ℕ) (hp : p.Prime) : (fun N => primeCls p hp N) ∈ unitSys := by
  intro N M h
  show ZMod.unitsMap h (primeCls p hp M) = primeCls p hp N
  unfold primeCls
  rw [unitsMap_kUnit h]
  exact kUnit_congr _ _ (wNat_cast_eq hp N.pos (Nat.le_of_dvd M.pos h))

/-- 素数 p の類（射影極限の元）。 -/
def primeSys (p : ℕ) (hp : p.Prime) : unitSys := ⟨fun N => primeCls p hp N, primeCls_mem p hp⟩

/-- **2c. κ_p の p 成分は 1**：p^a ∣ N なら、κ_p のレベル N の成分を法 p^a に落とすと 1。 -/
theorem unitsMap_primeCls_pow (p : ℕ) (hp : p.Prime) (N : ℕ+) {a : ℕ} (h : p ^ a ∣ (N : ℕ)) :
    ZMod.unitsMap h (primeCls p hp N) = 1 := by
  unfold primeCls
  rw [unitsMap_kUnit h, ← kUnit_one (Nat.coprime_one_left (p ^ a))]
  apply kUnit_congr
  rw [ZMod.natCast_eq_natCast_iff]
  have h1 : a < p ^ a := Nat.lt_pow_self hp.one_lt
  have h2 : p ^ a ≤ N := Nat.le_of_dvd N.pos h
  have h3 : (N : ℕ) ≤ (N : ℕ) ! := Nat.self_le_factorial N
  have h4 : p ^ a ∣ p ^ (N : ℕ) ! * (p - 1) := Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _
  have h5 : p ^ (N : ℕ) ! * (p - 1) ≡ 0 [MOD p ^ a] := Nat.modEq_zero_iff_dvd.mpr h4
  exact Nat.ModEq.add_left 1 h5

/-! ### 3. 射影極限での稠密性 -/

/-- L を割らない素数の類 (κ_p, −log p) の全体。 -/
noncomputable def primeGens (L : ℕ) : Set (unitSys × Multiplicative ℝ) :=
  {g | ∃ (p : ℕ) (hp : p.Prime), ¬ p ∣ L ∧ g = (primeSys p hp, Multiplicative.ofAdd (-Real.log p))}

/-- **3a.** L ∣ N とする。N と互いに素な正の整数 m について、L を割らない素数の類が生成する部分群の元 g で、
レベル N の成分が k_m、実数の成分が −log m のものがある（素因数分解についての帰納法）。 -/
theorem exists_mem_closure_level {L : ℕ} (N : ℕ+) (hL : L ∣ (N : ℕ)) :
    ∀ (m : ℕ), 0 < m → ∀ (hm : m.Coprime N), ∃ g ∈ Subgroup.closure (primeGens L),
      (g.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit m hm ∧ g.2 = Multiplicative.ofAdd (-Real.log m) := by
  intro m
  induction m using Nat.recOnMul with
  | zero => intro h; omega
  | one =>
    intro _ hm
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · rw [kUnit_one]; rfl
    · simp
  | prime p hp =>
    intro _ hm
    have hpL : ¬ p ∣ L := fun hdvd =>
      (Nat.Prime.coprime_iff_not_dvd hp).mp hm (dvd_trans hdvd hL)
    refine ⟨(primeSys p hp, Multiplicative.ofAdd (-Real.log p)), Subgroup.subset_closure ⟨p, hp, hpL, rfl⟩, ?_, rfl⟩
    exact primeCls_of_coprime p hp N hm
  | mul a b iha ihb =>
    intro hab0 hab
    have ha0 : 0 < a := by
      rcases Nat.eq_zero_or_pos a with h | h
      · rw [h, zero_mul] at hab0; omega
      · exact h
    have hb0 : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h, mul_zero] at hab0; omega
      · exact h
    have ha : a.Coprime N := Nat.Coprime.coprime_mul_right hab
    have hb : b.Coprime N := Nat.Coprime.coprime_mul_left hab
    obtain ⟨ga, hga, ha1, ha2⟩ := iha ha0 ha
    obtain ⟨gb, hgb, hb1, hb2⟩ := ihb hb0 hb
    refine ⟨ga * gb, Subgroup.mul_mem _ hga hgb, ?_, ?_⟩
    · rw [kUnit_mul ha hb hab, ← ha1, ← hb1]; rfl
    · rw [Prod.snd_mul, ha2, hb2, ← ofAdd_add]
      congr 1
      have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha0.ne'
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb0.ne'
      rw [Nat.cast_mul, Real.log_mul ha' hb']
      ring

/-- **3b. 開集合の各点はレベルの筒を含む**（逆向き「筒は開集合」は文にしていない）：unitSys の開集合 u と a ∈ u に対し、あるレベル N があって、
レベル N の成分が a と同じ系はすべて u に入る（有限個のレベルは、その積のレベルで決まる）。 -/
theorem exists_level {u : Set unitSys} (hu : IsOpen u) {a : unitSys} (ha : a ∈ u) :
    ∃ N : ℕ+, ∀ b : unitSys, (b : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N → b ∈ u := by
  obtain ⟨s, hs, rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨I, w, hw, hIs⟩ := isOpen_pi_iff.mp hs a.1 ha
  refine ⟨∏ i ∈ I, i, fun b hb => ?_⟩
  apply hIs
  intro i hi
  have hdvd : (i : ℕ) ∣ ((∏ j ∈ I, j : ℕ+) : ℕ) := PNat.dvd_iff.mp (Finset.dvd_prod_of_mem _ hi)
  have h1 := b.2 i (∏ j ∈ I, j) hdvd
  have h2 := a.2 i (∏ j ∈ I, j) hdvd
  have h3 : (b : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) i = (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) i := by
    rw [← h1, ← h2, hb]
  rw [h3]
  exact (hw i hi).2

/-- **3c. 射影極限での稠密性（有限個の素数を除いた形）**：L ≥ 1 を割らない素数の類 (κ_p, −log p) が生成する
unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_primeGens (L : ℕ+) :
    Dense ((Subgroup.closure (primeGens L) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := isOpen_prod_iff.mp hU x.1 x.2 hx
  obtain ⟨N₀, hN₀⟩ := exists_level hu hxu
  -- レベルを N = N₀·L に上げる
  set N : ℕ+ := N₀ * L with hNdef
  have hN₀N : (N₀ : ℕ) ∣ (N : ℕ) := by rw [hNdef, PNat.mul_coe]; exact Nat.dvd_mul_right _ _
  have hLN : (L : ℕ) ∣ (N : ℕ) := by rw [hNdef, PNat.mul_coe]; exact Nat.dvd_mul_left _ _
  have hN : ∀ b : unitSys, (b : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = (x.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N → b ∈ u := by
    intro b hb
    apply hN₀
    rw [← b.2 N₀ N hN₀N, ← x.1.2 N₀ N hN₀N, hb]
  have hv' : IsOpen (Multiplicative.ofAdd ⁻¹' v) := continuous_ofAdd.isOpen_preimage v hv
  have ht : Multiplicative.toAdd x.2 ∈ Multiplicative.ofAdd ⁻¹' v := by
    show Multiplicative.ofAdd (Multiplicative.toAdd x.2) ∈ v
    rw [ofAdd_toAdd]
    exact hxv
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hv' _ ht
  have : NeZero (N : ℕ) := ⟨N.pos.ne'⟩
  obtain ⟨m, n, hm, hn, hm0, hn0, hcls, hlog⟩ :=
    exists_cls_near ((x.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N) (Multiplicative.toAdd x.2) hε
  obtain ⟨gm, hgm, hm1, hm2⟩ := exists_mem_closure_level N hLN m hm0 hm
  obtain ⟨gn, hgn, hn1, hn2⟩ := exists_mem_closure_level N hLN n hn0 hn
  refine ⟨gm * gn⁻¹, huv ⟨?_, ?_⟩, Subgroup.mul_mem _ hgm (Subgroup.inv_mem _ hgn)⟩
  · apply hN
    show (gm.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N * ((gn.1 : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N)⁻¹ = _
    rw [hm1, hn1, hcls]
  · show gm.2 * gn.2⁻¹ ∈ v
    rw [hm2, hn2, ← ofAdd_neg, ← ofAdd_add]
    have hmem : (-Real.log m + - -Real.log n) ∈ Metric.ball (Multiplicative.toAdd x.2) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : -Real.log m + - -Real.log n - Multiplicative.toAdd x.2 =
          Real.log n - Real.log m - Multiplicative.toAdd x.2 := by ring
      rw [this]
      exact hlog
    exact hball hmem

/-- **3d. 射影極限での稠密性**：すべての素数の類 (κ_p, −log p) が生成する unitSys × ℝ の部分群は稠密。 -/
theorem dense_closure_allPrimes :
    Dense ((Subgroup.closure (primeGens 1) : Subgroup (unitSys × Multiplicative ℝ)) :
      Set (unitSys × Multiplicative ℝ)) :=
  dense_closure_primeGens 1

/-! ### 4. κ_p の一意性（独立照合 A の指摘で追加：稠密性は p 成分の取り方によらないので、κ_p を別に特徴づける） -/

/-- 補題：N = A·B、A と B が互いに素なら、(ℤ/N)^× の元は法 A と法 B への像で決まる。 -/
theorem units_eq_of_coprime_parts {N A B : ℕ} [NeZero N] (hN : N = A * B) (hAB : A.Coprime B)
    (hA : A ∣ N) (hB : B ∣ N) (b c : (ZMod N)ˣ)
    (h1 : ZMod.unitsMap hA b = ZMod.unitsMap hA c) (h2 : ZMod.unitsMap hB b = ZMod.unitsMap hB c) :
    b = c := by
  have e1 : (((b : ZMod N).val : ℕ) : ZMod A) = (((c : ZMod N).val : ℕ) : ZMod A) := by
    have := congrArg Units.val h1
    rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at this
    rw [ZMod.natCast_val, ZMod.natCast_val]
    exact this
  have e2 : (((b : ZMod N).val : ℕ) : ZMod B) = (((c : ZMod N).val : ℕ) : ZMod B) := by
    have := congrArg Units.val h2
    rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at this
    rw [ZMod.natCast_val, ZMod.natCast_val]
    exact this
  rw [ZMod.natCast_eq_natCast_iff] at e1 e2
  have e3 : (b : ZMod N).val ≡ (c : ZMod N).val [MOD A * B] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hAB).mp ⟨e1, e2⟩
  rw [← hN] at e3
  have e4 := (ZMod.natCast_eq_natCast_iff _ _ N).mpr e3
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at e4
  exact Units.ext e4

/-- **2d. κ_p の一意性**：両立する系 a が、p ∤ N のすべてのレベルで p⁻¹ に等しく、p の冪のレベルに落とすと 1 なら、a = κ_p。
2a・2c と合わせて、κ_p は「p 成分が 1、ほかの成分が p⁻¹」で決まるただ 1 つの元。 -/
theorem primeSys_unique (p : ℕ) (hp : p.Prime) (a : unitSys)
    (h1 : ∀ (N : ℕ+) (hpN : p.Coprime N), (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = kUnit p hpN)
    (h2 : ∀ (N : ℕ+) (k : ℕ) (h : p ^ k ∣ (N : ℕ)),
      ZMod.unitsMap h ((a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N) = 1) :
    a = primeSys p hp := by
  apply Subtype.ext
  funext N
  show (a : ∀ N : ℕ+, (ZMod (N : ℕ))ˣ) N = primeCls p hp N
  obtain ⟨k, M', hpM, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd N.pos.ne' p hp.ne_one
  have hcop : (p ^ k).Coprime M' := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM)
  have hA : p ^ k ∣ (N : ℕ) := ⟨M', hN⟩
  have hB : M' ∣ (N : ℕ) := ⟨p ^ k, by rw [hN, mul_comm]⟩
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · rw [h, mul_zero] at hN; exact absurd hN N.pos.ne'
    · exact h
  have : NeZero (N : ℕ) := ⟨N.pos.ne'⟩
  refine units_eq_of_coprime_parts hN hcop hA hB _ _ ?_ ?_
  · rw [h2 N k hA, unitsMap_primeCls_pow p hp N hA]
  · have hpM' : p.Coprime ((⟨M', hM'pos⟩ : ℕ+) : ℕ) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
    have ha := a.2 ⟨M', hM'pos⟩ N hB
    have hk := primeCls_mem p hp ⟨M', hM'pos⟩ N hB
    exact ha.trans ((h1 ⟨M', hM'pos⟩ hpM').trans
      ((primeCls_of_coprime p hp ⟨M', hM'pos⟩ hpM').symm.trans hk.symm))

end PAG.Part255

#print axioms PAG.Part255.pow_dvd_pow_factorial
#print axioms PAG.Part255.pow_factorial_modEq_one
#print axioms PAG.Part255.pow_factorial_modEq
#print axioms PAG.Part255.wNat
#print axioms PAG.Part255.wNat_coprime
#print axioms PAG.Part255.wNat_cast_eq
#print axioms PAG.Part255.wNat_cast_of_coprime
#print axioms PAG.Part255.kUnit_congr
#print axioms PAG.Part255.instTopUnitsLevel
#print axioms PAG.Part255.instDiscreteUnitsLevel
#print axioms PAG.Part255.unitSys
#print axioms PAG.Part255.primeCls
#print axioms PAG.Part255.primeCls_of_coprime
#print axioms PAG.Part255.primeCls_mem
#print axioms PAG.Part255.primeSys
#print axioms PAG.Part255.unitsMap_primeCls_pow
#print axioms PAG.Part255.primeGens
#print axioms PAG.Part255.exists_mem_closure_level
#print axioms PAG.Part255.exists_level
#print axioms PAG.Part255.dense_closure_primeGens
#print axioms PAG.Part255.dense_closure_allPrimes
#print axioms PAG.Part255.units_eq_of_coprime_parts
#print axioms PAG.Part255.primeSys_unique
