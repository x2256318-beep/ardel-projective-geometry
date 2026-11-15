/-
  PAG 2.0 Part 216（2026-10-28）— ブロックの既約成分への分解（層）と、その個数
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。V_{c,χ}（Part 215 の blockSpan）
  rad(d) ∣ c（abbrev RadDvd：d の素因数はすべて c を割る）
  n が d の層に入る（abbrev InLayer：n = d·e、e は c と互いに素）
  W(d) = {f ∈ V_{c,χ} : x.val が d の層でなければ f(x) = 0}（def layerPart）
  D = {d ∣ L : rad(d) ∣ c}（def layerIdx）
  0. 層の算術：層は一意、0 でない n はある d（rad(d) ∣ c）の層に入る、#D = Π_{p ∣ gcd(c, L)} (v_p(L) + 1)
  1. 台：k_d は d の層、G_v は v の層（v が d の層なら d の層）、H_w の点は N/(wc) の層、重なりの補題
  2. かなめ：rad(d) ∣ c なら G_d = B_d⁻¹·k_d。N/(wc) = d·e なら ⟨k_d, H_w⟩ = φ(N/d)^(−1/2)·conj(χ(e))·φ(wc)
  3. W(d)（d ∈ D）は殻の射影で閉じ、0 でなく、既約
  4. 分解：W(d)（d ∈ D）は独立（iSupIndep）、⨆_{d ∈ D} W(d) = V_{c,χ}。成分の個数は #D
  5. 成分は互いに同型でない：E_s・D_s と可換な写像 W(d) → W(d′)（d ≠ d′）は 0。各 W(d) の中ではスカラー（シューア型）
-/
import PAG219

namespace PAG.Part220

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 層の算術 -/

/-- rad(d) ∣ c：d の素因数はすべて c を割る。 -/
abbrev RadDvd (d c : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ d → q ∣ c

/-- n は d の層に入る：n = d·e（e は c と互いに素）。 -/
abbrev InLayer (c d n : ℕ) : Prop := ∃ e : ℕ, n = d * e ∧ Nat.Coprime e c

/-- **0a.** rad(d) ∣ c、gcd(e, c) = 1 なら gcd(d, e) = 1。 -/
theorem coprime_of_radDvd {d c e : ℕ} (hd : RadDvd d c) (he : Nat.Coprime e c) : Nat.Coprime d e :=
  Nat.coprime_of_dvd (fun q hq hqd hqe => by
    have h1 := Nat.dvd_gcd hqe (hd q hq hqd)
    rw [Nat.Coprime.gcd_eq_one he] at h1
    exact hq.one_lt.ne' (Nat.dvd_one.mp h1))

/-- **0b.** ψ(m) ≠ 0（ψ は法 n の指標）なら gcd(m, n) = 1。 -/
theorem coprime_of_chi_ne_zero {n : ℕ} (ψ : DirichletCharacter ℂ n) {m : ℕ} (h : ψ (m : ZMod n) ≠ 0) :
    Nat.Coprime m n := by
  by_contra hnc
  exact h (MulChar.map_nonunit _ (fun hu => hnc ((ZMod.isUnit_iff_coprime m n).mp hu)))

/-- **0c. 層は一意**：rad(d), rad(d′) ∣ c で n が d と d′ の両方の層に入るなら d = d′。 -/
theorem layer_unique {c d d' n : ℕ} (hd : RadDvd d c) (hd' : RadDvd d' c) (h : InLayer c d n)
    (h' : InLayer c d' n) : d = d' := by
  obtain ⟨e, rfl, he⟩ := h
  obtain ⟨e', hee, he'⟩ := h'
  apply Nat.dvd_antisymm
  · refine (coprime_of_radDvd hd he').dvd_of_dvd_mul_right ?_
    rw [← hee]
    exact Dvd.intro e rfl
  · refine (coprime_of_radDvd hd' he).dvd_of_dvd_mul_right ?_
    rw [hee]
    exact Dvd.intro e' rfl

/-- **0d.** 0 でない n は、rad(d) ∣ c のある d の層に入る（c 部分と残りへの分解）。 -/
theorem exists_layer (c : ℕ) : ∀ n : ℕ, n ≠ 0 → ∃ d, RadDvd d c ∧ InLayer c d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hcop : Nat.Coprime n c
    · exact ⟨1, fun q hq hq1 => absurd (Nat.dvd_one.mp hq1) hq.one_lt.ne', n, (one_mul n).symm, hcop⟩
    · obtain ⟨p, hp, hpn, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      obtain ⟨m, rfl⟩ := hpn
      have hm0 : m ≠ 0 := fun h => hn (by rw [h, mul_zero])
      have hlt : m < p * m := by
        have h2 := hp.two_le
        have hm := Nat.pos_of_ne_zero hm0
        nlinarith
      obtain ⟨d, hd, e, hde, he⟩ := ih m hlt hm0
      refine ⟨p * d, fun q hq hqd => ?_, e, by rw [hde, mul_assoc], he⟩
      rcases (Nat.Prime.dvd_mul hq).mp hqd with hqp | hqd'
      · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp hqp]
        exact hpc
      · exact hd q hq hqd'

open Classical in
/-- 層の番号 D = {d ∣ L : rad(d) ∣ c}。 -/
noncomputable def layerIdx (c L : ℕ) : Finset ℕ := L.divisors.filter (fun d => RadDvd d c)

/-- **0e.** D の元の判定。 -/
theorem mem_layerIdx (c L d : ℕ) : d ∈ layerIdx c L ↔ d ∈ L.divisors ∧ RadDvd d c := by
  classical
  unfold layerIdx
  rw [Finset.mem_filter]

/-- **0f. 層の番号の個数**：#D = Π_{p ∣ gcd(c, L)} (v_p(L) + 1)（L ≠ 0）。 -/
theorem card_layerIdx (c L : ℕ) (hL : L ≠ 0) :
    (layerIdx c L).card = ∏ p ∈ (Nat.gcd c L).primeFactors, (L.factorization p + 1) := by
  obtain ⟨Lc, hLc, L', hLeq, hL'⟩ := exists_layer c L hL
  have hLc0 : Lc ≠ 0 := fun h => hL (by rw [hLeq, h, zero_mul])
  have hL'0 : L' ≠ 0 := fun h => hL (by rw [hLeq, h, mul_zero])
  have hset : layerIdx c L = Lc.divisors := by
    ext d
    rw [mem_layerIdx, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdL, -⟩, hd⟩
      refine ⟨?_, hLc0⟩
      rw [hLeq] at hdL
      exact (coprime_of_radDvd hd hL').dvd_of_dvd_mul_right hdL
    · rintro ⟨hdLc, -⟩
      refine ⟨⟨dvd_trans hdLc ⟨L', hLeq⟩, hL⟩, fun q hq hqd => hLc q hq (dvd_trans hqd hdLc)⟩
  have hnd : ∀ p : ℕ, p.Prime → p ∣ c → ¬ p ∣ L' := fun p hp hpc hpL' => by
    have h1 := Nat.dvd_gcd hpL' hpc
    rw [Nat.Coprime.gcd_eq_one hL'] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hg0 : Nat.gcd c L ≠ 0 := (Nat.gcd_pos_of_pos_right c (Nat.pos_of_ne_zero hL)).ne'
  have hpf : Lc.primeFactors = (Nat.gcd c L).primeFactors := by
    ext p
    rw [Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hpLc, -⟩
      exact ⟨hp, Nat.dvd_gcd (hLc p hp hpLc) (dvd_trans hpLc ⟨L', hLeq⟩), hg0⟩
    · rintro ⟨hp, hpg, -⟩
      have hpc := dvd_trans hpg (Nat.gcd_dvd_left c L)
      have hpL := dvd_trans hpg (Nat.gcd_dvd_right c L)
      rw [hLeq] at hpL
      rcases (Nat.Prime.dvd_mul hp).mp hpL with h | h
      · exact ⟨hp, h, hLc0⟩
      · exact absurd h (hnd p hp hpc)
  rw [hset, Nat.card_divisors hLc0, hpf]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  obtain ⟨hpp, hpg, -⟩ := Nat.mem_primeFactors.mp hp
  have hpc := dvd_trans hpg (Nat.gcd_dvd_left c L)
  rw [hLeq, Nat.factorization_mul hLc0 hL'0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (hnd p hpp hpc), add_zero]

/-! ### 1. 台 -/

/-- **1a.** k_d の台は d の層：k_d(x) ≠ 0 ⇒ x.val は d の層。 -/
theorem kblock_layer (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) {d : ℕ} (x : ZMod N)
    (hx : kblock N c χ d x ≠ 0) : InLayer c d x.val := by
  by_cases h : d ∣ N ∧ c ∣ N / d
  · rw [kblock_of_dvd N c χ h.1 h.2, gket_apply] at hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos h.1 (Nat.pos_of_ne_zero (NeZero.ne N))
    by_cases hdx : d ∣ x.val
    · rw [ite_eq_left hdx] at hx
      obtain ⟨e, he⟩ := hdx
      refine ⟨e, he, ?_⟩
      rw [he, Nat.mul_div_cancel_left e hd0] at hx
      exact coprime_of_chi_ne_zero χ (right_ne_zero_of_mul hx)
    · rw [ite_eq_right hdx] at hx
      exact absurd rfl hx
  · exfalso
    apply hx
    unfold kblock
    rw [dite_eq_right h]
    rfl

/-- **1b.** G_v の台：v が d の層（rad(d) ∣ c）なら、G_v(x) ≠ 0 ⇒ x.val は d の層。 -/
theorem gblock_layer (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v d : ℕ} (hv : v ∣ N / c) (hd : RadDvd d c) (hvd : InLayer c d v) (x : ZMod N)
    (hx : gblock N c χ v x ≠ 0) : InLayer c d x.val := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hv0 : 0 < v := Nat.pos_of_dvd_of_pos hv hL0
  rw [gblock_eq_sum N c hcN χ hχ v hv, Finset.sum_apply] at hx
  obtain ⟨w, hw, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  rw [Pi.smul_apply, smul_eq_mul] at hne
  have hwv : w ∣ v := Nat.dvd_of_mem_divisors hw
  have hcop1 : Nat.Coprime (v / w) c :=
    coprime_of_chi_ne_zero χ⁻¹ (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne)))
  obtain ⟨a, ha, hacop⟩ := kblock_layer N c χ x (right_ne_zero_of_mul hne)
  obtain ⟨e, hve, hecop⟩ := hvd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos ⟨e, hve⟩ hv0
  have hdw : d ∣ w := by
    have h1 : d ∣ w * (v / w) := by
      rw [Nat.mul_div_cancel' hwv, hve]
      exact Dvd.intro e rfl
    exact (coprime_of_radDvd hd hcop1).dvd_of_dvd_mul_right h1
  obtain ⟨m, hm⟩ := hdw
  have hme : e = m * (v / w) := by
    have h2 : d * e = d * (m * (v / w)) := by
      rw [← hve, ← mul_assoc, ← hm, Nat.mul_div_cancel' hwv]
    exact Nat.eq_of_mul_eq_mul_left hd0 h2
  have hmcop : Nat.Coprime m c := Nat.Coprime.coprime_dvd_left (Dvd.intro _ hme.symm) hecop
  exact ⟨m * a, by rw [ha, hm, mul_assoc], Nat.Coprime.mul_left hmcop hacop⟩

/-- **1c.** H_w の台：H_w(x) ≠ 0 ⇒ x.val = (N/(wc))·y（y は c と互いに素）。 -/
theorem dft_gblock_support (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {w : ℕ}
    (hw : w ∣ N / c) (x : ZMod N) (hx : 𝓕 (gblock N c χ⁻¹ w) x ≠ 0) :
    ∃ y : ℕ, x.val = N / (w * c) * y ∧ Nat.Coprime y c := by
  have hsh : N / (w * c) * (w * c) = N := gblock_shell hcN hw
  have hs0 : 0 < N / (w * c) := Nat.pos_of_ne_zero (fun h => NeZero.ne N (by rw [← hsh, h, zero_mul]))
  unfold gblock at hx
  rw [dft_gbas_apply] at hx
  by_cases hs : N / (w * c) ∣ x.val
  · rw [ite_eq_left hs] at hx
    obtain ⟨y, hy⟩ := hs
    refine ⟨y, hy, ?_⟩
    rw [hy, Nat.mul_div_cancel_left y hs0] at hx
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_left c w) (coprime_of_chi_ne_zero _ hx)
  · rw [ite_eq_right hs] at hx
    exact absurd rfl hx

/-- **1d.** N/(wc) が d の層なら、H_w(x) ≠ 0 の点 x も d の層。 -/
theorem dft_gblock_layer (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {w d : ℕ}
    (hw : w ∣ N / c) (hl : InLayer c d (N / (w * c))) (x : ZMod N) (hx : 𝓕 (gblock N c χ⁻¹ w) x ≠ 0) :
    InLayer c d x.val := by
  obtain ⟨y, hy, hycop⟩ := dft_gblock_support N c hcN χ hw x hx
  obtain ⟨e, he, hecop⟩ := hl
  exact ⟨e * y, by rw [hy, he, mul_assoc], Nat.Coprime.mul_left hecop hycop⟩

/-- **1e. 重なりの補題**：rad(d) ∣ c、d > 0 で、H_w(x) ≠ 0 の点 x が d の層なら、N/(wc) も d の層。 -/
theorem layer_of_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {w d : ℕ} (hw : w ∣ N / c) (hd : RadDvd d c) (hd0 : 0 < d) (x : ZMod N)
    (hx : 𝓕 (gblock N c χ⁻¹ w) x ≠ 0) (hxd : InLayer c d x.val) : InLayer c d (N / (w * c)) := by
  obtain ⟨y, hy, hycop⟩ := dft_gblock_support N c hcN χ hw x hx
  obtain ⟨e, he, hecop⟩ := hxd
  have hdt : d ∣ N / (w * c) := by
    have h1 : d ∣ N / (w * c) * y := by
      rw [← hy, he]
      exact Dvd.intro e rfl
    exact (coprime_of_radDvd hd hycop).dvd_of_dvd_mul_right h1
  obtain ⟨m, hm⟩ := hdt
  have hme : e = m * y := by
    have h2 : d * e = d * (m * y) := by rw [← he, hy, hm, mul_assoc]
    exact Nat.eq_of_mul_eq_mul_left hd0 h2
  exact ⟨m, hm, Nat.Coprime.coprime_dvd_left (Dvd.intro _ hme.symm) hecop⟩

/-! ### 2. かなめ -/

/-- **2a.** rad(d) ∣ c、d ∣ N/c なら G_d = B_d⁻¹·k_d（B_d = kcoef(N/d, c, χ)）。 -/
theorem gblock_eq_smul_kblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) :
    gblock N c χ d = (kcoef (N / d) c χ)⁻¹ • kblock N c χ d := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
  rw [gblock_eq_sum N c hcN χ hχ d hdL, Finset.sum_eq_single d]
  · rw [Nat.div_self hd0, ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, map_one, one_mul,
      one_mul]
  · intro w hw hwd
    have hwdvd : w ∣ d := Nat.dvd_of_mem_divisors hw
    have hnc : ¬ Nat.Coprime (d / w) c := by
      intro hcop
      have h1 : d / w = 1 := by
        by_contra hne
        obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
        have hqc : q ∣ c := hd q hq (dvd_trans hqd (Nat.div_dvd_of_dvd hwdvd))
        have h3 := Nat.dvd_gcd hqd hqc
        rw [Nat.Coprime.gcd_eq_one hcop] at h3
        exact hq.one_lt.ne' (Nat.dvd_one.mp h3)
      apply hwd
      have h4 := Nat.div_mul_cancel hwdvd
      rw [h1, one_mul] at h4
      exact h4
    have h0 : χ⁻¹ ((d / w : ℕ) : ZMod c) = 0 :=
      MulChar.map_nonunit _ (fun hu => hnc ((ZMod.isUnit_iff_coprime _ _).mp hu))
    rw [h0, mul_zero, zero_mul, zero_smul]
  · intro hd'
    exact absurd (Nat.mem_divisors_self d hd0.ne') hd'

/-- **2b.** N/(wc) = d·e（d ∣ N/c、w ∣ N/c）なら ⟨k_d, H_w⟩ = φ(N/d)^(−1/2)·conj(χ(e))·φ(wc)。 -/
theorem inner_kblock_dft_gblock (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {d w e : ℕ} (hdL : d ∣ N / c) (hw : w ∣ N / c) (hde : N / (w * c) = d * e) :
    ∑ x, starRingEnd ℂ (kblock N c χ d x) * 𝓕 (gblock N c χ⁻¹ w) x =
      (((Real.sqrt (Nat.totient (N / d)))⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (χ (e : ZMod c)) * Nat.totient (w * c) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hw hL0
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
  have hwc : NeZero (w * c) := ⟨(Nat.mul_pos hw0 hc0).ne'⟩
  have hsh : N / (w * c) * (w * c) = N := gblock_shell hcN hw
  have hdvd : c ∣ w * c := dvd_mul_left c w
  obtain ⟨h1, h2⟩ := block_dvd hcN hdL
  have hH : 𝓕 (gblock N c χ⁻¹ w) =
      PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) := by
    unfold gblock
    rw [inv_inv, liftc_of_dvd χ hdvd, dft_gbas (N / (w * c)) (w * c) N hsh]
  rw [hH, kblock_of_dvd N c χ h1 h2]
  rw [show (∑ x, starRingEnd ℂ (gket d (N / d) N (Nat.mul_div_cancel' h1) c h2 χ x) *
      PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) x) =
      ∑ x, PAG.Part17.push (memb (N / (w * c)) (w * c) N hsh) (χ.changeLevel hdvd) x *
        starRingEnd ℂ (gket d (N / d) N (Nat.mul_div_cancel' h1) c h2 χ x) from
      Finset.sum_congr rfl (fun x _ => mul_comm _ _)]
  rw [PAG.Part17.sum_push_mul _ (memb_injective _ _ N hsh)]
  have hterm : ∀ y : ZMod (w * c), χ.changeLevel hdvd y *
      starRingEnd ℂ (gket d (N / d) N (Nat.mul_div_cancel' h1) c h2 χ (memb (N / (w * c)) (w * c) N hsh y)) =
      (((Real.sqrt (Nat.totient (N / d)))⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (χ (e : ZMod c)) *
        (χ.changeLevel hdvd y * starRingEnd ℂ (χ ((y.val : ℕ) : ZMod c))) := by
    intro y
    have hval : (memb (N / (w * c)) (w * c) N hsh y).val = d * (e * y.val) := by
      rw [memb_val, hde, mul_assoc]
    rw [gket_apply, hval, ite_eq_left (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ hd0, Nat.cast_mul]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.mul_sum, sum_changeLevel_mul_conj χ (w * c) hdvd]

/-- **2c.** rad(d) ∣ c、d ∣ N/c、N/(wc) が d の層なら ⟨G_d, H_w⟩ ≠ 0。 -/
theorem inner_gblock_dft_ne_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d w : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (hw : w ∣ N / c)
    (hl : InLayer c d (N / (w * c))) :
    ∑ x, starRingEnd ℂ (gblock N c χ d x) * 𝓕 (gblock N c χ⁻¹ w) x ≠ 0 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hw0 : 0 < w := Nat.pos_of_dvd_of_pos hw hL0
  obtain ⟨h1, h2⟩ := block_dvd hcN hdL
  obtain ⟨e, he, hecop⟩ := hl
  have hNd : N / d ≠ 0 := div_ne_zero_of_dvd (NeZero.ne N) h1
  have hB : kcoef (N / d) c χ ≠ 0 := kcoef_ne_zero (N / d) c hNd h2 χ hχ
  have hA : (((Real.sqrt (Nat.totient (N / d)))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have hφ : (0 : ℝ) < Real.sqrt (Nat.totient (N / d)) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hNd))
    exact_mod_cast (inv_pos.mpr hφ).ne'
  have hφ : (Nat.totient (w * c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hw0 hc0)).ne'
  rw [gblock_eq_smul_kblock N c hcN χ hχ hdL hd, inner_smul_left', inner_kblock_dft_gblock N c hcN χ hdL hw he]
  exact mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero hB))
    (mul_ne_zero (mul_ne_zero hA ((map_ne_zero _).mpr (chi_natCast_ne_zero χ e hecop))) hφ)

/-! ### 3. 層の成分 W(d) -/

/-- 層 d の成分 W(d) = {f ∈ V_{c,χ} : x.val が d の層でなければ f(x) = 0}。 -/
noncomputable def layerPart (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (d : ℕ) :
    Submodule ℂ (ZMod N → ℂ) where
  carrier := {f | f ∈ blockSpan N c χ ∧ ∀ x : ZMod N, ¬ InLayer c d x.val → f x = 0}
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun x hx => by
    rw [Pi.add_apply, ha.2 x hx, hb.2 x hx, add_zero]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩
  smul_mem' := fun r {f} hf => ⟨Submodule.smul_mem _ r hf.1, fun x hx => by
    rw [Pi.smul_apply, hf.2 x hx, smul_zero]⟩

/-- **3a.** W(d) の元の判定。 -/
theorem mem_layerPart (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (d : ℕ) (f : ZMod N → ℂ) :
    f ∈ layerPart N c χ d ↔ f ∈ blockSpan N c χ ∧ ∀ x : ZMod N, ¬ InLayer c d x.val → f x = 0 := Iff.rfl

/-- **3b.** v が d の層（rad(d) ∣ c、v ∣ N/c）なら G_v ∈ W(d)。 -/
theorem gblock_mem_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {v d : ℕ} (hv : v ∣ N / c) (hd : RadDvd d c) (hvd : InLayer c d v) :
    gblock N c χ v ∈ layerPart N c χ d :=
  (mem_layerPart N c χ d _).mpr ⟨gblock_mem N c hcN χ hχ hv, fun x hx => by
    by_contra hne
    exact hx (gblock_layer N c hcN χ hχ hv hd hvd x hne)⟩

/-- **3c.** u が d の層（u ∣ N/c）なら k_u ∈ W(d)。 -/
theorem kblock_mem_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {u d : ℕ} (hu : u ∣ N / c) (hud : InLayer c d u) : kblock N c χ u ∈ layerPart N c χ d := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  refine (mem_layerPart N c χ d _).mpr ⟨?_, fun x hx => ?_⟩
  · unfold blockSpan
    exact Submodule.subset_span ⟨⟨u, Nat.mem_divisors.mpr ⟨hu, hL0.ne'⟩⟩, rfl⟩
  · by_contra hne
    obtain ⟨a, ha, hacop⟩ := kblock_layer N c χ x hne
    obtain ⟨e, he, hecop⟩ := hud
    exact hx ⟨e * a, by rw [ha, he, mul_assoc], Nat.Coprime.mul_left hecop hacop⟩

/-- **3d.** W(d)（rad(d) ∣ c）は殻の射影で閉じる。 -/
theorem layerPart_shellInvariant (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hd : RadDvd d c) : ShellInvariant (layerPart N c χ d) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  intro s f hf
  obtain ⟨hfb, hfz⟩ := (mem_layerPart N c χ d f).mp hf
  have hPf := blockProj_of_mem N c hcN χ hχ hfb
  constructor
  · by_cases hs : ∃ v ∈ (N / c).divisors, s = N / (v * c)
    · obtain ⟨v, hv, rfl⟩ := hs
      have hv' : v ∣ N / c := Nat.dvd_of_mem_divisors hv
      rw [← hPf, geps_conv_blockProj_gblock N c hcN χ hχ hv' f]
      by_cases hvd : InLayer c d v
      · exact Submodule.smul_mem _ _ (gblock_mem_layerPart N c hcN χ hχ hv' hd hvd)
      · have h0 : ∑ x, starRingEnd ℂ (gblock N c χ v x) * f x = 0 := by
          refine Finset.sum_eq_zero (fun x _ => ?_)
          by_cases hfx : f x = 0
          · rw [hfx, mul_zero]
          · have hxd : InLayer c d x.val := by
              by_contra hn
              exact hfx (hfz x hn)
            have hg0 : gblock N c χ v x = 0 := by
              by_contra hne
              obtain ⟨dv, hdv, hvdv⟩ := exists_layer c v (Nat.pos_of_dvd_of_pos hv' hL0).ne'
              have hx' := gblock_layer N c hcN χ hχ hv' hdv hvdv x hne
              have heq := layer_unique hd hdv hxd hx'
              rw [← heq] at hvdv
              exact hvd hvdv
            rw [hg0, map_zero, zero_mul]
        rw [h0, mul_zero, zero_smul]
        exact zero_mem _
    · push Not at hs
      rw [← hPf, geps_conv_blockProj_eq_zero N c hcN χ hχ s hs f]
      exact zero_mem _
  · refine (mem_layerPart N c χ d _).mpr ⟨?_, fun x hx => by rw [Pi.mul_apply, hfz x hx, mul_zero]⟩
    rw [← hPf, dind_mul_blockProj N c hcN χ hχ s f]
    exact blockProj_mem_span N c χ _

/-- **3e.** d ∈ D なら W(d) ≠ 0（k_d ∈ W(d)）。 -/
theorem layerPart_ne_bot (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    {d : ℕ} (hdL : d ∣ N / c) : layerPart N c χ d ≠ ⊥ := by
  intro h
  have hk : kblock N c χ d ∈ layerPart N c χ d :=
    kblock_mem_layerPart N c hcN χ hdL ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  rw [h, Submodule.mem_bot] at hk
  exact kblock_ne_zero N c hcN χ hdL hk

/-- **3f. 層の成分は既約**：d ∈ D なら、殻の射影で閉じた W(d) の部分空間は 0 か W(d) 全体。 -/
theorem layerPart_irreducible (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (W : Submodule ℂ (ZMod N → ℂ))
    (hW : ShellInvariant W) (hWd : W ≤ layerPart N c χ d) : W = ⊥ ∨ W = layerPart N c χ d := by
  by_cases h0 : W = ⊥
  · exact Or.inl h0
  right
  refine le_antisymm hWd ?_
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdL hL0
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hφ : ∀ w : ℕ, w ∣ N / c → (Nat.totient (w * c) : ℂ) ≠ 0 := fun w hw => by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_dvd_of_pos hw hL0) hc0)).ne'
  -- ⟨H_w, g⟩ ≠ 0（g ∈ W(d)）なら N/(wc) は d の層
  have hover : ∀ (w : ℕ), w ∣ N / c → ∀ g ∈ layerPart N c χ d,
      ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w) k) * g k ≠ 0 → InLayer c d (N / (w * c)) := by
    intro w hw g hg hgw
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hgw
    have hHx : 𝓕 (gblock N c χ⁻¹ w) x ≠ 0 := fun h => hx (by rw [h, map_zero, zero_mul])
    have hgx : g x ≠ 0 := right_ne_zero_of_mul hx
    have hxd : InLayer c d x.val := by
      by_contra hn
      exact hgx (((mem_layerPart N c χ d g).mp hg).2 x hn)
    exact layer_of_dft_gblock N c hcN χ hw hd hd0 x hHx hxd
  -- 0 でない f ∈ W
  obtain ⟨f, hfW, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hfd := hWd hfW
  have hPf := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d f).mp hfd).1
  have hex : ∃ w ∈ (N / c).divisors, ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w) k) * f k ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf0
    rw [← hPf, blockProj_eq_sum_dft_gblock N c hcN χ hχ f]
    exact Finset.sum_eq_zero (fun w hw => by rw [hall w hw, mul_zero, zero_smul])
  obtain ⟨w, hw, hfw⟩ := hex
  have hw' : w ∣ N / c := Nat.dvd_of_mem_divisors hw
  have hlw := hover w hw' f hfd hfw
  -- H_w ∈ W
  have hHw : 𝓕 (gblock N c χ⁻¹ w) ∈ W := by
    have h1 := (hW (N / (w * c)) f hfW).2
    rw [← hPf, dind_mul_blockProj_dft_gblock N c hcN χ hχ hw' f] at h1
    exact (W.smul_mem_iff (mul_ne_zero (inv_ne_zero (hφ w hw')) hfw)).mp h1
  -- G_d ∈ W（E_{N/(dc)} を当てる）
  have hGd : gblock N c χ d ∈ W := by
    have h2 := (hW (N / (d * c)) _ hHw).1
    rw [← blockProj_dft_gblock_inv N c hcN χ hχ hw', geps_conv_blockProj_gblock N c hcN χ hχ hdL _] at h2
    refine (W.smul_mem_iff ?_).mp h2
    exact mul_ne_zero (div_ne_zero hN (hφ d hdL)) (inner_gblock_dft_ne_zero N c hcN χ hχ hdL hd hw' hlw)
  -- N/(w′c) が d の層の H_{w′} はすべて W に入る
  have hH : ∀ w' ∈ (N / c).divisors, InLayer c d (N / (w' * c)) → 𝓕 (gblock N c χ⁻¹ w') ∈ W := by
    intro w' hw'' hl'
    have hw2 : w' ∣ N / c := Nat.dvd_of_mem_divisors hw''
    have h3 := (hW (N / (w' * c)) _ hGd).2
    rw [← blockProj_gblock N c hcN χ hχ hdL, dind_mul_blockProj_dft_gblock N c hcN χ hχ hw2 _] at h3
    refine (W.smul_mem_iff ?_).mp h3
    refine mul_ne_zero (inv_ne_zero (hφ w' hw2)) ?_
    rw [PAG.Part215.inner_conj_symm]
    exact (map_ne_zero _).mpr (inner_gblock_dft_ne_zero N c hcN χ hχ hdL hd hw2 hl')
  -- W(d) ⊆ W
  intro g hg
  have hPg := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d g).mp hg).1
  rw [← hPg, blockProj_eq_sum_dft_gblock N c hcN χ hχ g]
  refine Submodule.sum_mem _ (fun w' hw' => ?_)
  by_cases hl' : InLayer c d (N / (w' * c))
  · exact Submodule.smul_mem _ _ (hH w' hw' hl')
  · have hz : ∑ k, starRingEnd ℂ (𝓕 (gblock N c χ⁻¹ w') k) * g k = 0 := by
      by_contra hne
      exact hl' (hover w' (Nat.dvd_of_mem_divisors hw') g hg hne)
    rw [hz, mul_zero, zero_smul]
    exact zero_mem _

/-! ### 4. 分解 -/

/-- **4a.** W(d)（rad(d) ∣ c）の元は、d の層の点の外で 0、とくに d と違う層 d′ の点では 0。 -/
theorem layerPart_apply_eq_zero (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) {d d' : ℕ}
    (hd : RadDvd d c) (hd' : RadDvd d' c) (hne : d ≠ d') {f : ZMod N → ℂ} (hf : f ∈ layerPart N c χ d)
    (x : ZMod N) (hx : InLayer c d' x.val) : f x = 0 := by
  by_contra hfx
  have hxd : InLayer c d x.val := by
    by_contra hn
    exact hfx (((mem_layerPart N c χ d f).mp hf).2 x hn)
  exact hne (layer_unique hd hd' hxd hx)

/-- **4b. 独立**：W(d)（d ∈ D）は独立（どの W(d) もほかの W(d′) の和と交わりが 0）。 -/
theorem layerPart_iSupIndep (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) :
    iSupIndep (fun d : layerIdx c (N / c) => layerPart N c χ (d : ℕ)) := by
  rw [iSupIndep_def]
  intro d
  have hd : RadDvd (d : ℕ) c := ((mem_layerIdx c (N / c) d).mp d.2).2
  -- ほかの成分の和の元は、d の層の点で 0
  let Z : Submodule ℂ (ZMod N → ℂ) :=
    { carrier := {g | ∀ x : ZMod N, InLayer c d x.val → g x = 0}
      add_mem' := fun ha hb x hx => by rw [Pi.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun r {g} hg x hx => by rw [Pi.smul_apply, hg x hx, smul_zero] }
  have hZ : (⨆ (j : layerIdx c (N / c)) (_ : j ≠ d), layerPart N c χ (j : ℕ)) ≤ Z := by
    refine iSup₂_le (fun j hj => ?_)
    intro g hg x hx
    have hj' : RadDvd (j : ℕ) c := ((mem_layerIdx c (N / c) j).mp j.2).2
    exact layerPart_apply_eq_zero N c χ hj' hd (fun h => hj (Subtype.ext h)) hg x hx
  rw [Submodule.disjoint_def]
  intro f hf1 hf2
  funext x
  show f x = 0
  by_cases hx : InLayer c d x.val
  · exact hZ hf2 x hx
  · exact ((mem_layerPart N c χ d f).mp hf1).2 x hx

/-- **4c. 和はブロック全体**：⨆_{d ∈ D} W(d) = V_{c,χ}。 -/
theorem iSup_layerPart (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    (⨆ d ∈ layerIdx c (N / c), layerPart N c χ d) = blockSpan N c χ := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  apply le_antisymm
  · exact iSup₂_le (fun d _ => fun f hf => ((mem_layerPart N c χ d f).mp hf).1)
  · unfold blockSpan
    rw [Submodule.span_le]
    rintro _ ⟨u, rfl⟩
    have hu : (u : ℕ) ∣ N / c := Nat.dvd_of_mem_divisors u.2
    obtain ⟨d, hd, hud⟩ := exists_layer c u (Nat.pos_of_dvd_of_pos hu hL0).ne'
    have hdL : d ∣ N / c := by
      obtain ⟨e, he, -⟩ := hud
      exact dvd_trans ⟨e, he⟩ hu
    have hdI : d ∈ layerIdx c (N / c) :=
      (mem_layerIdx c (N / c) d).mpr ⟨Nat.mem_divisors.mpr ⟨hdL, hL0.ne'⟩, hd⟩
    exact (le_iSup₂ (f := fun d (_ : d ∈ layerIdx c (N / c)) => layerPart N c χ d) d hdI)
      (kblock_mem_layerPart N c hcN χ hu hud)

/-- **4d. 既約成分への分解（まとめ）**：V_{c,χ} は W(d)（d ∈ D）の独立な和で、各 W(d) は 0 でなく、
殻の射影で閉じていて既約。成分の個数は #D = Π_{p ∣ gcd(c, N/c)} (v_p(N/c) + 1)。 -/
theorem block_decomposition (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    iSupIndep (fun d : layerIdx c (N / c) => layerPart N c χ (d : ℕ)) ∧
      (⨆ d ∈ layerIdx c (N / c), layerPart N c χ d) = blockSpan N c χ ∧
      (∀ d ∈ layerIdx c (N / c), layerPart N c χ d ≠ ⊥ ∧ ShellInvariant (layerPart N c χ d) ∧
        ∀ W : Submodule ℂ (ZMod N → ℂ), ShellInvariant W → W ≤ layerPart N c χ d →
          W = ⊥ ∨ W = layerPart N c χ d) ∧
      (layerIdx c (N / c)).card = ∏ p ∈ (Nat.gcd c (N / c)).primeFactors, ((N / c).factorization p + 1) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  refine ⟨layerPart_iSupIndep N c χ, iSup_layerPart N c hcN χ, fun d hdI => ?_, card_layerIdx c (N / c) hL0.ne'⟩
  obtain ⟨hdD, hd⟩ := (mem_layerIdx c (N / c) d).mp hdI
  have hdL : d ∣ N / c := Nat.dvd_of_mem_divisors hdD
  exact ⟨layerPart_ne_bot N c hcN χ hdL, layerPart_shellInvariant N c hcN χ hχ hd,
    fun W hW hWd => layerPart_irreducible N c hcN χ hχ hdL hd W hW hWd⟩

/-! ### 5. 成分は互いに同型でない（シューア型） -/

/-- **5a.** E_s・D_s とすべて可換な線形写像は、代数 A（PAG218.shellAlg）のすべての元と可換。 -/
theorem commute_shellAlg (N : ℕ) [NeZero N] (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ) (f : ZMod N → ℂ), T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ) (f : ZMod N → ℂ), T (dind N s * f) = dind N s * T f)
    {S : Module.End ℂ (ZMod N → ℂ)} (hS : S ∈ shellAlg N) (f : ZMod N → ℂ) : T (S f) = S (T f) := by
  unfold shellAlg at hS
  induction hS using Algebra.adjoin_induction generalizing f with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact hTE s f
    · exact hTD s f
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [Module.End.mul_apply, Module.End.mul_apply, hx, hy]

/-- **5b. 成分の中の推移性**：d ∈ D、f ∈ W(d) なら S G_d = f となる A の元 S がある。 -/
theorem layerPart_exists_apply (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) {f : ZMod N → ℂ}
    (hf : f ∈ layerPart N c χ d) : ∃ S ∈ shellAlg N, S (gblock N c χ d) = f := by
  let W : Submodule ℂ (ZMod N → ℂ) :=
    (Subalgebra.toSubmodule (shellAlg N)).map (LinearMap.applyₗ (gblock N c χ d))
  have hmem : ∀ h, h ∈ W ↔ ∃ S ∈ shellAlg N, S (gblock N c χ d) = h := by
    intro h
    simp only [W, Submodule.mem_map, Subalgebra.mem_toSubmodule, LinearMap.applyₗ_apply_apply]
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hinvd := (shellInvariant_iff N (layerPart N c χ d)).mp (layerPart_shellInvariant N c hcN χ hχ hd)
  have hWinv : ShellInvariant W := by
    intro s h hh
    obtain ⟨S, hS, rfl⟩ := (hmem h).mp hh
    constructor
    · refine (hmem _).mpr ⟨PAG.Part15.convL (geps N s) * S, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hS
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)
    · refine (hmem _).mpr ⟨LinearMap.mulLeft ℂ (dind N s) * S, ?_, rfl⟩
      refine Subalgebra.mul_mem _ ?_ hS
      unfold shellAlg
      exact Algebra.subset_adjoin (Or.inr ⟨s, rfl⟩)
  have hWd : W ≤ layerPart N c χ d := by
    intro h hh
    obtain ⟨S, hS, rfl⟩ := (hmem h).mp hh
    exact hinvd S hS _ hGd
  have hGW : gblock N c χ d ∈ W := (hmem _).mpr ⟨1, Subalgebra.one_mem _, rfl⟩
  rcases layerPart_irreducible N c hcN χ hχ hdL hd W hWinv hWd with h | h
  · exfalso
    rw [h, Submodule.mem_bot] at hGW
    exact gblock_ne_zero N c hcN χ hdL hGW
  · rw [← h] at hf
    exact (hmem f).mp hf

/-- **5c. 成分は互いに同型でない**：d ≠ d′（d ∈ D、rad(d′) ∣ c）で、E_s・D_s と可換な線形写像 T が
W(d) を W(d′) に写すなら、T は W(d) の上で 0。 -/
theorem layerPart_hom_eq_zero (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d d' : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (hd' : RadDvd d' c) (hne : d ≠ d')
    (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ) (f : ZMod N → ℂ), T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ) (f : ZMod N → ℂ), T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c χ d') :
    ∀ f ∈ layerPart N c χ d, T f = 0 := by
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  have hTG : T (gblock N c χ d) = 0 := by
    have hE : PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d) = gblock N c χ d := by
      rw [geps_conv_gblock N c hcN χ hdL (N / (d * c)), ite_eq_left rfl]
    have hTGd := hT _ hGd
    have hP := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d' _).mp hTGd).1
    have h0 : ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x = 0 := by
      refine Finset.sum_eq_zero (fun x _ => ?_)
      by_cases hgx : gblock N c χ d x = 0
      · rw [hgx, map_zero, zero_mul]
      · have hxd : InLayer c d x.val := by
          by_contra hn
          exact hgx (((mem_layerPart N c χ d _).mp hGd).2 x hn)
        rw [layerPart_apply_eq_zero N c χ hd' hd (Ne.symm hne) hTGd x hxd, mul_zero]
    calc T (gblock N c χ d) = T (PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d)) := by rw [hE]
      _ = PAG.Part15.conv (geps N (N / (d * c))) (T (gblock N c χ d)) := hTE _ _
      _ = PAG.Part15.conv (geps N (N / (d * c))) (blockProj N c χ (T (gblock N c χ d))) := by rw [hP]
      _ = 0 := by rw [geps_conv_blockProj_gblock N c hcN χ hχ hdL _, h0, mul_zero, zero_smul]
  intro f hf
  obtain ⟨S, hS, rfl⟩ := layerPart_exists_apply N c hcN χ hχ hdL hd hf
  rw [commute_shellAlg N T hTE hTD hS, hTG, map_zero]

/-- **5d. 成分の中のシューア型**：d ∈ D で、E_s・D_s と可換な線形写像 T が W(d) を W(d) に写すなら、
T は W(d) の上でスカラー。 -/
theorem layerPart_commute_scalar (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {d : ℕ} (hdL : d ∣ N / c) (hd : RadDvd d c) (T : Module.End ℂ (ZMod N → ℂ))
    (hTE : ∀ (s : ℕ) (f : ZMod N → ℂ), T (PAG.Part15.conv (geps N s) f) = PAG.Part15.conv (geps N s) (T f))
    (hTD : ∀ (s : ℕ) (f : ZMod N → ℂ), T (dind N s * f) = dind N s * T f)
    (hT : ∀ f ∈ layerPart N c χ d, T f ∈ layerPart N c χ d) :
    ∃ μ : ℂ, ∀ f ∈ layerPart N c χ d, T f = μ • f := by
  have hGd : gblock N c χ d ∈ layerPart N c χ d :=
    gblock_mem_layerPart N c hcN χ hχ hdL hd ⟨1, (mul_one d).symm, Nat.coprime_one_left c⟩
  set μ : ℂ := (N : ℂ) / (Nat.totient (d * c) : ℂ) *
    ∑ x, starRingEnd ℂ (gblock N c χ d x) * T (gblock N c χ d) x with hμ
  have hTG : T (gblock N c χ d) = μ • gblock N c χ d := by
    have hE : PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d) = gblock N c χ d := by
      rw [geps_conv_gblock N c hcN χ hdL (N / (d * c)), ite_eq_left rfl]
    have hP := blockProj_of_mem N c hcN χ hχ ((mem_layerPart N c χ d _).mp (hT _ hGd)).1
    calc T (gblock N c χ d) = T (PAG.Part15.conv (geps N (N / (d * c))) (gblock N c χ d)) := by rw [hE]
      _ = PAG.Part15.conv (geps N (N / (d * c))) (T (gblock N c χ d)) := hTE _ _
      _ = PAG.Part15.conv (geps N (N / (d * c))) (blockProj N c χ (T (gblock N c χ d))) := by rw [hP]
      _ = μ • gblock N c χ d := geps_conv_blockProj_gblock N c hcN χ hχ hdL _
  refine ⟨μ, fun f hf => ?_⟩
  obtain ⟨S, hS, rfl⟩ := layerPart_exists_apply N c hcN χ hχ hdL hd hf
  rw [commute_shellAlg N T hTE hTD hS, hTG, map_smul]

end PAG.Part220

#print axioms PAG.Part220.RadDvd
#print axioms PAG.Part220.InLayer
#print axioms PAG.Part220.coprime_of_radDvd
#print axioms PAG.Part220.coprime_of_chi_ne_zero
#print axioms PAG.Part220.layer_unique
#print axioms PAG.Part220.exists_layer
#print axioms PAG.Part220.layerIdx
#print axioms PAG.Part220.mem_layerIdx
#print axioms PAG.Part220.card_layerIdx
#print axioms PAG.Part220.kblock_layer
#print axioms PAG.Part220.gblock_layer
#print axioms PAG.Part220.dft_gblock_support
#print axioms PAG.Part220.dft_gblock_layer
#print axioms PAG.Part220.layer_of_dft_gblock
#print axioms PAG.Part220.gblock_eq_smul_kblock
#print axioms PAG.Part220.inner_kblock_dft_gblock
#print axioms PAG.Part220.inner_gblock_dft_ne_zero
#print axioms PAG.Part220.layerPart
#print axioms PAG.Part220.mem_layerPart
#print axioms PAG.Part220.gblock_mem_layerPart
#print axioms PAG.Part220.kblock_mem_layerPart
#print axioms PAG.Part220.layerPart_shellInvariant
#print axioms PAG.Part220.layerPart_ne_bot
#print axioms PAG.Part220.layerPart_irreducible
#print axioms PAG.Part220.layerPart_apply_eq_zero
#print axioms PAG.Part220.layerPart_iSupIndep
#print axioms PAG.Part220.iSup_layerPart
#print axioms PAG.Part220.block_decomposition
#print axioms PAG.Part220.commute_shellAlg
#print axioms PAG.Part220.layerPart_exists_apply
#print axioms PAG.Part220.layerPart_hom_eq_zero
#print axioms PAG.Part220.layerPart_commute_scalar
