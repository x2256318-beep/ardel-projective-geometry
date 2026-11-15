/-
  PAG 2.0 Part 210（2026-10-25）— ブロックの中の取り替え行列（ディリクレ畳み込みとメビウス反転）と正規化されたケット
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。u, v, w は L の約数
  k_u = |u, χ⟩_N（def kblock）、B_u = kcoef(N/u, c, χ)、G_v = g_{N/(vc), χ̄′}（def gblock。法 vc の基底ベクトル）
  1. 行列のメビウス反転：X_χ(u, v) = [v ∣ u]χ(u/v)（Part 209 の blockX）の逆行列は X_{μχ}(u, v) = [v ∣ u]μ(u/v)χ(u/v)
     （χ は法 c のどの指標でもよい）
  2. ケット → G：k_u = B_u·Σ_{v ∣ u} χ̄(u/v)·G_v（取り替え行列は B·X_χ̄）
     G → ケット：G_v = Σ_{w ∣ v} μ(v/w)·χ̄(v/w)·B_w⁻¹·k_w（取り替え行列は X_{μχ̄}·B⁻¹）
  3. φ(s·c) = s·φ(c) ⇔ s の素因数がすべて c を割る（rad(s) ∣ c）。
     系：‖|u, χ⟩‖ = 1 ⇔ rad(s₀) ∣ c（s₀ = M/c。χ は法 c のどの指標でもよい）。
     Part 201・203 の条件 (R)（rad(u) ∣ c）とは別の条件。
     Part 197 の形 φ(M·t) = φ(M)·t ⇔ t の素因数がすべて M を割る、Part 196 の形 ‖|u, χ⟩‖ = 1 ⇔ M の素因数がすべて c を割る
  4. 逆行列：A_χ⁻¹ = X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ}（成分は Σ_{v ∣ L, u ∣ v, u′ ∣ v} μ(v/u)χ̄(v/u)μ(v/u′)χ(v/u′)/φ(vc)）、
     系としてスミスの行列の逆行列 (gcd(u, u′))⁻¹(u, u′) = Σ_{v ∣ L, u ∣ v, u′ ∣ v} μ(v/u)μ(v/u′)/φ(v)。
     ブロックのグラム行列の逆行列 G⁻¹ = diag(B_u⁻¹)·A_χ⁻¹·diag(N/conj(B_u))（χ 原始的）
-/
import PAG213

namespace PAG.Part214

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

/-- **0a.** w ∣ u ≠ 0 なら Σ_{v ∣ u, w ∣ v} f(v/w) = Σ_{m ∣ u/w} f(m)。 -/
theorem sum_divisors_filter_dvd {R : Type*} [AddCommMonoid R] (u w : ℕ) (hu : u ≠ 0) (hw : w ∣ u)
    (f : ℕ → R) :
    ∑ v ∈ u.divisors.filter (fun v => w ∣ v), f (v / w) = ∑ m ∈ (u / w).divisors, f m := by
  obtain ⟨r, rfl⟩ := hw
  have hw0 : 0 < w := Nat.pos_of_ne_zero (left_ne_zero_of_mul hu)
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hu
  rw [Nat.mul_div_cancel_left r hw0]
  apply Finset.sum_nbij' (fun v => v / w) (fun m => w * m)
  · intro v hv
    simp only [Finset.mem_filter, Nat.mem_divisors] at hv
    obtain ⟨⟨hvu, _⟩, m, rfl⟩ := hv
    simp only [Nat.mem_divisors, Nat.mul_div_cancel_left m hw0]
    exact ⟨Nat.dvd_of_mul_dvd_mul_left hw0 hvu, hr0⟩
  · intro m hm
    simp only [Nat.mem_divisors] at hm
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left w hm.1, hu⟩, dvd_mul_right w m⟩
  · intro v hv
    simp only [Finset.mem_filter] at hv
    exact Nat.mul_div_cancel' hv.2
  · intro m _
    exact Nat.mul_div_cancel_left m hw0
  · intro v _
    rfl

/-- **0b.** w ∣ v ∣ u（v, w > 0）なら (u/v)·(v/w) = u/w。 -/
theorem div_mul_div_of_dvd {u v w : ℕ} (hv : 0 < v) (hw : 0 < w) (hvu : v ∣ u) (hwv : w ∣ v) :
    u / v * (v / w) = u / w := by
  obtain ⟨a, rfl⟩ := hvu
  obtain ⟨b, rfl⟩ := hwv
  rw [Nat.mul_div_cancel_left a hv, Nat.mul_div_cancel_left b hw, mul_assoc, Nat.mul_div_cancel_left _ hw,
    mul_comm]

/-! ### 1. 行列のメビウス反転 -/

/-- X_{μχ}(u, v) = [v ∣ u]·μ(u/v)·χ(u/v)（u, v は L の約数）。 -/
noncomputable def blockXmu (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : Matrix L.divisors L.divisors ℂ :=
  Matrix.of fun u v => if (v : ℕ) ∣ u then
    (ArithmeticFunction.moebius ((u : ℕ) / v) : ℂ) * χ (((u : ℕ) / v : ℕ) : ZMod c) else 0

/-- **1a. メビウス反転**：X_χ·X_{μχ} = 1（L ≠ 0）。 -/
theorem blockX_mul_blockXmu (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    blockX L c χ * blockXmu L c χ = 1 := by
  ext u w
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [blockX, blockXmu, Matrix.of_apply]
  have hu0 : 0 < (u : ℕ) := Nat.pos_of_mem_divisors u.2
  have hw0 : 0 < (w : ℕ) := Nat.pos_of_mem_divisors w.2
  have huL : (u : ℕ) ∣ L := Nat.dvd_of_mem_divisors u.2
  refine (Finset.sum_coe_sort L.divisors (fun v => (if v ∣ (u : ℕ) then χ (((u : ℕ) / v : ℕ) : ZMod c) else 0) *
    (if (w : ℕ) ∣ v then (ArithmeticFunction.moebius (v / (w : ℕ)) : ℂ) * χ ((v / (w : ℕ) : ℕ) : ZMod c)
      else 0))).trans ?_
  -- 各項：[v ∣ u, w ∣ v]·χ(u/w)·μ(v/w)
  have hterm : ∀ v ∈ L.divisors,
      (if v ∣ (u : ℕ) then χ (((u : ℕ) / v : ℕ) : ZMod c) else 0) *
        (if (w : ℕ) ∣ v then (ArithmeticFunction.moebius (v / (w : ℕ)) : ℂ) * χ ((v / (w : ℕ) : ℕ) : ZMod c)
          else 0) =
      if v ∣ (u : ℕ) ∧ (w : ℕ) ∣ v then
        χ (((u : ℕ) / w : ℕ) : ZMod c) * (ArithmeticFunction.moebius (v / (w : ℕ)) : ℂ) else 0 := by
    intro v hv
    have hv0 : 0 < v := Nat.pos_of_mem_divisors hv
    by_cases h1 : v ∣ (u : ℕ)
    · by_cases h2 : (w : ℕ) ∣ v
      · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (And.intro h1 h2),
          ← div_mul_div_of_dvd hv0 hw0 h1 h2, Nat.cast_mul, map_mul]
        ring
      · rw [ite_eq_right h2, ite_eq_right (show ¬(v ∣ (u : ℕ) ∧ (w : ℕ) ∣ v) from fun hh => h2 hh.2), mul_zero]
    · rw [ite_eq_right h1, ite_eq_right (show ¬(v ∣ (u : ℕ) ∧ (w : ℕ) ∣ v) from fun hh => h1 hh.1), zero_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfilt : L.divisors.filter (fun v => v ∣ (u : ℕ) ∧ (w : ℕ) ∣ v) =
      (u : ℕ).divisors.filter (fun v => (w : ℕ) ∣ v) := by
    ext v
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hvu, hwv⟩
      exact ⟨⟨hvu, hu0.ne'⟩, hwv⟩
    · rintro ⟨⟨hvu, _⟩, hwv⟩
      exact ⟨⟨dvd_trans hvu huL, hL⟩, hvu, hwv⟩
  rw [hfilt, ← Finset.mul_sum]
  by_cases hwu : (w : ℕ) ∣ u
  · rw [sum_divisors_filter_dvd (u : ℕ) w hu0.ne' hwu (fun m => (ArithmeticFunction.moebius m : ℂ)),
      sum_moebius_divisors]
    by_cases hr : (u : ℕ) / w = 1
    · have huw : u = w := by
        apply Subtype.ext
        rw [← Nat.div_mul_cancel hwu, hr, one_mul]
      rw [ite_eq_left hr, ite_eq_left huw, hr, Nat.cast_one, map_one, mul_one]
    · have huw : u ≠ w := by
        intro e
        apply hr
        rw [e, Nat.div_self hw0]
      rw [ite_eq_right hr, ite_eq_right huw, mul_zero]
  · have hempty : (u : ℕ).divisors.filter (fun v => (w : ℕ) ∣ v) = ∅ := by
      ext v
      simp only [Finset.mem_filter, Nat.mem_divisors, Finset.notMem_empty, iff_false, not_and]
      intro ⟨hvu, _⟩ hwv
      exact hwu (dvd_trans hwv hvu)
    have huw : u ≠ w := by
      intro e
      exact hwu (by rw [e])
    rw [hempty, Finset.sum_empty, mul_zero, ite_eq_right huw]

/-- **1b.** X_{μχ}·X_χ = 1。 -/
theorem blockXmu_mul_blockX (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    blockXmu L c χ * blockX L c χ = 1 :=
  mul_eq_one_comm.mp (blockX_mul_blockXmu L c hL χ)

/-- **1c.** X_χ⁻¹ = X_{μχ}。 -/
theorem blockX_inv (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    (blockX L c χ)⁻¹ = blockXmu L c χ :=
  Matrix.inv_eq_right_inv (blockX_mul_blockXmu L c hL χ)

/-! ### 2. ケットと基底ベクトル G_v の取り替え -/

/-- ブロック (c, χ) のケット：w ∣ N かつ c ∣ N/w なら |w, χ⟩_N、そうでなければ 0。 -/
noncomputable def kblock (N c : ℕ) [NeZero N] (χ : ZMod c → ℂ) (w : ℕ) : ZMod N → ℂ :=
  if h : w ∣ N ∧ c ∣ N / w then gket w (N / w) N (Nat.mul_div_cancel' h.1) c h.2 χ else 0

/-- ブロック (c, χ) の基底ベクトル G_v = g_{N/(vc), χ̄′}（法 vc。χ̄′ は χ⁻¹ を法 vc へ持ち上げたもの）。 -/
noncomputable def gblock (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (v : ℕ) : ZMod N → ℂ :=
  gbas (N / (v * c)) (v * c) N (liftc χ⁻¹ (v * c))

/-- **2a.** w ∣ N、c ∣ N/w なら kblock はケット |w, χ⟩_N。 -/
theorem kblock_of_dvd (N c : ℕ) [NeZero N] (χ : ZMod c → ℂ) {w : ℕ} (hw : w ∣ N) (hc : c ∣ N / w) :
    kblock N c χ w = gket w (N / w) N (Nat.mul_div_cancel' hw) c hc χ := by
  unfold kblock
  exact dite_eq_left ⟨hw, hc⟩

/-- **2b. ケット → G**：u ∣ N/c なら k_u = B_u·Σ_{v ∣ u} χ̄(u/v)·G_v。 -/
theorem kblock_eq_sum (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (u : ℕ) (hu : u ∣ N / c) :
    kblock N c χ u = kcoef (N / u) c χ • ∑ v ∈ u.divisors, χ⁻¹ ((u / v : ℕ) : ZMod c) • gblock N c χ v := by
  obtain ⟨huN, hcu⟩ := block_dvd hcN hu
  have hN0 : N ≠ 0 := NeZero.ne N
  have hu0 : u ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at huN; exact hN0 huN
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hNu : u * (N / u) = N := Nat.mul_div_cancel' huN
  have hNuc : N / u / c * c = N / u := Nat.div_mul_cancel hcu
  rw [kblock_of_dvd N c χ huN hcu, gket_eq_sum_gbas u (N / u) N hNu c hcu χ hχ, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_filter, ← Nat.sum_div_divisors u]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have hv' : v ∣ u := Nat.dvd_of_mem_divisors hv
  have hv0 : 0 < v := Nat.pos_of_mem_divisors hv
  have huv : u / (u / v) = v := Nat.div_div_self hv' hu0
  have hshell : N / u / c * (u / v) = N / (v * c) := by
    symm
    apply Nat.div_eq_of_eq_mul_left (Nat.mul_pos hv0 hc0)
    calc N = u * (N / u / c * c) := by rw [hNuc, hNu]
      _ = N / u / c * (u / v) * (v * c) := by
        rw [show N / u / c * (u / v) * (v * c) = N / u / c * c * (u / v * v) by ring, Nat.div_mul_cancel hv']
        ring
  by_cases hcop : (u / v).Coprime c
  · rw [ite_eq_left hcop, hshell,
      gbas_congr (N / (v * c)) N (show u / (u / v) * c = v * c by rw [huv]) (dvd_mul_left c (u / (u / v)))
        (dvd_mul_left c v) χ⁻¹, smul_smul]
    unfold gblock
    rw [liftc_of_dvd χ⁻¹ (dvd_mul_left c v)]
  · have h0 : χ⁻¹ ((u / v : ℕ) : ZMod c) = 0 :=
      MulChar.map_nonunit _ (fun hh => hcop ((ZMod.isUnit_iff_coprime _ _).mp hh))
    rw [ite_eq_right hcop, h0, zero_smul, smul_zero]

/-- **2c. G → ケット**：v ∣ N/c なら G_v = Σ_{w ∣ v} μ(v/w)·χ̄(v/w)·B_w⁻¹·k_w。 -/
theorem gblock_eq_sum (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (v : ℕ) (hv : v ∣ N / c) :
    gblock N c χ v = ∑ w ∈ v.divisors,
      ((ArithmeticFunction.moebius (v / w) : ℂ) * χ⁻¹ ((v / w : ℕ) : ZMod c) * (kcoef (N / w) c χ)⁻¹) •
        kblock N c χ w := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hvc : v * c ∣ N := by
    have := (Nat.dvd_div_iff_mul_dvd hcN).mp hv
    rwa [mul_comm] at this
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hvc
    exact hN0 hvc
  have hsn : N / (v * c) * (v * c) = N := Nat.div_mul_cancel hvc
  have hs0 : 0 < N / (v * c) := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hsn; exact hN0 hsn.symm)
  unfold gblock
  rw [liftc_of_dvd χ⁻¹ (dvd_mul_left c v),
    gbas_eq_sum_rk (N / (v * c)) (v * c) N hsn c (dvd_mul_left c v) χ⁻¹ (PAG.Part16.isPrimitive_inv hχ), inv_inv]
  -- 和の範囲：(vc の約数で c と互いに素) = (v の約数で c と互いに素)
  have hfilt : (v * c).divisors.filter (fun e => e.Coprime c) = v.divisors.filter (fun e => e.Coprime c) := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨he, _⟩, hec⟩
      exact ⟨⟨Nat.Coprime.dvd_of_dvd_mul_right hec he, hv0⟩, hec⟩
    · rintro ⟨⟨he, _⟩, hec⟩
      exact ⟨⟨dvd_mul_of_dvd_left he c, Nat.mul_ne_zero hv0 hc0.ne'⟩, hec⟩
  rw [hfilt, Finset.sum_filter, ← Nat.sum_div_divisors v]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  have hw' : w ∣ v := Nat.dvd_of_mem_divisors hw
  have hw0 : 0 < w := Nat.pos_of_mem_divisors hw
  have hwL : w ∣ N / c := dvd_trans hw' hv
  obtain ⟨hwN, hcw⟩ := block_dvd hcN hwL
  have hNw0 : N / w ≠ 0 := by
    intro h0
    have := Nat.mul_div_cancel' hwN
    rw [h0, mul_zero] at this
    exact hN0 this.symm
  -- s·(v/w)·c = N/w、N/(s·(v/w)·c) = w
  have hsec : N / (v * c) * (v / w) * c = N / w := by
    symm
    apply Nat.div_eq_of_eq_mul_left hw0
    calc N = N / (v * c) * (v * c) := hsn.symm
      _ = N / (v * c) * (v / w) * c * w := by
        rw [show N / (v * c) * (v / w) * c * w = N / (v * c) * (v / w * w) * c by ring, Nat.div_mul_cancel hw']
        ring
  have hNsec : N / (N / w) = w := Nat.div_div_self hwN hN0
  by_cases hcop : (v / w).Coprime c
  · rw [ite_eq_left hcop, hsec, hNsec, rk_eq_gket w (N / w) N (Nat.mul_div_cancel' hwN) c hcw χ,
      kblock_of_dvd N c χ hwN hcw, smul_smul, kcoef_inv (N / w) c hNw0 hcw χ hχ]
    congr 1
    have hNwC : ((N / w : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hNw0
    field_simp
  · have h0 : χ⁻¹ ((v / w : ℕ) : ZMod c) = 0 :=
      MulChar.map_nonunit _ (fun hh => hcop ((ZMod.isUnit_iff_coprime _ _).mp hh))
    rw [ite_eq_right hcop, h0, mul_zero, zero_mul, zero_smul]

/-! ### 3. 正規化されたケットの判定 -/

/-- **3a.** 法 s·c の元で、法 c に落とすと単数になるものの個数は s·φ(c)。 -/
theorem card_isUnit_castHom (s c : ℕ) [NeZero s] [NeZero c] :
    ((Finset.univ.filter (fun x : ZMod (s * c) =>
        IsUnit (ZMod.castHom (dvd_mul_left c s) (ZMod c) x))).card : ℂ) = (s : ℂ) * Nat.totient c := by
  have hc : c ≠ 0 := NeZero.ne c
  have hcs : c ∣ s * c := dvd_mul_left c s
  have e := PAG.Part17.sum_comp_surj (ZMod.castHom hcs (ZMod c)).toAddMonoidHom (ZMod.ringHom_surjective _)
    (fun z => (1 : DirichletCharacter ℂ c) z)
  have hk := PAG.Part201.card_ker_cast (N := c) (N' := s * c) hcs
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hks : ((Finset.univ.filter (fun z : ZMod (s * c) =>
      (ZMod.castHom hcs (ZMod c)).toAddMonoidHom z = 0)).card : ℂ) = (s : ℂ) := by
    apply mul_right_cancel₀ hc0
    rw [hk]
    push_cast
    ring
  rw [Finset.natCast_card_filter]
  calc ∑ x : ZMod (s * c), (if IsUnit (ZMod.castHom hcs (ZMod c) x) then (1 : ℂ) else 0)
      = ∑ x : ZMod (s * c), (fun z => (1 : DirichletCharacter ℂ c) z) ((ZMod.castHom hcs (ZMod c)).toAddMonoidHom x) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        show (if IsUnit (ZMod.castHom hcs (ZMod c) x) then (1 : ℂ) else 0) =
          (1 : DirichletCharacter ℂ c) (ZMod.castHom hcs (ZMod c) x)
        by_cases hx : IsUnit (ZMod.castHom hcs (ZMod c) x)
        · rw [ite_eq_left hx, MulChar.one_apply hx]
        · rw [ite_eq_right hx, MulChar.map_nonunit _ hx]
    _ = _ := e
    _ = (s : ℂ) * Nat.totient c := by
        rw [hks, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

/-- **3b.** 法 n の単数の個数は φ(n)。 -/
theorem card_isUnit (n : ℕ) [NeZero n] :
    ((Finset.univ.filter (fun x : ZMod n => IsUnit x)).card : ℂ) = Nat.totient n := by
  rw [Finset.natCast_card_filter]
  calc ∑ x : ZMod n, (if IsUnit x then (1 : ℂ) else 0) = ∑ x : ZMod n, (1 : DirichletCharacter ℂ n) x := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : IsUnit x
        · rw [ite_eq_left hx, MulChar.one_apply hx]
        · rw [ite_eq_right hx, MulChar.map_nonunit _ hx]
    _ = Nat.totient n := by rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]

/-- **3c. φ の判定**：s, c ≠ 0 なら φ(s·c) = s·φ(c) ⇔ s の素因数はすべて c を割る。 -/
theorem totient_mul_eq_iff (s c : ℕ) (hs : s ≠ 0) (hc : c ≠ 0) :
    Nat.totient (s * c) = s * Nat.totient c ↔ ∀ p : ℕ, p.Prime → p ∣ s → p ∣ c := by
  have : NeZero s := ⟨hs⟩
  have : NeZero c := ⟨hc⟩
  have hcs : c ∣ s * c := dvd_mul_left c s
  -- U = 単数、V = 法 c に落とすと単数
  have hUV : Finset.univ.filter (fun x : ZMod (s * c) => IsUnit x) ⊆
      Finset.univ.filter (fun x : ZMod (s * c) => IsUnit (ZMod.castHom hcs (ZMod c) x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.map _
  have hU := card_isUnit (s * c)
  have hV := card_isUnit_castHom s c
  constructor
  · intro heq p hp hps
    by_contra hpc
    -- x = p は V に入るが U に入らない
    have hxV : (p : ZMod (s * c)) ∈ Finset.univ.filter (fun x : ZMod (s * c) =>
        IsUnit (ZMod.castHom hcs (ZMod c) x)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_natCast]
      exact (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpc
    have hxU : (p : ZMod (s * c)) ∉ Finset.univ.filter (fun x : ZMod (s * c) => IsUnit x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ZMod.isUnit_prime_iff_not_dvd hp, not_not]
      exact dvd_mul_of_dvd_left hps c
    have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hUV).mpr ⟨_, hxV, hxU⟩)
    have hU' : (Finset.univ.filter (fun x : ZMod (s * c) => IsUnit x)).card = Nat.totient (s * c) := by
      exact_mod_cast hU
    have hV' : (Finset.univ.filter (fun x : ZMod (s * c) =>
        IsUnit (ZMod.castHom hcs (ZMod c) x))).card = s * Nat.totient c := by
      exact_mod_cast hV
    rw [hU', hV', heq] at hlt
    exact lt_irrefl _ hlt
  · intro hR
    have hVU : Finset.univ.filter (fun x : ZMod (s * c) => IsUnit (ZMod.castHom hcs (ZMod c) x)) ⊆
        Finset.univ.filter (fun x : ZMod (s * c) => IsUnit x) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.isUnit_iff_coprime] at hx
      rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
      refine Nat.coprime_of_dvd (fun k hk hkx hksc => ?_)
      rcases (Nat.Prime.dvd_mul hk).mp hksc with hks | hkc
      · exact Nat.Prime.one_lt hk |>.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hkx hx) (hR k hk hks))
      · exact Nat.Prime.one_lt hk |>.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hkx hx) hkc)
    have heq := Finset.Subset.antisymm hUV hVU
    have : ((Nat.totient (s * c) : ℕ) : ℂ) = ((s * Nat.totient c : ℕ) : ℂ) := by
      rw [← hU, heq, hV]
      push_cast
      ring
    exact_mod_cast this

/-- **3d. 正規化されたケット**：‖|u, χ⟩‖ = 1 ⇔ s₀ = M/c の素因数はすべて c を割る（χ は法 c のどの指標でもよい）。 -/
theorem normSq_gket_eq_one_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x) = 1 ↔ ∀ p : ℕ, p.Prime → p ∣ M / c → p ∣ c := by
  have hMZ := neZero_of_mul h
  have hM0 : M ≠ 0 := NeZero.ne M
  have hc0 : c ≠ 0 := NeZero.ne c
  have hs0 : M / c ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hc) (Nat.pos_of_ne_zero hc0)).ne'
  have hφ : (Nat.totient M : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hM0)).ne'
  rw [normSq_gket_eq u M N h c hc χ, div_eq_one_iff_eq hφ, ← totient_mul_eq_iff (M / c) c hs0 hc0,
    Nat.div_mul_cancel hc, eq_comm]
  constructor
  · intro e
    exact_mod_cast e
  · intro e
    exact_mod_cast e

/-- **3e.** Part 197 の形：M, t ≠ 0 なら φ(M·t) = φ(M)·t ⇔ t の素因数はすべて M を割る
（「⇐」は Part 197 の `totient_mul_of_primes`）。 -/
theorem totient_mul_eq_iff' (M t : ℕ) (hM : M ≠ 0) (ht : t ≠ 0) :
    Nat.totient (M * t) = Nat.totient M * t ↔ ∀ q : ℕ, q.Prime → q ∣ t → q ∣ M := by
  rw [mul_comm M t, mul_comm (Nat.totient M) t]
  exact totient_mul_eq_iff t M ht hM

/-- **3f.** Part 196 の形：‖|u, χ⟩‖ = 1 ⇔ M の素因数はすべて c を割る（「⇐」は Part 196 の `norm_gket`）。 -/
theorem normSq_gket_eq_one_iff' (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) [NeZero c] (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) :
    ∑ x, Complex.normSq (gket u M N h c hc χ x) = 1 ↔ ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c := by
  rw [normSq_gket_eq_one_iff u M N h c hc χ]
  constructor
  · intro H q hq hqM
    rw [← Nat.div_mul_cancel hc] at hqM
    rcases (Nat.Prime.dvd_mul hq).mp hqM with h1 | h1
    · exact H q hq h1
    · exact h1
  · intro H q hq hqs
    exact H q hq (dvd_trans hqs (Nat.div_dvd_of_dvd hc))

/-! ### 4. 逆行列：A_χ⁻¹、スミスの行列の逆行列、ブロックのグラム行列の逆行列 -/

/-- X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ}（A_χ の逆行列になる）。 -/
noncomputable def blockAinv (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) : Matrix L.divisors L.divisors ℂ :=
  (blockXmu L c χ).conjTranspose *
    Matrix.diagonal (fun v : L.divisors => ((Nat.totient ((v : ℕ) * c) : ℂ))⁻¹) * blockXmu L c χ

/-- **4a.** A_χ·(X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ}) = 1（L ≠ 0。χ は法 c のどの指標でもよい）。 -/
theorem blockA_mul_blockAinv (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    blockA L c χ * blockAinv L c χ = 1 := by
  have hΦ : ∀ R : Matrix L.divisors L.divisors ℂ,
      Matrix.diagonal (fun v : L.divisors => (Nat.totient ((v : ℕ) * c) : ℂ)) *
        (Matrix.diagonal (fun v : L.divisors => ((Nat.totient ((v : ℕ) * c) : ℂ))⁻¹) * R) = R := by
    intro R
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have e : (fun v : L.divisors => (Nat.totient ((v : ℕ) * c) : ℂ) * ((Nat.totient ((v : ℕ) * c) : ℂ))⁻¹) =
        fun _ => 1 := by
      funext v
      have hv : (Nat.totient ((v : ℕ) * c) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos (Nat.pos_of_mem_divisors v.2)
          (Nat.pos_of_ne_zero (NeZero.ne c)))).ne'
      exact mul_inv_cancel₀ hv
    rw [e, Matrix.diagonal_one, Matrix.one_mul]
  have hX : ∀ R : Matrix L.divisors L.divisors ℂ,
      (blockX L c χ).conjTranspose * ((blockXmu L c χ).conjTranspose * R) = R := by
    intro R
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, blockXmu_mul_blockX L c hL χ, Matrix.conjTranspose_one,
      Matrix.one_mul]
  rw [blockA_eq L c hL χ, blockAinv]
  simp only [Matrix.mul_assoc]
  rw [hX, hΦ, blockX_mul_blockXmu L c hL χ]

/-- **4b.** A_χ⁻¹ = X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ}。 -/
theorem blockA_inv (L c : ℕ) [NeZero c] (hL : L ≠ 0) (χ : DirichletCharacter ℂ c) :
    (blockA L c χ)⁻¹ = blockAinv L c χ :=
  Matrix.inv_eq_right_inv (blockA_mul_blockAinv L c hL χ)

/-- **4c.** 成分：(X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ})(u, u′) = Σ_{v ∣ L, u ∣ v, u′ ∣ v} μ(v/u)χ̄(v/u)·μ(v/u′)χ(v/u′)/φ(vc)。 -/
theorem blockAinv_apply (L c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) (u u' : L.divisors) :
    blockAinv L c χ u u' = ∑ v ∈ L.divisors.filter (fun v => (u : ℕ) ∣ v ∧ (u' : ℕ) ∣ v),
      (ArithmeticFunction.moebius (v / u) : ℂ) * χ⁻¹ ((v / u : ℕ) : ZMod c) *
        ((ArithmeticFunction.moebius (v / u') : ℂ) * χ ((v / u' : ℕ) : ZMod c)) / (Nat.totient (v * c) : ℂ) := by
  rw [blockAinv, Matrix.mul_apply, Finset.sum_filter, ← Finset.sum_coe_sort L.divisors]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, blockXmu, Matrix.of_apply]
  by_cases h1 : (u : ℕ) ∣ v
  · by_cases h2 : (u' : ℕ) ∣ v
    · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (show (u : ℕ) ∣ v ∧ (u' : ℕ) ∣ v from ⟨h1, h2⟩),
        star_mul', star_intCast, MulChar.star_apply', div_eq_mul_inv]
      ring
    · rw [ite_eq_right h2, ite_eq_right (show ¬((u : ℕ) ∣ v ∧ (u' : ℕ) ∣ v) from fun hh => h2 hh.2), mul_zero]
  · rw [ite_eq_right h1, ite_eq_right (show ¬((u : ℕ) ∣ v ∧ (u' : ℕ) ∣ v) from fun hh => h1 hh.1), star_zero,
      zero_mul, zero_mul]

/-- **4d. スミスの行列の逆行列**（c = 1）：(gcd(u, u′))⁻¹(u, u′) = Σ_{v ∣ L, u ∣ v, u′ ∣ v} μ(v/u)μ(v/u′)/φ(v)。 -/
theorem smith_inv (L : ℕ) (hL : L ≠ 0) :
    (Matrix.of fun u u' : L.divisors => (Nat.gcd (u : ℕ) u' : ℂ))⁻¹ =
      Matrix.of fun u u' : L.divisors => ∑ v ∈ L.divisors.filter (fun v => (u : ℕ) ∣ v ∧ (u' : ℕ) ∣ v),
        (ArithmeticFunction.moebius (v / u) : ℂ) * ArithmeticFunction.moebius (v / u') / (Nat.totient v : ℂ) := by
  have e : (Matrix.of fun u u' : L.divisors => (Nat.gcd (u : ℕ) u' : ℂ)) =
      blockA L 1 (1 : DirichletCharacter ℂ 1) := by
    ext u u'
    simp only [blockA, Matrix.of_apply, chi_level_one, one_mul, mul_one]
    exact_mod_cast (Nat.sum_totient (Nat.gcd (u : ℕ) u')).symm
  rw [e, blockA_inv L 1 hL 1]
  ext u u'
  rw [blockAinv_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [chi_level_one, mul_one]

/-- ブロック (c, χ) のグラム行列の逆行列：H = diag(B_u⁻¹)·A_χ⁻¹·diag(N/conj(B_u))（B_u = kcoef(N/u, c, χ)）。 -/
noncomputable def blockGramInv (N c : ℕ) [NeZero c] (χ : DirichletCharacter ℂ c) :
    Matrix (N / c).divisors (N / c).divisors ℂ :=
  Matrix.diagonal (fun u : (N / c).divisors => (kcoef (N / u) c χ)⁻¹) * blockAinv (N / c) c χ *
    Matrix.diagonal (fun u : (N / c).divisors => (N : ℂ) / starRingEnd ℂ (kcoef (N / u) c χ))

/-- **4e.** G·H = 1（χ 原始的）。 -/
theorem blockGram_mul_blockGramInv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : blockGram N c hcN χ * blockGramInv N c χ = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hL : N / c ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hN0 hcN) (Nat.pos_of_ne_zero (NeZero.ne c))).ne'
  have hB : ∀ u : (N / c).divisors, kcoef (N / u) c χ ≠ 0 := fun u => by
    obtain ⟨h1, h2⟩ := block_dvd hcN (Nat.dvd_of_mem_divisors u.2)
    exact kcoef_ne_zero (N / u) c (Nat.div_pos (Nat.le_of_dvd hN0 h1) (Nat.pos_of_mem_divisors u.2)).ne' h2 χ hχ
  have hD2 : ∀ R : Matrix (N / c).divisors (N / c).divisors ℂ,
      Matrix.diagonal (fun u : (N / c).divisors => kcoef (N / u) c χ) *
        (Matrix.diagonal (fun u : (N / c).divisors => (kcoef (N / u) c χ)⁻¹) * R) = R := by
    intro R
    rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    have e : (fun u : (N / c).divisors => kcoef (N / u) c χ * (kcoef (N / u) c χ)⁻¹) = fun _ => 1 :=
      funext fun u => mul_inv_cancel₀ (hB u)
    rw [e, Matrix.diagonal_one, Matrix.one_mul]
  have hA : ∀ R : Matrix (N / c).divisors (N / c).divisors ℂ,
      blockA (N / c) c χ * (blockAinv (N / c) c χ * R) = R := by
    intro R
    rw [← Matrix.mul_assoc, blockA_mul_blockAinv (N / c) c hL χ, Matrix.one_mul]
  rw [blockGram_eq N c hcN χ hχ, blockGramInv]
  simp only [Matrix.mul_assoc]
  rw [hD2, hA, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext u
  have h1 : starRingEnd ℂ (kcoef (N / u) c χ) ≠ 0 := (map_ne_zero _).mpr (hB u)
  have h2 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [div_mul_div_comm, mul_comm (starRingEnd ℂ (kcoef (N / u) c χ)) (N : ℂ), div_self (mul_ne_zero h2 h1)]

/-- **4f. ブロックのグラム行列の逆行列**：G⁻¹ = diag(B_u⁻¹)·X_{μχ}*·diag(φ(vc)⁻¹)·X_{μχ}·diag(N/conj(B_u))（χ 原始的）。 -/
theorem blockGram_inv (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) : (blockGram N c hcN χ)⁻¹ = blockGramInv N c χ :=
  Matrix.inv_eq_right_inv (blockGram_mul_blockGramInv N c hcN χ hχ)

end PAG.Part214

#print axioms PAG.Part214.sum_divisors_filter_dvd
#print axioms PAG.Part214.div_mul_div_of_dvd
#print axioms PAG.Part214.blockXmu
#print axioms PAG.Part214.blockX_mul_blockXmu
#print axioms PAG.Part214.blockXmu_mul_blockX
#print axioms PAG.Part214.blockX_inv
#print axioms PAG.Part214.kblock
#print axioms PAG.Part214.gblock
#print axioms PAG.Part214.kblock_of_dvd
#print axioms PAG.Part214.kblock_eq_sum
#print axioms PAG.Part214.gblock_eq_sum
#print axioms PAG.Part214.card_isUnit_castHom
#print axioms PAG.Part214.card_isUnit
#print axioms PAG.Part214.totient_mul_eq_iff
#print axioms PAG.Part214.normSq_gket_eq_one_iff
#print axioms PAG.Part214.totient_mul_eq_iff'
#print axioms PAG.Part214.normSq_gket_eq_one_iff'
#print axioms PAG.Part214.blockAinv
#print axioms PAG.Part214.blockA_mul_blockAinv
#print axioms PAG.Part214.blockA_inv
#print axioms PAG.Part214.blockAinv_apply
#print axioms PAG.Part214.smith_inv
#print axioms PAG.Part214.blockGramInv
#print axioms PAG.Part214.blockGram_mul_blockGramInv
#print axioms PAG.Part214.blockGram_inv
