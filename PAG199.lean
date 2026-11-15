/-
  PAG 2.0 Part 195（2026-10-23）— ℤ/N のケットと、定理 A の乗法性
  u·M = N、c ∣ M、χ は法 c の指標（または関数）として、ℤ/N のケットを
      |u, χ⟩_N (x) = φ(M)^(−1/2)·[x = u y]·χ(y mod c)（y ∈ ℤ/M、y ↦ u y は単射）
  と直接定義する（`gket`）。X₁′X₂′ は法 c₁c₂ に持ち上げた積の指標（`cmul`）。
  1. memb：殻の埋め込み ZMod M → ZMod N、y ↦ u y（`memb_val`, `memb_injective`, `exists_memb_iff`）。
     gket_apply：|u, χ⟩_N (x) = [u ∣ x] φ(M)^(−1/2) χ(x/u)。gket_eq_ket：N = p^K では Part 17 のケットと一致
  2. gket_crt：N = N₁N₂（互いに素）、u = u₁u₂、M = M₁M₂、c = c₁c₂ で
     X₁(u₂)X₂(u₁)·|u, X₁′X₂′⟩_N (x) = |u₁, X₁⟩(x mod N₁)·|u₂, X₂⟩(x mod N₂)
  3. gauss_ratio_mul：A_iB_i = Ψ_i∘π（法 c_i → d_i）なら
     τ(A)τ(B)/τ(Ψ) = Ψ₁(c₂/d₂)Ψ₂(c₁/d₁)·Π_i τ(A_i)τ(B_i)/τ(Ψ_i)（原始性は要らない）
  4. thmA_mul_aux：各因子で |u_i, A_i⟩ ⋆ |u_i, B_i⟩ = l_i |u_i′, Ψ_i⟩ なら
     |u, A⟩ ⋆ |u, B⟩ = Ψ₁(c₂/d₂)Ψ₂(c₁/d₁) l₁ l₂ |u′, Ψ⟩（ずれの係数 X(u_j) は打ち消し合う）
  5. ℤ/N の定理 A（`ThmA`、定数 `thmAConst` = √(N/φ(uc))·τ(A)τ(B)/(τ(Ψ)√(c·c/d))）：
     素数冪では Part 21 の定理 A（`thmA_prime_power`）、互いに素な積で閉じる（`thmA_mul`）。
     系：N = p^K q^L で |u, A⟩ ⋆ |u, B⟩ = C·|u·c/d, Ψ⟩（`thmA_two_prime`、定数は大域のガウス和）
  6. normSq_gket_crt：ノルムも積に分かれる。系：N = p^K q^L の原始的な積のケットは単位ベクトル
-/
import PAG198

namespace PAG.Part199

open Complex Finset
open ZMod (stdAddChar)

/-! ### 1. 殻の埋め込みと ℤ/N のケット -/

/-- 殻の埋め込み ι_u : ZMod M → ZMod N、y ↦ u y（u M = N）。 -/
noncomputable def memb (u M N : ℕ) (h : u * M = N) : ZMod M →+ ZMod N :=
  ZMod.lift M ⟨(u : ZMod N) • (Int.castAddHom (ZMod N)), by
    simp only [AddMonoidHom.smul_apply, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Int.cast_natCast, smul_eq_mul]
    rw [← Nat.cast_mul, h, ZMod.natCast_self]⟩

theorem neZero_of_mul {u M N : ℕ} [NeZero N] (h : u * M = N) : NeZero M :=
  ⟨fun hM => NeZero.ne N (by rw [← h, hM, mul_zero])⟩

theorem pos_of_mul {u M N : ℕ} [NeZero N] (h : u * M = N) : 0 < u :=
  Nat.pos_of_ne_zero (fun hu => NeZero.ne N (by rw [← h, hu, zero_mul]))

theorem memb_apply (u M N : ℕ) [NeZero N] (h : u * M = N) (y : ZMod M) :
    memb u M N h y = ((u * y.val : ℕ) : ZMod N) := by
  have := neZero_of_mul h
  conv_lhs => rw [← ZMod.natCast_zmod_val y, ← Int.cast_natCast]
  rw [memb, ZMod.lift_coe]
  simp [Int.castAddHom]

/-- (u y).val = u · y.val（u y < u M = N）。 -/
theorem memb_val (u M N : ℕ) [NeZero N] (h : u * M = N) (y : ZMod M) :
    (memb u M N h y).val = u * y.val := by
  have := neZero_of_mul h
  have hy := ZMod.val_lt y
  have hu := pos_of_mul h
  rw [memb_apply, ZMod.val_natCast_of_lt]
  calc u * y.val < u * M := Nat.mul_lt_mul_of_pos_left hy hu
    _ = N := h

theorem memb_injective (u M N : ℕ) [NeZero N] (h : u * M = N) : Function.Injective (memb u M N h) := by
  have := neZero_of_mul h
  intro y₁ y₂ hy
  have e := congrArg ZMod.val hy
  rw [memb_val, memb_val] at e
  exact ZMod.val_injective M (Nat.eq_of_mul_eq_mul_left (pos_of_mul h) e)

/-- 像の判定：x = u y となる y がある ⇔ u ∣ x.val。 -/
theorem exists_memb_iff (u M N : ℕ) [NeZero N] (h : u * M = N) (x : ZMod N) :
    (∃ y, memb u M N h y = x) ↔ u ∣ x.val := by
  have := neZero_of_mul h
  constructor
  · rintro ⟨y, rfl⟩
    rw [memb_val]
    exact Dvd.intro _ rfl
  · rintro ⟨k, hk⟩
    have hkM : k < M := by
      have hx := ZMod.val_lt x
      rw [hk, ← h] at hx
      exact Nat.lt_of_mul_lt_mul_left hx
    refine ⟨(k : ZMod M), ?_⟩
    apply ZMod.val_injective N
    rw [memb_val, ZMod.val_natCast_of_lt hkM, hk]

/-- **ℤ/N のケット** |u, χ⟩_N = φ(M)^(−1/2)·ι_{u,*}(χ ∘ π)（u M = N、c ∣ M、π : ZMod M → ZMod c）。 -/
noncomputable def gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M) (χ : ZMod c → ℂ) :
    ZMod N → ℂ :=
  have : NeZero M := neZero_of_mul h
  (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) •
    PAG.Part17.push (memb u M N h) (χ ∘ (ZMod.castHom hc (ZMod c)).toAddMonoidHom)

theorem gket_memb (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M) (χ : ZMod c → ℂ)
    (y : ZMod M) :
    gket u M N h c hc χ (memb u M N h y)
      = (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * χ (ZMod.castHom hc (ZMod c) y) := by
  have := neZero_of_mul h
  simp only [gket, Pi.smul_apply, smul_eq_mul, PAG.Part17.push, (memb_injective u M N h).extend_apply]
  rfl

/-- **値の公式**：|u, χ⟩_N (x) = [u ∣ x] φ(M)^(−1/2)·χ(x/u)。 -/
theorem gket_apply (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M) (χ : ZMod c → ℂ)
    (x : ZMod N) :
    gket u M N h c hc χ x =
      if u ∣ x.val then (((Real.sqrt (Nat.totient M))⁻¹ : ℝ) : ℂ) * χ ((x.val / u : ℕ) : ZMod c) else 0 := by
  have := neZero_of_mul h
  by_cases hx : u ∣ x.val
  · obtain ⟨k, hk⟩ := hx
    have hkM : k < M := by
      have hxv := ZMod.val_lt x
      rw [hk, ← h] at hxv
      exact Nat.lt_of_mul_lt_mul_left hxv
    have hx' : memb u M N h (k : ZMod M) = x := by
      apply ZMod.val_injective N
      rw [memb_val, ZMod.val_natCast_of_lt hkM, hk]
    have hdiv : x.val / u = k := by rw [hk, Nat.mul_div_cancel_left k (pos_of_mul h)]
    rw [ite_eq_left ⟨k, hk⟩, hdiv, ← hx', gket_memb, map_natCast]
  · rw [ite_eq_right hx]
    have hx' : ¬ ∃ y, memb u M N h y = x := fun hy => hx ((exists_memb_iff u M N h x).mp hy)
    simp only [gket, Pi.smul_apply, smul_eq_mul, PAG.Part17.push, Function.extend_apply' _ _ _ hx',
      Pi.zero_apply, mul_zero]

/-- 素数冪の正規化：w < K なら |S_w| = p^(K−1−w)(p−1) = φ(p^(K−w))。 -/
theorem sz_eq_totient {p : ℕ} [hp : Fact p.Prime] (K w : ℕ) (hw : w < K) :
    PAG.Part19.sz p K w = Nat.totient (p ^ (K - w)) := by
  rw [PAG.Part19.sz, Nat.totient_prime_pow hp.out (by omega), show K - w - 1 = K - 1 - w by omega]

/-- 素数冪の殻の埋め込みは Part 17 の shellEmb と一致する。 -/
theorem memb_eq_shellEmb {p : ℕ} [hp : Fact p.Prime] (K w : ℕ) (hw : w ≤ K) :
    memb (p ^ w) (p ^ (K - w)) (p ^ K) (by rw [← pow_add, Nat.add_sub_cancel' hw])
      = PAG.Part17.shellEmb (p := p) K w hw := by
  apply AddMonoidHom.ext
  intro y
  rw [memb_apply, PAG.Part17.shellEmb_apply]

/-- **N = p^K では Part 17 のケットと一致する**（w < K）。 -/
theorem gket_eq_ket {p : ℕ} [hp : Fact p.Prime] (K w c : ℕ) (hwc : w + c ≤ K) (hw : w < K)
    (χ : ZMod (p ^ c) → ℂ) :
    gket (p ^ w) (p ^ (K - w)) (p ^ K) (by rw [← pow_add, Nat.add_sub_cancel' hw.le]) (p ^ c)
      (pow_dvd_pow p (by omega)) χ = PAG.Part21.ket K w c hwc χ := by
  unfold gket PAG.Part21.ket
  rw [sz_eq_totient K w hw, memb_eq_shellEmb K w hw.le]

/-! ### 2. 中国剰余の分解 -/

/-- 法 c₁c₂ に持ち上げた積の指標 X₁′X₂′。 -/
noncomputable def cmul {c₁ c₂ : ℕ} (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) :
    DirichletCharacter ℂ (c₁ * c₂) :=
  X₁.changeLevel (dvd_mul_right c₁ c₂) * X₂.changeLevel (dvd_mul_left c₂ c₁)

theorem cmul_apply {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (X₁ : DirichletCharacter ℂ c₁)
    (X₂ : DirichletCharacter ℂ c₂) (x : ZMod (c₁ * c₂)) :
    cmul X₁ X₂ x = X₁ (ZMod.castHom (dvd_mul_right c₁ c₂) (ZMod c₁) x) *
      X₂ (ZMod.castHom (dvd_mul_left c₂ c₁) (ZMod c₂) x) :=
  PAG.Part193.mul_changeLevel_apply X₁ X₂ x

section CRT

variable {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- **2. 中国剰余の分解**：X₁(u₂)X₂(u₁)·|u₁u₂, X₁′X₂′⟩_N (x) = |u₁, X₁⟩(x mod N₁)·|u₂, X₂⟩(x mod N₂)。 -/
theorem gket_crt (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂)
    (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) (x : ZMod (N₁ * N₂)) :
    X₁ (u₂ : ZMod c₁) * X₂ (u₁ : ZMod c₂) *
        gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (by rw [← h₁, ← h₂]; ring) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂)
          (cmul X₁ X₂) x
      = gket u₁ M₁ N₁ h₁ c₁ hc₁ X₁ (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x) *
        gket u₂ M₂ N₂ h₂ c₂ hc₂ X₂ (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x) := by
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have : NeZero c₁ := ⟨fun h0 => NeZero.ne M₁ (Nat.eq_zero_of_zero_dvd (h0 ▸ hc₁))⟩
  have : NeZero c₂ := ⟨fun h0 => NeZero.ne M₂ (Nat.eq_zero_of_zero_dvd (h0 ▸ hc₂))⟩
  have hu₁ := pos_of_mul h₁
  have hu₂ := pos_of_mul h₂
  have hcopM : M₁.Coprime M₂ :=
    (hcop.coprime_dvd_left (Dvd.intro_left _ h₁)).coprime_dvd_right (Dvd.intro_left _ h₂)
  have hcopu : u₁.Coprime u₂ :=
    (hcop.coprime_dvd_left (Dvd.intro _ h₁)).coprime_dvd_right (Dvd.intro _ h₂)
  have v₁ : (ZMod.castHom (dvd_mul_right N₁ N₂) (ZMod N₁) x).val = x.val % N₁ := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  have v₂ : (ZMod.castHom (dvd_mul_left N₂ N₁) (ZMod N₂) x).val = x.val % N₂ := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
  rw [gket_apply, gket_apply, gket_apply, v₁, v₂]
  by_cases hx : u₁ * u₂ ∣ x.val
  · obtain ⟨t, ht⟩ := hx
    have e₁ : x.val % N₁ = u₁ * (u₂ * t % M₁) := by
      rw [ht, ← h₁, mul_assoc, Nat.mul_mod_mul_left]
    have e₂ : x.val % N₂ = u₂ * (u₁ * t % M₂) := by
      rw [ht, ← h₂, show u₁ * u₂ * t = u₂ * (u₁ * t) by ring, Nat.mul_mod_mul_left]
    have d₀ : x.val / (u₁ * u₂) = t := by rw [ht, Nat.mul_div_cancel_left t (Nat.mul_pos hu₁ hu₂)]
    rw [ite_eq_left ⟨t, ht⟩, e₁, e₂, ite_eq_left (Dvd.intro _ rfl), ite_eq_left (Dvd.intro _ rfl),
      Nat.mul_div_cancel_left _ hu₁, Nat.mul_div_cancel_left _ hu₂, d₀,
      cmul_apply, map_natCast (ZMod.castHom (dvd_mul_right c₁ c₂) (ZMod c₁)),
      map_natCast (ZMod.castHom (dvd_mul_left c₂ c₁) (ZMod c₂))]
    have m₁ : ((u₂ * t % M₁ : ℕ) : ZMod c₁) = (u₂ : ZMod c₁) * (t : ZMod c₁) := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hc₁]
    have m₂ : ((u₁ * t % M₂ : ℕ) : ZMod c₂) = (u₁ : ZMod c₂) * (t : ZMod c₂) := by
      rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hc₂]
    rw [m₁, m₂, map_mul, map_mul]
    have hφ : ((Nat.totient (M₁ * M₂) : ℕ) : ℝ) = (Nat.totient M₁ : ℝ) * (Nat.totient M₂ : ℝ) := by
      rw [Nat.totient_mul hcopM, Nat.cast_mul]
    rw [hφ, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv]
    push_cast
    ring
  · rw [ite_eq_right hx, mul_zero]
    have hnot : ¬ (u₁ ∣ x.val % N₁ ∧ u₂ ∣ x.val % N₂) := by
      rintro ⟨d₁, d₂⟩
      exact hx (hcopu.mul_dvd_of_dvd_of_dvd ((Nat.dvd_mod_iff (Dvd.intro _ h₁)).mp d₁)
        ((Nat.dvd_mod_iff (Dvd.intro _ h₂)).mp d₂))
    by_cases d₁ : u₁ ∣ x.val % N₁
    · rw [ite_eq_right (fun d₂ => hnot ⟨d₁, d₂⟩), mul_zero]
    · rw [ite_eq_right d₁, zero_mul]

end CRT

/-! ### 3. ガウス和の比の大域形 -/

/-- 単数での指標の値は 0 でない。 -/
theorem chi_natCast_ne_zero {d : ℕ} (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Ψ (n : ZMod d) ≠ 0 := by
  rw [← ZMod.coe_unitOfCoprime n hn]
  exact ((ZMod.unitOfCoprime n hn).isUnit.map Ψ).ne_zero

/-- 持ち上げた指標の自然数での値：n が c と互いに素なら Ψ′(n) = Ψ(n)。 -/
theorem changeLevel_natCast {d c : ℕ} (hd : d ∣ c) (Ψ : DirichletCharacter ℂ d) (n : ℕ)
    (hn : n.Coprime c) : Ψ.changeLevel hd (n : ZMod c) = Ψ (n : ZMod d) := by
  rw [← ZMod.coe_unitOfCoprime n hn, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.coe_unitOfCoprime, ZMod.cast_natCast hd]

/-- **3. ガウス和の比の大域形**：A_iB_i = Ψ_i∘π（法 c_i → d_i）なら
τ(A)τ(B)/τ(Ψ) = Ψ₁(c₂/d₂)Ψ₂(c₁/d₁)·Π_i τ(A_i)τ(B_i)/τ(Ψ_i)（A = A₁′A₂′ など。原始性は要らない）。 -/
theorem gauss_ratio_mul {c₁ c₂ d₁ d₂ : ℕ} [NeZero c₁] [NeZero c₂] [NeZero d₁] [NeZero d₂]
    (hcop : c₁.Coprime c₂)
    (hd₁ : d₁ ∣ c₁) (hd₂ : d₂ ∣ c₂)
    (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂)
    (Ψ₁ : DirichletCharacter ℂ d₁) (Ψ₂ : DirichletCharacter ℂ d₂)
    (hΨ₁ : A₁ * B₁ = Ψ₁.changeLevel hd₁) (hΨ₂ : A₂ * B₂ = Ψ₂.changeLevel hd₂) :
    gaussSum (cmul A₁ A₂) stdAddChar * gaussSum (cmul B₁ B₂) stdAddChar / gaussSum (cmul Ψ₁ Ψ₂) stdAddChar
      = Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂) *
        (gaussSum A₁ stdAddChar * gaussSum B₁ stdAddChar / gaussSum Ψ₁ stdAddChar) *
        (gaussSum A₂ stdAddChar * gaussSum B₂ stdAddChar / gaussSum Ψ₂ stdAddChar) := by
  have hcopd : d₁.Coprime d₂ := (hcop.coprime_dvd_left hd₁).coprime_dvd_right hd₂
  have k₁ : A₁ (c₂ : ZMod c₁) * B₁ (c₂ : ZMod c₁)
      = Ψ₁ (d₂ : ZMod d₁) * Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) := by
    rw [← MulChar.mul_apply, hΨ₁, changeLevel_natCast hd₁ Ψ₁ c₂ hcop.symm, ← map_mul, ← Nat.cast_mul,
      Nat.mul_div_cancel' hd₂]
  have k₂ : A₂ (c₁ : ZMod c₂) * B₂ (c₁ : ZMod c₂)
      = Ψ₂ (d₁ : ZMod d₂) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂) := by
    rw [← MulChar.mul_apply, hΨ₂, changeLevel_natCast hd₂ Ψ₂ c₁ hcop, ← map_mul, ← Nat.cast_mul,
      Nat.mul_div_cancel' hd₁]
  have hne : Ψ₁ (d₂ : ZMod d₁) * Ψ₂ (d₁ : ZMod d₂) ≠ 0 :=
    mul_ne_zero (chi_natCast_ne_zero Ψ₁ d₂ hcopd.symm) (chi_natCast_ne_zero Ψ₂ d₁ hcopd)
  unfold cmul
  rw [PAG.Part193.gaussSum_mul_coprime hcop, PAG.Part193.gaussSum_mul_coprime hcop,
    PAG.Part193.gaussSum_mul_coprime hcopd]
  have hnum : A₁ (c₂ : ZMod c₁) * A₂ (c₁ : ZMod c₂) * gaussSum A₁ stdAddChar * gaussSum A₂ stdAddChar *
      (B₁ (c₂ : ZMod c₁) * B₂ (c₁ : ZMod c₂) * gaussSum B₁ stdAddChar * gaussSum B₂ stdAddChar)
      = (Ψ₁ (d₂ : ZMod d₁) * Ψ₂ (d₁ : ZMod d₂)) *
        (Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂) *
          (gaussSum A₁ stdAddChar * gaussSum B₁ stdAddChar) * (gaussSum A₂ stdAddChar * gaussSum B₂ stdAddChar)) := by
    calc _ = (A₁ (c₂ : ZMod c₁) * B₁ (c₂ : ZMod c₁)) * (A₂ (c₁ : ZMod c₂) * B₂ (c₁ : ZMod c₂)) *
          (gaussSum A₁ stdAddChar * gaussSum B₁ stdAddChar) * (gaussSum A₂ stdAddChar * gaussSum B₂ stdAddChar) := by
          ring
      _ = _ := by rw [k₁, k₂]; ring
  have hden : Ψ₁ (d₂ : ZMod d₁) * Ψ₂ (d₁ : ZMod d₂) * gaussSum Ψ₁ stdAddChar * gaussSum Ψ₂ stdAddChar
      = (Ψ₁ (d₂ : ZMod d₁) * Ψ₂ (d₁ : ZMod d₂)) * (gaussSum Ψ₁ stdAddChar * gaussSum Ψ₂ stdAddChar) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hne]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-! ### 4. 定理 A の乗法性 -/

/-- (a f) ⊗ (b g) = (ab)(f ⊗ g)。 -/
theorem tens_smul_smul {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    (a b : ℂ) (f : G → ℂ) (g : H → ℂ) :
    PAG.Part108.tens (a • f) (b • g) = (a * b) • PAG.Part108.tens f g := by
  funext z
  simp only [PAG.Part108.tens, Pi.smul_apply, smul_eq_mul]
  ring

/-- 積の等式 u₁u₂·M₁M₂ = N₁N₂。 -/
theorem prod_eq {u₁ u₂ M₁ M₂ N₁ N₂ : ℕ} (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂) :
    u₁ * u₂ * (M₁ * M₂) = N₁ * N₂ := by
  rw [← h₁, ← h₂]; ring

section Mul

variable {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ : ℕ} [NeZero N₁] [NeZero N₂]

/-- 中国剰余の分解（関数の形）：X₁(u₂)X₂(u₁)·|u, X⟩_N = (|u₁, X₁⟩ ⊗ |u₂, X₂⟩) ∘ crt。 -/
theorem gket_crt_fun (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂)
    (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂) (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) :
    (X₁ (u₂ : ZMod c₁) * X₂ (u₁ : ZMod c₂)) •
        gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul X₁ X₂)
      = PAG.Part108.tens (gket u₁ M₁ N₁ h₁ c₁ hc₁ X₁) (gket u₂ M₂ N₂ h₂ c₂ hc₂ X₂) ∘
          (PAG.Part194.crt hcop).toAddEquiv := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, gket_crt hcop h₁ h₂ hc₁ hc₂ X₁ X₂ x]
  rfl

/-- **4. 定理 A の乗法性（係数の形）**：N₁, N₂ が互いに素で、各因子で
|u_i, A_i⟩ ⋆ |u_i, B_i⟩ = l_i |u_i′, Ψ_i⟩（A_iB_i = Ψ_i∘π、u_i′ = u_i·c_i/d_i）なら
|u, A⟩ ⋆ |u, B⟩ = Ψ₁(c₂/d₂)Ψ₂(c₁/d₁) l₁ l₂ |u′, Ψ⟩（A = A₁′A₂′ など）。 -/
theorem thmA_mul_aux (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂)
    (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂) {u₁' u₂' M₁' M₂' d₁ d₂ : ℕ}
    (h₁' : u₁' * M₁' = N₁) (h₂' : u₂' * M₂' = N₂) (hd₁ : d₁ ∣ M₁') (hd₂ : d₂ ∣ M₂')
    (hdc₁ : d₁ ∣ c₁) (hdc₂ : d₂ ∣ c₂) (hu₁' : u₁' = u₁ * (c₁ / d₁)) (hu₂' : u₂' = u₂ * (c₂ / d₂))
    (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂)
    (Ψ₁ : DirichletCharacter ℂ d₁) (Ψ₂ : DirichletCharacter ℂ d₂)
    (hΨ₁ : A₁ * B₁ = Ψ₁.changeLevel hdc₁) (hΨ₂ : A₂ * B₂ = Ψ₂.changeLevel hdc₂) (l₁ l₂ : ℂ)
    (H₁ : PAG.Part15.conv (gket u₁ M₁ N₁ h₁ c₁ hc₁ A₁) (gket u₁ M₁ N₁ h₁ c₁ hc₁ B₁)
      = l₁ • gket u₁' M₁' N₁ h₁' d₁ hd₁ Ψ₁)
    (H₂ : PAG.Part15.conv (gket u₂ M₂ N₂ h₂ c₂ hc₂ A₂) (gket u₂ M₂ N₂ h₂ c₂ hc₂ B₂)
      = l₂ • gket u₂' M₂' N₂ h₂' d₂ hd₂ Ψ₂) :
    PAG.Part15.conv
        (gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul A₁ A₂))
        (gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul B₁ B₂))
      = (Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂) * l₁ * l₂) •
        gket (u₁' * u₂') (M₁' * M₂') (N₁ * N₂) (prod_eq h₁' h₂') (d₁ * d₂) (mul_dvd_mul hd₁ hd₂)
          (cmul Ψ₁ Ψ₂) := by
  -- 互いに素の関係
  have hN₁c₁ : c₁ ∣ N₁ := hc₁.trans (Dvd.intro_left _ h₁)
  have hN₂c₂ : c₂ ∣ N₂ := hc₂.trans (Dvd.intro_left _ h₂)
  have hu₂c₁ : u₂.Coprime c₁ :=
    (hcop.symm.coprime_dvd_left (Dvd.intro _ h₂)).coprime_dvd_right hN₁c₁
  have hu₁c₂ : u₁.Coprime c₂ :=
    (hcop.coprime_dvd_left (Dvd.intro _ h₁)).coprime_dvd_right hN₂c₂
  have hu₂d₁ : u₂.Coprime d₁ := hu₂c₁.coprime_dvd_right hdc₁
  have hu₁d₂ : u₁.Coprime d₂ := hu₁c₂.coprime_dvd_right hdc₂
  set φ := (PAG.Part194.crt hcop).toAddEquiv
  set a := A₁ (u₂ : ZMod c₁) * A₂ (u₁ : ZMod c₂) with ha_def
  set b := B₁ (u₂ : ZMod c₁) * B₂ (u₁ : ZMod c₂) with hb_def
  have ha : a ≠ 0 := mul_ne_zero (chi_natCast_ne_zero A₁ u₂ hu₂c₁) (chi_natCast_ne_zero A₂ u₁ hu₁c₂)
  have hb : b ≠ 0 := mul_ne_zero (chi_natCast_ne_zero B₁ u₂ hu₂c₁) (chi_natCast_ne_zero B₂ u₁ hu₁c₂)
  have eA : gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul A₁ A₂)
      = a⁻¹ • (PAG.Part108.tens (gket u₁ M₁ N₁ h₁ c₁ hc₁ A₁) (gket u₂ M₂ N₂ h₂ c₂ hc₂ A₂) ∘ φ) := by
    rw [← gket_crt_fun hcop h₁ h₂ hc₁ hc₂ A₁ A₂, inv_smul_smul₀ ha]
  have eB : gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul B₁ B₂)
      = b⁻¹ • (PAG.Part108.tens (gket u₁ M₁ N₁ h₁ c₁ hc₁ B₁) (gket u₂ M₂ N₂ h₂ c₂ hc₂ B₂) ∘ φ) := by
    rw [← gket_crt_fun hcop h₁ h₂ hc₁ hc₂ B₁ B₂, inv_smul_smul₀ hb]
  have eΨ := gket_crt_fun hcop h₁' h₂' hd₁ hd₂ Ψ₁ Ψ₂
  rw [eA, eB, PAG.Part15.conv_smul_smul, PAG.Part108.conv_comp_equiv, PAG.Part108.conv_tens, H₁, H₂,
    tens_smul_smul,
    show ((l₁ * l₂) • PAG.Part108.tens (gket u₁' M₁' N₁ h₁' d₁ hd₁ Ψ₁) (gket u₂' M₂' N₂ h₂' d₂ hd₂ Ψ₂)) ∘ φ
      = (l₁ * l₂) • (PAG.Part108.tens (gket u₁' M₁' N₁ h₁' d₁ hd₁ Ψ₁) (gket u₂' M₂' N₂ h₂' d₂ hd₂ Ψ₂) ∘ φ)
      from rfl, ← eΨ, smul_smul, smul_smul]
  congr 1
  -- 係数：a b = Ψ₁(u₂)Ψ₂(u₁)、s = Ψ₁(u₂′)Ψ₂(u₁′) = a b Ψ₁(c₂/d₂)Ψ₂(c₁/d₁)
  have hab : a * b = Ψ₁ (u₂ : ZMod d₁) * Ψ₂ (u₁ : ZMod d₂) := by
    rw [ha_def, hb_def]
    calc A₁ (u₂ : ZMod c₁) * A₂ (u₁ : ZMod c₂) * (B₁ (u₂ : ZMod c₁) * B₂ (u₁ : ZMod c₂))
        = (A₁ * B₁) (u₂ : ZMod c₁) * (A₂ * B₂) (u₁ : ZMod c₂) := by
          rw [MulChar.mul_apply, MulChar.mul_apply]; ring
      _ = _ := by rw [hΨ₁, hΨ₂, changeLevel_natCast hdc₁ Ψ₁ u₂ hu₂c₁, changeLevel_natCast hdc₂ Ψ₂ u₁ hu₁c₂]
  have hs : Ψ₁ (u₂' : ZMod d₁) * Ψ₂ (u₁' : ZMod d₂)
      = a * b * (Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂)) := by
    rw [hab, hu₁', hu₂', Nat.cast_mul, Nat.cast_mul, map_mul, map_mul]; ring
  rw [hs]
  field_simp

end Mul

/-! ### 5. 大域の定数と、ℤ/N の定理 A -/

/-- **定理 A の大域の定数** √(N/φ(uc))·(τ(A)τ(B)/τ(Ψ))/√(c·c/d)。 -/
noncomputable def thmAConst (N u c d : ℕ) [NeZero c] [NeZero d] (A B : DirichletCharacter ℂ c)
    (Ψ : DirichletCharacter ℂ d) : ℂ :=
  ((Real.sqrt ((N : ℝ) / (Nat.totient (u * c) : ℝ)) : ℝ) : ℂ) *
    (gaussSum A stdAddChar * gaussSum B stdAddChar / gaussSum Ψ stdAddChar) /
      ((Real.sqrt ((c * (c / d) : ℕ) : ℝ) : ℝ) : ℂ)

/-- 定数の乗法性：Ψ₁(c₂/d₂)Ψ₂(c₁/d₁)·C(N₁)·C(N₂) = C(N₁N₂)。 -/
theorem thmAConst_mul {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ d₁ d₂ : ℕ} [NeZero N₁] [NeZero N₂]
    [NeZero c₁] [NeZero c₂] [NeZero d₁] [NeZero d₂]
    (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂) (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (hdc₁ : d₁ ∣ c₁) (hdc₂ : d₂ ∣ c₂)
    (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂)
    (Ψ₁ : DirichletCharacter ℂ d₁) (Ψ₂ : DirichletCharacter ℂ d₂)
    (hΨ₁ : A₁ * B₁ = Ψ₁.changeLevel hdc₁) (hΨ₂ : A₂ * B₂ = Ψ₂.changeLevel hdc₂) :
    Ψ₁ ((c₂ / d₂ : ℕ) : ZMod d₁) * Ψ₂ ((c₁ / d₁ : ℕ) : ZMod d₂) * thmAConst N₁ u₁ c₁ d₁ A₁ B₁ Ψ₁ *
        thmAConst N₂ u₂ c₂ d₂ A₂ B₂ Ψ₂
      = thmAConst (N₁ * N₂) (u₁ * u₂) (c₁ * c₂) (d₁ * d₂) (cmul A₁ A₂) (cmul B₁ B₂) (cmul Ψ₁ Ψ₂) := by
  have hNc₁ : u₁ * c₁ ∣ N₁ := h₁ ▸ mul_dvd_mul_left u₁ hc₁
  have hNc₂ : u₂ * c₂ ∣ N₂ := h₂ ▸ mul_dvd_mul_left u₂ hc₂
  have hcop' : (u₁ * c₁).Coprime (u₂ * c₂) := (hcop.coprime_dvd_left hNc₁).coprime_dvd_right hNc₂
  have hcopc : c₁.Coprime c₂ :=
    (hcop.coprime_dvd_left (Dvd.dvd.trans (Dvd.intro_left _ rfl) hNc₁)).coprime_dvd_right
      (Dvd.dvd.trans (Dvd.intro_left _ rfl) hNc₂)
  have hφ : Nat.totient (u₁ * u₂ * (c₁ * c₂)) = Nat.totient (u₁ * c₁) * Nat.totient (u₂ * c₂) := by
    rw [show u₁ * u₂ * (c₁ * c₂) = (u₁ * c₁) * (u₂ * c₂) by ring, Nat.totient_mul hcop']
  have hs : c₁ * c₂ * (c₁ * c₂ / (d₁ * d₂)) = c₁ * (c₁ / d₁) * (c₂ * (c₂ / d₂)) := by
    rw [← Nat.div_mul_div_comm hdc₁ hdc₂]; ring
  unfold thmAConst
  rw [gauss_ratio_mul hcopc hdc₁ hdc₂ A₁ B₁ A₂ B₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂, hφ, hs]
  have e1 : ((Real.sqrt (((N₁ * N₂ : ℕ) : ℝ) / ((Nat.totient (u₁ * c₁) * Nat.totient (u₂ * c₂) : ℕ) : ℝ)) : ℝ) : ℂ)
      = ((Real.sqrt ((N₁ : ℝ) / (Nat.totient (u₁ * c₁) : ℝ)) : ℝ) : ℂ) *
        ((Real.sqrt ((N₂ : ℝ) / (Nat.totient (u₂ * c₂) : ℝ)) : ℝ) : ℂ) := by
    rw [Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm,
      Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), Complex.ofReal_mul]
  have e2 : ((Real.sqrt ((c₁ * (c₁ / d₁) * (c₂ * (c₂ / d₂)) : ℕ) : ℝ) : ℝ) : ℂ)
      = ((Real.sqrt ((c₁ * (c₁ / d₁) : ℕ) : ℝ) : ℝ) : ℂ) * ((Real.sqrt ((c₂ * (c₂ / d₂) : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [Nat.cast_mul (c₁ * (c₁ / d₁)), Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  rw [e1, e2]
  ring

/-- **ℤ/N の定理 A の主張**：|u, A⟩ ⋆ |u, B⟩ = C(N, u, c, d; A, B, Ψ)·|u′, Ψ⟩。 -/
def ThmA (N u M c d u' M' : ℕ) [NeZero N] [NeZero c] [NeZero d] (h : u * M = N) (hc : c ∣ M)
    (h' : u' * M' = N) (hd : d ∣ M')
    (A B : DirichletCharacter ℂ c) (Ψ : DirichletCharacter ℂ d) : Prop :=
  PAG.Part15.conv (gket u M N h c hc A) (gket u M N h c hc B) = thmAConst N u c d A B Ψ • gket u' M' N h' d hd Ψ

/-- **5a. 素数冪の場合**（Part 17・21 の定理 A の言い換え）。 -/
theorem thmA_prime_power {p : ℕ} [hp : Fact p.Prime] (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : χ₁ * χ₂ = ψ.changeLevel (pow_dvd_pow p (Nat.sub_le (n + 1) v))) :
    ThmA (p ^ K) (p ^ w) (p ^ (K - w)) (p ^ (n + 1)) (p ^ (n + 1 - v)) (p ^ (w + v)) (p ^ (K - (w + v)))
      (pow_mul_pow_sub p (by omega)) (pow_dvd_pow p (by omega)) (pow_mul_pow_sub p (by omega))
      (pow_dvd_pow p (by omega)) χ₁ χ₂ ψ := by
  have hcast : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x) := by
    intro x
    rw [hprod, PAG.Part47.changeLevel_apply_cast (by omega) (Nat.sub_le (n + 1) v)]
  unfold ThmA
  rw [gket_eq_ket K w (n + 1) hK (by omega), gket_eq_ket K w (n + 1) hK (by omega),
    gket_eq_ket K (w + v) (n + 1 - v) (by omega) (by omega),
    PAG.Part21.thmA_ket K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hcast]
  congr 1
  have e1 : PAG.Part19.sz p K (K - (n + 1) - w) = Nat.totient (p ^ w * p ^ (n + 1)) := by
    rw [sz_eq_totient K _ (by omega), ← pow_add]
    congr 2
    omega
  have e2 : p ^ (n + 1) * (p ^ (n + 1) / p ^ (n + 1 - v)) = p ^ (n + 1 + v) := by
    rw [Nat.pow_div (Nat.sub_le _ _) hp.out.pos, ← pow_add]
    congr 1
    omega
  unfold thmAConst
  rw [e1, e2]
  push_cast
  ring

/-- **5b. 定理 A の乗法性（大域の形）**：N₁, N₂ が互いに素で、各因子で ℤ/N_i の定理 A が成り立てば、
ℤ/N₁N₂ でも成り立つ（A = A₁′A₂′、B = B₁′B₂′、Ψ = Ψ₁′Ψ₂′、定数は大域のガウス和で書ける）。 -/
theorem thmA_mul {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ d₁ d₂ u₁' u₂' M₁' M₂' : ℕ} [NeZero N₁] [NeZero N₂]
    [NeZero c₁] [NeZero c₂] [NeZero d₁] [NeZero d₂]
    (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂) (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂)
    (h₁' : u₁' * M₁' = N₁) (h₂' : u₂' * M₂' = N₂) (hd₁ : d₁ ∣ M₁') (hd₂ : d₂ ∣ M₂')
    (hdc₁ : d₁ ∣ c₁) (hdc₂ : d₂ ∣ c₂) (hu₁' : u₁' = u₁ * (c₁ / d₁)) (hu₂' : u₂' = u₂ * (c₂ / d₂))
    (A₁ B₁ : DirichletCharacter ℂ c₁) (A₂ B₂ : DirichletCharacter ℂ c₂)
    (Ψ₁ : DirichletCharacter ℂ d₁) (Ψ₂ : DirichletCharacter ℂ d₂)
    (hΨ₁ : A₁ * B₁ = Ψ₁.changeLevel hdc₁) (hΨ₂ : A₂ * B₂ = Ψ₂.changeLevel hdc₂)
    (H₁ : ThmA N₁ u₁ M₁ c₁ d₁ u₁' M₁' h₁ hc₁ h₁' hd₁ A₁ B₁ Ψ₁)
    (H₂ : ThmA N₂ u₂ M₂ c₂ d₂ u₂' M₂' h₂ hc₂ h₂' hd₂ A₂ B₂ Ψ₂) :
    ThmA (N₁ * N₂) (u₁ * u₂) (M₁ * M₂) (c₁ * c₂) (d₁ * d₂) (u₁' * u₂') (M₁' * M₂')
      (prod_eq h₁ h₂) (mul_dvd_mul hc₁ hc₂) (prod_eq h₁' h₂') (mul_dvd_mul hd₁ hd₂)
      (cmul A₁ A₂) (cmul B₁ B₂) (cmul Ψ₁ Ψ₂) := by
  unfold ThmA at H₁ H₂ ⊢
  rw [thmA_mul_aux hcop h₁ h₂ hc₁ hc₂ h₁' h₂' hd₁ hd₂ hdc₁ hdc₂ hu₁' hu₂' A₁ B₁ A₂ B₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ _ _ H₁ H₂,
    thmAConst_mul hcop h₁ h₂ hc₁ hc₂ hdc₁ hdc₂ A₁ B₁ A₂ B₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂]

/-- **5c. 2 つの素数での ℤ/N の定理 A**：N = p^K q^L（p ≠ q）、u = p^w q^{w′}、c = p^{n+1} q^{m+1}、
d = p^{n+1−v} q^{m+1−v′} で |u, χ₁′η₁′⟩ ⋆ |u, χ₂′η₂′⟩ = C·|p^{w+v} q^{w′+v′}, ψ′ψ″⟩、
C = √(N/φ(uc))·τ(A)τ(B)/(τ(Ψ)√(c·c/d))（大域のガウス和）。 -/
theorem thmA_two_prime {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (L w' m v' : ℕ) (hv' : v' ≤ m) (hL : w' + (m + 1) ≤ L)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : χ₁ * χ₂ = ψ.changeLevel (pow_dvd_pow p (Nat.sub_le (n + 1) v)))
    (η₁ η₂ : DirichletCharacter ℂ (q ^ (m + 1))) (g₁ : η₁.IsPrimitive) (g₂ : η₂.IsPrimitive)
    (ψ' : DirichletCharacter ℂ (q ^ (m + 1 - v'))) (hψ' : ψ'.IsPrimitive)
    (hprod' : η₁ * η₂ = ψ'.changeLevel (pow_dvd_pow q (Nat.sub_le (m + 1) v'))) :
    ThmA (p ^ K * q ^ L) (p ^ w * q ^ w') (p ^ (K - w) * q ^ (L - w')) (p ^ (n + 1) * q ^ (m + 1))
      (p ^ (n + 1 - v) * q ^ (m + 1 - v')) (p ^ (w + v) * q ^ (w' + v'))
      (p ^ (K - (w + v)) * q ^ (L - (w' + v')))
      (prod_eq (pow_mul_pow_sub p (by omega)) (pow_mul_pow_sub q (by omega)))
      (mul_dvd_mul (pow_dvd_pow p (by omega)) (pow_dvd_pow q (by omega)))
      (prod_eq (pow_mul_pow_sub p (by omega)) (pow_mul_pow_sub q (by omega)))
      (mul_dvd_mul (pow_dvd_pow p (by omega)) (pow_dvd_pow q (by omega)))
      (cmul χ₁ η₁) (cmul χ₂ η₂) (cmul ψ ψ') := by
  have hcop : (p ^ K).Coprime (q ^ L) := Nat.Coprime.pow K L ((Nat.coprime_primes hp.out hq.out).mpr hpq)
  have hu₁ : p ^ (w + v) = p ^ w * (p ^ (n + 1) / p ^ (n + 1 - v)) := by
    rw [Nat.pow_div (Nat.sub_le _ _) hp.out.pos, ← pow_add]
    congr 1
    omega
  have hu₂ : q ^ (w' + v') = q ^ w' * (q ^ (m + 1) / q ^ (m + 1 - v')) := by
    rw [Nat.pow_div (Nat.sub_le _ _) hq.out.pos, ← pow_add]
    congr 1
    omega
  exact thmA_mul hcop _ _ _ _ _ _ _ _ (pow_dvd_pow p (Nat.sub_le _ _)) (pow_dvd_pow q (Nat.sub_le _ _)) hu₁ hu₂
    χ₁ χ₂ η₁ η₂ ψ ψ' hprod hprod' (thmA_prime_power K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod)
    (thmA_prime_power L w' m v' hv' hL η₁ η₂ g₁ g₂ ψ' hψ' hprod')

/-! ### 6. ノルム -/

/-- 単数での指標の値は絶対値 1。 -/
theorem normSq_chi_natCast {d : ℕ} [NeZero d] (Ψ : DirichletCharacter ℂ d) (n : ℕ) (hn : n.Coprime d) :
    Complex.normSq (Ψ (n : ZMod d)) = 1 := by
  rw [← ZMod.coe_unitOfCoprime n hn]
  have h := PAG.Part193.chi_unit_root Ψ (ZMod.unitOfCoprime n hn)
  rw [Complex.normSq_eq_norm_sq, Complex.norm_eq_one_of_pow_eq_one h (orderOf_pos _).ne', one_pow]

/-- **6. ノルムの乗法性**：‖|u₁u₂, X₁′X₂′⟩_N‖² = ‖|u₁, X₁⟩‖²·‖|u₂, X₂⟩‖²。 -/
theorem normSq_gket_crt {N₁ N₂ u₁ u₂ M₁ M₂ c₁ c₂ : ℕ} [NeZero N₁] [NeZero N₂]
    (hcop : N₁.Coprime N₂) (h₁ : u₁ * M₁ = N₁) (h₂ : u₂ * M₂ = N₂)
    (hc₁ : c₁ ∣ M₁) (hc₂ : c₂ ∣ M₂) (X₁ : DirichletCharacter ℂ c₁) (X₂ : DirichletCharacter ℂ c₂) :
    ∑ x, Complex.normSq
        (gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul X₁ X₂) x)
      = (∑ x, Complex.normSq (gket u₁ M₁ N₁ h₁ c₁ hc₁ X₁ x)) *
        ∑ x, Complex.normSq (gket u₂ M₂ N₂ h₂ c₂ hc₂ X₂ x) := by
  have hM₁ := neZero_of_mul h₁
  have hM₂ := neZero_of_mul h₂
  have : NeZero c₁ := ⟨fun h0 => NeZero.ne M₁ (Nat.eq_zero_of_zero_dvd (h0 ▸ hc₁))⟩
  have : NeZero c₂ := ⟨fun h0 => NeZero.ne M₂ (Nat.eq_zero_of_zero_dvd (h0 ▸ hc₂))⟩
  have hN₁c₁ : c₁ ∣ N₁ := hc₁.trans (Dvd.intro_left _ h₁)
  have hN₂c₂ : c₂ ∣ N₂ := hc₂.trans (Dvd.intro_left _ h₂)
  have hu₂c₁ : u₂.Coprime c₁ :=
    (hcop.symm.coprime_dvd_left (Dvd.intro _ h₂)).coprime_dvd_right hN₁c₁
  have hu₁c₂ : u₁.Coprime c₂ :=
    (hcop.coprime_dvd_left (Dvd.intro _ h₁)).coprime_dvd_right hN₂c₂
  have ha : Complex.normSq (X₁ (u₂ : ZMod c₁) * X₂ (u₁ : ZMod c₂)) = 1 := by
    rw [map_mul, normSq_chi_natCast X₁ u₂ hu₂c₁, normSq_chi_natCast X₂ u₁ hu₁c₂, one_mul]
  calc ∑ x, Complex.normSq
        (gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂) (cmul X₁ X₂) x)
      = ∑ x, Complex.normSq (((X₁ (u₂ : ZMod c₁) * X₂ (u₁ : ZMod c₂)) •
          gket (u₁ * u₂) (M₁ * M₂) (N₁ * N₂) (prod_eq h₁ h₂) (c₁ * c₂) (mul_dvd_mul hc₁ hc₂)
            (cmul X₁ X₂)) x) := by
        refine sum_congr rfl (fun x _ => ?_)
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ha, one_mul]
    _ = ∑ x, Complex.normSq ((PAG.Part108.tens (gket u₁ M₁ N₁ h₁ c₁ hc₁ X₁) (gket u₂ M₂ N₂ h₂ c₂ hc₂ X₂) ∘
          (PAG.Part194.crt hcop).toAddEquiv) x) := by
        rw [gket_crt_fun hcop h₁ h₂ hc₁ hc₂ X₁ X₂]
    _ = _ := by rw [PAG.Part108.normSq_comp_equiv, PAG.Part108.normSq_tens]

/-- **系**：N = p^K q^L の原始的な指標の積のケットは単位ベクトル。 -/
theorem norm_gket_two_prime {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (K w n : ℕ) (hK : w + (n + 1) ≤ K) (L w' m : ℕ) (hL : w' + (m + 1) ≤ L)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive)
    (η : DirichletCharacter ℂ (q ^ (m + 1))) (hη : η.IsPrimitive) :
    ∑ x, Complex.normSq (gket (p ^ w * q ^ w') (p ^ (K - w) * q ^ (L - w')) (p ^ K * q ^ L)
      (prod_eq (pow_mul_pow_sub p (by omega)) (pow_mul_pow_sub q (by omega))) (p ^ (n + 1) * q ^ (m + 1))
      (mul_dvd_mul (pow_dvd_pow p (by omega)) (pow_dvd_pow q (by omega))) (cmul χ η) x) = 1 := by
  have hcop : (p ^ K).Coprime (q ^ L) := Nat.Coprime.pow K L ((Nat.coprime_primes hp.out hq.out).mpr hpq)
  rw [normSq_gket_crt hcop (pow_mul_pow_sub p (by omega)) (pow_mul_pow_sub q (by omega))
      (pow_dvd_pow p (by omega)) (pow_dvd_pow q (by omega)) χ η,
    gket_eq_ket K w (n + 1) hK (by omega), gket_eq_ket L w' (m + 1) hL (by omega),
    PAG.Part39.norm_ket K w n hK χ hχ, PAG.Part39.norm_ket L w' m hL η hη, one_mul]

end PAG.Part199

#print axioms PAG.Part199.neZero_of_mul
#print axioms PAG.Part199.pos_of_mul
#print axioms PAG.Part199.memb_apply
#print axioms PAG.Part199.memb_val
#print axioms PAG.Part199.memb_injective
#print axioms PAG.Part199.exists_memb_iff
#print axioms PAG.Part199.gket_memb
#print axioms PAG.Part199.gket_apply
#print axioms PAG.Part199.sz_eq_totient
#print axioms PAG.Part199.memb_eq_shellEmb
#print axioms PAG.Part199.gket_eq_ket
#print axioms PAG.Part199.cmul_apply
#print axioms PAG.Part199.gket_crt
#print axioms PAG.Part199.chi_natCast_ne_zero
#print axioms PAG.Part199.changeLevel_natCast
#print axioms PAG.Part199.gauss_ratio_mul
#print axioms PAG.Part199.tens_smul_smul
#print axioms PAG.Part199.prod_eq
#print axioms PAG.Part199.gket_crt_fun
#print axioms PAG.Part199.thmA_mul_aux
#print axioms PAG.Part199.thmAConst_mul
#print axioms PAG.Part199.thmA_prime_power
#print axioms PAG.Part199.thmA_mul
#print axioms PAG.Part199.thmA_two_prime
#print axioms PAG.Part199.normSq_chi_natCast
#print axioms PAG.Part199.normSq_gket_crt
#print axioms PAG.Part199.norm_gket_two_prime
