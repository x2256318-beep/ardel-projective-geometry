/-
  PAG 2.0 Part 188（2026-10-23）— 一般の m のハッセ・ダベンポートの関係（1 の冪根を除いて）
  p は素数、χ は法 p の位数 n の指標、ψ は原始的な加法的指標、z(φ) = τ(φ, ψ)/√p、⟨x⟩ = x mod n。
  1. family_root_iff：f_t ≢ 0 (mod n) の族について、∏_t z(χ^{f_t})^{b_t} が 1 の冪根 ⇔
     n と互いに素なすべての c で Σ_t b_t (n − 2⟨c f_t⟩) = 0（Part 186 の判定を、重複を許す族に移したもの）
  2. frac_identity（分数部分の恒等式）：n = m d、c が n と互いに素なら
     Σ_{a<m} ⟨c(k + d a)⟩ = ⟨c k m⟩ + Σ_{1≤a<m} ⟨c d a⟩
  3. hasse_davenport_root：n = m d、ψ′ = χ^d（位数 m）、χ^{km} ≠ 1 のとき
     ∏_{a=0}^{m−1} z(χ^k ψ′^a) / ( z(χ^{km}) ∏_{a=1}^{m−1} z(ψ′^a) ) は 1 の冪根
     （古典的なハッセ・ダベンポートの関係では、この比は χ(m)^{−km}。今回は 1 の冪根であることまでを示す）
-/
import PAG191

namespace PAG.Part192

open Complex Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### 1. 指標の族の判定 -/

/-- 0 でない z について ∏_t z^{b_t} = z^{Σ b_t}。 -/
theorem prod_zpow_const {κ : Type*} (s : Finset κ) (z : ℂ) (hz : z ≠ 0) (b : κ → ℤ) :
    ∏ t ∈ s, z ^ b t = z ^ (∑ t ∈ s, b t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, zpow_add₀ hz]

/-- z(φ) ≠ 0（φ ≠ 1）。 -/
theorem z_ne_zero (φ : MulChar (ZMod p) ℂ) (hφ : φ ≠ 1) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) : gaussSum φ ψ / ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := PAG.Part190.norm_z φ hφ hψ
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- **1. 族の判定**：f_t ≢ 0 (mod n) の族について、∏_t z(χ^{f_t})^{b_t} が 1 の冪根 ⇔
  n と互いに素なすべての c で Σ_t b_t (n − 2⟨c f_t⟩) = 0。 -/
theorem family_root_iff (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    {κ : Type*} (s : Finset κ) (f : κ → ℕ) (hf : ∀ t ∈ s, ¬ orderOf χ ∣ f t) (b : κ → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ t ∈ s, (gaussSum (χ ^ f t) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b t) ^ N = 1) ↔
      ∀ c : ℕ, c.Coprime (orderOf χ) →
        ∑ t ∈ s, b t * ((orderOf χ : ℤ) - 2 * ((c * f t % orderOf χ : ℕ) : ℤ)) = 0 := by
  classical
  have hnpos : 0 < orderOf χ := PAG.Part185.orderOf_pos_chi χ
  have hmaps : ∀ t ∈ s, f t % orderOf χ ∈ Ico 1 (orderOf χ) := by
    intro t ht
    rw [mem_Ico]
    exact ⟨Nat.pos_of_ne_zero (fun h0 => hf t ht (Nat.dvd_of_mod_eq_zero h0)), Nat.mod_lt _ hnpos⟩
  set e : ℕ → ℤ := fun j => ∑ t ∈ s with f t % orderOf χ = j, b t with he
  -- 積を j ごとにまとめる
  have hprod : ∏ t ∈ s, (gaussSum (χ ^ f t) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b t
      = ∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ e j := by
    rw [← prod_fiberwise_of_maps_to hmaps]
    refine prod_congr rfl (fun j hj => ?_)
    rw [mem_Ico] at hj
    have hz : gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ) ≠ 0 :=
      z_ne_zero _ (pow_ne_one_of_lt_orderOf (by omega) hj.2) hψ
    rw [he, ← prod_zpow_const _ _ hz]
    refine prod_congr rfl (fun t ht => ?_)
    rw [mem_filter] at ht
    rw [← pow_mod_orderOf χ (f t), ht.2]
  -- 和も j ごとにまとめる
  have hsum : ∀ c : ℕ, ∑ t ∈ s, b t * ((orderOf χ : ℤ) - 2 * ((c * f t % orderOf χ : ℕ) : ℤ))
      = ∑ j ∈ Ico 1 (orderOf χ), e j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) := by
    intro c
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_congr rfl (fun j _ => ?_)
    rw [he, sum_mul]
    refine sum_congr rfl (fun t ht => ?_)
    rw [mem_filter] at ht
    rw [← Nat.mul_mod_mod c (f t) (orderOf χ), ht.2]
  rw [hprod, PAG.Part190.same_prime_root_iff χ hψ e]
  exact forall_congr' (fun c => imp_congr_right (fun _ => by rw [hsum c]))

/-! ### 2. 分数部分の恒等式 -/

omit hp in
/-- r < d なら (r + d x) mod (m d) = r + d (x mod m)。 -/
theorem add_mul_mod_mul (r d x m : ℕ) (hr : r < d) (hm : 0 < m) :
    (r + d * x) % (m * d) = r + d * (x % m) := by
  have hx := Nat.div_add_mod x m
  have h1 : x % m + 1 ≤ m := Nat.mod_lt x hm
  have h2 : d * (x % m + 1) ≤ d * m := Nat.mul_le_mul_left d h1
  rw [mul_add, mul_one] at h2
  have hlt : r + d * (x % m) < m * d := by rw [mul_comm m d]; omega
  conv_lhs => rw [← hx]
  rw [show r + d * (m * (x / m) + x % m) = (r + d * (x % m)) + (m * d) * (x / m) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

omit hp in
/-- c が m と互いに素なら Σ_{a<m} ((q + c a) mod m) = Σ_{b<m} b。 -/
theorem sum_affine_mod (m c q : ℕ) (hc : c.Coprime m) :
    ∑ a ∈ range m, (q + c * a) % m = ∑ b ∈ range m, b := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hinj : Set.InjOn (fun a => (q + c * a) % m) (range m) := by
    intro a ha a' ha' h
    simp only [coe_range, Set.mem_Iio] at ha ha'
    have h1 : c * a ≡ c * a' [MOD m] := Nat.ModEq.add_left_cancel' q h
    have h2 : a ≡ a' [MOD m] := Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.symm hc) h1
    exact Nat.ModEq.eq_of_lt_of_lt h2 ha ha'
  have himg : (range m).image (fun a => (q + c * a) % m) = range m := by
    apply eq_of_subset_of_card_le
    · intro b hb
      rw [mem_image] at hb
      obtain ⟨a, -, rfl⟩ := hb
      exact mem_range.mpr (Nat.mod_lt _ hm)
    · rw [card_image_of_injOn hinj]
  conv_rhs => rw [← himg]
  rw [sum_image hinj]

omit hp in
/-- **2. 分数部分の恒等式**：c が m d と互いに素なら
  Σ_{a<m} (c(k + d a) mod m d) = (c k m mod m d) + Σ_{1≤a<m} (c d a mod m d)。 -/
theorem frac_identity (m d k c : ℕ) (hm : 0 < m) (hd : 0 < d) (hc : c.Coprime (m * d)) :
    ∑ a ∈ range m, c * (k + d * a) % (m * d)
      = c * (k * m) % (m * d) + ∑ a ∈ Ico 1 m, c * (d * a) % (m * d) := by
  have hcm : c.Coprime m := Nat.Coprime.coprime_dvd_right (Dvd.intro d rfl) hc
  have hck : c * k = c * k % d + d * (c * k / d) := (Nat.mod_add_div (c * k) d).symm
  have hr : c * k % d < d := Nat.mod_lt _ hd
  have hL : ∀ a, c * (k + d * a) % (m * d) = c * k % d + d * ((c * k / d + c * a) % m) := by
    intro a
    rw [show c * (k + d * a) = c * k % d + d * (c * k / d + c * a) by
      rw [mul_add, mul_add, ← add_assoc, ← hck]; ring]
    exact add_mul_mod_mul _ d _ m hr hm
  have hM : c * (k * m) % (m * d) = m * (c * k % d) := by
    rw [show c * (k * m) = m * (c * k) by ring, Nat.mul_mod_mul_left]
  have hR : ∀ a, c * (d * a) % (m * d) = d * (c * a % m) := by
    intro a
    rw [show c * (d * a) = d * (c * a) by ring, show m * d = d * m by ring, Nat.mul_mod_mul_left]
  have hIco : ∑ a ∈ Ico 1 m, c * a % m = ∑ a ∈ range m, c * a % m := by
    rw [sum_range_eq_add_Ico _ hm]
    simp
  have hzero := sum_affine_mod m c 0 hcm
  simp only [zero_add] at hzero
  rw [sum_congr rfl (fun a _ => hL a), sum_congr rfl (fun a _ => hR a), hM, sum_add_distrib, sum_const,
    card_range, smul_eq_mul, ← mul_sum, ← mul_sum, sum_affine_mod m c _ hcm, hIco, hzero]

/-! ### 3. ハッセ・ダベンポート（1 の冪根を除いて） -/

/-- **3. ハッセ・ダベンポートの関係（1 の冪根を除いて）**：位数 n = m d の指標 χ、ψ′ = χ^d（位数 m）、
  χ^{km} ≠ 1 のとき、∏_{a=0}^{m−1} z(χ^k ψ′^a) / (z((χ^k)^m) ∏_{a=1}^{m−1} z(ψ′^a)) は 1 の冪根。 -/
theorem hasse_davenport_root (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (m d k : ℕ) (hmd : m * d = orderOf χ) (hk : ¬ orderOf χ ∣ k * m) :
    ∃ N : ℕ, 0 < N ∧
      ((∏ a ∈ range m, gaussSum (χ ^ k * (χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ)) /
        ((gaussSum ((χ ^ k) ^ m) ψ / ((Real.sqrt p : ℝ) : ℂ)) *
          ∏ a ∈ Ico 1 m, gaussSum ((χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ))) ^ N = 1 := by
  classical
  have hnpos : 0 < orderOf χ := PAG.Part185.orderOf_pos_chi χ
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hmd; omega)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at hmd; omega)
  -- 族：inl a ↦ k + d a（冪 +1）、inr 0 ↦ k m、inr a ↦ d a（冪 −1）
  set f : ℕ ⊕ ℕ → ℕ := fun t => Sum.elim (fun a => k + d * a)
    (fun a => if a = 0 then k * m else d * a) t with hf
  set b : ℕ ⊕ ℕ → ℤ := fun t => Sum.elim (fun _ => (1 : ℤ)) (fun _ => -1) t with hb
  set s : Finset (ℕ ⊕ ℕ) := (range m).disjSum (range m) with hs
  have hfn : ∀ t ∈ s, ¬ orderOf χ ∣ f t := by
    intro t ht
    rcases t with a | a
    · intro hdiv
      apply hk
      have : orderOf χ ∣ m * (k + d * a) := Dvd.dvd.mul_left hdiv m
      rw [show m * (k + d * a) = k * m + (m * d) * a by ring, hmd] at this
      exact (Nat.dvd_add_right (dvd_mul_right _ a)).mp (by rwa [add_comm] at this)
    · have ha : a < m := by simpa [hs] using ht
      simp only [hf, Sum.elim_inr]
      by_cases h0 : a = 0
      · rw [ite_eq_left h0]; exact hk
      · rw [ite_eq_right h0]
        intro hdiv
        have h1 : 0 < d * a := Nat.mul_pos hd (Nat.pos_of_ne_zero h0)
        have h2 : d * a < orderOf χ := by
          rw [← hmd, mul_comm m d]; exact Nat.mul_lt_mul_of_pos_left ha hd
        exact absurd (Nat.le_of_dvd h1 hdiv) (by omega)
  -- 族の積が目的の比
  have hden : ∏ a ∈ range m, gaussSum (χ ^ (if a = 0 then k * m else d * a)) ψ / ((Real.sqrt p : ℝ) : ℂ)
      = gaussSum ((χ ^ k) ^ m) ψ / ((Real.sqrt p : ℝ) : ℂ) *
          ∏ a ∈ Ico 1 m, gaussSum ((χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ) := by
    rw [prod_range_eq_mul_Ico _ hm, ite_eq_left (rfl : (0 : ℕ) = 0), ← pow_mul]
    congr 1
    refine prod_congr rfl (fun a ha => ?_)
    rw [ite_eq_right (by have := (mem_Ico.mp ha).1; omega), ← pow_mul]
  have hnum : ∏ a ∈ range m, gaussSum (χ ^ (k + d * a)) ψ / ((Real.sqrt p : ℝ) : ℂ)
      = ∏ a ∈ range m, gaussSum (χ ^ k * (χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ) := by
    refine prod_congr rfl (fun a _ => ?_)
    rw [← pow_mul, ← pow_add]
  have hprod : ∏ t ∈ s, (gaussSum (χ ^ f t) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b t
      = (∏ a ∈ range m, gaussSum (χ ^ k * (χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ)) /
        ((gaussSum ((χ ^ k) ^ m) ψ / ((Real.sqrt p : ℝ) : ℂ)) *
          ∏ a ∈ Ico 1 m, gaussSum ((χ ^ d) ^ a) ψ / ((Real.sqrt p : ℝ) : ℂ)) := by
    rw [hs, prod_disjSum]
    simp only [hf, hb, Sum.elim_inl, Sum.elim_inr, zpow_one, zpow_neg]
    rw [prod_inv_distrib, ← div_eq_mul_inv, hden, hnum]
  rw [← hprod, family_root_iff χ hψ s f hfn b]
  intro c hc
  have hid := frac_identity m d k c hm hd (by rw [hmd]; exact hc)
  rw [hmd] at hid
  have hidZ : (∑ a ∈ range m, ((c * (k + d * a) % orderOf χ : ℕ) : ℤ))
      = ((c * (k * m) % orderOf χ : ℕ) : ℤ) + ∑ a ∈ Ico 1 m, ((c * (d * a) % orderOf χ : ℕ) : ℤ) := by
    exact_mod_cast hid
  have hden2 : ∑ a ∈ range m,
      ((orderOf χ : ℤ) - 2 * (((c * if a = 0 then k * m else d * a) % orderOf χ : ℕ) : ℤ))
      = ((orderOf χ : ℤ) - 2 * ((c * (k * m) % orderOf χ : ℕ) : ℤ)) +
        ∑ a ∈ Ico 1 m, ((orderOf χ : ℤ) - 2 * ((c * (d * a) % orderOf χ : ℕ) : ℤ)) := by
    rw [sum_range_eq_add_Ico _ hm, ite_eq_left (rfl : (0 : ℕ) = 0)]
    congr 1
    refine sum_congr rfl (fun a ha => ?_)
    rw [ite_eq_right (by have := (mem_Ico.mp ha).1; omega)]
  have e1 : ∑ a ∈ range m, ((orderOf χ : ℤ) - 2 * ((c * (k + d * a) % orderOf χ : ℕ) : ℤ))
      = (m : ℤ) * orderOf χ - 2 * ∑ a ∈ range m, ((c * (k + d * a) % orderOf χ : ℕ) : ℤ) := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
  have e2 : ∑ a ∈ Ico 1 m, ((orderOf χ : ℤ) - 2 * ((c * (d * a) % orderOf χ : ℕ) : ℤ))
      = ((m : ℤ) - 1) * orderOf χ - 2 * ∑ a ∈ Ico 1 m, ((c * (d * a) % orderOf χ : ℕ) : ℤ) := by
    rw [sum_sub_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul, ← mul_sum,
      Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast; ring
  rw [hs, sum_disjSum]
  simp only [hf, hb, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul, sum_neg_distrib]
  rw [hden2, e1, e2, hidZ]
  ring

/-- **3b.** 鎖の記号（PAG184 の zOf、stdAddChar とディリクレ指標）での形。 -/
theorem hasse_davenport_root_chain (χ : DirichletCharacter ℂ p) (m d k : ℕ) (hmd : m * d = orderOf χ)
    (hk : ¬ orderOf χ ∣ k * m) :
    ∃ N : ℕ, 0 < N ∧
      ((∏ a ∈ range m, PAG.Part184.zOf (χ ^ k * (χ ^ d) ^ a)) /
        (PAG.Part184.zOf ((χ ^ k) ^ m) * ∏ a ∈ Ico 1 m, PAG.Part184.zOf ((χ ^ d) ^ a))) ^ N = 1 :=
  hasse_davenport_root χ (ZMod.isPrimitive_stdAddChar p) m d k hmd hk

end PAG.Part192

#print axioms PAG.Part192.prod_zpow_const
#print axioms PAG.Part192.z_ne_zero
#print axioms PAG.Part192.family_root_iff
#print axioms PAG.Part192.add_mul_mod_mul
#print axioms PAG.Part192.sum_affine_mod
#print axioms PAG.Part192.frac_identity
#print axioms PAG.Part192.hasse_davenport_root
#print axioms PAG.Part192.hasse_davenport_root_chain
