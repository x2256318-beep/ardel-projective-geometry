/-
  PAG 2.0 Part 118（2026-10-20）— 積のケットの特性多項式の閉じた形
  「根が F(t₀) μ_o に一様に分布する」性質 Unif について
  1. Unif は定数倍で保たれる
  2. Unif T F t₀ o ⇒ Unif T F^k t₀ (o / gcd(o, k))（ファイバーの大きさは gcd 個ずつ重なる）
  3. charpoly((k₁⊗k₂)⋆|V) = (X^ℓ − (z₁z₂)^ℓ)^{d₁d₂/ℓ}、ℓ = lcm(ord χ₁, ord χ₂)、z_i = 𝓕k_i(t_i⁰)
-/
import PAG121

namespace PAG.Part122

open ZMod Finset Polynomial PAG.Part116 PAG.Part121

section Unif

variable {α : Type*} [DecidableEq α]

/-- 根が F(t₀) μ_o に一様に分布する。 -/
def Unif (T : Finset α) (F : α → ℂ) (t₀ : α) (o : ℕ) : Prop :=
  t₀ ∈ T ∧ 0 < o ∧ F t₀ ≠ 0 ∧ (∀ t ∈ T, (F t / F t₀) ^ o = 1) ∧
    (∀ ξ : ℂ, ξ ^ o = 1 → o * (T.filter (fun t => F t = F t₀ * ξ)).card = T.card)

theorem closed_of_unif {T : Finset α} {F : α → ℂ} {t₀ : α} {o : ℕ} (h : Unif T F t₀ o) :
    ∏ t ∈ T, (X - C (F t)) = (X ^ o - C (F t₀ ^ o)) ^ (T.card / o) :=
  prod_closed T F t₀ o h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

omit [DecidableEq α] in
theorem dvd_card {T : Finset α} {F : α → ℂ} {t₀ : α} {o : ℕ} (h : Unif T F t₀ o) : o ∣ T.card :=
  ⟨_, (h.2.2.2.2 1 (one_pow _)).symm⟩

omit [DecidableEq α] in
/-- **1. 定数倍**。 -/
theorem unif_smul {T : Finset α} {F : α → ℂ} {t₀ : α} {o : ℕ} (h : Unif T F t₀ o) (a : ℂ) (ha : a ≠ 0) :
    Unif T (fun t => a * F t) t₀ o := by
  obtain ⟨h0, ho, hF0, hpow, hfib⟩ := h
  refine ⟨h0, ho, mul_ne_zero ha hF0, fun t ht => ?_, fun ξ hξ => ?_⟩
  · simp only; rw [mul_div_mul_left _ _ ha]; exact hpow t ht
  · rw [← hfib ξ hξ]
    congr 2
    apply Finset.filter_congr
    intro t _
    rw [mul_assoc]
    exact ⟨fun e => mul_left_cancel₀ ha e, fun e => by simp only; rw [e]⟩

/-- 剰余類の数え上げ: #{j < o' g : j % o' = r} = g（r < o'）。 -/
theorem card_mod_eq (o' g r : ℕ) (hr : r < o') :
    ((range (o' * g)).filter (fun j => j % o' = r)).card = g := by
  have key : (range g).card = ((range (o' * g)).filter (fun j => j % o' = r)).card := by
    refine Finset.card_nbij' (fun i => r + o' * i) (fun j => j / o') ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi ⊢
      refine ⟨?_, ?_⟩
      · nlinarith
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    · intro j hj
      simp only [Finset.coe_range, Set.mem_Iio, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj ⊢
      exact Nat.div_lt_of_lt_mul hj.1
    · intro i _
      simp only
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hr, zero_add]
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
      simp only
      rw [← hj.2]; exact Nat.mod_add_div j o'
  rw [← key, Finset.card_range]

/-- **2. 冪**: Unif T F t₀ o ⇒ Unif T F^k t₀ (o / gcd(o,k))。 -/
theorem unif_pow {T : Finset α} {F : α → ℂ} {t₀ : α} {o : ℕ} (h : Unif T F t₀ o) (k : ℕ) :
    Unif T (fun t => F t ^ k) t₀ (o / Nat.gcd o k) := by
  classical
  obtain ⟨h0, ho, hF0, hpow, hfib⟩ := h
  set g := Nat.gcd o k
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ ho
  set o' := o / g
  have hoo : o' * g = o := Nat.div_mul_cancel (Nat.gcd_dvd_left o k)
  have ho' : 0 < o' := Nat.div_pos (Nat.gcd_le_left _ ho) hg
  have hkg : k * o' = o * (k / g) := by
    simp only [o']
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left o k), ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right o k), mul_comm]
  refine ⟨h0, ho', pow_ne_zero _ hF0, fun t ht => ?_, fun ξ hξ => ?_⟩
  · simp only
    rw [← div_pow, ← pow_mul, hkg, pow_mul, hpow t ht, one_pow]
  -- ファイバー
  have : NeZero o := ⟨ho.ne'⟩
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / o)
  have hω : IsPrimitiveRoot ω o := Complex.isPrimitiveRoot_exp o ho.ne'
  have hex : ∀ t ∈ T, ∃ j < o, ω ^ j = F t / F t₀ := fun t ht => hω.eq_pow_of_pow_eq_one (hpow t ht)
  let jf : α → ℕ := fun t => if ht : t ∈ T then Classical.choose (hex t ht) else 0
  have hjf : ∀ t ∈ T, jf t < o ∧ F t = F t₀ * ω ^ jf t := by
    intro t ht
    have hs := Classical.choose_spec (hex t ht)
    simp only [jf, ht, ↓reduceDIte]
    refine ⟨hs.1, ?_⟩
    rw [hs.2]; field_simp
  have hmaps : ∀ t ∈ T, jf t ∈ range o := fun t ht => mem_range.mpr (hjf t ht).1
  -- ω^k は原始 o' 乗根
  have hη : IsPrimitiveRoot (ω ^ k) o' := hω.pow_div_gcd k hg.ne'
  have : NeZero o' := ⟨ho'.ne'⟩
  obtain ⟨r, hr, hrξ⟩ := hη.eq_pow_of_pow_eq_one hξ
  have hfin : IsOfFinOrder (ω ^ k) := isOfFinOrder_iff_pow_eq_one.mpr ⟨o', ho', hη.pow_eq_one⟩
  have hord : orderOf (ω ^ k) = o' := hη.eq_orderOf.symm
  -- 条件の言い換え
  have hcond : ∀ t ∈ T, (F t ^ k = F t₀ ^ k * ξ ↔ jf t % o' = r) := by
    intro t ht
    rw [(hjf t ht).2, mul_pow, ← pow_mul, mul_comm (jf t) k, pow_mul]
    constructor
    · intro e
      have e' : (ω ^ k) ^ jf t = (ω ^ k) ^ r := by rw [hrξ]; exact mul_left_cancel₀ (pow_ne_zero _ hF0) e
      have := hfin.pow_inj_mod.mp e'
      rw [hord, Nat.mod_eq_of_lt hr] at this
      exact this
    · intro e
      rw [← hrξ]
      congr 1
      apply hfin.pow_inj_mod.mpr
      rw [hord, e, Nat.mod_eq_of_lt hr]
  have hfilt : T.filter (fun t => F t ^ k = F t₀ ^ k * ξ) = T.filter (fun t => jf t % o' = r) :=
    Finset.filter_congr hcond
  simp only
  rw [hfilt]
  -- ファイバーを j ごとに分ける
  have hsplit : (T.filter (fun t => jf t % o' = r)).card
      = ∑ j ∈ (range o).filter (fun j => j % o' = r), (T.filter (fun t => jf t = j)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range]
      constructor
      · rintro ⟨ht, hr'⟩; exact ⟨jf t, ⟨(hjf t ht).1, hr'⟩, ht, rfl⟩
      · rintro ⟨j, ⟨_, hj⟩, ht, rfl⟩; exact ⟨ht, hj⟩
    · intro i _ j _ hij
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro t hi hj
      exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)
  have hjfib : ∀ j ∈ range o, o * (T.filter (fun t => jf t = j)).card = T.card := by
    intro j hj
    rw [← hfib (ω ^ j) (by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow])]
    congr 2
    apply Finset.filter_congr
    intro t ht
    constructor
    · intro e; rw [← e]; exact (hjf t ht).2
    · intro e
      have e2 : ω ^ jf t = ω ^ j := by
        have := (hjf t ht).2; rw [this] at e; exact mul_left_cancel₀ hF0 e
      exact hω.pow_inj (hjf t ht).1 (mem_range.mp hj) e2
  have hcnt : ∀ j ∈ (range o).filter (fun j => j % o' = r), (T.filter (fun t => jf t = j)).card = T.card / o := by
    intro j hj
    have := hjfib j (Finset.mem_filter.mp hj).1
    rw [← this, Nat.mul_div_cancel_left _ ho]
  have hJ : ((range o).filter (fun j => j % o' = r)).card = g := by
    rw [← hoo]; exact card_mod_eq o' g r hr
  have hdvd : o ∣ T.card := ⟨_, (hfib 1 (one_pow _)).symm⟩
  rw [hsplit, Finset.sum_congr rfl hcnt, Finset.sum_const, smul_eq_mul, hJ]
  calc o' * (g * (T.card / o)) = (o' * g) * (T.card / o) := by ring
    _ = T.card := by rw [hoo, Nat.mul_div_cancel' hdvd]

end Unif

/-! ## 3. ケットへの適用 -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part95

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

theorem ket_unif {p : ℕ} [Fact p.Prime] (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (t₀ : ZMod (p ^ K)) (ht₀ : t₀ ∈ Tset (p := p) K (K - (n + 1) - w)) :
    Unif (Tset (p := p) K (K - (n + 1) - w)) (fun t => 𝓕 (ket K w (n + 1) h χ) t) t₀ (orderOf χ) := by
  obtain ⟨hF0, hpow, hfib⟩ := ket_root_facts K w n h χ hχ t₀ ht₀
  exact ⟨ht₀, orderOf_pos χ, hF0, hpow, hfib⟩

theorem unif_ne_zero {α : Type*} {T : Finset α} {F : α → ℂ} {t₀ : α} {o : ℕ} (h : Unif T F t₀ o)
    (t : α) (ht : t ∈ T) : F t ≠ 0 := by
  intro h0
  have := h.2.2.2.1 t ht
  rw [h0, zero_div, zero_pow h.2.1.ne'] at this
  exact zero_ne_one this

/-- **3. 積のケットの特性多項式の閉じた形**。 -/
theorem charpoly_T12_closed (K L w₁ c₁ w₂ c₂ : ℕ) (h₁ : w₁ + (c₁ + 1) ≤ K) (h₂ : w₂ + (c₂ + 1) ≤ L)
    (χ₁ : DirichletCharacter ℂ (p ^ (c₁ + 1))) (χ₂ : DirichletCharacter ℂ (q ^ (c₂ + 1)))
    (hχ₁ : χ₁.IsPrimitive) (hχ₂ : χ₂.IsPrimitive)
    (t₁ : ZMod (p ^ K)) (ht₁ : t₁ ∈ Tset (p := p) K (K - (c₁ + 1) - w₁))
    (t₂ : ZMod (q ^ L)) (ht₂ : t₂ ∈ Tset (p := q) L (L - (c₂ + 1) - w₂)) :
    (T12 (p := p) (q := q) K L (K - (c₁ + 1) - w₁) (L - (c₂ + 1) - w₂) (by omega) (by omega)
        (ket K w₁ (c₁ + 1) h₁ χ₁) (ket L w₂ (c₂ + 1) h₂ χ₂)).charpoly
      = (X ^ Nat.lcm (orderOf χ₁) (orderOf χ₂)
          - C ((𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) t₁ * 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) t₂) ^ Nat.lcm (orderOf χ₁) (orderOf χ₂)))
        ^ (sz p K (K - (c₁ + 1) - w₁) * sz q L (L - (c₂ + 1) - w₂) / Nat.lcm (orderOf χ₁) (orderOf χ₂)) := by
  classical
  set T₁ := Tset (p := p) K (K - (c₁ + 1) - w₁)
  set T₂ := Tset (p := q) L (L - (c₂ + 1) - w₂)
  set F₁ := fun s => 𝓕 (ket K w₁ (c₁ + 1) h₁ χ₁) s
  set F₂ := fun t => 𝓕 (ket L w₂ (c₂ + 1) h₂ χ₂) t
  set o₁ := orderOf χ₁
  set o₂ := orderOf χ₂
  have hU₁ := ket_unif K w₁ c₁ h₁ χ₁ hχ₁ t₁ ht₁
  have hU₂ := ket_unif L w₂ c₂ h₂ χ₂ hχ₂ t₂ ht₂
  have hd₁ : T₁.card = sz p K (K - (c₁ + 1) - w₁) := card_Tset K _ _ ⟨w₁, c₁, h₁, χ₁, hχ₁, rfl, rfl⟩
  have hd₂ : T₂.card = sz q L (L - (c₂ + 1) - w₂) := card_Tset L _ _ ⟨w₂, c₂, h₂, χ₂, hχ₂, rfl, rfl⟩
  rw [charpoly_T12 K L w₁ c₁ w₂ c₂ h₁ h₂ χ₁ χ₂ hχ₁ hχ₂]
  -- 内側
  have hinner : ∀ s ∈ T₁, ∏ t ∈ T₂, (X - C (F₁ s * F₂ t)) = (X ^ o₂ - C ((F₁ s * F₂ t₂) ^ o₂)) ^ (T₂.card / o₂) :=
    fun s hs => closed_of_unif (unif_smul hU₂ (F₁ s) (unif_ne_zero hU₁ s hs))
  show ∏ s ∈ T₁, ∏ t ∈ T₂, (X - C (F₁ s * F₂ t)) = _
  rw [Finset.prod_congr rfl hinner, Finset.prod_pow]
  -- 外側: X^{o₂} への代入
  set g := Nat.gcd o₁ o₂
  set o' := o₁ / g
  have hG : Unif T₁ (fun s => F₂ t₂ ^ o₂ * F₁ s ^ o₂) t₁ o' :=
    unif_smul (unif_pow hU₁ o₂) _ (pow_ne_zero _ (unif_ne_zero hU₂ t₂ ht₂))
  have hcomp : ∏ s ∈ T₁, (X ^ o₂ - C ((F₁ s * F₂ t₂) ^ o₂))
      = (∏ s ∈ T₁, (X - C (F₂ t₂ ^ o₂ * F₁ s ^ o₂))).comp (X ^ o₂) := by
    rw [Polynomial.prod_comp]
    apply Finset.prod_congr rfl; intro s _
    rw [sub_comp, X_comp, C_comp, mul_pow, mul_comm]
  rw [hcomp, closed_of_unif hG]
  simp only [pow_comp, sub_comp, X_comp, C_comp]
  have hl : o₂ * o' = Nat.lcm o₁ o₂ := by
    simp only [o', g, Nat.lcm]
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left o₁ o₂), mul_comm]
  have hc : (F₂ t₂ ^ o₂ * F₁ t₁ ^ o₂) ^ o' = (F₁ t₁ * F₂ t₂) ^ Nat.lcm o₁ o₂ := by
    rw [← hl, ← mul_pow, pow_mul, mul_comm]
  have h1 : o' ∣ T₁.card := dvd_card hG
  have h2 : o₂ ∣ T₂.card := dvd_card hU₂
  rw [show ((X : ℂ[X]) ^ o₂) ^ o' = X ^ (o₂ * o') from (pow_mul X o₂ o').symm, hl, hc, ← pow_mul]
  rw [Nat.div_mul_div_comm h1 h2, hd₁, hd₂, mul_comm o' o₂, hl]

end Ket

end PAG.Part122

#print axioms PAG.Part122.closed_of_unif
#print axioms PAG.Part122.dvd_card
#print axioms PAG.Part122.unif_smul
#print axioms PAG.Part122.card_mod_eq
#print axioms PAG.Part122.unif_pow
#print axioms PAG.Part122.ket_unif
#print axioms PAG.Part122.unif_ne_zero
#print axioms PAG.Part122.charpoly_T12_closed
