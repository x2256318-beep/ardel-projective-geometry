/-
  Projective Adelic Geometry 2.0, Part 2 — formalization（PAG6.lean）
  動径セクター（c = 0）の Hartley 変換の対角和と、ルジャンドルセクターとの「偶奇シーソー」。

  記号: c_v(v) は p^{K/2}·⟨e_v|F_0|e_v⟩（Ramanujan 和）で、0 ≤ v ≤ K について
    c_K(K) = 1、K ≤ 2v なら φ(p^{K−v})、2v + 1 = K なら −p^{K−v−1}、それ以外 0。
  （この式と作用素のトレースとの対応は研究ノートの命題 2.4 で、Lean ではなく紙の上で示している。）
  j = K − v と置き換えた形 d_j でも書き、両者の和が等しいことを証明する。
-/
import PAG5

open Finset

namespace PAG.Seesaw

/-- c_v(v)（v は殻番号 0 ≤ v ≤ K）。 -/
def cv (p K v : ℕ) : ℤ :=
  if v = K then 1
  else if K ≤ 2 * v then (Nat.totient (p ^ (K - v)) : ℤ)
  else if 2 * v + 1 = K then -((p : ℤ) ^ (K - v - 1))
  else 0

/-- j = K − v での表示。 -/
def dj (p K j : ℕ) : ℤ :=
  if j = 0 then 1
  else if 2 * j ≤ K then (Nat.totient (p ^ j) : ℤ)
  else if 2 * j = K + 1 then -((p : ℤ) ^ (j - 1))
  else 0

/-- 動径の対角和 D(K) = Σ_{v=0}^{K} c_v(v)。 -/
def D (p K : ℕ) : ℤ := ∑ v ∈ range (K + 1), cv p K v

/-- 添字の付け替え v = K − j。 -/
theorem D_eq_sum_dj (p K : ℕ) : D p K = ∑ j ∈ range (K + 1), dj p K j := by
  unfold D
  rw [← sum_range_reflect (fun v => cv p K v) (K + 1)]
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hj)
  simp only [Nat.add_sub_cancel]
  unfold cv dj
  have e1 : K - (K - j) = j := Nat.sub_sub_self hj
  by_cases h0 : j = 0
  · subst h0; simp
  · rw [ite_eq_right (by omega), ite_eq_right h0]
    by_cases h1 : 2 * j ≤ K
    · rw [ite_eq_left (by omega), ite_eq_left h1, e1]
    · rw [ite_eq_right (by omega), ite_eq_right h1]
      by_cases h2 : 2 * j = K + 1
      · rw [ite_eq_left (by omega), ite_eq_left h2]
        congr 2; omega
      · rw [ite_eq_right (by omega), ite_eq_right h2]

/-- Σ_{i<m} φ(p^{i+1}) = p^m − 1（整数で）。 -/
theorem sum_totient_int (p m : ℕ) (hp : p.Prime) :
    (∑ i ∈ range m, (Nat.totient (p ^ (i + 1)) : ℤ)) = (p : ℤ) ^ m - 1 := by
  have h := PAG.Shells.sum_totient_prime_pow p m hp
  have h' : ((∑ i ∈ range m, Nat.totient (p ^ (i + 1)) : ℕ) : ℤ) + 1 = (p : ℤ) ^ m := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- 内側の和: Σ_{j<m+1} d_j = p^m（2m ≤ K のとき、j ≤ m の項はすべて φ(p^j)、j = 0 は 1）。 -/
theorem inner_sum (p K m : ℕ) (hp : p.Prime) (hm : 2 * m ≤ K) :
    (∑ j ∈ range (m + 1), dj p K j) = (p : ℤ) ^ m := by
  rw [sum_range_succ']
  have : ∀ i ∈ range m, dj p K (i + 1) = (Nat.totient (p ^ (i + 1)) : ℤ) := by
    intro i hi
    have := mem_range.mp hi
    unfold dj
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [sum_congr rfl this, sum_totient_int p m hp]
  simp [dj]

/-- **K = 2m（偶数）**: 動径の対角和は p^m（負の Ramanujan 項は現れない）。 -/
theorem D_even (p m : ℕ) (hp : p.Prime) : D p (2 * m) = (p : ℤ) ^ m := by
  rw [D_eq_sum_dj, ← sum_range_add_sum_Ico _ (show m + 1 ≤ 2 * m + 1 by omega),
    inner_sum p (2 * m) m hp le_rfl]
  have : ∑ j ∈ Ico (m + 1) (2 * m + 1), dj p (2 * m) j = 0 := by
    refine sum_eq_zero fun j hj => ?_
    have := mem_Ico.mp hj
    unfold dj
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [this, add_zero]

/-- **K = 2m + 1（奇数）**: v = m の負の項 −p^m が内側の和 p^m を打ち消し、対角和は 0。 -/
theorem D_odd (p m : ℕ) (hp : p.Prime) : D p (2 * m + 1) = 0 := by
  rw [D_eq_sum_dj, ← sum_range_add_sum_Ico _ (show m + 1 ≤ 2 * m + 1 + 1 by omega),
    inner_sum p (2 * m + 1) m hp (by omega)]
  have : ∑ j ∈ Ico (m + 1) (2 * m + 1 + 1), dj p (2 * m + 1) j = -((p : ℤ) ^ m) := by
    rw [sum_eq_single (m + 1)]
    · unfold dj
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      simp
    · intro j hj hne
      have := mem_Ico.mp hj
      unfold dj
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · intro h; exact absurd (mem_Ico.mpr ⟨le_rfl, by omega⟩) h
  rw [this]; ring

/-- ルジャンドルセクターの不動殻（H_0 の v ↦ (K−1) − v の不動点）の個数。 -/
def legFixed (K : ℕ) : ℕ := ((range K).filter (fun v => v + v + 1 = K)).card

/-- 不動殻は K が奇数のときちょうど 1 個、偶数のとき 0 個。 -/
theorem legFixed_eq (K : ℕ) : legFixed K = if K % 2 = 1 then 1 else 0 := by
  unfold legFixed
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨K / 2, ?_⟩
    ext v; simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨_, hv⟩; omega
    · intro hv; subst hv; constructor <;> omega
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro v _; omega

/-- **偶奇シーソー（整数版）**: K = 2m なら (D, 不動殻) = (p^m, 0)、K = 2m+1 なら (0, 1)。 -/
theorem seesaw (p K : ℕ) (hp : p.Prime) :
    (K % 2 = 0 → D p K = (p : ℤ) ^ (K / 2) ∧ legFixed K = 0) ∧
    (K % 2 = 1 → D p K = 0 ∧ legFixed K = 1) := by
  constructor
  · intro h
    obtain ⟨m, rfl⟩ : ∃ m, K = 2 * m := ⟨K / 2, by omega⟩
    refine ⟨?_, ?_⟩
    · rw [D_even p m hp]; congr 1; omega
    · rw [legFixed_eq]; simp
  · intro h
    obtain ⟨m, rfl⟩ : ∃ m, K = 2 * m + 1 := ⟨K / 2, by omega⟩
    exact ⟨D_odd p m hp, by rw [legFixed_eq]; simp⟩

/-- **偶奇シーソー（トレース版）**: Tr(H_0|_{c=0}) + Tr(H_0|_{ルジャンドル}) = D(K)/p^{K/2} + #不動殻 = 1。
（ルジャンドル指標のルート数は 1 なので、不動殻 1 個はトレース 1 を与える。） -/
theorem trace_seesaw (p K : ℕ) (hp : p.Prime) :
    (D p K : ℝ) / (Real.sqrt p) ^ K + (legFixed K : ℝ) = 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rcases Nat.even_or_odd K with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hK : K = 2 * m := by omega
    subst hK
    rw [D_even p m hp, legFixed_eq]
    have hs : (Real.sqrt p) ^ (2 * m) = (p : ℝ) ^ m := by
      rw [pow_mul, Real.sq_sqrt hp0.le]
    rw [hs]
    have : (2 * m) % 2 = 0 := by omega
    simp only [this]
    push_cast
    rw [div_self (pow_ne_zero _ hp0.ne')]
    norm_num
  · subst hm
    rw [D_odd p m hp, legFixed_eq]
    have : (2 * m + 1) % 2 = 1 := by omega
    simp [this]

end PAG.Seesaw

#print axioms PAG.Seesaw.D_eq_sum_dj
#print axioms PAG.Seesaw.sum_totient_int
#print axioms PAG.Seesaw.inner_sum
#print axioms PAG.Seesaw.D_even
#print axioms PAG.Seesaw.D_odd
#print axioms PAG.Seesaw.legFixed_eq
#print axioms PAG.Seesaw.seesaw
#print axioms PAG.Seesaw.trace_seesaw
