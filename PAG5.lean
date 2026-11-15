/-
  Projective Adelic Geometry 2.0 — formalization（PAG5.lean）
  対象:
    1. 殻番号 ℤ 上の 2 つの鏡映 R_global(v) = −v と R_chart(v) = L − v（L = K − c）
       - それぞれ対合
       - 合成 R_global ∘ R_chart は並進 v ↦ v − L、逆順は v ↦ v + L
       - 可換 ⇔ L = 0（すなわち c = K）
       - 合成の n 乗は並進 v ↦ v − nL（L ≠ 0 なら無限二面体群を生成）
    2. 殻の大きさの恒等式 Σ_{v=−K}^{K} |S_v| = p^K + p^{K−1}
       （|S_0| = φ(p^K)、0 < |v| < K で |S_v| = φ(p^{K−|v|})、|S_{±K}| = 1）
-/
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

open Finset

namespace PAG.Shells

/-! ## 1. 鏡映と並進 -/

/-- 大域射影反転の殻番号への作用 v ↦ −v。 -/
def Rg (v : ℤ) : ℤ := -v

/-- チャート内 Hartley 変換の殻番号への作用 v ↦ L − v（L = K − c）。 -/
def Rc (L v : ℤ) : ℤ := L - v

theorem Rg_invol (v : ℤ) : Rg (Rg v) = v := by simp [Rg]

theorem Rc_invol (L v : ℤ) : Rc L (Rc L v) = v := by simp [Rc]

/-- 合成は並進: R_global ∘ R_chart = (v ↦ v − L)。 -/
theorem Rg_comp_Rc (L v : ℤ) : Rg (Rc L v) = v - L := by simp [Rg, Rc]

/-- 逆順の合成は逆向きの並進: R_chart ∘ R_global = (v ↦ v + L)。 -/
theorem Rc_comp_Rg (L v : ℤ) : Rc L (Rg v) = v + L := by simp [Rg, Rc]; ring

/-- 2 つの鏡映が可換 ⇔ L = 0（c = K）。 -/
theorem comm_iff (L : ℤ) : (∀ v, Rg (Rc L v) = Rc L (Rg v)) ↔ L = 0 := by
  constructor
  · intro h
    have := h 0
    rw [Rg_comp_Rc, Rc_comp_Rg] at this
    linarith
  · intro hL v
    rw [Rg_comp_Rc, Rc_comp_Rg, hL]; ring

/-- 合成の n 回反復は並進 v ↦ v − nL。 -/
theorem iterate_comp (L : ℤ) (n : ℕ) (v : ℤ) :
    (fun w => Rg (Rc L w))^[n] v = v - n * L := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Rg_comp_Rc]
    push_cast; ring

/-- L ≠ 0 なら合成は位数無限（どの n ≥ 1 でも恒等写像にならない）。 -/
theorem comp_infinite_order {L : ℤ} (hL : L ≠ 0) (n : ℕ) (hn : 0 < n) :
    (fun w => Rg (Rc L w))^[n] ≠ id := by
  intro h
  have := congrFun h 0
  rw [iterate_comp] at this
  simp at this
  rcases this with h1 | h1
  · omega
  · exact hL h1

/-- 殻区間の保存: 0 ≤ v ≤ L なら 0 ≤ L − v ≤ L（チャート内鏡映は南半分の区間を保つ）。 -/
theorem Rc_maps_interval {L v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ L) : 0 ≤ Rc L v ∧ Rc L v ≤ L := by
  unfold Rc; constructor <;> omega

/-- 並進先: 0 ≤ v ≤ L なら −L ≤ v − L ≤ 0（南半分を北半分へ送る）。 -/
theorem comp_maps_south_to_north {L v : ℤ} (h0 : 0 ≤ v) (h1 : v ≤ L) :
    -L ≤ Rg (Rc L v) ∧ Rg (Rc L v) ≤ 0 := by
  rw [Rg_comp_Rc]; constructor <;> omega

/-! ## 2. 殻の大きさの和 -/

/-- Σ_{j=1}^{m} φ(p^j) + 1 = p^m（p 素数）。 -/
theorem sum_totient_prime_pow (p m : ℕ) (hp : p.Prime) :
    (∑ j ∈ range m, Nat.totient (p ^ (j + 1))) + 1 = p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, Nat.totient_prime_pow_succ hp]
    have h1 : 1 ≤ p := hp.one_lt.le
    calc (∑ j ∈ range m, Nat.totient (p ^ (j + 1))) + p ^ m * (p - 1) + 1
        = ((∑ j ∈ range m, Nat.totient (p ^ (j + 1))) + 1) + p ^ m * (p - 1) := by ring
      _ = p ^ m + p ^ m * (p - 1) := by rw [ih]
      _ = p ^ m * p := by
          rw [Nat.mul_sub, mul_one]
          have : p ^ m ≤ p ^ m * p := Nat.le_mul_of_pos_right _ (by omega)
          omega
      _ = p ^ (m + 1) := by rw [pow_succ]

/-- **殻の大きさの恒等式**（K = m + 1 ≥ 1）:
|S_0| + 2 Σ_{0<v<K} |S_v| + 2 |S_{±K}| = φ(p^K) + 2 Σ_{j=1}^{K−1} φ(p^j) + 2 = p^K + p^{K−1}。 -/
theorem shell_count (p m : ℕ) (hp : p.Prime) :
    Nat.totient (p ^ (m + 1)) + 2 * (∑ j ∈ range m, Nat.totient (p ^ (j + 1))) + 2
      = p ^ (m + 1) + p ^ m := by
  have hs := sum_totient_prime_pow p m hp
  rw [Nat.totient_prime_pow_succ hp]
  have h1 : 1 ≤ p := hp.one_lt.le
  have hS : (∑ j ∈ range m, Nat.totient (p ^ (j + 1))) = p ^ m - 1 := by omega
  have hpm : 1 ≤ p ^ m := Nat.one_le_pow _ _ (by omega)
  rw [hS, pow_succ]
  have e : p ^ m * (p - 1) + p ^ m = p ^ m * p := by
    rw [Nat.mul_sub, mul_one]
    have : p ^ m ≤ p ^ m * p := Nat.le_mul_of_pos_right _ (by omega)
    omega
  omega

end PAG.Shells

#print axioms PAG.Shells.Rg_invol
#print axioms PAG.Shells.Rc_invol
#print axioms PAG.Shells.Rg_comp_Rc
#print axioms PAG.Shells.Rc_comp_Rg
#print axioms PAG.Shells.comm_iff
#print axioms PAG.Shells.iterate_comp
#print axioms PAG.Shells.comp_infinite_order
#print axioms PAG.Shells.Rc_maps_interval
#print axioms PAG.Shells.comp_maps_south_to_north
#print axioms PAG.Shells.sum_totient_prime_pow
#print axioms PAG.Shells.shell_count
