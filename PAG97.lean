/-
  PAG 2.0 Part 93（2026-10-19）— T_k のスペクトル（固有ベクトル・固有値・トレース）
  任意の素数、k = 原始ケット（双対殻 a）、λ = p^K/|S_a|、e_t(x) = e(xt)（加法指標）
  1. T_k e_t = 𝓕k(t)·e_t（加法指標が共通の固有ベクトル）
  2. t ∈ T_a なら |𝓕k(t)|² = λ（U_k の固有値は単位円上）、t ∉ T_a なら 𝓕k(t) = 0
  3. トレース: Σ_{t ∈ T_a} 𝓕k(t) = 0（U_k|V_a のトレースは 0）
  4. 冪のトレース: Σ_{t ∈ T_a} 𝓕k(t)^(n+1) = p^K · (k^{⋆(n+1)})(0)
-/
import PAG96

namespace PAG.Part97

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part89 PAG.Part90 PAG.Part95

variable {p : ℕ} [hp : Fact p.Prime]

/-- 加法指標 e_t。 -/
noncomputable def echar (K : ℕ) (t : ZMod (p ^ K)) : ZMod (p ^ K) → ℂ := fun x => stdAddChar (x * t)

/-- **固有ベクトル**: f ⋆ e_t = 𝓕f(t)·e_t（任意の f）。 -/
theorem conv_echar (K : ℕ) (f : ZMod (p ^ K) → ℂ) (t : ZMod (p ^ K)) :
    conv f (echar K t) = 𝓕 f t • echar K t := by
  funext x
  simp only [conv, echar, Pi.smul_apply, smul_eq_mul, dft_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [show (x - y) * t = -(y * t) + x * t by ring, AddChar.map_add_eq_mul]
  ring

/-- **固有値の大きさ**: t ∈ T_a なら |𝓕k(t)|² = λ、t ∉ T_a なら 𝓕k(t) = 0。 -/
theorem eigen_abs (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) (t : ZMod (p ^ K)) :
    (t ∈ Tset (p := p) K a → Complex.normSq (𝓕 k t) = (p : ℝ) ^ K / (sz p K a : ℝ)) ∧
    (t ∉ Tset (p := p) K a → 𝓕 k t = 0) := by
  obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hk
  rcases normSq_dft_ket_cases K w n h χ hχ t with ⟨h0e, h0⟩ | ⟨h1e, h1⟩
  · refine ⟨fun ht => ?_, fun _ => Complex.normSq_eq_zero.mp h0⟩
    have : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 := by simpa [Tset] using ht
    have h0' : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 0 := h0e
    rw [h0'] at this; exact absurd this zero_ne_one
  · refine ⟨fun _ => h1, fun ht => ?_⟩
    have h1' : 𝓕 (eps (p := p) K (K - (n + 1) - w)) t = 1 := h1e
    exact absurd (by simp [Tset, h1']) ht

/-- 台の外では消えるので、和は T_a 上の和に等しい。 -/
theorem sum_dft_Tset (K a : ℕ) (g : ZMod (p ^ K) → ℂ) (hg : ∀ t, t ∉ Tset (p := p) K a → 𝓕 g t = 0) :
    ∑ t ∈ Tset (p := p) K a, 𝓕 g t = (p ^ K : ℕ) * g 0 := by
  rw [← PAG.Part39.sum_dft g]
  refine (Finset.sum_subset (Finset.subset_univ _) (fun t _ ht => hg t ht)).trans rfl

/-- **トレース 0**: Σ_{t ∈ T_a} 𝓕k(t) = 0。 -/
theorem trace_zero (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    ∑ t ∈ Tset (p := p) K a, 𝓕 k t = 0 := by
  rw [sum_dft_Tset K a k (fun t ht => (eigen_abs K a k hk t).2 ht)]
  obtain ⟨w, n, h, χ, -, -, rfl⟩ := hk
  rw [PAG.Part49.ket_apply_zero K w (n + 1) (by omega) h χ, mul_zero]

/-- **冪のトレース**: Σ_{t ∈ T_a} 𝓕k(t)^(n+1) = p^K·(k ⋆ ⋯ ⋆ k)(0)（n+1 個）。 -/
theorem trace_pow (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) (n : ℕ) :
    ∑ t ∈ Tset (p := p) K a, 𝓕 k t ^ (n + 1) = (p ^ K : ℕ) * prodConv k (List.replicate n k) 0 := by
  have hd : ∀ t, 𝓕 (prodConv k (List.replicate n k)) t = 𝓕 k t ^ (n + 1) := by
    intro t
    rw [dft_prodConv, ← List.replicate_succ, List.map_replicate, List.prod_replicate]
  simp_rw [← hd]
  apply sum_dft_Tset
  intro t ht
  rw [hd, (eigen_abs K a k hk t).2 ht, zero_pow (by omega)]

end PAG.Part97

#print axioms PAG.Part97.conv_echar
#print axioms PAG.Part97.eigen_abs
#print axioms PAG.Part97.sum_dft_Tset
#print axioms PAG.Part97.trace_zero
#print axioms PAG.Part97.trace_pow
