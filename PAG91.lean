/-
  PAG 2.0 Part 87（2026-10-19）— V_a 上の T_k の行列成分（ε_a 方向を含む）
  k を双対殻 a の原始ケット、λ = p^K/|S_a| とする。任意の素数で
  1. ‖ε_a‖² = 1/λ（ε̂_a = √λ·ε_a が単位ベクトル）
  2. ⟨ε_a, k'⟩ = 0（原始ケットは ε_a 方向と直交）
  3. 列 ε: T_k ε_a = k
  4. 行 ε: ⟨ε_a, T_k g⟩ = (k ⋆ g)(0)（任意の g）。とくに ⟨ε_a, T_k k''⟩ = [k'' = k̄]·χ(−1)（同じ殻・導手）
-/
import PAG90

namespace PAG.Part91

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part30 PAG.Part41 PAG.Part52 PAG.Part89 PAG.Part90

variable {p : ℕ} [hp : Fact p.Prime]

/-- **‖ε_a‖² = 1/λ**（双対殻 a の原始ケットが存在するとき）。 -/
theorem norm_eps (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    ∑ x, Complex.normSq (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a x)
      = (sz p K a : ℝ) / (p : ℝ) ^ K := by
  obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hk
  set e := PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w)
  have hN : ((p ^ K : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.out.ne_zero
  have hsz : (sz p K (K - (n + 1) - w) : ℝ) ≠ 0 := by
    have : 0 < sz p K (K - (n + 1) - w) := by
      unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
    exact_mod_cast this.ne'
  -- Σ_t |𝓕e(t)|² = #supp、Σ_t |𝓕k(t)|² = λ·#supp
  have he2 : ∀ t, Complex.normSq (𝓕 e t) = (if 𝓕 e t = 1 then 1 else 0) := by
    intro t
    rcases PAG.Part31.dft_eps_zero_or_one (p := p) K (K - (n + 1) - w) (by omega) t with h0 | h1
    · have h0' : 𝓕 e t = 0 := h0
      simp [h0']
    · have h1' : 𝓕 e t = 1 := h1
      simp [h1']
  have hk2 : ∀ t, Complex.normSq (𝓕 (ket K w (n + 1) h χ) t)
      = (p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ) * (if 𝓕 e t = 1 then 1 else 0) := by
    intro t
    rcases normSq_dft_ket_cases K w n h χ hχ t with ⟨h0e, h0⟩ | ⟨h1e, h1⟩
    · have h0' : 𝓕 e t = 0 := h0e
      rw [h0]; simp [h0']
    · have h1' : 𝓕 e t = 1 := h1e
      rw [h1]; simp [h1']
  have P1 := PAG.Part39.plancherel_normSq e
  have P2 := PAG.Part39.plancherel_normSq (ket K w (n + 1) h χ)
  rw [PAG.Part39.norm_ket K w n h χ hχ, mul_one] at P2
  simp_rw [he2] at P1
  simp_rw [hk2] at P2
  rw [← Finset.mul_sum] at P2
  set S := ∑ t, (if 𝓕 e t = 1 then (1 : ℝ) else 0)
  have hpK : (p : ℝ) ^ K ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hS : S = (sz p K (K - (n + 1) - w) : ℝ) := by
    have h2 := P2
    push_cast at h2
    rw [div_mul_eq_mul_div, div_eq_iff hsz] at h2
    exact mul_left_cancel₀ hpK h2
  rw [hS] at P1
  push_cast at P1
  rw [eq_div_iff hpK, mul_comm]
  exact P1.symm

/-- **ε_a 方向との内積は原点での値**: ⟨ε_a, F⟩ = (F ⋆ ε_a)(0)。 -/
theorem ip_eps (K a : ℕ) (F : ZMod (p ^ K) → ℂ) :
    ip (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) F
      = conv F (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) 0 := by
  rw [ip_eq_conv, PAG.Part31.tilde_eps]

/-- **原始ケットは ε_a 方向と直交**。 -/
theorem ip_eps_ket (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    ip (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) k = 0 := by
  rw [ip_eps, conv_comm, hk.eps]
  obtain ⟨w, n, h, χ, -, -, rfl⟩ := hk
  exact PAG.Part49.ket_apply_zero K w (n + 1) (by omega) h χ

/-- **列 ε**: T_k ε_a = k。 -/
theorem T_eps (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) :
    conv k (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) = k := by
  rw [conv_comm]; exact hk.eps

/-- **行 ε**: ⟨ε_a, T_k g⟩ = (k ⋆ g)(0)。 -/
theorem ip_eps_T (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (hk : KetDual (p := p) K a k) (g : ZMod (p ^ K) → ℂ) :
    ip (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) (conv k g) = conv k g 0 := by
  rw [ip_eps, PAG.Part80.conv_right_comm, T_eps K a k hk]

open Classical in
/-- **行 ε と原始ケットの列**: 同じ殻・同じ導手で ⟨ε_a, T_k k''⟩ = [χ'' = χ⁻¹]·χ(−1)。 -/
theorem ip_eps_T_ket (K w n : ℕ) (h : w + (n + 1) ≤ K) (χ χ'' : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) (hχ'' : χ''.IsPrimitive) :
    ip (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K (K - (n + 1) - w))
      (conv (ket K w (n + 1) h χ) (ket K w (n + 1) h χ'')) = if χ'' = χ⁻¹ then χ (-1) else 0 := by
  rw [ip_eps_T K _ _ ⟨w, n, h, χ, hχ, rfl, rfl⟩, PAG.Part81.conv_zero_same K w n h χ χ'' hχ hχ'']

end PAG.Part91

#print axioms PAG.Part91.norm_eps
#print axioms PAG.Part91.ip_eps
#print axioms PAG.Part91.ip_eps_ket
#print axioms PAG.Part91.T_eps
#print axioms PAG.Part91.ip_eps_T
#print axioms PAG.Part91.ip_eps_T_ket
