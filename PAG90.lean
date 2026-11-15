/-
  PAG 2.0 Part 86（2026-10-19）— 多重積 k₁ ⋆ k₂ ⋆ ⋯ ⋆ k_n
  1. 同じ双対殻 a の原始ケットの多重積は V_a に入り、‖k₁ ⋆ ⋯ ⋆ k_n‖² = λ^(n−1)
  2. 双対殻の異なる二つの因子を含めば多重積は 0
  （任意の素数。Part 85 の部分等長性の繰り返しと、フーリエ側の積公式による）
-/
import PAG89

namespace PAG.Part90

open ZMod Finset PAG.Part15 PAG.Part19 PAG.Part21 PAG.Part41 PAG.Part89

variable {p : ℕ} [hp : Fact p.Prime]

/-- 多重積（右から順に畳み込む）: prodConv k [k₂, …, k_n] = k ⋆ (k₂ ⋆ (⋯ ⋆ k_n))。 -/
noncomputable def prodConv {N : ℕ} [NeZero N] (k : ZMod N → ℂ) : List (ZMod N → ℂ) → ZMod N → ℂ
  | [] => k
  | k' :: l => conv k (prodConv k' l)

/-- 双対殻 a の原始ケットであること。 -/
def KetDual (K a : ℕ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∃ w n : ℕ, ∃ h : w + (n + 1) ≤ K, ∃ χ : DirichletCharacter ℂ (p ^ (n + 1)), χ.IsPrimitive ∧
    K - (n + 1) - w = a ∧ f = ket K w (n + 1) h χ

theorem KetDual.le {K a : ℕ} {f : ZMod (p ^ K) → ℂ} (hf : KetDual (p := p) K a f) : a ≤ K := by
  obtain ⟨w, n, h, χ, -, ha, -⟩ := hf; omega

theorem KetDual.eps {K a : ℕ} {f : ZMod (p ^ K) → ℂ} (hf : KetDual (p := p) K a f) :
    conv (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) f = f := by
  obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hf
  rw [conv_comm]; exact PAG.Part58.ket_conv_eps_self K w n h χ hχ

theorem KetDual.norm {K a : ℕ} {f : ZMod (p ^ K) → ℂ} (hf : KetDual (p := p) K a f) :
    ∑ x, Complex.normSq (f x) = 1 := by
  obtain ⟨w, n, h, χ, hχ, -, rfl⟩ := hf
  exact PAG.Part39.norm_ket K w n h χ hχ

theorem KetDual.dft_zero {K a : ℕ} {f : ZMod (p ^ K) → ℂ} (hf : KetDual (p := p) K a f) (t : ZMod (p ^ K))
    (h0 : 𝓕 (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) t = 0) : 𝓕 f t = 0 := by
  obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hf
  exact PAG.Part79.dft_ket_eq_zero K w n h χ hχ t h0

/-- **多重積のノルム**: すべて双対殻 a なら V_a に入り、‖⋯‖² = λ^(l.length)。 -/
theorem prodConv_same_dual (K a : ℕ) (k : ZMod (p ^ K) → ℂ) (l : List (ZMod (p ^ K) → ℂ))
    (hk : KetDual (p := p) K a k) (hl : ∀ g ∈ l, KetDual (p := p) K a g) :
    conv (PAG.Part14.epsBall (PAG.Part28.Pavg (p := p) K) K a) (prodConv k l) = prodConv k l ∧
    ∑ x, Complex.normSq (prodConv k l x) = ((p : ℝ) ^ K / (sz p K a : ℝ)) ^ l.length := by
  induction l generalizing k with
  | nil => exact ⟨hk.eps, by rw [List.length_nil, pow_zero]; exact hk.norm⟩
  | cons k' l ih =>
    obtain ⟨he, hn⟩ := ih k' (hl k' List.mem_cons_self) (fun g hg => hl g (List.mem_cons_of_mem _ hg))
    simp only [prodConv]
    refine ⟨?_, ?_⟩
    · rw [← conv_assoc', hk.eps]
    · obtain ⟨w, n, h, χ, hχ, rfl, rfl⟩ := hk
      rw [norm_conv_eq_of_mem K w n h χ hχ _ he, hn, List.length_cons, pow_succ, mul_comm]

/-- フーリエ側の積公式。 -/
theorem dft_prodConv (K : ℕ) (k : ZMod (p ^ K) → ℂ) (l : List (ZMod (p ^ K) → ℂ)) (t : ZMod (p ^ K)) :
    𝓕 (prodConv k l) t = ((k :: l).map (fun g => 𝓕 g t)).prod := by
  induction l generalizing k with
  | nil => simp [prodConv]
  | cons k' l ih =>
    simp only [prodConv]
    rw [PAG.Part16.dft_conv, Pi.mul_apply, ih k']
    simp

/-- **双対殻の異なる因子を含めば多重積は 0**。 -/
theorem prodConv_diff_dual (K a b : ℕ) (hab : a ≠ b) (k : ZMod (p ^ K) → ℂ) (l : List (ZMod (p ^ K) → ℂ))
    (g₁ g₂ : ZMod (p ^ K) → ℂ) (h₁ : g₁ ∈ k :: l) (h₂ : g₂ ∈ k :: l)
    (hg₁ : KetDual (p := p) K a g₁) (hg₂ : KetDual (p := p) K b g₂) :
    prodConv k l = 0 := by
  apply (ZMod.dft (N := p ^ K) (E := ℂ)).injective
  rw [map_zero]
  funext t
  rw [dft_prodConv, Pi.zero_apply]
  apply List.prod_eq_zero
  rcases PAG.Part31.dft_eps_zero_or_one (p := p) K a hg₁.le t with h0 | h1
  · exact List.mem_map.mpr ⟨g₁, h₁, hg₁.dft_zero t h0⟩
  · have e := PAG.Part41.dft_eps_mul_eq_zero (p := p) K a b hg₁.le hg₂.le hab t
    rw [h1, one_mul] at e
    exact List.mem_map.mpr ⟨g₂, h₂, hg₂.dft_zero t e⟩

end PAG.Part90

#print axioms PAG.Part90.KetDual.le
#print axioms PAG.Part90.KetDual.eps
#print axioms PAG.Part90.KetDual.norm
#print axioms PAG.Part90.KetDual.dft_zero
#print axioms PAG.Part90.prodConv_same_dual
#print axioms PAG.Part90.dft_prodConv
#print axioms PAG.Part90.prodConv_diff_dual
