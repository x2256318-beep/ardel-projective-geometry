/-
  PAG 2.0 Part 105（2026-10-19）— 積構造の完成: 固定 ⟺ 切り口の条件、三つ以上の因子への帰納
  1. 一般の有限加法群での結合律 (f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)
  2. ε₁, ε₂ がべき等なら (ε₁ ⊗ ε₂) ⋆ g = g ⟺ 切り口が両方とも固定される（PAG108.tens_fix の逆）
  3. 等長性が積で閉じる: (e₁ ⊗ e₂, k₁ ⊗ k₂) が再び「V 上で λ₁λ₂ 倍の等長」の仮定を満たす
  4. 系: 三つの因子で λ₁λ₂λ₃（帰納の一段）
  5. 一般の互いに素な m, n での中国剰余の持ち上げ
-/
import PAG108

namespace PAG.Part109

open Finset PAG.Part15 PAG.Part108

section Generic

variable {G H I : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] [AddCommGroup I] [Fintype I]

/-- **1. 結合律**（一般の有限加法群）。 -/
theorem conv_assoc_gen (f g h : G → ℂ) : conv (conv f g) h = conv f (conv g h) := by
  funext x
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro z _
  exact Fintype.sum_equiv (Equiv.subRight z) _ _ (fun t => by
    simp only [Equiv.subRight_apply]; rw [sub_sub_sub_cancel_right]; ring)

/-- 切り口による表示（順序を入れ替えたもの）。 -/
theorem conv_tens_apply' (k₁ : G → ℂ) (k₂ : H → ℂ) (g : G × H → ℂ) (x : G) (y : H) :
    conv (tens k₁ k₂) g (x, y) = conv k₂ (fun y' => conv k₁ (fun x' => g (x', y')) x) y := by
  simp only [conv, tens, Fintype.sum_prod_type, Prod.mk_sub_mk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro y' _; apply sum_congr rfl; intro x' _; ring

/-- **2. 固定 ⟺ 切り口の条件**（ε₁, ε₂ はべき等）。 -/
theorem tens_fix_iff (e₁ : G → ℂ) (e₂ : H → ℂ) (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂)
    (g : G × H → ℂ) :
    conv (tens e₁ e₂) g = g ↔
      (∀ y, conv e₁ (fun x => g (x, y)) = fun x => g (x, y)) ∧
      (∀ x, conv e₂ (fun y => g (x, y)) = fun y => g (x, y)) := by
  constructor
  · intro hg
    constructor
    · intro y
      have e : (fun x => g (x, y)) = conv e₁ (fun x' => conv e₂ (fun y' => g (x', y')) y) := by
        funext x; rw [← conv_tens_apply, hg]
      rw [e, ← conv_assoc_gen, h₁]
    · intro x
      have e : (fun y => g (x, y)) = conv e₂ (fun y' => conv e₁ (fun x' => g (x', y')) x) := by
        funext y; rw [← conv_tens_apply', hg]
      rw [e, ← conv_assoc_gen, h₂]
  · rintro ⟨h₁', h₂'⟩
    exact tens_fix e₁ e₂ g h₁' h₂'

/-- テンソルのべき等性。 -/
theorem tens_idem (e₁ : G → ℂ) (e₂ : H → ℂ) (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂) :
    conv (tens e₁ e₂) (tens e₁ e₂) = tens e₁ e₂ := by
  rw [conv_tens, h₁, h₂]

/-- 「e で固定される関数の上で k は λ 倍の等長」。 -/
def IsoOn {X : Type*} [AddCommGroup X] [Fintype X] (e k : X → ℂ) (l : ℝ) : Prop :=
  ∀ f, conv e f = f → ∑ x, Complex.normSq (conv k f x) = l * ∑ x, Complex.normSq (f x)

/-- **3. 等長性は積で閉じる**。 -/
theorem isoOn_tens (e₁ k₁ : G → ℂ) (e₂ k₂ : H → ℂ) (l₁ l₂ : ℝ)
    (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂)
    (hk₁ : IsoOn e₁ k₁ l₁) (hk₂ : IsoOn e₂ k₂ l₂) :
    IsoOn (tens e₁ e₂) (tens k₁ k₂) (l₁ * l₂) := by
  intro g hg
  obtain ⟨a, b⟩ := (tens_fix_iff e₁ e₂ h₁ h₂ g).mp hg
  exact norm_conv_tens e₁ k₁ e₂ k₂ l₁ l₂ hk₁ hk₂ g a b

/-- **4. 三つの因子**: λ₁λ₂λ₃。 -/
theorem isoOn_tens3 (e₁ k₁ : G → ℂ) (e₂ k₂ : H → ℂ) (e₃ k₃ : I → ℂ) (l₁ l₂ l₃ : ℝ)
    (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂) (h₃ : conv e₃ e₃ = e₃)
    (hk₁ : IsoOn e₁ k₁ l₁) (hk₂ : IsoOn e₂ k₂ l₂) (hk₃ : IsoOn e₃ k₃ l₃) :
    IsoOn (tens (tens e₁ e₂) e₃) (tens (tens k₁ k₂) k₃) (l₁ * l₂ * l₃) :=
  isoOn_tens _ _ _ _ _ _ (tens_idem e₁ e₂ h₁ h₂) h₃ (isoOn_tens _ _ _ _ _ _ h₁ h₂ hk₁ hk₂) hk₃

/-- 加法同型で等長性を移す。 -/
theorem isoOn_comp_equiv (φ : G ≃+ H) (e k : H → ℂ) (l : ℝ) (h : IsoOn e k l) :
    IsoOn (e ∘ φ) (k ∘ φ) l := by
  intro f hf
  obtain ⟨F, rfl⟩ : ∃ F, f = F ∘ φ := ⟨f ∘ φ.symm, by funext x; simp⟩
  rw [conv_comp_equiv] at hf
  have hF : conv e F = F := by
    funext y
    have := congrFun hf (φ.symm y)
    simpa using this
  rw [conv_comp_equiv, normSq_comp_equiv, normSq_comp_equiv, h _ hF]

end Generic

/-! ## 5. 一般の互いに素な法での中国剰余 -/

/-- ZMod (m n) ≃+ ZMod m × ZMod n（m, n は互いに素）。 -/
noncomputable def crtN (m n : ℕ) (h : m.Coprime n) : ZMod (m * n) ≃+ ZMod m × ZMod n :=
  (ZMod.chineseRemainder h).toAddEquiv

theorem isoOn_crtN (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) (e₁ k₁ : ZMod m → ℂ) (e₂ k₂ : ZMod n → ℂ)
    (l₁ l₂ : ℝ) (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂) (hk₁ : IsoOn e₁ k₁ l₁) (hk₂ : IsoOn e₂ k₂ l₂) :
    IsoOn (tens e₁ e₂ ∘ crtN m n h) (tens k₁ k₂ ∘ crtN m n h) (l₁ * l₂) :=
  isoOn_comp_equiv _ _ _ _ (isoOn_tens e₁ k₁ e₂ k₂ l₁ l₂ h₁ h₂ hk₁ hk₂)

/-! ## 6. 原始ケットでの具体化 -/

section Ket

open PAG.Part59 PAG.Part89

variable {p : ℕ} [hp : Fact p.Prime]

theorem isoOn_ket (K w n : ℕ) (hK : w + (n + 1) ≤ K) (χ : DirichletCharacter ℂ (p ^ (n + 1)))
    (hχ : χ.IsPrimitive) :
    IsoOn (eps (p := p) K (K - (n + 1) - w)) (PAG.Part21.ket K w (n + 1) hK χ)
      ((p : ℝ) ^ K / (PAG.Part19.sz p K (K - (n + 1) - w) : ℝ)) :=
  fun f hf => norm_conv_eq_of_mem K w n hK χ hχ f hf

theorem eps_idem (K a : ℕ) (ha : a ≤ K) : conv (eps (p := p) K a) (eps (p := p) K a) = eps (p := p) K a := by
  rw [eps_conv_eps K a a ha ha, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

end Ket

end PAG.Part109

#print axioms PAG.Part109.conv_assoc_gen
#print axioms PAG.Part109.conv_tens_apply'
#print axioms PAG.Part109.tens_fix_iff
#print axioms PAG.Part109.tens_idem
#print axioms PAG.Part109.isoOn_tens
#print axioms PAG.Part109.isoOn_tens3
#print axioms PAG.Part109.isoOn_comp_equiv
#print axioms PAG.Part109.isoOn_crtN
#print axioms PAG.Part109.isoOn_ket
#print axioms PAG.Part109.eps_idem
