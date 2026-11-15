/-
  PAG 2.0 Part 30（2026-10-19）
  1. 法 p（素数）での数え上げ: 原始指標 p − 2 個、#{χ₂ 原始 | χ₁χ₂ 原始} = p − 3
  2. 組全体の個数: #{(χ₁, χ₂) | 原始・原始・導手 p^m} = #原始 × (φ(p^m) − φ(p^(m−1))) など
  3. (Z/2)² = {1, W, ~, W~} の作用と B_S^proj, B_N^proj の同変性を一つの定理に:
     B_{b ⊕ s}(g·Φ, g·Ψ) = g·B_b(Φ, Ψ)（g = (s, t)）
-/
import PAG33

namespace PAG.Part34

open ZMod Finset PAG.Part26 PAG.Part27 PAG.Part28 PAG.Part29 PAG.Part32 PAG.Part33

open Classical

/-! ## 1. 法 p での数え上げ -/

section LevelP

variable {p : ℕ} [hp : Fact p.Prime]

instance : NeZero p := ⟨hp.out.ne_zero⟩

/-- 法 p の原始指標は p − 2 個。 -/
theorem card_prim_level_p :
    Fintype.card {χ : DirichletCharacter ℂ p // χ.IsPrimitive} = p - 2 := by
  have e : Fintype.card {χ : DirichletCharacter ℂ p // χ.IsPrimitive}
      = Fintype.card {χ : DirichletCharacter ℂ p // χ ≠ 1} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun χ => prim_level_p_iff χ))
  rw [e, Fintype.card_subtype_compl, card_chars, Nat.totient_prime hp.out]
  simp only [Fintype.card_unique]
  omega

/-- 原始 χ₁ に対し、χ₁χ₂ が自明な原始 χ₂ はちょうど 1 個（χ₁⁻¹）。 -/
theorem card_level_p_trivial (χ₁ : DirichletCharacter ℂ p) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ p // χ₂.IsPrimitive ∧ ¬ (χ₁ * χ₂).IsPrimitive} = 1 := by
  rw [Fintype.card_eq_one_iff]
  have hinv : (χ₁⁻¹).IsPrimitive := by
    rw [prim_level_p_iff] at h₁ ⊢; exact fun h => h₁ (inv_eq_one.mp h)
  refine ⟨⟨χ₁⁻¹, hinv, by rw [mul_inv_cancel, prim_level_p_iff, not_not]⟩, ?_⟩
  rintro ⟨χ₂, _, h2⟩
  rw [prim_level_p_iff, not_not] at h2
  exact Subtype.ext (eq_inv_of_mul_eq_one_right h2)

/-- **法 p: #{χ₂ 原始 | χ₁χ₂ 原始} = p − 3**（割合 (p−3)/(p−2)）。 -/
theorem card_level_p_mul_prim (χ₁ : DirichletCharacter ℂ p) (h₁ : χ₁.IsPrimitive) :
    Fintype.card {χ₂ : DirichletCharacter ℂ p // χ₂.IsPrimitive ∧ (χ₁ * χ₂).IsPrimitive} = p - 3 := by
  have h := card_split (fun χ₂ : DirichletCharacter ℂ p => χ₂.IsPrimitive) (fun χ₂ => (χ₁ * χ₂).IsPrimitive)
  rw [card_level_p_trivial χ₁ h₁, card_prim_level_p] at h
  omega

end LevelP

/-! ## 2. 組全体の個数 -/

section Pairs

/-- ファイバーの個数が一定なら、組の個数は積。 -/
theorem card_pairs {α : Type*} [Fintype α] (P : α → Prop) (R : α → α → Prop) [DecidablePred P]
    [∀ a, DecidablePred (R a)] (k : ℕ)
    (hk : ∀ a, P a → Fintype.card {b // R a b} = k) :
    Fintype.card {x : α × α // P x.1 ∧ R x.1 x.2} = Fintype.card {a // P a} * k := by
  have e : {x : α × α // P x.1 ∧ R x.1 x.2} ≃ Σ a : {a // P a}, {b // R a.1 b} :=
    { toFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
      invFun := fun s => ⟨(s.1.1, s.2.1), s.1.2, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  rw [Finset.sum_congr rfl (fun a _ => hk a.1 a.2), Finset.sum_const, Finset.card_univ, smul_eq_mul]

variable {p : ℕ} [hp : Fact p.Prime] {c : ℕ}

/-- **組の個数（導手 p^m）**: #原始 × (φ(p^m) − φ(p^(m−1)))（1 ≤ m ≤ c）。 -/
theorem card_pairs_conductor (hc : 1 ≤ c) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ c) :
    Fintype.card {x : DirichletCharacter ℂ (p ^ (c + 1)) × DirichletCharacter ℂ (p ^ (c + 1)) //
        x.1.IsPrimitive ∧ (x.2.IsPrimitive ∧ (x.1 * x.2).conductor = p ^ m)}
      = ((p ^ (c + 1)).totient - (p ^ c).totient) * ((p ^ m).totient - (p ^ (m - 1)).totient) := by
  have h := card_pairs (α := DirichletCharacter ℂ (p ^ (c + 1))) (fun a => a.IsPrimitive) (fun a b => b.IsPrimitive ∧ (a * b).conductor = p ^ m) _
    (fun a ha => by convert card_mul_conductor (p := p) hc hm1 hm a ha)
  exact h.trans (by rw [card_prim hc])

/-- **組の個数（積が原始的）**: #原始 × (φ(p^(c+1)) − 2φ(p^c))。 -/
theorem card_pairs_prim (hc : 1 ≤ c) :
    Fintype.card {x : DirichletCharacter ℂ (p ^ (c + 1)) × DirichletCharacter ℂ (p ^ (c + 1)) //
        x.1.IsPrimitive ∧ (x.2.IsPrimitive ∧ (x.1 * x.2).IsPrimitive)}
      = ((p ^ (c + 1)).totient - (p ^ c).totient)
          * ((p ^ (c + 1)).totient - (p ^ c).totient - (p ^ c).totient) := by
  have h := card_pairs (α := DirichletCharacter ℂ (p ^ (c + 1))) (fun a => a.IsPrimitive) (fun a b => b.IsPrimitive ∧ (a * b).IsPrimitive) _
    (fun a ha => by convert card_mul_prim (p := p) hc a ha)
  exact h.trans (by rw [card_prim hc])

/-- **組の個数（積が自明）**: #原始。 -/
theorem card_pairs_trivial (hc : 1 ≤ c) :
    Fintype.card {x : DirichletCharacter ℂ (p ^ (c + 1)) × DirichletCharacter ℂ (p ^ (c + 1)) //
        x.1.IsPrimitive ∧ (x.2.IsPrimitive ∧ (x.1 * x.2).FactorsThrough (p ^ 0))}
      = (p ^ (c + 1)).totient - (p ^ c).totient := by
  have h := card_pairs (α := DirichletCharacter ℂ (p ^ (c + 1))) (fun a => a.IsPrimitive) (fun a b => b.IsPrimitive ∧ (a * b).FactorsThrough (p ^ 0)) 1
    (fun a ha => by convert card_mul_trivial (p := p) hc a ha)
  exact h.trans (by rw [card_prim hc, mul_one])

end Pairs

/-! ## 3. (Z/2)² 同変性 -/

section Sym

variable {N : ℕ}

/-- (Z/2)² の作用: (s, t) ↦ W^s ∘ ~^t。 -/
noncomputable def sym (s t : Bool) (Φ : ProjLine N → ℂ) : ProjLine N → ℂ :=
  (if s then Wpull else id) ((if t then tildePull else id) Φ)

theorem sym_ff (Φ : ProjLine N → ℂ) : sym false false Φ = Φ := rfl

end Sym

section SymK

variable {p : ℕ} [hp : Fact p.Prime] (K : ℕ) (hK : 1 ≤ K)

include hK in
/-- **群の法則**: sym s t ∘ sym s' t' = sym (s ⊕ s') (t ⊕ t')。 -/
theorem sym_mul (s t s' t' : Bool) (Φ : ProjLine (p ^ K) → ℂ) :
    sym s t (sym s' t' Φ) = sym (xor s s') (xor t t') Φ := by
  cases s <;> cases t <;> cases s' <;> cases t' <;>
    simp only [sym, Bool.false_eq_true, ↓reduceIte, id, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      Wpull_Wpull, tildePull_tildePull, tildePull_Wpull K hK]

/-- B_b: b = false で B_S^proj、true で B_N^proj。 -/
noncomputable def Bb (b : Bool) : (ProjLine (p ^ K) → ℂ) → (ProjLine (p ^ K) → ℂ) → ProjLine (p ^ K) → ℂ :=
  if b then BNproj K hK else BSproj K hK

theorem BSproj_W (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BSproj K hK (Wpull Φ) (Wpull Ψ) = Wpull (BNproj K hK Φ Ψ) := by
  rw [BNproj_eq, Wpull_Wpull]

theorem BNproj_W (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BNproj K hK (Wpull Φ) (Wpull Ψ) = Wpull (BSproj K hK Φ Ψ) := by
  rw [BNproj_eq, Wpull_Wpull, Wpull_Wpull]

/-- **(Z/2)² 同変性**: B_{b ⊕ s}(g·Φ, g·Ψ) = g·B_b(Φ, Ψ)（g = (s, t)）。
W は南北の畳み込みを入れ替え、~ はそれぞれを保つ。 -/
theorem B_equivariant (b s t : Bool) (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    Bb K hK (xor b s) (sym s t Φ) (sym s t Ψ) = sym s t (Bb K hK b Φ Ψ) := by
  cases b <;> cases s <;> cases t <;>
    simp only [Bb, sym, Bool.false_eq_true, ↓reduceIte, id, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false,
      BSproj_tilde, BNproj_tilde, BSproj_W, BNproj_W]

/-- **南ケットの軌道**: g·|w,χ⟩_S は ±|w,χ^{±1}⟩_S, ±|−w,χ^{±1}⟩_N のいずれか。 -/
theorem sym_ketS (w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    sym false false (ketS_proj K hK w c h χ) = ketS_proj K hK w c h χ ∧
    sym false true (ketS_proj K hK w c h χ) = χ (-1) • ketS_proj K hK w c h χ⁻¹ ∧
    sym true false (ketS_proj K hK w c h χ) = ketN_proj K hK w c h χ⁻¹ ∧
    sym true true (ketS_proj K hK w c h χ) = χ (-1) • ketN_proj K hK w c h χ := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact tildePull_ketS K hK w c h χ
  · exact Wpull_ketS_proj K hK w c h χ
  · exact Wpull_tildePull_ketS K hK w c h χ

end SymK

end PAG.Part34

#print axioms PAG.Part34.card_prim_level_p
#print axioms PAG.Part34.card_level_p_trivial
#print axioms PAG.Part34.card_level_p_mul_prim
#print axioms PAG.Part34.card_pairs
#print axioms PAG.Part34.card_pairs_conductor
#print axioms PAG.Part34.card_pairs_prim
#print axioms PAG.Part34.card_pairs_trivial
#print axioms PAG.Part34.sym
#print axioms PAG.Part34.sym_ff
#print axioms PAG.Part34.sym_mul
#print axioms PAG.Part34.Bb
#print axioms PAG.Part34.BSproj_W
#print axioms PAG.Part34.BNproj_W
#print axioms PAG.Part34.B_equivariant
#print axioms PAG.Part34.sym_ketS
