/-
  PAG 2.0 Part 109（2026-10-19）— 次元の公式 finrank V_𝐚 = ∏ |S_{a_i}|（トレースによる）
  1. 畳み込み作用素のトレース: tr(e ⋆ ·) = |G| · e(0)
  2. べき等な e について finrank {f : e ⋆ f = f} = |G| · e(0)（IsProj.trace）
  3. 積: finrank V(⊗e_i) = ∏ finrank V(e_i)（(⊗e_i)(0) = ∏ e_i(0)、|∏G_i| = ∏|G_i|）
  4. 素数の族: finrank V_𝐚 = ∏ |S_{a_i}|（原始ケットが存在する双対殻の組）
-/
import PAG112

namespace PAG.Part113

open ZMod Finset PAG.Part15 PAG.Part108 PAG.Part109 PAG.Part110

section Generic

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- **1. 畳み込み作用素のトレース**。 -/
theorem trace_convL (e : G → ℂ) :
    LinearMap.trace ℂ (G → ℂ) (convL e) = (Fintype.card G : ℂ) * e 0 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ G), Matrix.trace]
  have h : ∀ x, Matrix.diag (LinearMap.toMatrix (Pi.basisFun ℂ G) (Pi.basisFun ℂ G) (convL e)) x = e 0 := by
    intro x
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr]
    show conv e (Pi.single x 1) x = e 0
    simp only [conv]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      rw [Pi.single_apply, ite_eq_right_of_eq_false _ _ (eq_false (by
        intro h'; apply hb; have := congrArg (fun z => x - z) h'; simpa using this)), mul_zero]
    · simp
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq G] in
theorem idem_convL (e : G → ℂ) (he : conv e e = e) : IsIdempotentElem (convL e) := by
  apply LinearMap.ext; intro f
  show conv e (conv e f) = conv e f
  rw [← conv_assoc_gen, he]

omit [DecidableEq G] in
theorem mem_range_convL (e : G → ℂ) (he : conv e e = e) (f : G → ℂ) :
    f ∈ LinearMap.range (convL e) ↔ conv e f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    show conv e (conv e g) = conv e g
    rw [← conv_assoc_gen, he]
  · intro hf; exact ⟨f, hf⟩

/-- **2. 固定空間の次元** = |G| · e(0)。 -/
theorem finrank_fix (e : G → ℂ) (he : conv e e = e) :
    (Module.finrank ℂ (LinearMap.range (convL e)) : ℂ) = (Fintype.card G : ℂ) * e 0 := by
  rw [← LinearMap.IsProj.trace ((LinearMap.isProj_range_iff_isIdempotentElem _).mpr (idem_convL e he)), trace_convL]

end Generic

section Pi

variable {n : ℕ} {G : Fin n → Type} [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]

/-- **3. 積の次元**: finrank V(⊗e_i) = ∏ finrank V(e_i)。 -/
theorem finrank_ptens (e : ∀ i, G i → ℂ) (he : ∀ i, conv (e i) (e i) = e i) :
    Module.finrank ℂ (LinearMap.range (convL (ptens e)))
      = ∏ i, Module.finrank ℂ (LinearMap.range (convL (e i))) := by
  have hidem : conv (ptens e) (ptens e) = ptens e := by rw [conv_ptens]; simp only [he]
  apply Nat.cast_injective (R := ℂ)
  rw [finrank_fix _ hidem, Nat.cast_prod]
  simp only [fun i => finrank_fix (e i) (he i)]
  rw [Finset.prod_mul_distrib, Fintype.card_pi, Nat.cast_prod]
  rfl

end Pi

section Generic2

variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- 二つの因子の場合。 -/
theorem finrank_tens (e₁ : G → ℂ) (e₂ : H → ℂ) (h₁ : conv e₁ e₁ = e₁) (h₂ : conv e₂ e₂ = e₂) :
    Module.finrank ℂ (LinearMap.range (convL (tens e₁ e₂)))
      = Module.finrank ℂ (LinearMap.range (convL e₁)) * Module.finrank ℂ (LinearMap.range (convL e₂)) := by
  apply Nat.cast_injective (R := ℂ)
  rw [finrank_fix _ (tens_idem e₁ e₂ h₁ h₂), Nat.cast_mul, finrank_fix _ h₁, finrank_fix _ h₂,
    Fintype.card_prod, Nat.cast_mul]
  show _ * (e₁ 0 * e₂ 0) = _
  ring

end Generic2

/-! ## 4. 素数の族での具体化 -/

section Primes

open PAG.Part19 PAG.Part21 PAG.Part59 PAG.Part93 PAG.Part95

theorem range_convL_eps {p : ℕ} [Fact p.Prime] (K a : ℕ) (ha : a ≤ K) :
    LinearMap.range (convL (eps (p := p) K a)) = Va (p := p) K a := by
  ext f
  rw [mem_range_convL _ (eps_idem K a ha), Va_eq_span K a ha f]

theorem finrank_eps_ket {p : ℕ} [Fact p.Prime] (K w c : ℕ) (h : w + (c + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    Module.finrank ℂ (LinearMap.range (convL (eps (p := p) K (K - (c + 1) - w)))) = sz p K (K - (c + 1) - w) := by
  rw [range_convL_eps K _ (by omega), finrank_Va K _ (by omega), card_Tset K _ _ ⟨w, c, h, χ, hχ, rfl, rfl⟩]

/-- **4. finrank V_𝐚 = ∏ |S_{a_i}|**（双対殻 a_i に原始ケットがある組）。 -/
theorem finrank_ptens_eps {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)
    (h : ∀ i, w i + (c i + 1) ≤ K i) (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1)))
    (hχ : ∀ i, (χ i).IsPrimitive) :
    Module.finrank ℂ (LinearMap.range (convL (ptens (fun i => eps (p := p i) (K i) (K i - (c i + 1) - w i)))))
      = ∏ i, sz (p i) (K i) (K i - (c i + 1) - w i) := by
  rw [finrank_ptens (G := fun i => ZMod (p i ^ K i)) _ (fun i => eps_idem (K i) _ (by omega))]
  exact Finset.prod_congr rfl fun i _ => finrank_eps_ket (K i) (w i) (c i) (h i) (χ i) (hχ i)

/-- 系: 値 ε_a(0) = |S_a| / p^K（次元公式の言い換え）。 -/
theorem eps_zero_val {p : ℕ} [hp : Fact p.Prime] (K w c : ℕ) (h : w + (c + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (c + 1))) (hχ : χ.IsPrimitive) :
    eps (p := p) K (K - (c + 1) - w) 0 = (sz p K (K - (c + 1) - w) : ℂ) / (p : ℂ) ^ K := by
  have e := finrank_fix (eps (p := p) K (K - (c + 1) - w)) (eps_idem K _ (by omega))
  rw [finrank_eps_ket K w c h χ hχ, ZMod.card] at e
  have hp0 : ((p : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  rw [e]; push_cast; field_simp

end Primes

end PAG.Part113

#print axioms PAG.Part113.trace_convL
#print axioms PAG.Part113.idem_convL
#print axioms PAG.Part113.mem_range_convL
#print axioms PAG.Part113.finrank_fix
#print axioms PAG.Part113.finrank_ptens
#print axioms PAG.Part113.finrank_tens
#print axioms PAG.Part113.range_convL_eps
#print axioms PAG.Part113.finrank_eps_ket
#print axioms PAG.Part113.finrank_ptens_eps
#print axioms PAG.Part113.eps_zero_val
