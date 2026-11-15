/-
  PAG 2.0 Part 121（2026-10-21）— n 個の素数の積の特性多項式の閉じた形
  1. Unif は埋め込みでの写像と同値に移る（unif_map）、部分型の全体へ移る（unif_attach）
  2. n 個の因子の一様分布の積（Fin n の帰納法）: 周期は lcmF（反復 lcm）
  3. charpoly((⊗k_i)⋆|V_𝐚) = (X^L − (∏ z_i)^L)^{∏|S_{a_i}| / L}、L = lcmF(ord χ_i)
-/
import PAG124

namespace PAG.Part125

open ZMod Finset Polynomial PAG.Part122 PAG.Part123 PAG.Part124

/-- 反復 lcm。 -/
def lcmF : ∀ n : ℕ, (Fin n → ℕ) → ℕ
  | 0, _ => 1
  | n + 1, o => Nat.lcm (o 0) (lcmF n (fun i => o i.succ))

section Map

variable {β γ : Type*} [DecidableEq β] [DecidableEq γ]

omit [DecidableEq β] [DecidableEq γ] in
/-- **1a. 埋め込みでの移送**。 -/
theorem unif_map (e : β ↪ γ) (S : Finset β) (G : γ → ℂ) (t₀ : β) (o : ℕ) :
    Unif (S.map e) G (e t₀) o ↔ Unif S (fun x => G (e x)) t₀ o := by
  unfold Unif
  rw [Finset.mem_map' e, Finset.card_map]
  simp only [Finset.forall_mem_map, Finset.filter_map, Finset.card_map]
  rfl

end Map

/-- **1b. 部分型の全体へ**。 -/
theorem unif_attach {β : Type*} [DecidableEq β] {T : Finset β} {F : β → ℂ} {t₀ : β} {o : ℕ}
    (h : Unif T F t₀ o) (ht₀ : t₀ ∈ T) :
    Unif (univ : Finset T) (fun x => F x) ⟨t₀, ht₀⟩ o := by
  rw [Finset.univ_eq_attach]
  have key := unif_map (Function.Embedding.subtype (· ∈ T)) T.attach F ⟨t₀, ht₀⟩ o
  rw [Finset.attach_map_val] at key
  exact key.mp h

/-- **2. n 個の因子の一様分布の積**。 -/
theorem unif_pi : ∀ (n : ℕ) (β : Fin n → Type) [∀ i, DecidableEq (β i)] [∀ i, Fintype (β i)]
    (F : ∀ i, β i → ℂ) (t₀ : ∀ i, β i) (o : Fin n → ℕ),
    (∀ i, Unif (univ : Finset (β i)) (F i) (t₀ i) (o i)) →
      Unif (univ : Finset (∀ i, β i)) (fun v => ∏ i, F i (v i)) t₀ (lcmF n o) := by
  intro n
  induction n with
  | zero =>
    intro β _ _ F t₀ o _
    refine ⟨mem_univ _, Nat.one_pos, by simp, fun t _ => by simp, fun ξ hξ => ?_⟩
    change ξ ^ 1 = 1 at hξ
    rw [pow_one] at hξ; subst hξ
    show 1 * _ = _
    rw [one_mul]
    congr 1
    apply Finset.filter_true_of_mem
    intro v _
    simp
  | succ n ih =>
    intro β _ _ F t₀ o h
    have hmul := unif_mul (h 0) (ih (fun i => β i.succ) (fun i => F i.succ) (fun i => t₀ i.succ)
      (fun i => o i.succ) (fun i => h i.succ))
    have e := (unif_map (Fin.consEquiv β).toEmbedding (univ ×ˢ univ) (fun v => ∏ i, F i (v i))
      (t₀ 0, fun i => t₀ i.succ) (lcmF (n + 1) o)).mpr (by
        convert hmul using 2
        simp only [Equiv.toEmbedding_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rfl)
    rw [Finset.univ_product_univ, Finset.map_univ_equiv] at e
    convert e using 1
    simp only [Equiv.toEmbedding_apply, Fin.consEquiv_apply]
    exact (Fin.cons_self_tail t₀).symm

/-! ## 3. ケットへの適用 -/

section Ket

open PAG.Part19 PAG.Part21 PAG.Part95

variable {n : ℕ} (p : Fin n → ℕ) [hp : ∀ i, Fact (p i).Prime] (K w c : Fin n → ℕ)

/-- **3. n 個の素数の積のケットの特性多項式の閉じた形**。 -/
theorem charpoly_Tn_closed (h : ∀ i, w i + (c i + 1) ≤ K i)
    (χ : ∀ i, DirichletCharacter ℂ (p i ^ (c i + 1))) (hχ : ∀ i, (χ i).IsPrimitive)
    (t : ∀ i, ZMod (p i ^ K i)) (ht : ∀ i, t i ∈ Tset (p := p i) (K i) (K i - (c i + 1) - w i)) :
    (Tn p K (fun i => K i - (c i + 1) - w i) (fun i => by omega)
        (fun i => ket (K i) (w i) (c i + 1) (h i) (χ i))).charpoly
      = (X ^ lcmF n (fun i => orderOf (χ i))
          - C ((∏ i, 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (t i)) ^ lcmF n (fun i => orderOf (χ i))))
        ^ ((∏ i, sz (p i) (K i) (K i - (c i + 1) - w i)) / lcmF n (fun i => orderOf (χ i))) := by
  classical
  rw [charpoly_Tn]
  have hU := unif_pi n (fun i => (Tset (p := p i) (K i) (K i - (c i + 1) - w i)))
    (fun i x => 𝓕 (ket (K i) (w i) (c i + 1) (h i) (χ i)) (x : ZMod (p i ^ K i)))
    (fun i => ⟨t i, ht i⟩) (fun i => orderOf (χ i))
    (fun i => unif_attach (PAG.Part122.ket_unif (K i) (w i) (c i) (h i) (χ i) (hχ i) (t i) (ht i)) (ht i))
  have := closed_of_unif hU
  simp only at this
  rw [this, Finset.card_univ, Fintype.card_pi]
  congr 2
  apply Finset.prod_congr rfl; intro i _
  rw [Fintype.card_coe, card_Tset (K i) _ _ ⟨w i, c i, h i, χ i, hχ i, rfl, rfl⟩]

end Ket

end PAG.Part125

#print axioms PAG.Part125.unif_map
#print axioms PAG.Part125.unif_attach
#print axioms PAG.Part125.unif_pi
#print axioms PAG.Part125.charpoly_Tn_closed
