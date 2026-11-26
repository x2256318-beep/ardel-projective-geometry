
import PAG260

open ZMod Complex

namespace PAG.Part261

variable {ι : Type*} (N : ι → ℕ) [hN : ∀ i, NeZero (N i)]

def lvl : List ι → ℕ
  | [] => 1
  | a :: l => N a * lvl l

omit hN in
theorem lvl_cons (a : ι) (l : List ι) : lvl N (a :: l) = N a * lvl N l := rfl

omit hN in
theorem lvl_eq_prod (l : List ι) : lvl N l = (l.map N).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lvl, ih]

instance lvl_neZero (l : List ι) : NeZero (lvl N l) := ⟨by
  induction l with
  | nil => simp [lvl]
  | cons a l ih => exact mul_ne_zero (NeZero.ne (N a)) ih⟩

variable {N}

noncomputable def listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) :
    (l : List ι) → DirichletCharacter ℂ (lvl N l)
  | [] => 1
  | a :: l => PAG.Part260.prodChar (χ a) (listChar χ l)

noncomputable def cross (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℂ
  | [] => 1
  | a :: l => χ a (lvl N l : ZMod (N a)) * listChar χ l (N a : ZMod (lvl N l)) * cross χ l

omit hN in
theorem coprime_lvl {a : ι} {l : List ι} (h : ∀ j ∈ l, (N a).Coprime (N j)) :
    (N a).Coprime (lvl N l) := by
  induction l with
  | nil => simp [lvl]
  | cons b l ih =>
    rw [lvl_cons]
    exact Nat.Coprime.mul_right (h b (by simp)) (ih fun j hj => h j (by simp [hj]))

theorem gaussSum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    gaussSum (listChar χ l) stdAddChar =
      cross χ l * (l.map fun i => gaussSum (χ i) stdAddChar).prod := by
  induction l with
  | nil =>
    show gaussSum (1 : DirichletCharacter ℂ 1) stdAddChar = 1 * 1
    rw [PAG.Part203.gaussSum_level_one]; ring
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h : gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _ :=
      PAG.Part193.gaussSum_mul_coprime (coprime_lvl hl.1) (χ a) (listChar χ l)
    show gaussSum (PAG.Part260.prodChar (χ a) (listChar χ l)) stdAddChar = _
    rw [h, ih hl.2]
    simp only [cross, List.map_cons, List.prod_cons]
    ring

theorem listChar_natCast (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (n : ℕ) :
    listChar χ l (n : ZMod (lvl N l)) = (l.map fun j => χ j (n : ZMod (N j))).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1
    exact MulChar.one_apply (isUnit_of_subsingleton _)
  | cons a l ih =>
    have h : PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _ :=
      PAG.Part193.mul_changeLevel_apply (χ a) (listChar χ l) (n : ZMod (N a * lvl N l))
    show PAG.Part260.prodChar (χ a) (listChar χ l) (n : ZMod (N a * lvl N l)) = _
    rw [h, ZMod.castHom_apply, ZMod.castHom_apply,
      ZMod.cast_natCast (dvd_mul_right _ _), ZMod.cast_natCast (dvd_mul_left _ _), ih]
    simp

theorem listChar_neg_one (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (l.map fun j => χ j (-1)).prod := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact MulChar.one_apply isUnit_one.neg
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) (-1) = _
    rw [PAG.Part260.prodChar_neg_one, ih]
    simp

variable [DecidableEq ι]

theorem cross_eq_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i))).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => χ i ((((a :: l).erase i).map N).prod : ZMod (N i))) =
        l.map fun i => χ i (N a : ZMod (N i)) * χ i (((l.erase i).map N).prod : ZMod (N i)) := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons, Nat.cast_mul,
        map_mul]
    rw [key, List.prod_map_mul]
    ring

theorem cross_eq_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) (hnd : l.Nodup) :
    cross χ l = (l.map fun i => ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    simp only [cross, List.map_cons, List.prod_cons, List.erase_cons_head]
    rw [ih hnd.2, listChar_natCast, lvl_eq_prod]
    have key : (l.map fun i => (((a :: l).erase i).map fun j => χ j (N i : ZMod (N j))).prod) =
        l.map fun i => χ a (N i : ZMod (N a)) *
          ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod := by
      apply List.map_congr_left
      intro i hi
      have hne : a ≠ i := fun h => hnd.1 (h ▸ hi)
      rw [List.erase_cons_tail (by simpa using hne), List.map_cons, List.prod_cons]
    have hprod : χ a (((l.map N).prod : ℕ) : ZMod (N a)) =
        (l.map fun i => χ a (N i : ZMod (N a))).prod := by
      rw [Nat.cast_list_prod, map_list_prod, List.map_map, List.map_map]
      rfl
    rw [key, List.prod_map_mul, hprod]
    ring

omit hN [DecidableEq ι] in
theorem sqrt_lvl (l : List ι) :
    ((Real.sqrt (lvl N l) : ℝ) : ℂ) = (l.map fun i => ((Real.sqrt (N i) : ℝ) : ℂ)).prod := by
  induction l with
  | nil => simp [lvl]
  | cons a l ih =>
    rw [lvl_cons, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, ih]
    simp

omit hN [DecidableEq ι] in
theorem prod_map_div' {f g : ι → ℂ} (l : List ι) :
    (l.map fun i => f i / g i).prod = (l.map f).prod / (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, div_mul_div_comm]

theorem rootNum_listChar_formII (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ) *
        ((l.erase i).map fun j => χ j (N i : ZMod (N j))).prod).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formII χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

theorem rootNum_listChar_formI (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hnd : l.Nodup) :
    PAG.Part256.rootNum (listChar χ l) = PAG.Part256.parFac (listChar χ l) *
      (l.map fun i => χ i (((l.erase i).map N).prod : ZMod (N i)) *
        (gaussSum (χ i) stdAddChar / ((Real.sqrt (N i) : ℝ) : ℂ))).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, cross_eq_formI χ l hnd, sqrt_lvl,
    List.prod_map_mul, prod_map_div']
  ring

omit [DecidableEq ι] in
open Classical in

noncomputable def oddCount (χ : ∀ i, DirichletCharacter ℂ (N i)) : List ι → ℕ
  | [] => 0
  | a :: l => (if (χ a).Odd then 1 else 0) + oddCount χ l

omit [DecidableEq ι] in
theorem listChar_neg_one_pow (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    listChar χ l (-1) = (-1) ^ oddCount χ l := by
  rw [listChar_neg_one]
  induction l with
  | nil => simp [oddCount]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, oddCount, ih, pow_add]
    rcases (χ a).even_or_odd with h | h
    · have hn := h.not_odd
      unfold DirichletCharacter.Even at h
      simp [hn, h]
    · have h' := h
      unfold DirichletCharacter.Odd at h'
      simp [h, h']

omit hN in
theorem tri_succ (k : ℕ) : (1 + k) * (1 + k - 1) / 2 = k * (k - 1) / 2 + k := by
  rcases k with _ | m
  · simp
  · have e : (1 + (m + 1)) * (1 + (m + 1) - 1) = (m + 1) * (m + 1 - 1) + (m + 1) * 2 := by
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num)]

omit [DecidableEq ι] in

theorem parFac_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι) :
    PAG.Part256.parFac (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) *
        (l.map fun i => PAG.Part256.parFac (χ i)).prod := by
  induction l with
  | nil =>
    show PAG.Part256.parFac (1 : DirichletCharacter ℂ 1) = _
    rw [PAG.Part256.parFac_of_even (MulChar.one_apply isUnit_one.neg)]
    simp [oddCount]
  | cons a l ih =>
    show PAG.Part256.parFac (PAG.Part260.prodChar (χ a) (listChar χ l)) = _
    rw [PAG.Part260.parFac_prodChar, ih]
    have hk := listChar_neg_one_pow χ l
    have hodd : (listChar χ l).Odd ↔ _root_.Odd (oddCount χ l) := by
      unfold DirichletCharacter.Odd
      rw [hk]
      exact neg_one_pow_eq_neg_one_iff_odd (by norm_num)
    simp only [oddCount, List.map_cons, List.prod_cons]
    unfold PAG.Part260.crossSign
    rcases (χ a).even_or_odd with h | h
    · have hn := h.not_odd
      simp only [hn, false_and, ↓reduceIte, zero_add]
      ring
    · simp only [h, true_and, ↓reduceIte, hodd]
      rw [tri_succ, pow_add]
      by_cases hk2 : _root_.Odd (oddCount χ l)
      · simp only [hk2, ↓reduceIte, hk2.neg_one_pow]; ring
      · simp only [hk2, ↓reduceIte, (Nat.not_odd_iff_even.mp hk2).neg_one_pow]; ring

omit [DecidableEq ι] in

theorem rootNum_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    PAG.Part256.rootNum (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part256.rootNum (χ i)).prod := by
  rw [PAG.Part256.rootNum_eq, gaussSum_listChar χ l hl, parFac_listChar, sqrt_lvl]
  simp_rw [PAG.Part256.rootNum_eq]
  rw [prod_map_div', List.prod_map_mul]
  ring

omit [DecidableEq ι] in

theorem isPrimitive_listChar_iff (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) :
    (listChar χ l).IsPrimitive ↔ ∀ i ∈ l, (χ i).IsPrimitive := by
  induction l with
  | nil =>
    show (1 : DirichletCharacter ℂ 1).IsPrimitive ↔ _
    simpa using (DirichletCharacter.isPrimitive_one_level_one : (1 : DirichletCharacter ℂ 1).IsPrimitive)
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    have hiff := PAG.Part194.isPrimitive_iff hc (PAG.Part260.prodChar (χ a) (listChar χ l))
    have h1 : PAG.Part194.comp₁ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = χ a :=
      PAG.Part194.comp₁_mul hc (χ a) (listChar χ l)
    have h2 : PAG.Part194.comp₂ hc (PAG.Part260.prodChar (χ a) (listChar χ l)) = listChar χ l :=
      PAG.Part194.comp₂_mul hc (χ a) (listChar χ l)
    rw [h1, h2, ih hl.2] at hiff
    show (PAG.Part260.prodChar (χ a) (listChar χ l)).IsPrimitive ↔ _
    rw [hiff]
    simp

omit [DecidableEq ι] in

theorem phaseA1_listChar (χ : ∀ i, DirichletCharacter ℂ (N i)) (l : List ι)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (hp : ∀ i ∈ l, (χ i).IsPrimitive) :
    PAG.Part258.phaseA1 (listChar χ l) =
      (-1) ^ (oddCount χ l * (oddCount χ l - 1) / 2) * cross χ l *
        (l.map fun i => PAG.Part258.phaseA1 (χ i)).prod := by
  rw [PAG.Part258.phaseA1_of_isPrimitive ((isPrimitive_listChar_iff χ l hl).mpr hp),
    rootNum_listChar χ l hl]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  rw [PAG.Part258.phaseA1_of_isPrimitive (hp i hi)]

omit hN [DecidableEq ι] in
theorem listChar_congr {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (l : List ι)
    (h : ∀ i ∈ l, χ i = χ' i) : listChar χ l = listChar χ' l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show PAG.Part260.prodChar (χ a) (listChar χ l) = PAG.Part260.prodChar (χ' a) (listChar χ' l)
    rw [h a (by simp), ih fun i hi => h i (by simp [hi])]

theorem exists_listChar (l : List ι) (hnd : l.Nodup)
    (hl : l.Pairwise fun i j => (N i).Coprime (N j)) (Ψ : DirichletCharacter ℂ (lvl N l)) :
    ∃ χ : ∀ i, DirichletCharacter ℂ (N i), listChar χ l = Ψ := by
  induction l with
  | nil =>
    refine ⟨fun _ => 1, ?_⟩
    show (1 : DirichletCharacter ℂ 1) = Ψ
    exact (DirichletCharacter.level_one Ψ).symm
  | cons a l ih =>
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hl
    have hc := coprime_lvl hl.1
    obtain ⟨χ', hχ'⟩ := ih hnd.2 hl.2 (PAG.Part194.comp₂ hc Ψ)
    refine ⟨Function.update χ' a (PAG.Part194.comp₁ hc Ψ), ?_⟩
    show PAG.Part260.prodChar _ (listChar _ l) = Ψ
    rw [Function.update_self,
      listChar_congr l (fun i hi => Function.update_of_ne (fun h : i = a => hnd.1 (h ▸ hi)) _ _), hχ']
    exact (PAG.Part194.decomp hc Ψ).symm

omit [DecidableEq ι] in

theorem listChar_injective (l : List ι) (hl : l.Pairwise fun i j => (N i).Coprime (N j))
    {χ χ' : ∀ i, DirichletCharacter ℂ (N i)} (h : listChar χ l = listChar χ' l) :
    ∀ i ∈ l, χ i = χ' i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hl
    have h' : PAG.Part236.charMul (χ a) (listChar χ l) = PAG.Part236.charMul (χ' a) (listChar χ' l) := h
    obtain ⟨h1, h2⟩ := PAG.Part236.charMul_injective (coprime_lvl hl.1) h'
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact h1
    · exact ih hl.2 h2 i hi

omit [DecidableEq ι] in

theorem gaussSum_listChar_singleton (χ : ∀ i, DirichletCharacter ℂ (N i)) (a : ι) :
    gaussSum (listChar χ [a]) stdAddChar = gaussSum (χ a) stdAddChar := by
  rw [gaussSum_listChar χ [a] (List.pairwise_singleton _ _)]
  have h1 : listChar χ [] (N a : ZMod (lvl N [])) = 1 := listChar_natCast χ [] (N a)
  have h2 : χ a (lvl N [] : ZMod (N a)) = 1 := by
    show χ a ((1 : ℕ) : ZMod (N a)) = 1
    rw [Nat.cast_one, map_one]
  simp only [cross, h1, h2, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

end PAG.Part261

namespace PAG.Part261

theorem pairwise_primeFactors (n : ℕ) :
    n.primeFactors.toList.Pairwise fun p q => (p ^ n.factorization p).Coprime (q ^ n.factorization q) := by
  refine (Finset.nodup_toList _).imp_of_mem (fun hp hq hne => ?_)
  have hp' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hp)
  have hq' := Nat.prime_of_mem_primeFactors (Finset.mem_toList.mp hq)
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp' hq').mpr hne)

theorem lvl_primeFactors (n : ℕ) (hn : n ≠ 0) : lvl (fun p => p ^ n.factorization p) n.primeFactors.toList = n := by
  rw [lvl_eq_prod, Finset.prod_map_toList]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

theorem gaussSum_primeFactors (n : ℕ) [NeZero n] (Ψ : DirichletCharacter ℂ n) :
    ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
      (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
      gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
        ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod := by
  have key : ∀ (m : ℕ) [NeZero m], lvl (fun p => p ^ n.factorization p) n.primeFactors.toList = m →
      ∀ Ψ : DirichletCharacter ℂ m, ∃ χ : ∀ p, DirichletCharacter ℂ (p ^ n.factorization p),
        (∀ x : ℕ, Ψ x = (n.primeFactors.toList.map fun p => χ p (x : ZMod (p ^ n.factorization p))).prod) ∧
        gaussSum Ψ stdAddChar = (n.primeFactors.toList.map fun p => gaussSum (χ p) stdAddChar *
          ((n.primeFactors.toList.erase p).map fun q => χ q ((p ^ n.factorization p : ℕ) : ZMod (q ^ n.factorization q))).prod).prod := by
    intro m _ hm Ψ
    subst hm
    obtain ⟨χ, hχ⟩ := exists_listChar _ (Finset.nodup_toList _) (pairwise_primeFactors n) Ψ
    refine ⟨χ, fun x => ?_, ?_⟩
    · rw [← hχ, listChar_natCast]
    · rw [← hχ, gaussSum_listChar χ _ (pairwise_primeFactors n),
        cross_eq_formII χ _ (Finset.nodup_toList _), List.prod_map_mul, mul_comm]
  exact key n (lvl_primeFactors n (NeZero.ne n)) Ψ

end PAG.Part261

#print axioms PAG.Part261.lvl_cons
#print axioms PAG.Part261.lvl_eq_prod
#print axioms PAG.Part261.coprime_lvl
#print axioms PAG.Part261.gaussSum_listChar
#print axioms PAG.Part261.listChar_natCast
#print axioms PAG.Part261.listChar_neg_one
#print axioms PAG.Part261.cross_eq_formI
#print axioms PAG.Part261.cross_eq_formII
#print axioms PAG.Part261.sqrt_lvl
#print axioms PAG.Part261.prod_map_div'
#print axioms PAG.Part261.rootNum_listChar_formII
#print axioms PAG.Part261.rootNum_listChar_formI
#print axioms PAG.Part261.listChar_neg_one_pow
#print axioms PAG.Part261.tri_succ
#print axioms PAG.Part261.parFac_listChar
#print axioms PAG.Part261.rootNum_listChar
#print axioms PAG.Part261.isPrimitive_listChar_iff
#print axioms PAG.Part261.phaseA1_listChar
#print axioms PAG.Part261.listChar_congr
#print axioms PAG.Part261.exists_listChar
#print axioms PAG.Part261.listChar_injective
#print axioms PAG.Part261.gaussSum_listChar_singleton
#print axioms PAG.Part261.pairwise_primeFactors
#print axioms PAG.Part261.lvl_primeFactors
#print axioms PAG.Part261.gaussSum_primeFactors
