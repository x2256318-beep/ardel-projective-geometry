/-
  PAG 2.0 Part 94（2026-10-19）— 巡回構造の予想の証明: U_k^{o} は V_a 上のスカラー（χ^o = 1）
  任意の素数、k = |w, χ⟩（原始、双対殻 a）、χ^o = 1（o ≥ 1）のとき
    t, t' ∈ T_a ⇒ 𝓕k(t)^o = 𝓕k(t')^o
  すなわち T_k^o は V_a 上でスカラー（固有値がすべて等しい）
  証明: (1) ケットの単数同変性 k(u x) = χ(u) k(x)
        (2) 同変性は畳み込みで掛け合わされる ⇒ k^{⋆o} は χ^o = 1 同変、すなわち単数不変
        (3) 単数不変な関数は IndSpan に入る（殻の上で定数）
        (4) V_a ∩ IndSpan = span{ε_a} ⇒ k^{⋆o} = c·ε_a ⇒ (𝓕k)^o = c·𝓕ε_a は T_a 上で定数
-/
import PAG97

namespace PAG.Part98

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part51 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part59 PAG.Part89 PAG.Part90
  PAG.Part93 PAG.Part95 PAG.Part97

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- shellEmb は自然数倍と可換。 -/
theorem natCast_mul_shellEmb (K w : ℕ) (hw : w ≤ K) (m : ℕ) (y : ZMod (p ^ (K - w))) :
    (m : ZMod (p ^ K)) * shellEmb (p := p) K w hw y = shellEmb (p := p) K w hw ((m : ZMod (p ^ (K - w))) * y) := by
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]

/-- 同変性。 -/
def Equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (f : ZMod (p ^ K) → ℂ) : Prop :=
  ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), f (u * x) = α u * f x

/-- **(1) ケットの単数同変性**。 -/
theorem ket_equivariant (K w c : ℕ) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    Equivariant (p := p) K (fun u => χ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K)) (ZMod (p ^ c)) u))
      (ket K w c h χ) := by
  intro u x
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set m := (u : ZMod (p ^ K)).val with hm
  have hu : ((m : ℕ) : ZMod (p ^ K)) = u := ZMod.natCast_zmod_val _
  by_cases hx : ∃ y, shellEmb (p := p) K w (by omega) y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [← hu, natCast_mul_shellEmb, ket_apply_emb, ket_apply_emb, map_mul, map_natCast]
    simp only []
    rw [← hu, map_natCast, map_mul]
    ring
  · have h0 : ket K w c h χ x = 0 := by
      unfold ket; rw [Pi.smul_apply, push_apply_not _ _ _ hx, smul_zero]
    have h1 : ket K w c h χ (↑u * x) = 0 := by
      unfold ket
      rw [Pi.smul_apply, push_apply_not _ _ _ ?_, smul_zero]
      rintro ⟨y, hy⟩
      apply hx
      set m' := ((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)).val
      have hu' : ((m' : ℕ) : ZMod (p ^ K)) = ((u⁻¹ : (ZMod (p ^ K))ˣ) : ZMod (p ^ K)) := ZMod.natCast_zmod_val _
      refine ⟨((m' : ℕ) : ZMod (p ^ (K - w))) * y, ?_⟩
      rw [← natCast_mul_shellEmb, hy, hu', ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [h0, h1, mul_zero]

/-- **(2) 同変性は畳み込みで掛け合わされる**。 -/
theorem conv_equivariant (K : ℕ) (α β : (ZMod (p ^ K))ˣ → ℂ) (f g : ZMod (p ^ K) → ℂ)
    (hf : Equivariant (p := p) K α f) (hg : Equivariant (p := p) K β g) :
    Equivariant (p := p) K (fun u => α u * β u) (conv f g) := by
  intro u x
  unfold conv
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Units.mulLeft u) _ _ (fun z => ?_) |>.symm
  simp only [Units.mulLeft_apply]
  rw [show (u : ZMod (p ^ K)) * x - u * z = u * (x - z) by ring, hf, hg]
  ring

/-- 多重積の同変性: prodConv k (replicate n k) は α^(n+1) 同変。 -/
theorem prodConv_equivariant (K : ℕ) (α : (ZMod (p ^ K))ˣ → ℂ) (k : ZMod (p ^ K) → ℂ)
    (hk : Equivariant (p := p) K α k) (n : ℕ) :
    Equivariant (p := p) K (fun u => α u ^ (n + 1)) (prodConv k (List.replicate n k)) := by
  induction n with
  | zero => simpa [prodConv] using hk
  | succ n ih =>
    simp only [List.replicate_succ, prodConv]
    have := conv_equivariant K α (fun u => α u ^ (n + 1)) k _ hk ih
    intro u x
    rw [this u x]
    simp only []
    ring

/-- 殻の点は単数倍で移り合う: shellEmb_w(y) = u·shellEmb_w(1)（y 単数）。 -/
theorem shell_point_eq_unit_mul (K w : ℕ) (hw : w < K) (y : ZMod (p ^ (K - w))) (hy : IsUnit y) :
    ∃ u : (ZMod (p ^ K))ˣ, shellEmb (p := p) K w hw.le y = u * shellEmb (p := p) K w hw.le 1 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (pow_dvd_pow p (Nat.sub_le K w) : p ^ (K - w) ∣ p ^ K) hy.unit
  refine ⟨u, ?_⟩
  have hv : ((u : ZMod (p ^ K)).val : ZMod (p ^ K)) = u := ZMod.natCast_zmod_val _
  have hy' : (((u : ZMod (p ^ K)).val : ℕ) : ZMod (p ^ (K - w))) = y := by
    have e := congrArg (fun v : (ZMod (p ^ (K - w)))ˣ => (v : ZMod (p ^ (K - w)))) hu
    simp only [ZMod.unitsMap_val, IsUnit.unit_spec] at e
    rw [← e, ZMod.cast_eq_val]
  rw [← hv, natCast_mul_shellEmb, mul_one, hy']

/-- **(3) 単数不変な関数は IndSpan に入る**。 -/
theorem invariant_mem_IndSpan (K : ℕ) (F : ZMod (p ^ K) → ℂ)
    (hF : ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), F (u * x) = F x) : F ∈ IndSpan (p := p) K := by
  have e : F = ∑ v : Fin K, F (shellEmb (p := p) K v (by omega) 1) • shellInd (p := p) K v v.2
      + F 0 • Pi.single (0 : ZMod (p ^ K)) (1 : ℂ) := by
    funext x
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x = 0
    · subst hx
      simp [shellInd_zero]
    · obtain ⟨w, hw, y, hy, rfl⟩ := exists_shell (p := p) K x hx
      rw [Finset.sum_eq_single ⟨w, hw⟩]
      · rw [shellInd_apply K w w hw hw y hy, ite_eq_left_of_eq_true _ _ (eq_true rfl), mul_one, Pi.single_apply,
          ite_eq_right_of_eq_false _ _ (eq_false hx), mul_zero, add_zero]
        obtain ⟨u, hu⟩ := shell_point_eq_unit_mul K w hw y hy
        rw [hu, hF]
      · intro v _ hv
        rw [shellInd_apply K v w v.2 hw y hy, ite_eq_right_of_eq_false _ _ (eq_false (fun h => hv (Fin.ext h))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  rw [e]
  refine Submodule.add_mem _ (Submodule.sum_mem _ (fun v _ => Submodule.smul_mem _ _ ?_))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))
  exact Submodule.subset_span (Or.inl ⟨v, v.2, rfl⟩)

/-- **巡回構造の定理**: χ^(n+1) = 1 なら、t, t' ∈ T_a で 𝓕k(t)^(n+1) = 𝓕k(t')^(n+1)。 -/
theorem pow_eigen_const (K w c : ℕ) (h : w + c ≤ K) (hc : 1 ≤ c) (χ : DirichletCharacter ℂ (p ^ c))
    (hχ : χ.IsPrimitive) (n : ℕ) (ho : χ ^ (n + 1) = 1) (t t' : ZMod (p ^ K))
    (ht : t ∈ Tset (p := p) K (K - c - w)) (ht' : t' ∈ Tset (p := p) K (K - c - w)) :
    𝓕 (ket K w c h χ) t ^ (n + 1) = 𝓕 (ket K w c h χ) t' ^ (n + 1) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  set k := ket K w (c' + 1) h χ
  have hkd : KetDual (p := p) K (K - (c' + 1) - w) k := ⟨w, c', h, χ, hχ, rfl, rfl⟩
  set F := prodConv k (List.replicate n k)
  -- F は単数不変
  have hinv : ∀ (u : (ZMod (p ^ K))ˣ) (x : ZMod (p ^ K)), F (u * x) = F x := by
    intro u x
    have := prodConv_equivariant K _ k (ket_equivariant K w (c' + 1) h χ) n u x
    show prodConv k (List.replicate n k) (u * x) = prodConv k (List.replicate n k) x
    rw [this]
    simp only []
    rw [← MulChar.pow_apply' χ (by omega : n + 1 ≠ 0), ho, MulChar.one_apply ((Units.isUnit u).map _), one_mul]
  -- F ∈ V_a
  have hVa : conv (eps (p := p) K (K - (c' + 1) - w)) F = F :=
    (prodConv_same_dual K _ k (List.replicate n k) hkd (fun g hg => by
      rw [List.eq_of_mem_replicate hg]; exact hkd)).1
  -- F = c·ε_a
  have hmem := PAG.Part93.eps_conv_mem K (K - (c' + 1) - w) (by omega) F (invariant_mem_IndSpan K F hinv)
  rw [hVa] at hmem
  obtain ⟨C, hC⟩ := Submodule.mem_span_singleton.mp hmem
  have hd : ∀ s, 𝓕 k s ^ (n + 1) = C * 𝓕 (eps (p := p) K (K - (c' + 1) - w)) s := by
    intro s
    have e1 : 𝓕 F s = 𝓕 k s ^ (n + 1) := by
      rw [dft_prodConv, ← List.replicate_succ, List.map_replicate, List.prod_replicate]
    rw [← e1, ← hC, LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul]
  have h1 : 𝓕 (eps (p := p) K (K - (c' + 1) - w)) t = 1 := by simpa [Tset] using ht
  have h2 : 𝓕 (eps (p := p) K (K - (c' + 1) - w)) t' = 1 := by simpa [Tset] using ht'
  rw [hd t, hd t', h1, h2]

end PAG.Part98

#print axioms PAG.Part98.natCast_mul_shellEmb
#print axioms PAG.Part98.ket_equivariant
#print axioms PAG.Part98.conv_equivariant
#print axioms PAG.Part98.prodConv_equivariant
#print axioms PAG.Part98.shell_point_eq_unit_mul
#print axioms PAG.Part98.invariant_mem_IndSpan
#print axioms PAG.Part98.pow_eigen_const
