/-
  PAG 2.0 Part 102（2026-10-19）— ケットの引き戻しと作用素の整合（帰納系 K → K+1）
  任意の素数、1 ≤ c、w + c ≤ K、χ（法 p^c）について
  1. π^*|w, χ⟩_K = √p · |w, χ⟩_{K+1}（殻・導手は同じ、双対殻は a → a+1）
  2. 作用素の整合: π^*(k ⋆ f) = (1/√p) · k' ⋆ π^* f（k' = |w, χ⟩_{K+1}）
  3. 系: J = p^{-1/2} π^* は等長で、J U_k = U_{k'} J（λ' = p λ）
-/
import PAG105

namespace PAG.Part106

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part54 PAG.Part55 PAG.Part57 PAG.Part105

variable {p : ℕ} [hp : Fact p.Prime]

/-- π(ι_{K+1,v} y) = ι_{K,v}(y mod p^{K−v})。 -/
theorem proj_shellEmb (K v : ℕ) (hv : v ≤ K) (y : ZMod (p ^ (K + 1 - v))) :
    proj (p := p) K (shellEmb (p := p) (K + 1) v (by omega) y)
      = shellEmb (p := p) K v hv (ZMod.castHom (pow_dvd_pow p (by omega : K - v ≤ K + 1 - v)) _ y) := by
  have : NeZero (p ^ (K + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [proj_apply, shellEmb_apply, shellEmb_apply, map_natCast, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.val_natCast]
  rw [ZMod.natCast_eq_natCast_iff']
  have hK : p ^ K = p ^ v * p ^ (K - v) := by rw [← pow_add]; congr 1; omega
  rw [hK, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]

/-- 異なる殻の点では、非単数で消える関数の押し出しは 0。 -/
theorem push_shell_ne (K w v : ℕ) (hw : w < K) (hv : v < K) (hne : v ≠ w)
    (f : ZMod (p ^ (K - w)) → ℂ) (hf : VanishNU f) (y : ZMod (p ^ (K - v))) (hy : IsUnit y) :
    push (shellEmb (p := p) K w hw.le) f (shellEmb (p := p) K v hv.le y) = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- v < w: 点は殻 w の像に入らない
    apply push_apply_not
    rintro ⟨z, hz⟩
    rw [shellEmb_lower K w v hlt hw z] at hz
    have e := shellEmb_injective (p := p) K v hv.le hz
    apply not_dvd_val_of_unit (m := K - v) (by omega) y hy
    rw [← e, ZMod.val_natCast]
    have hlt' : p ^ (w - v) * z.val < p ^ (K - v) := by
      have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
      calc p ^ (w - v) * z.val < p ^ (w - v) * p ^ (K - w) :=
            Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) (pow_pos hp.out.pos _)
        _ = p ^ (K - v) := by rw [← pow_add]; congr 1; omega
    rw [Nat.mod_eq_of_lt hlt']
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  · -- w < v: 点は殻 w の非単数の像
    rw [shellEmb_lower K v w hgt hv y, push_apply_emb _ (shellEmb_injective K w hw.le)]
    apply hf
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_left]
    rintro ⟨h1, -⟩
    rw [Nat.coprime_pow_left_iff (by omega), Nat.coprime_pow_right_iff (by omega), Nat.coprime_self] at h1
    exact hp.out.one_lt.ne' h1

theorem ket_shell_ne (K w c v : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (hv : v < K) (hne : v ≠ w)
    (χ : DirichletCharacter ℂ (p ^ c)) (y : ZMod (p ^ (K - v))) (hy : IsUnit y) :
    ket K w c h χ (shellEmb (p := p) K v hv.le y) = 0 := by
  rw [ket_eq_push, Pi.smul_apply, push_shell_ne K w v (by omega) hv hne _ (vanish_ket K w c hc h χ) y hy,
    smul_zero]

omit hp in
theorem sz_succ (K w : ℕ) (hw : w < K) : sz p (K + 1) w = p * sz p K w := by
  unfold sz
  rw [show K + 1 - 1 - w = (K - 1 - w) + 1 by omega, pow_succ]; ring

/-- **ケットの引き戻し**: π^*|w, χ⟩_K = √p · |w, χ⟩_{K+1}。 -/
theorem pull_ket (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c)) :
    pull (p := p) K (ket K w c h χ) = ((Real.sqrt p : ℝ) : ℂ) • ket (K + 1) w c (by omega) χ := by
  have : NeZero (p ^ (K + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  funext x
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hx : x = 0
  · subst hx
    simp only [pull, Function.comp, map_zero]
    rw [PAG.Part49.ket_apply_zero K w c hc h χ, PAG.Part49.ket_apply_zero (K + 1) w c hc (by omega) χ, mul_zero]
  obtain ⟨v, hv, y, hy, rfl⟩ := exists_shell (p := p) (K + 1) x hx
  simp only [pull, Function.comp]
  rw [proj_shellEmb K v (by omega) y]
  have hy' : IsUnit (ZMod.castHom (pow_dvd_pow p (by omega : K - v ≤ K + 1 - v)) (ZMod (p ^ (K - v))) y) :=
    hy.map _
  by_cases hvw : v = w
  · subst hvw
    rw [PAG.Part51.ket_apply_emb, PAG.Part51.ket_apply_emb]
    have hcast : ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - v)) (ZMod (p ^ c))
        (ZMod.castHom (pow_dvd_pow p (by omega : K - v ≤ K + 1 - v)) (ZMod (p ^ (K - v))) y)
        = ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K + 1 - v)) (ZMod (p ^ c)) y := by
      have : NeZero (p ^ (K + 1 - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
      have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
      simp only [ZMod.castHom_apply]
      have e1 : (y.cast : ZMod (p ^ (K - v))) = ((y.val : ℕ) : ZMod (p ^ (K - v))) := ZMod.cast_eq_val y
      have e2 : (y.cast : ZMod (p ^ c)) = ((y.val : ℕ) : ZMod (p ^ c)) := ZMod.cast_eq_val y
      rw [e1, e2, ZMod.cast_natCast (pow_dvd_pow p (by omega : c ≤ K - v))]
    rw [hcast]
    have hs := sz_succ (p := p) K v (by omega)
    have hpos : (0 : ℝ) < sz p K v := by
      have : 0 < sz p K v := by
        unfold sz; exact Nat.mul_pos (pow_pos hp.out.pos _) (Nat.sub_pos_of_lt hp.out.one_lt)
      exact_mod_cast this
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have hr : (Real.sqrt (sz p K v))⁻¹ = Real.sqrt p * (Real.sqrt (sz p (K + 1) v))⁻¹ := by
      rw [hs, Nat.cast_mul, Real.sqrt_mul hp0.le, mul_inv, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hp0).ne',
        one_mul]
    rw [hr]; push_cast; ring
  · rw [ket_shell_ne (K + 1) w c v hc (by omega) hv hvw χ y hy, mul_zero]
    by_cases hvK : v = K
    · subst hvK
      have : ZMod.castHom (pow_dvd_pow p (by omega : v - v ≤ v + 1 - v)) (ZMod (p ^ (v - v))) y = 0 := by
        have : Subsingleton (ZMod (p ^ (v - v))) := by rw [Nat.sub_self, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [this, map_zero, PAG.Part49.ket_apply_zero v w c hc h χ]
    · exact ket_shell_ne K w c v hc h (by omega) hvw χ _ hy'

/-- **作用素の整合**: π^*(k ⋆ f) = (1/√p)·(k' ⋆ π^* f)。 -/
theorem pull_conv_ket (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (χ : DirichletCharacter ℂ (p ^ c))
    (f : ZMod (p ^ K) → ℂ) :
    (Real.sqrt p : ℂ) • pull (p := p) K (conv (ket K w c h χ) f)
      = conv (ket (K + 1) w c (by omega) χ) (pull (p := p) K f) := by
  have e := conv_pull (p := p) K (ket K w c h χ) f
  rw [pull_ket K w c hc h χ] at e
  have hsq : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by exact_mod_cast hp.out.pos.le)]; simp
  have hs0 : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
    exact_mod_cast this.ne'
  rw [show conv (((Real.sqrt p : ℝ) : ℂ) • ket (K + 1) w c (by omega) χ) (pull (p := p) K f)
      = ((Real.sqrt p : ℝ) : ℂ) • conv (ket (K + 1) w c (by omega) χ) (pull (p := p) K f) by
    rw [conv_comm, PAG.Part58.conv_smul_right', conv_comm], ← hsq, mul_smul] at e
  exact (smul_right_injective _ hs0 e).symm

end PAG.Part106

#print axioms PAG.Part106.proj_shellEmb
#print axioms PAG.Part106.push_shell_ne
#print axioms PAG.Part106.ket_shell_ne
#print axioms PAG.Part106.sz_succ
#print axioms PAG.Part106.pull_ket
#print axioms PAG.Part106.pull_conv_ket
