/-
  PAG 2.0 Part 15（2026-10-18）
  1. 定理 B の一般殻版: ι_*π^*χ ⋆ ι_*π^*χ⁻¹ = q χ(−1) · ι_*π^*(c_N)
  2. 核の大きさ q = |ker π| の値: |G| = q |H|、ZMod では q = p^(m−c)
  3. 規格化係数の整理（Part 5 定理 A の √(p^K/|S_{w0}|) との一致、二乗形）
-/
import PAG18

namespace PAG.Part19

open ZMod Finset PAG.Part17 PAG.Part18

/-! ## 1. 定理 B の一般殻版 -/

section ThmB

variable {N : ℕ} [NeZero N]

/-- ラマヌジャン和 c_N(x) = Σ_{k 単数} ψ(kx)（Mathlib の形: Σ_k ψ(kx)·1(−k)）。 -/
noncomputable def ram (x : ZMod N) : ℂ :=
  ∑ k : ZMod N, stdAddChar (k * x) * (1 : DirichletCharacter ℂ N) (-k)

/-- 頂上殻の定理 B（関数の等式）: χ ⋆ χ⁻¹ = χ(−1) · c_N。 -/
theorem conv_char_inv_fun (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (χ : ZMod N → ℂ) (χ⁻¹ : DirichletCharacter ℂ N) = χ (-1) • (ram (N := N)) := by
  funext x
  rw [PAG.Part16.conv_char_inv χ hχ x, Pi.smul_apply, smul_eq_mul, ram]

/-- **定理 B（一般殻）**: ι_*π^*χ ⋆ ι_*π^*χ⁻¹ = (q χ(−1)) · ι_*π^*(c_N)。 -/
theorem conv_shell_inv {G L : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup L] [Fintype L]
    (ι : L →+ G) (hι : Function.Injective ι) (π : L →+ ZMod N) (hπ : Function.Surjective π)
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (push ι ((χ : ZMod N → ℂ) ∘ π)) (push ι (((χ⁻¹ : DirichletCharacter ℂ N) : ZMod N → ℂ) ∘ π))
      = (((univ.filter (fun z : L => π z = 0)).card : ℂ) * χ (-1)) • push ι (ram (N := N) ∘ π) := by
  classical
  rw [conv_shell_general ι hι π hπ, conv_char_inv_fun χ hχ]
  rw [show (χ (-1) • ram (N := N)) ∘ π = χ (-1) • (ram (N := N) ∘ π) from rfl, push_smul ι hι, smul_smul]

end ThmB

/-! ## 2. 核の大きさ -/

section Kernel

/-- 全射準同型 π : G → H について |G| = |ker π| · |H|。 -/
theorem card_eq_ker_mul {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    [DecidableEq H] (π : G →+ H) (hπ : Function.Surjective π) :
    (Fintype.card G : ℂ) = ((univ.filter (fun z : G => π z = 0)).card : ℂ) * Fintype.card H := by
  have := sum_comp_surj π hπ (fun _ => (1 : ℂ))
  simpa [Finset.card_univ] using this

/-- **q = p^(m−c)**: 射影 ZMod p^m → ZMod p^c（c ≤ m）の核の大きさ。 -/
theorem card_ker_castHom (p m c : ℕ) [hp : Fact p.Prime] (hc : c ≤ m) :
    have : NeZero (p ^ m) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    (univ.filter (fun z : ZMod (p ^ m) =>
      (ZMod.castHom (pow_dvd_pow p hc) (ZMod (p ^ c))).toAddMonoidHom z = 0)).card = p ^ (m - c) := by
  intro _ _
  have h := card_eq_ker_mul (ZMod.castHom (pow_dvd_pow p hc) (ZMod (p ^ c))).toAddMonoidHom
    (ZMod.ringHom_surjective _)
  rw [ZMod.card, ZMod.card] at h
  have h' : p ^ m = (univ.filter (fun z : ZMod (p ^ m) =>
      (ZMod.castHom (pow_dvd_pow p hc) (ZMod (p ^ c))).toAddMonoidHom z = 0)).card * p ^ c := by
    exact_mod_cast h
  have hpc : 0 < p ^ c := pow_pos hp.out.pos c
  have e : p ^ m = p ^ (m - c) * p ^ c := by rw [← pow_add, Nat.sub_add_cancel hc]
  exact Nat.eq_of_mul_eq_mul_right hpc (h'.symm.trans e)

end Kernel

/-! ## 3. 規格化係数の整理 -/

section Coef

/-- 殻サイズ |S_u| = p^(K−1−u)(p−1)。 -/
def sz (p K u : ℕ) : ℕ := p ^ (K - 1 - u) * (p - 1)

/-- **規格化係数の一致（二乗形）**: c = v + c'' + 1（c' = c − v ≥ 1）、K = w + c + a のとき
|S_{w+v}| · q² · p^(c+v) · |S_{w0}| = p^K · |S_w|²（q = p^(K−w−c)、w0 = K − c − w）。
これは |S_w|⁻¹ √|S_{w+v}| q p^(c−c'/2) = √(p^K/|S_{w0}|) の二乗を払った形
（p^(2c−c') = p^(c+v)）。 -/
theorem coef_identity (p K c w v c'' a : ℕ) (hc : c = v + c'' + 1) (hK : K = w + c + a) :
    sz p K (w + v) * (p ^ (K - w - c)) ^ 2 * p ^ (c + v) * sz p K (K - c - w) = p ^ K * (sz p K w) ^ 2 := by
  have h1 : K - 1 - (w + v) = c'' + a := by omega
  have h2 : K - w - c = a := by omega
  have h3 : K - 1 - (K - c - w) = v + c'' + w := by omega
  have h4 : K - 1 - w = v + c'' + a := by omega
  simp only [sz, h1, h2, h3, h4]
  subst hK; subst hc
  ring

/-- 実数版: |S_{w+v}| q² p^(c+v) / |S_w|² = p^K / |S_{w0}|（p ≥ 2）。 -/
theorem coef_identity_real (p K c w v c'' a : ℕ) (hp : 2 ≤ p) (hc : c = v + c'' + 1) (hK : K = w + c + a) :
    (sz p K (w + v) : ℝ) * ((p : ℝ) ^ (K - w - c)) ^ 2 * (p : ℝ) ^ (c + v) / (sz p K w : ℝ) ^ 2
      = (p : ℝ) ^ K / sz p K (K - c - w) := by
  have hS : ∀ u, (sz p K u : ℝ) ≠ 0 := fun u => by
    unfold sz; exact_mod_cast Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
  have keyR : (sz p K (w + v) : ℝ) * ((p : ℝ) ^ (K - w - c)) ^ 2 * (p : ℝ) ^ (c + v) * sz p K (K - c - w)
      = (p : ℝ) ^ K * (sz p K w : ℝ) ^ 2 := by exact_mod_cast coef_identity p K c w v c'' a hc hK
  rw [div_eq_div_iff (pow_ne_zero 2 (hS w)) (hS _)]
  linear_combination keyR

end Coef

/-! ## 4. ラマヌジャン和の値（殻ごとの展開） -/

section Ramanujan

variable {p n : ℕ} [hp : Fact p.Prime]

/-- 非単数 = 殻 ≥ 1 = ι_1 の像（ZMod p^(n+1)）。 -/
theorem not_isUnit_iff_mem_range (k : ZMod (p ^ (n + 1))) :
    ¬ IsUnit k ↔ ∃ j, shellEmb (p := p) (n + 1) 1 (by omega) j = k := by
  have : NeZero (p ^ (n + 1 - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpow : p ^ (n + 1) = p * p ^ (n + 1 - 1) := by rw [Nat.add_sub_cancel, pow_succ']
  constructor
  · intro hk
    obtain ⟨t, ht⟩ := PAG.Part8.p_dvd_val_of_not_isUnit k hk
    refine ⟨(t : ZMod (p ^ (n + 1 - 1))), ?_⟩
    rw [shellEmb_apply, pow_one, ZMod.val_natCast, ← ZMod.natCast_zmod_val k, ht,
      ZMod.natCast_eq_natCast_iff']
    rw [hpow, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left, Nat.mod_mod]
  · rintro ⟨j, rfl⟩ hu
    rw [shellEmb_apply, pow_one, ZMod.isUnit_iff_coprime] at hu
    have h1 : Nat.Coprime p (p ^ (n + 1)) := Nat.Coprime.coprime_dvd_left (dvd_mul_right p _) hu
    have h2 : p ∣ Nat.gcd p (p ^ (n + 1)) := Nat.dvd_gcd dvd_rfl (dvd_pow_self p (Nat.succ_ne_zero n))
    rw [h1] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)

/-- (1 : χ)(−k) = 1 − ι_{1,*}1(k)。 -/
theorem one_neg_eq (k : ZMod (p ^ (n + 1))) :
    (1 : DirichletCharacter ℂ (p ^ (n + 1))) (-k)
      = 1 - push (shellEmb (p := p) (n + 1) 1 (by omega)) (fun _ => (1 : ℂ)) k := by
  by_cases hk : IsUnit k
  · have hnot : ¬ ∃ j, shellEmb (p := p) (n + 1) 1 (by omega) j = k :=
      fun h => (not_isUnit_iff_mem_range k).mpr h hk
    rw [MulChar.one_apply hk.neg, push, Function.extend_apply' _ _ _ hnot, Pi.zero_apply, sub_zero]
  · obtain ⟨j, hj⟩ := (not_isUnit_iff_mem_range k).mp hk
    have hnk : ¬ IsUnit (-k) := fun h => hk (by simpa using h.neg)
    rw [MulChar.map_nonunit _ hnk, ← hj, push, (shellEmb_injective (p := p) (n + 1) 1 (by omega)).extend_apply,
      sub_self]

/-- **ラマヌジャン和の値**: c_{p^(n+1)}(x) = p^(n+1)·[x = 0] − p^n·[x ≡ 0 mod p^n]。
すなわち v_p(x) ≥ n+1 で φ(p^(n+1))、v_p(x) = n で −p^n、それ以外で 0。 -/
theorem ram_eq (x : ZMod (p ^ (n + 1))) :
    have : NeZero (p ^ (n + 1 - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    ram x = (if x = 0 then ((p ^ (n + 1) : ℕ) : ℂ) else 0)
      - (if ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) 1)) (ZMod (p ^ (n + 1 - 1))) x = 0
          then ((p ^ (n + 1 - 1) : ℕ) : ℂ) else 0) := by
  intro _
  set ι := shellEmb (p := p) (n + 1) 1 (by omega)
  have hι := shellEmb_injective (p := p) (n + 1) 1 (by omega)
  unfold ram
  simp_rw [one_neg_eq, mul_sub, mul_one, sum_sub_distrib]
  congr 1
  · rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar _), ZMod.card]
    split_ifs <;> simp
  · have hF := dft_push (n + 1) 1 (by omega) (fun _ => (1 : ℂ)) (-x)
    dsimp only at hF
    rw [dft_apply, dft_apply] at hF
    simp only [smul_eq_mul, mul_one, neg_neg, mul_neg] at hF
    rw [show (∑ k, stdAddChar (k * x) * push ι (fun _ => (1 : ℂ)) k)
        = ∑ k, stdAddChar (k * x) * push (shellEmb (p := p) (n + 1) 1 (by omega)) (fun _ => (1 : ℂ)) k from rfl]
    rw [hF, map_neg]
    simp only [mul_neg, neg_neg]
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar _), ZMod.card]
    split_ifs <;> simp

end Ramanujan

end PAG.Part19

#print axioms PAG.Part19.conv_char_inv_fun
#print axioms PAG.Part19.conv_shell_inv
#print axioms PAG.Part19.card_eq_ker_mul
#print axioms PAG.Part19.card_ker_castHom
#print axioms PAG.Part19.coef_identity
#print axioms PAG.Part19.coef_identity_real
#print axioms PAG.Part19.not_isUnit_iff_mem_range
#print axioms PAG.Part19.one_neg_eq
#print axioms PAG.Part19.ram_eq
