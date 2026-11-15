/-
  PAG 2.0 Part 186（2026-10-23）— 同じ素数の上の積：十分条件と完全な判定
  p は素数、χ は法 p の乗法的指標で n = ord χ、ψ は原始的な加法的指標、z_j = τ(χ^j)/√p（1 ≤ j ≤ n − 1）、
  ⟨x⟩ = x mod n、S_c(a) = Σ_j a_j (n − 2⟨cj⟩)。
  1. ℤ[μ] からの環準同型：生成元を 1 の原始 n 乗根に送るものがある。ℤ_p への ι_c と ℂ への σ_c
     （σ_c ∘ χ = χ^c）
  2. ヴァンデルモンド：det(V)·w = adj(V)(Vw)。ℤ_p では行列式が単元なので「評価がすべて p^m で割れる ⇒
     座標が p^m で割れる」。ℂ では「評価の絶対値が 1 以下 ⇒ 座標が有界」
  3. クロネッカー（ℤ[μ] の中で）：すべての σ_k で絶対値 1 の元は 1 の冪根
  4. α_j = (pP)^{2j}、β_j = p^n Q_j^{2n} と、逆の指標の積で作る ᾱ_j, β̄_j：α_j ᾱ_j = β_j β̄_j = p^{2nj}
  5. 主定理 same_prime_sufficient：すべての c ∈ (ℤ/n)^× で S_c(a) = 0 なら ∏_j z_j^{a_j} は 1 の冪根
     （Y = (∏ z_j^{a_j})^{2n} = T/p^M。T が p^M ℤ[μ] に入ることをヴァンデルモンドで示し、T/p^M に
     クロネッカーを使う）
  6. 完全な判定 same_prime_root_iff：∏_j z_j^{a_j} が 1 の冪根 ⇔ すべての c で S_c(a) = 0（Part 185 と合わせる）
-/
import PAG189
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace PAG.Part190

open Complex Finset Polynomial Matrix
open PAG.Part185 (powChar)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### 1. ℤ[μ] からの環準同型 -/

/-- **1a.** 生成元の最小多項式が Φ_n なら、生成元を 1 の原始 n 乗根 ζ に送る環準同型がある。 -/
theorem exists_lift {A : Subalgebra ℤ ℂ} (pb : PowerBasis ℤ A) {n : ℕ} (hn : 0 < n)
    (hmin : minpoly ℤ pb.gen = cyclotomic n ℤ) {R : Type*} [CommRing R] [IsDomain R] (ζ : R)
    (hζ : IsPrimitiveRoot ζ n) : ∃ f : A →+* R, f pb.gen = ζ := by
  have hroot : aeval ζ (minpoly ℤ pb.gen) = 0 := by
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hn
  exact ⟨(pb.lift ζ hroot).toRingHom, pb.lift_gen ζ hroot⟩

/-- **1b.** 生成元 a の冪の像：f(χ_A(a^j)) = f(gen)^j。 -/
theorem lift_chiA_pow (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) (hμ : IsPrimitiveRoot (χ a) (orderOf χ))
    (pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ))) (hgen : (pb.gen : ℂ) = χ a)
    {R : Type*} [CommRing R] (f : Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ) →+* R) (j : ℕ) :
    f (PAG.Part185.chiA χ hμ ((a ^ j : (ZMod p)ˣ) : ZMod p)) = f pb.gen ^ j := by
  have : PAG.Part185.chiA χ hμ ((a ^ j : (ZMod p)ˣ) : ZMod p) = pb.gen ^ j := by
    apply Subtype.ext
    rw [PAG.Part185.chiA_apply, SubmonoidClass.coe_pow, hgen, Units.val_pow_eq_pow_val, map_pow]
  rw [this, map_pow]

/-- **1c.** ℤ_p への ι で ι(gen) ≡ a^{kc} (mod p) なら、mod p で χ_A ↦ powChar(kc)。 -/
theorem hev_of_lift (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) (ha : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, a ^ j = x)
    (hμ : IsPrimitiveRoot (χ a) (orderOf χ))
    (pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ))) (hgen : (pb.gen : ℂ) = χ a)
    (ι : Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ) →+* ℤ_[p]) (m : ℕ)
    (hι : PadicInt.toZMod (ι pb.gen) = (a : ZMod p) ^ m) :
    (PAG.Part185.chiA χ hμ).ringHomComp (PadicInt.toZMod.comp ι) = powChar m := by
  refine MulChar.ext (fun u => ?_)
  obtain ⟨j, rfl⟩ := ha u
  rw [MulChar.ringHomComp_apply, RingHom.comp_apply, lift_chiA_pow χ a hμ pb hgen ι j, map_pow, hι,
    PAG.Part185.powChar, MulChar.ofUnitHom_coe, powMonoidHom_apply, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm]

/-- **1d.** ℂ への σ で σ(gen) = μ^c なら、σ ∘ χ_A = χ^c。 -/
theorem hsig_of_lift (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) (ha : ∀ x : (ZMod p)ˣ, ∃ j : ℕ, a ^ j = x)
    (hμ : IsPrimitiveRoot (χ a) (orderOf χ))
    (pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ))) (hgen : (pb.gen : ℂ) = χ a)
    (σ : Algebra.adjoin ℤ ({(χ a : ℂ)} : Set ℂ) →+* ℂ) (c : ℕ) (hσ : σ pb.gen = χ a ^ c) :
    (PAG.Part185.chiA χ hμ).ringHomComp σ = χ ^ c := by
  refine MulChar.ext (fun u => ?_)
  obtain ⟨j, rfl⟩ := ha u
  rw [MulChar.ringHomComp_apply, lift_chiA_pow χ a hμ pb hgen σ j, hσ, MulChar.pow_apply_coe,
    Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul, mul_comm]

/-! ### 2. 座標とヴァンデルモンド -/

/-- **2a.** 冪基底の座標で f(y) = Σ_i y_i f(gen)^i。 -/
theorem eval_repr {A : Subalgebra ℤ ℂ} (pb : PowerBasis ℤ A) {R : Type*} [CommRing R] (f : A →+* R)
    (y : A) : f y = ∑ i : Fin pb.dim, ((pb.basis.repr y i : ℤ) : R) * f pb.gen ^ (i : ℕ) := by
  conv_lhs => rw [← pb.basis.sum_repr y]
  rw [map_sum]
  refine sum_congr rfl (fun i _ => ?_)
  rw [pb.basis_eq_pow, map_zsmul, map_pow, zsmul_eq_mul]

/-- **2b.** det(V)·w = adj(V)·(V·w)。 -/
theorem vandermonde_solve {R : Type*} [CommRing R] {d : ℕ} (v w : Fin d → R) :
    (vandermonde v).det • w = (vandermonde v).adjugate *ᵥ (vandermonde v *ᵥ w) := by
  rw [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]

/-- **2c. ℤ_p**：ヴァンデルモンドの行列式が単元で、評価 Σ_i w_i v_k^i がすべて p^m で割れるなら、
  整数 w_i もすべて p^m で割れる。 -/
theorem int_dvd_of_padic {d : ℕ} (v : Fin d → ℤ_[p]) (hv : IsUnit (vandermonde v).det) (w : Fin d → ℤ)
    (m : ℕ) (h : ∀ k, (p : ℤ_[p]) ^ m ∣ ∑ i, ((w i : ℤ) : ℤ_[p]) * v k ^ (i : ℕ)) :
    ∀ i, (p : ℤ) ^ m ∣ w i := by
  intro i
  set W : Fin d → ℤ_[p] := fun i => ((w i : ℤ) : ℤ_[p]) with hW
  have hsol := congrFun (vandermonde_solve v W) i
  have he : ∀ k, (p : ℤ_[p]) ^ m ∣ (vandermonde v *ᵥ W) k := by
    intro k
    have : (vandermonde v *ᵥ W) k = ∑ i, ((w i : ℤ) : ℤ_[p]) * v k ^ (i : ℕ) := by
      simp only [mulVec, dotProduct, vandermonde_apply, hW]
      exact sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [this]; exact h k
  have hadj : (p : ℤ_[p]) ^ m ∣ ((vandermonde v).adjugate *ᵥ (vandermonde v *ᵥ W)) i := by
    simp only [mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ => Dvd.dvd.mul_left (he k) _)
  rw [← hsol, Pi.smul_apply, smul_eq_mul] at hadj
  obtain ⟨u, hu⟩ := hv
  have hWi : (p : ℤ_[p]) ^ m ∣ W i := by
    have := Dvd.dvd.mul_left hadj (↑u⁻¹ : ℤ_[p])
    rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at this
  exact (PadicInt.pow_p_dvd_int_iff m (w i)).mp hWi

/-- **2d. ℂ**：ヴァンデルモンドの行列式が 0 でなければ、評価の絶対値がすべて 1 以下の座標は一様に有界。 -/
theorem coord_bound {d : ℕ} (v : Fin d → ℂ) (hv : (vandermonde v).det ≠ 0) :
    ∃ B : ℝ, ∀ w : Fin d → ℂ, (∀ k, ‖(vandermonde v *ᵥ w) k‖ ≤ 1) → ∀ i, ‖w i‖ ≤ B := by
  refine ⟨‖(vandermonde v).det‖⁻¹ * ∑ i, ∑ k, ‖(vandermonde v).adjugate i k‖, fun w hw i => ?_⟩
  have hsol := congrFun (vandermonde_solve v w) i
  rw [Pi.smul_apply, smul_eq_mul] at hsol
  have hwi : w i = (vandermonde v).det⁻¹ * ((vandermonde v).adjugate *ᵥ (vandermonde v *ᵥ w)) i := by
    rw [← hsol, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]
  rw [hwi, norm_mul, norm_inv]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (norm_nonneg _))
  calc ‖((vandermonde v).adjugate *ᵥ (vandermonde v *ᵥ w)) i‖
      ≤ ∑ k, ‖(vandermonde v).adjugate i k‖ * ‖(vandermonde v *ᵥ w) k‖ := by
        simp only [mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ k, ‖(vandermonde v).adjugate i k‖ := by
        apply sum_le_sum; intro k _
        exact mul_le_of_le_one_right (norm_nonneg _) (hw k)
    _ ≤ ∑ i, ∑ k, ‖(vandermonde v).adjugate i k‖ :=
        single_le_sum (f := fun i => ∑ k, ‖(vandermonde v).adjugate i k‖)
          (fun i _ => sum_nonneg (fun _ _ => norm_nonneg _)) (mem_univ i)

/-! ### 3. クロネッカー（ℤ[μ] の中で） -/

/-- **3a.** σ_k（k = 0, …, d − 1、d = 次数）での値の絶対値がすべて 1 以下の元は有限個。 -/
theorem finite_of_bounded {A : Subalgebra ℤ ℂ} (pb : PowerBasis ℤ A) (σ : Fin pb.dim → (A →+* ℂ))
    (hv : (vandermonde (fun k => σ k pb.gen)).det ≠ 0) :
    {y : A | ∀ k, ‖σ k y‖ ≤ 1}.Finite := by
  obtain ⟨B, hB⟩ := coord_bound (fun k => σ k pb.gen) hv
  have hfin : (Set.pi Set.univ (fun _ : Fin pb.dim => Set.Icc (-⌈B⌉) ⌈B⌉)).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  have hinj : Function.Injective (fun y : A => (fun i => pb.basis.repr y i : Fin pb.dim → ℤ)) := by
    intro y y' h
    apply pb.basis.repr.injective
    ext i
    exact congrFun h i
  refine (hfin.preimage hinj.injOn).subset (fun y hy => ?_)
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have hw := hB (fun i => ((pb.basis.repr y i : ℤ) : ℂ)) (fun k => by
    have e1 := eval_repr pb (σ k) y
    have e2 : (vandermonde (fun k => σ k pb.gen) *ᵥ (fun i => ((pb.basis.repr y i : ℤ) : ℂ))) k
        = σ k y := by
      simp only [mulVec, dotProduct, vandermonde_apply]
      rw [e1]
      exact sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [e2]; exact hy k) i
  rw [Complex.norm_intCast] at hw
  have h1 := (le_abs_self ((pb.basis.repr y i : ℤ) : ℝ)).trans (hw.trans (Int.le_ceil B))
  have h2 := (neg_abs_le ((pb.basis.repr y i : ℤ) : ℝ)).trans' (neg_le_neg (hw.trans (Int.le_ceil B)))
  constructor
  · exact_mod_cast h2
  · exact_mod_cast h1

/-- **3b. クロネッカー**：y ≠ 0 で、すべての σ_k で |σ_k(y)| = 1 なら、y は 1 の冪根。 -/
theorem root_of_norm_eq_one {A : Subalgebra ℤ ℂ} (pb : PowerBasis ℤ A) (σ : Fin pb.dim → (A →+* ℂ))
    (hv : (vandermonde (fun k => σ k pb.gen)).det ≠ 0) (y : A) (hy0 : y ≠ 0)
    (hy : ∀ k, ‖σ k y‖ = 1) : ∃ N : ℕ, 0 < N ∧ y ^ N = 1 := by
  obtain ⟨m, -, l, -, hml, h⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo (f := fun m : ℕ => y ^ m)
    Set.infinite_univ (fun m _ => show ∀ k, ‖σ k (y ^ m)‖ ≤ 1 from fun k => by
      rw [map_pow, norm_pow, hy k, one_pow])
    (finite_of_bounded pb σ hv)
  rcases lt_or_gt_of_ne hml with hlt | hlt
  · refine ⟨l - m, by omega, ?_⟩
    have : y ^ m * y ^ (l - m) = y ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]; exact h.symm
    exact mul_left_cancel₀ (pow_ne_zero _ hy0) this
  · refine ⟨m - l, by omega, ?_⟩
    have : y ^ l * y ^ (m - l) = y ^ l * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]; exact h
    exact mul_left_cancel₀ (pow_ne_zero _ hy0) this

/-! ### 3c. 節点 -/

omit hp in
/-- n と互いに素な 0 ≤ c < n を φ(n) 個並べる。 -/
theorem exists_nodes (n d : ℕ) (hd : d = n.totient) :
    ∃ cc : Fin d → ℕ, Function.Injective cc ∧ ∀ k, cc k < n ∧ (cc k).Coprime n := by
  set C := (range n).filter n.Coprime with hC
  have hcard : Fintype.card C = d := by rw [Fintype.card_coe, hd, Nat.totient_eq_card_coprime]
  let e := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun k => (e k).1, fun k l hkl => e.injective (Subtype.ext hkl), fun k => ?_⟩
  have h := Finset.mem_filter.mp (e k).2
  exact ⟨Finset.mem_range.mp h.1, h.2.symm⟩

omit hp in
/-- ℂ の節点 μ^{c_k} のヴァンデルモンドの行列式は 0 でない。 -/
theorem det_ne_zero_complex {n d : ℕ} {μ : ℂ} (hμ : IsPrimitiveRoot μ n) (cc : Fin d → ℕ)
    (hinj : Function.Injective cc) (hlt : ∀ k, cc k < n) :
    (vandermonde (fun k => μ ^ cc k)).det ≠ 0 := by
  rw [Ne, det_vandermonde_eq_zero_iff]
  rintro ⟨i, j, hij, hne⟩
  exact hne (hinj (hμ.pow_inj (hlt i) (hlt j) hij))

/-- ℤ_p の節点 z^{c_k}（z mod p が 1 の原始 n 乗根）のヴァンデルモンドの行列式は単元。 -/
theorem det_isUnit_padic {n d : ℕ} {z : ℤ_[p]} (hz : IsPrimitiveRoot (PadicInt.toZMod z) n)
    (cc : Fin d → ℕ) (hinj : Function.Injective cc) (hlt : ∀ k, cc k < n) :
    IsUnit (vandermonde (fun k => z ^ cc k)).det := by
  rw [PadicInt.isUnit_iff]
  apply PAG.Part189.norm_eq_one_of_toZMod_ne_zero
  rw [det_vandermonde, map_prod]
  refine prod_ne_zero_iff.mpr (fun i _ => ?_)
  rw [map_prod]
  refine prod_ne_zero_iff.mpr (fun j hj => ?_)
  rw [map_sub, map_pow, map_pow, sub_ne_zero]
  intro h
  rw [mem_Ioi] at hj
  exact absurd (hinj (hz.pow_inj (hlt j) (hlt i) h)) (ne_of_gt hj)

/-! ### 4. α_j, β_j とその共役 -/

section AB

variable {A : Subalgebra ℤ ℂ}

/-- α_j = (p·P)^{2j}（P = ∏_{i=1}^{n−2} J(χ_A, χ_A^i)）。 -/
noncomputable def alphaA (χA : MulChar (ZMod p) A) (n j : ℕ) : A :=
  ((p : A) * ∏ i ∈ Ico 1 (n - 1), jacobiSum χA (χA ^ i)) ^ (2 * j)

/-- β_j = p^n·Q_j^{2n}（Q_j = ∏_{i=1}^{j−1} J(χ_A, χ_A^i)）。 -/
noncomputable def betaA (χA : MulChar (ZMod p) A) (n j : ℕ) : A :=
  (p : A) ^ n * (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i)) ^ (2 * n)

/-- ᾱ_j：逆の指標どうしのヤコビ和で作った α_j。 -/
noncomputable def alphaB (χA : MulChar (ZMod p) A) (n j : ℕ) : A :=
  ((p : A) * ∏ i ∈ Ico 1 (n - 1), jacobiSum (χA ^ (n - 1)) (χA ^ (n - i))) ^ (2 * j)

/-- β̄_j。 -/
noncomputable def betaB (χA : MulChar (ZMod p) A) (n j : ℕ) : A :=
  (p : A) ^ n * (∏ i ∈ Ico 1 j, jacobiSum (χA ^ (n - 1)) (χA ^ (n - i))) ^ (2 * n)

/-- **4a.** 環準同型 f : A → ℂ で χ_A ↦ χ′ なら、f(α_j) = (p·∏ J(χ′, χ′^i))^{2j}。 -/
theorem map_alphaA (χA : MulChar (ZMod p) A) (n j : ℕ) (f : A →+* ℂ) {χ' : MulChar (ZMod p) ℂ}
    (hf : χA.ringHomComp f = χ') :
    f (alphaA χA n j) = ((p : ℂ) * ∏ i ∈ Ico 1 (n - 1), jacobiSum χ' (χ' ^ i)) ^ (2 * j) := by
  simp only [alphaA, map_pow, map_mul, map_natCast, map_prod]
  congr 2
  refine prod_congr rfl (fun i _ => ?_)
  rw [← jacobiSum_ringHomComp, ← MulChar.ringHomComp_pow, hf]

/-- **4b.** 同じく f(β_j) = p^n (∏_{i<j} J(χ′, χ′^i))^{2n}。 -/
theorem map_betaA (χA : MulChar (ZMod p) A) (n j : ℕ) (f : A →+* ℂ) {χ' : MulChar (ZMod p) ℂ}
    (hf : χA.ringHomComp f = χ') :
    f (betaA χA n j) = (p : ℂ) ^ n * (∏ i ∈ Ico 1 j, jacobiSum χ' (χ' ^ i)) ^ (2 * n) := by
  simp only [betaA, map_pow, map_mul, map_natCast, map_prod]
  congr 2
  refine prod_congr rfl (fun i _ => ?_)
  rw [← jacobiSum_ringHomComp, ← MulChar.ringHomComp_pow, hf]

variable {χ : MulChar (ZMod p) ℂ} {χA : MulChar (ZMod p) A}

/-- ヤコビ和の対の積：∏_{i=1}^{m−1} J(χ_A, χ_A^i)·J(χ_A^{n−1}, χ_A^{n−i}) = p^{m−1}（m ≤ n − 1）。 -/
theorem prod_pair (hval : χA.ringHomComp A.val.toRingHom = χ) (m : ℕ) (hm : m + 1 ≤ orderOf χ) :
    (∏ i ∈ Ico 1 m, jacobiSum χA (χA ^ i)) *
        (∏ i ∈ Ico 1 m, jacobiSum (χA ^ (orderOf χ - 1)) (χA ^ (orderOf χ - i)))
      = (p : A) ^ (m - 1) := by
  rw [← prod_mul_distrib, prod_congr rfl (fun i hi => PAG.Part189.jacobi_pair hval i
    (mem_Ico.mp hi).1 (by have := (mem_Ico.mp hi).2; omega)), prod_const, Nat.card_Ico]

/-- **4c.** α_j ᾱ_j = p^{2nj}（n ≥ 2）。 -/
theorem alpha_mul_alphaB (hval : χA.ringHomComp A.val.toRingHom = χ) (hn : 2 ≤ orderOf χ) (j : ℕ) :
    alphaA χA (orderOf χ) j * alphaB χA (orderOf χ) j = (p : A) ^ (2 * orderOf χ * j) := by
  rw [alphaA, alphaB, ← mul_pow, mul_mul_mul_comm, prod_pair hval (orderOf χ - 1) (by omega), ← pow_two,
    ← pow_add, ← pow_mul]
  congr 1
  rw [show 2 + (orderOf χ - 1 - 1) = orderOf χ by omega]
  ring

/-- **4d.** β_j β̄_j = p^{2nj}（1 ≤ j ≤ n − 1）。 -/
theorem beta_mul_betaB (hval : χA.ringHomComp A.val.toRingHom = χ) (j : ℕ) (hj1 : 1 ≤ j)
    (hjn : j + 1 ≤ orderOf χ) :
    betaA χA (orderOf χ) j * betaB χA (orderOf χ) j = (p : A) ^ (2 * orderOf χ * j) := by
  have hQ := prod_pair hval j hjn
  calc betaA χA (orderOf χ) j * betaB χA (orderOf χ) j
      = (p : A) ^ orderOf χ * (p : A) ^ orderOf χ *
          ((∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i)) *
            ∏ i ∈ Ico 1 j, jacobiSum (χA ^ (orderOf χ - 1)) (χA ^ (orderOf χ - i))) ^ (2 * orderOf χ) := by
        rw [betaA, betaB]; ring
    _ = (p : A) ^ (2 * orderOf χ * j) := by
        rw [hQ, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rw [Nat.add_sub_cancel]
        ring

/-- **4e.** ℤ_p での付値：ι(α_j), ι(β_j) ≠ 0 で、v(ι α_j) − v(ι β_j) = n − 2⟨cj⟩（Part 185 の計算）。 -/
theorem val_alpha_beta {c : ℕ} {ι : A →+* ℤ_[p]} (hval : χA.ringHomComp A.val.toRingHom = χ)
    (hev : χA.ringHomComp (PadicInt.toZMod.comp ι) = powChar ((p - 1) / orderOf χ * c))
    (hc : c.Coprime (orderOf χ)) (hn : 2 ≤ orderOf χ) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j < orderOf χ) :
    ι (alphaA χA (orderOf χ) j) ≠ 0 ∧ ι (betaA χA (orderOf χ) j) ≠ 0 ∧
      ((ι (alphaA χA (orderOf χ) j)).valuation : ℤ) - (ι (betaA χA (orderOf χ) j)).valuation
        = (orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ) := by
  obtain ⟨hP0, hPv⟩ := PAG.Part189.val_PA hval hev hc hn
  obtain ⟨hQ0, hQv⟩ := PAG.Part189.val_QA hval hev hc j hj1 (by omega)
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have ea : ι (alphaA χA (orderOf χ) j)
      = ((p : ℤ_[p]) * ι (∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χA (χA ^ i))) ^ (2 * j) := by
    simp only [alphaA, map_pow, map_mul, map_natCast]
  have eb : ι (betaA χA (orderOf χ) j)
      = (p : ℤ_[p]) ^ orderOf χ * ι (∏ i ∈ Ico 1 j, jacobiSum χA (χA ^ i)) ^ (2 * orderOf χ) := by
    simp only [betaA, map_pow, map_mul, map_natCast]
  refine ⟨by rw [ea]; exact pow_ne_zero _ (mul_ne_zero hp0 hP0),
    by rw [eb]; exact mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hQ0), ?_⟩
  rw [ea, eb, PadicInt.valuation_pow, PadicInt.valuation_mul hp0 hP0, PadicInt.valuation_p,
    PadicInt.valuation_mul (pow_ne_zero _ hp0) (pow_ne_zero _ hQ0), PadicInt.valuation_pow,
    PadicInt.valuation_pow, PadicInt.valuation_p]
  push_cast
  rw [hPv]
  push_cast at hQv ⊢
  linear_combination (-2 : ℤ) * hQv

end AB

/-! ### 5. 十分条件 -/

/-- 整数冪の積の分解：∏ (x_i/y_i)^{b_i} = ∏ x_i^{b⁺} y_i^{b⁻} / ∏ x_i^{b⁻} y_i^{b⁺}。 -/
theorem prod_zpow_div {κ : Type*} (s : Finset κ) (x y : κ → ℂ) (b : κ → ℤ) :
    ∏ i ∈ s, (x i / y i) ^ b i
      = (∏ i ∈ s, x i ^ (b i).toNat * y i ^ (-b i).toNat) / ∏ i ∈ s, x i ^ (-b i).toNat * y i ^ (b i).toNat := by
  simp only [PAG.Part186.zpow_div_split]
  rw [prod_div_distrib]

/-- 付値の差：v(∏ x^{b⁺} y^{b⁻}) − v(∏ x^{b⁻} y^{b⁺}) = Σ b_i (v(x_i) − v(y_i))。 -/
theorem val_split {κ : Type*} (s : Finset κ) (x y : κ → ℤ_[p]) (hx : ∀ i ∈ s, x i ≠ 0)
    (hy : ∀ i ∈ s, y i ≠ 0) (b : κ → ℤ) :
    ((∏ i ∈ s, x i ^ (b i).toNat * y i ^ (-b i).toNat).valuation : ℤ)
      - (∏ i ∈ s, x i ^ (-b i).toNat * y i ^ (b i).toNat).valuation
      = ∑ i ∈ s, b i * (((x i).valuation : ℤ) - (y i).valuation) := by
  rw [PAG.Part189.valuation_prod s x y _ _ hx hy, PAG.Part189.valuation_prod s x y _ _ hx hy]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun i _ => ?_)
  have hb : ((b i).toNat : ℤ) - ((-b i).toNat : ℤ) = b i := Int.toNat_sub_toNat_neg (b i)
  linear_combination (((x i).valuation : ℤ) - (y i).valuation) * hb

/-- |τ(φ, ψ)/√p| = 1（φ ≠ 1、ψ 原始的）。 -/
theorem norm_z (φ : MulChar (ZMod p) ℂ) (hφ : φ ≠ 1) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum φ ψ / ((Real.sqrt p : ℝ) : ℂ)‖ = 1 := by
  have h1 := gaussSum_mul_gaussSum_eq_card hφ hψ
  rw [← star_gaussSum_eq, ZMod.card, Complex.star_def, Complex.mul_conj] at h1
  have h2 : Complex.normSq (gaussSum φ ψ) = p := by exact_mod_cast h1
  rw [Complex.normSq_eq_norm_sq] at h2
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hp.out.pos)
  have h3 : ‖gaussSum φ ψ‖ = Real.sqrt p := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [norm_div, h3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp, div_self hsp.ne']

section Suff

variable {A : Subalgebra ℤ ℂ} {χ : MulChar (ZMod p) ℂ} {χA : MulChar (ZMod p) A}

/-- **5a.** V·V̄ = p^M（M = Σ_j 2nj(a⁺_j + a⁻_j)）。 -/
theorem V_mul_Vb (hval : χA.ringHomComp A.val.toRingHom = χ) (hn : 2 ≤ orderOf χ) (a : ℕ → ℤ) :
    (∏ j ∈ Ico 1 (orderOf χ), alphaA χA (orderOf χ) j ^ (-a j).toNat * betaA χA (orderOf χ) j ^ (a j).toNat) *
      (∏ j ∈ Ico 1 (orderOf χ), alphaB χA (orderOf χ) j ^ (-a j).toNat * betaB χA (orderOf χ) j ^ (a j).toNat)
      = (p : A) ^ (∑ j ∈ Ico 1 (orderOf χ), 2 * orderOf χ * j * ((a j).toNat + (-a j).toNat)) := by
  rw [← prod_mul_distrib, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl (fun j hj => ?_)
  rw [mem_Ico] at hj
  rw [mul_mul_mul_comm, ← mul_pow, ← mul_pow, alpha_mul_alphaB hval hn,
    beta_mul_betaB hval j hj.1 (by omega), ← pow_mul, ← pow_mul, ← pow_add]
  congr 1; ring

/-- **5b.** ℤ_p：S_c(a) = 0 なら p^M ∣ ι(U·V̄)。 -/
theorem padic_dvd_T {c : ℕ} {ι : A →+* ℤ_[p]} (hval : χA.ringHomComp A.val.toRingHom = χ)
    (hev : χA.ringHomComp (PadicInt.toZMod.comp ι) = powChar ((p - 1) / orderOf χ * c))
    (hc : c.Coprime (orderOf χ)) (hn : 2 ≤ orderOf χ) (a : ℕ → ℤ)
    (hSc : ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0) :
    (p : ℤ_[p]) ^ (∑ j ∈ Ico 1 (orderOf χ), 2 * orderOf χ * j * ((a j).toNat + (-a j).toNat)) ∣
      ι ((∏ j ∈ Ico 1 (orderOf χ),
          alphaA χA (orderOf χ) j ^ (a j).toNat * betaA χA (orderOf χ) j ^ (-a j).toNat) *
        ∏ j ∈ Ico 1 (orderOf χ),
          alphaB χA (orderOf χ) j ^ (-a j).toNat * betaB χA (orderOf χ) j ^ (a j).toNat) := by
  set M := ∑ j ∈ Ico 1 (orderOf χ), 2 * orderOf χ * j * ((a j).toNat + (-a j).toNat)
  have hp0 : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hab := fun j (hj : j ∈ Ico 1 (orderOf χ)) =>
    val_alpha_beta hval hev hc hn j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2
  have hx : ∀ j ∈ Ico 1 (orderOf χ), ι (alphaA χA (orderOf χ) j) ≠ 0 := fun j hj => (hab j hj).1
  have hy : ∀ j ∈ Ico 1 (orderOf χ), ι (betaA χA (orderOf χ) j) ≠ 0 := fun j hj => (hab j hj).2.1
  -- v(ι U) = v(ι V)
  have hUV := val_split (Ico 1 (orderOf χ)) (fun j => ι (alphaA χA (orderOf χ) j))
    (fun j => ι (betaA χA (orderOf χ) j)) hx hy a
  rw [sum_congr rfl (fun j hj => by rw [(hab j hj).2.2]), hSc] at hUV
  -- V·V̄ = p^M
  have hVV := congrArg ι (V_mul_Vb hval hn a)
  simp only [map_mul, map_prod, map_pow, map_natCast] at hVV
  have hV0 : ∏ j ∈ Ico 1 (orderOf χ), ι (alphaA χA (orderOf χ) j) ^ (-a j).toNat *
      ι (betaA χA (orderOf χ) j) ^ (a j).toNat ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => mul_ne_zero (pow_ne_zero _ (hx j hj)) (pow_ne_zero _ (hy j hj))
  have hU0 : ∏ j ∈ Ico 1 (orderOf χ), ι (alphaA χA (orderOf χ) j) ^ (a j).toNat *
      ι (betaA χA (orderOf χ) j) ^ (-a j).toNat ≠ 0 :=
    prod_ne_zero_iff.mpr fun j hj => mul_ne_zero (pow_ne_zero _ (hx j hj)) (pow_ne_zero _ (hy j hj))
  have hVb0 : ∏ j ∈ Ico 1 (orderOf χ), ι (alphaB χA (orderOf χ) j) ^ (-a j).toNat *
      ι (betaB χA (orderOf χ) j) ^ (a j).toNat ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hVV; exact pow_ne_zero _ hp0 hVV.symm
  have hvV := congrArg PadicInt.valuation hVV
  rw [PadicInt.valuation_mul hV0 hVb0, PadicInt.valuation_pow, PadicInt.valuation_p, mul_one] at hvV
  simp only [map_mul, map_prod, map_pow]
  rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ (mul_ne_zero hU0 hVb0),
    PadicInt.valuation_mul hU0 hVb0]
  omega

/-- **5c.** 環準同型 f : A → ℂ で χ_A ↦ χ′（位数 n）なら、f(α_j) = (τ(χ′^j)/√p)^{2n}·f(β_j)。 -/
theorem map_alpha_eq (f : A →+* ℂ) {χ' : MulChar (ZMod p) ℂ} (hf : χA.ringHomComp f = χ') (n : ℕ)
    (hord : orderOf χ' = n) (hn : 2 ≤ n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j < n) :
    f (alphaA χA n j) = (gaussSum (χ' ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n) * f (betaA χA n j) := by
  rw [map_alphaA χA n j f hf, map_betaA χA n j f hf]
  have := PAG.Part189.W_eq χ' (hord ▸ hn) hψ j hj1 (hord ▸ hjn)
  simp only [PAG.Part185.Pj, hord] at this
  exact this.symm

/-- **5d.** f(U)/f(V) = ∏_j ((τ(χ′^j)/√p)^{2n})^{a_j}。 -/
theorem map_U_div_V (f : A →+* ℂ) {χ' : MulChar (ZMod p) ℂ} (hf : χA.ringHomComp f = χ') (n : ℕ)
    (hord : orderOf χ' = n) (hn : 2 ≤ n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) (a : ℕ → ℤ)
    (hβ : ∀ j ∈ Ico 1 n, f (betaA χA n j) ≠ 0) :
    f (∏ j ∈ Ico 1 n, alphaA χA n j ^ (a j).toNat * betaA χA n j ^ (-a j).toNat) /
        f (∏ j ∈ Ico 1 n, alphaA χA n j ^ (-a j).toNat * betaA χA n j ^ (a j).toNat)
      = ∏ j ∈ Ico 1 n, ((gaussSum (χ' ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j := by
  simp only [map_prod, map_mul, map_pow]
  rw [← prod_zpow_div]
  refine prod_congr rfl (fun j hj => ?_)
  rw [mem_Ico] at hj
  rw [map_alpha_eq f hf n hord hn hψ j hj.1 hj.2, mul_div_cancel_right₀ _ (hβ j (mem_Ico.mpr hj))]

/-- 上の積の絶対値は 1。 -/
theorem norm_prod_z (χ' : MulChar (ZMod p) ℂ) (n : ℕ) (hord : orderOf χ' = n) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (a : ℕ → ℤ) :
    ‖∏ j ∈ Ico 1 n, ((gaussSum (χ' ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j‖ = 1 := by
  rw [norm_prod]
  refine prod_eq_one (fun j hj => ?_)
  rw [mem_Ico] at hj
  have hne : χ' ^ j ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  rw [norm_zpow, norm_pow, norm_z (χ' ^ j) hne hψ, one_pow, one_zpow]

/-- f(β_j) ≠ 0（f(β_j)·f(β̄_j) = p^{2nj}）。 -/
theorem map_betaA_ne_zero (hval : χA.ringHomComp A.val.toRingHom = χ) (f : A →+* ℂ) (j : ℕ)
    (hj1 : 1 ≤ j) (hjn : j + 1 ≤ orderOf χ) : f (betaA χA (orderOf χ) j) ≠ 0 := by
  intro h0
  have := congrArg f (beta_mul_betaB hval j hj1 hjn)
  rw [map_mul, h0, zero_mul, map_pow, map_natCast] at this
  exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero) this.symm

end Suff

/-! ### 6. 主定理 -/

/-- **6a. 十分条件**：すべての c ∈ (ℤ/n)^× で S_c(a) = Σ_j a_j (n − 2⟨cj⟩) = 0 なら、
  ∏_{j=1}^{n−1} z_j^{a_j} は 1 の冪根。 -/
theorem same_prime_sufficient (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (a : ℕ → ℤ)
    (hS : ∀ c : ℕ, c.Coprime (orderOf χ) →
      ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0) :
    ∃ N : ℕ, 0 < N ∧
      (∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ N = 1 := by
  rcases Nat.lt_or_ge (orderOf χ) 2 with hn | hn
  · exact ⟨1, one_pos, by rw [Ico_eq_empty_of_le (by omega), prod_empty, one_pow]⟩
  have hnpos : 0 < orderOf χ := by omega
  -- データ：生成元 g、μ = χ(g)、A = ℤ[μ]、冪基底
  obtain ⟨g, hg⟩ := PAG.Part185.exists_gen (p := p)
  have hμ := PAG.Part185.isPrimitiveRoot_gen χ g hg
  have hint : IsIntegral ℤ (χ g) := hμ.isIntegral hnpos
  obtain ⟨pb, hgen⟩ : ∃ pb : PowerBasis ℤ (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)),
      pb.gen = ⟨χ g, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :=
    ⟨Algebra.adjoin.powerBasis' hint, Algebra.adjoin.powerBasis'_gen hint⟩
  have hgen' : (pb.gen : ℂ) = χ g := by rw [hgen]
  have hmin : minpoly ℤ pb.gen = cyclotomic (orderOf χ) ℤ := by
    rw [hgen, ← minpoly.algHom_eq (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val Subtype.val_injective]
    exact (cyclotomic_eq_minpoly hμ hnpos).symm
  have hdim : pb.dim = (orderOf χ).totient := by
    rw [← pb.natDegree_minpoly, hmin, natDegree_cyclotomic]
  have hval : (PAG.Part185.chiA χ hμ).ringHomComp
      (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom = χ := MulChar.ext' (fun x => rfl)
  set χA := PAG.Part185.chiA χ hμ with hχA
  set n := orderOf χ with hn_def
  -- U, V, V̄
  set U := ∏ j ∈ Ico 1 n, alphaA χA n j ^ (a j).toNat * betaA χA n j ^ (-a j).toNat with hU
  set V := ∏ j ∈ Ico 1 n, alphaA χA n j ^ (-a j).toNat * betaA χA n j ^ (a j).toNat with hV
  set Vb := ∏ j ∈ Ico 1 n, alphaB χA n j ^ (-a j).toNat * betaB χA n j ^ (a j).toNat with hVb
  set M := ∑ j ∈ Ico 1 n, 2 * n * j * ((a j).toNat + (-a j).toNat) with hM
  have hVVb : V * Vb = (p : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)) ^ M := V_mul_Vb hval hn a
  -- ℤ_p の 1 の原始 n 乗根 z ≡ g^k
  have hdvd : n ∣ p - 1 := PAG.Part185.orderOf_dvd_sub_one χ
  have h2p := hp.out.two_le
  have hkn : (p - 1) / n * n = p - 1 := Nat.div_mul_cancel hdvd
  have hkpos : 0 < (p - 1) / n := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hnpos
  have hga : IsPrimitiveRoot ((g : ZMod p)) (p - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← PAG.Part185.orderOf_gen g hg]
    exact IsPrimitiveRoot.orderOf g
  have hgk : IsPrimitiveRoot ((g : ZMod p) ^ ((p - 1) / n)) n := by
    have := hga.pow_of_dvd hkpos.ne' (Dvd.intro _ hkn)
    rwa [Nat.div_div_self hdvd (by omega)] at this
  have hnp : ((n : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
    have := Nat.le_of_dvd hnpos h; have := Nat.le_of_dvd (by omega) hdvd; omega
  obtain ⟨z, hz, hzy⟩ := PAG.Part189.exists_padic_root n hnpos hnp _ hgk
  -- 節点と埋め込み
  obtain ⟨cc, hccinj, hcc⟩ := exists_nodes n pb.dim hdim
  choose ι hιg using fun k : Fin pb.dim =>
    exists_lift pb hnpos hmin (z ^ cc k) (hz.pow_of_coprime _ (hcc k).2)
  choose σ hσg using fun k : Fin pb.dim =>
    exists_lift pb hnpos hmin ((χ g : ℂ) ^ cc k) (hμ.pow_of_coprime _ (hcc k).2)
  -- (1) すべての k で p^M ∣ ι_k(U·V̄)
  have hdivT : ∀ k, (p : ℤ_[p]) ^ M ∣ ι k (U * Vb) := by
    intro k
    have hev : χA.ringHomComp (PadicInt.toZMod.comp (ι k)) = powChar ((p - 1) / n * cc k) :=
      hev_of_lift χ g hg hμ pb hgen' (ι k) _ (by rw [hιg k, map_pow, hzy, ← pow_mul])
    exact padic_dvd_T hval hev (hcc k).2 hn a (hS (cc k) (hcc k).2)
  -- (2) ヴァンデルモンド：U·V̄ = p^M·T₀
  have hrepr : ∀ i, (p : ℤ) ^ M ∣ pb.basis.repr (U * Vb) i := by
    apply int_dvd_of_padic (fun k => z ^ cc k)
      (det_isUnit_padic (by rw [hzy]; exact hgk) cc hccinj (fun k => (hcc k).1))
    intro k
    have := eval_repr pb (ι k) (U * Vb)
    rw [hιg k] at this
    rw [← this]
    exact hdivT k
  choose q hq using hrepr
  set T₀ : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) := ∑ i, q i • pb.basis i with hT₀
  have hTT₀ : U * Vb = (p : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)) ^ M * T₀ := by
    conv_lhs => rw [← pb.basis.sum_repr (U * Vb)]
    rw [hT₀, mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    rw [hq i, mul_smul, zsmul_eq_mul]
    push_cast
    rfl
  -- (3) X^{2n} = T₀
  have hpM : ((p : ℂ)) ^ M ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hβC : ∀ j ∈ Ico 1 n,
      (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom (betaA χA n j) ≠ 0 := fun j hj =>
    map_betaA_ne_zero hval _ j (mem_Ico.mp hj).1 (by have := (mem_Ico.mp hj).2; omega)
  have hY := map_U_div_V (Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ)).val.toRingHom hval n rfl hn hψ a hβC
  have hX : (∏ j ∈ Ico 1 n, (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ (2 * n)
      = ∏ j ∈ Ico 1 n, ((gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ (2 * n)) ^ a j := by
    rw [← prod_pow]
    refine prod_congr rfl (fun j _ => ?_)
    rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast _ (2 * n), ← zpow_mul, mul_comm]
  have e1 : (U : ℂ) * (Vb : ℂ) = (p : ℂ) ^ M * (T₀ : ℂ) := by
    have := congrArg (fun x : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) => (x : ℂ)) hTT₀
    simpa using this
  have e2 : (V : ℂ) * (Vb : ℂ) = (p : ℂ) ^ M := by
    have := congrArg (fun x : Algebra.adjoin ℤ ({(χ g : ℂ)} : Set ℂ) => (x : ℂ)) hVVb
    simpa using this
  have hVV0 : (V : ℂ) * (Vb : ℂ) ≠ 0 := by rw [e2]; exact hpM
  have hUV : (U : ℂ) / (V : ℂ) = (T₀ : ℂ) := by
    rw [div_eq_iff (left_ne_zero_of_mul hVV0)]
    apply mul_right_cancel₀ (right_ne_zero_of_mul hVV0)
    rw [e1, mul_assoc, e2, mul_comm]
  have hXT : (∏ j ∈ Ico 1 n, (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ (2 * n)
      = (T₀ : ℂ) := by
    rw [hX, ← hY]; exact hUV
  -- (4) クロネッカー
  have hσχ : ∀ k, χA.ringHomComp (σ k) = χ ^ cc k :=
    fun k => hsig_of_lift χ g hg hμ pb hgen' (σ k) (cc k) (hσg k)
  have hord : ∀ k, orderOf (χ ^ cc k) = n := fun k => Nat.Coprime.orderOf_pow (hcc k).2.symm
  have hnorm : ∀ k, ‖σ k T₀‖ = 1 := by
    intro k
    have hYk := map_U_div_V (σ k) (hσχ k) n (hord k) hn hψ a (fun j hj =>
      map_betaA_ne_zero hval (σ k) j (mem_Ico.mp hj).1 (by have := (mem_Ico.mp hj).2; omega))
    have hnk := norm_prod_z (χ ^ cc k) n (hord k) hψ a
    rw [← hYk] at hnk
    have f2 := congrArg (σ k) hVVb
    rw [map_mul, map_pow, map_natCast] at f2
    have f1 := congrArg (σ k) hTT₀
    rw [map_mul, map_mul, map_pow, map_natCast] at f1
    have hV0 : σ k V ≠ 0 := left_ne_zero_of_mul (by rw [f2]; exact hpM)
    rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hV0)] at hnk
    have h3 := congrArg norm f1
    rw [norm_mul, norm_mul, hnk, ← norm_mul, f2] at h3
    have hpMn : ‖(p : ℂ) ^ M‖ ≠ 0 := norm_ne_zero_iff.mpr hpM
    exact mul_left_cancel₀ hpMn (h3.symm.trans (mul_one _).symm)
  have hdet : (vandermonde (fun k => σ k pb.gen)).det ≠ 0 := by
    have : (fun k => σ k pb.gen) = fun k => (χ g : ℂ) ^ cc k := funext hσg
    rw [this]
    exact det_ne_zero_complex hμ cc hccinj (fun k => (hcc k).1)
  have hdpos : 0 < pb.dim := by rw [hdim]; exact Nat.totient_pos.mpr hnpos
  have hT0 : T₀ ≠ 0 := by
    intro h0
    have := hnorm ⟨0, hdpos⟩
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨N, hN, hTN⟩ := root_of_norm_eq_one pb σ hdet T₀ hT0 hnorm
  refine ⟨2 * n * N, by positivity, ?_⟩
  rw [pow_mul, hXT, ← SubmonoidClass.coe_pow, hTN, OneMemClass.coe_one]

/-- **6b. 完全な判定**：∏_{j=1}^{n−1} z_j^{a_j} が 1 の冪根 ⇔ n と互いに素なすべての c で
  Σ_j a_j (n − 2⟨cj⟩) = 0。 -/
theorem same_prime_root_iff (χ : MulChar (ZMod p) ℂ) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (a : ℕ → ℤ) :
    (∃ N : ℕ, 0 < N ∧
      (∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a j) ^ N = 1) ↔
      ∀ c : ℕ, c.Coprime (orderOf χ) →
        ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0 :=
  ⟨fun ⟨N, hN, h⟩ c hc => PAG.Part189.same_prime_necessary χ hψ a N hN h c hc,
    same_prime_sufficient χ hψ a⟩

/-- **6c.** 鎖の記号（PAG184 の zOf）での完全な判定。 -/
theorem same_prime_root_iff_chain (χ : DirichletCharacter ℂ p) (a : ℕ → ℤ) :
    (∃ N : ℕ, 0 < N ∧ (∏ j ∈ Ico 1 (orderOf χ), PAG.Part184.zOf (χ ^ j) ^ a j) ^ N = 1) ↔
      ∀ c : ℕ, c.Coprime (orderOf χ) →
        ∑ j ∈ Ico 1 (orderOf χ), a j * ((orderOf χ : ℤ) - 2 * ((c * j % orderOf χ : ℕ) : ℤ)) = 0 :=
  same_prime_root_iff χ (ZMod.isPrimitive_stdAddChar p) a

/-! ### 7. 系 -/

omit hp in
/-- 判定は c mod n だけで決まる：0 ≤ c < n で確かめれば十分。 -/
theorem crit_of_lt (n : ℕ) (a : ℕ → ℤ)
    (h : ∀ c < n, c.Coprime n → ∑ j ∈ Ico 1 n, a j * ((n : ℤ) - 2 * ((c * j % n : ℕ) : ℤ)) = 0) :
    ∀ c : ℕ, c.Coprime n → ∑ j ∈ Ico 1 n, a j * ((n : ℤ) - 2 * ((c * j % n : ℕ) : ℤ)) = 0 := by
  intro c hc
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  have hc' : (c % n).Coprime n := by
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]; exact hc
  rw [← h (c % n) (Nat.mod_lt c hnpos) hc']
  refine sum_congr rfl (fun j _ => ?_)
  rw [Nat.mod_mul_mod]

omit hp in
/-- ⟨c(n − 1)⟩ + ⟨c⟩ = n（c は n と互いに素、n ≥ 2）。 -/
theorem mul_pred_mod (c n : ℕ) (hn : 2 ≤ n) (hc : c.Coprime n) : c * (n - 1) % n + c % n = n := by
  have hnpos : 0 < n := by omega
  have hz : (c * (n - 1) + c) % n = 0 := by
    rw [show c * (n - 1) + c = c * n by
      rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right c hnpos)]]
    exact Nat.mul_mod_left c n
  have hr1 : c % n ≠ 0 := by
    have := PAG.Part189.mul_mod_ne_zero c n 1 hc one_pos (by omega); rwa [mul_one] at this
  rcases PAG.Part189.add_mod_cases n (c * (n - 1)) c hnpos with ⟨h1, _⟩ | ⟨h1, _⟩
  · omega
  · omega

/-- **7a.** n ≥ 3：z(χ)^a·z(χ^{n−1})^b が 1 の冪根 ⇔ a = b
  （Part 169 の z(χ)z(χ⁻¹) = χ(−1) の一般化と、その逆）。 -/
theorem inverse_pair_root_iff (χ : MulChar (ZMod p) ℂ) (hn : 3 ≤ orderOf χ) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) (a b : ℤ) :
    (∃ N : ℕ, 0 < N ∧ ((gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a *
      (gaussSum (χ ^ (orderOf χ - 1)) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b) ^ N = 1) ↔ a = b := by
  set n := orderOf χ with hn_def
  set e : ℕ → ℤ := fun j => if j = 1 then a else if j = n - 1 then b else 0 with he
  have h1n : (1 : ℕ) ≠ n - 1 := by omega
  have hmem1 : 1 ∈ Ico 1 n := mem_Ico.mpr ⟨le_refl 1, by omega⟩
  have hmem2 : n - 1 ∈ Ico 1 n := mem_Ico.mpr ⟨by omega, by omega⟩
  have he1 : e 1 = a := by simp [he]
  have he2 : e (n - 1) = b := by simp [he, h1n.symm]
  have hprod : ∏ j ∈ Ico 1 n, (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ e j
      = (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ a *
        (gaussSum (χ ^ (n - 1)) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ b := by
    rw [prod_eq_mul_of_mem 1 (n - 1) hmem1 hmem2 h1n (fun j _ hj => by
      rw [he]; simp only [ite_eq_right hj.1, ite_eq_right hj.2, zpow_zero])]
    rw [he1, he2, pow_one]
  have hsum : ∀ c : ℕ, c.Coprime n →
      ∑ j ∈ Ico 1 n, e j * ((n : ℤ) - 2 * ((c * j % n : ℕ) : ℤ))
        = (a - b) * ((n : ℤ) - 2 * ((c % n : ℕ) : ℤ)) := by
    intro c hc
    rw [sum_eq_add_of_mem 1 (n - 1) hmem1 hmem2 h1n (fun j _ hj => by
      rw [he]; simp only [ite_eq_right hj.1, ite_eq_right hj.2, zero_mul])]
    rw [he1, he2, mul_one]
    have := mul_pred_mod c n (by omega) hc
    have hZ : ((c * (n - 1) % n : ℕ) : ℤ) = n - ((c % n : ℕ) : ℤ) := by
      have : ((c * (n - 1) % n : ℕ) : ℤ) + ((c % n : ℕ) : ℤ) = n := by exact_mod_cast this
      linarith
    rw [hZ]; ring
  rw [← hprod, same_prime_root_iff χ hψ e]
  constructor
  · intro h
    have h1 := h 1 (Nat.coprime_one_left _)
    rw [hsum 1 (Nat.coprime_one_left _), Nat.one_mod_eq_one.mpr (by omega)] at h1
    have : ((n : ℤ) - 2 * ((1 : ℕ) : ℤ)) ≠ 0 := by push_cast; omega
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right this)
  · intro hab c hc
    rw [hsum c hc, hab, sub_self, zero_mul]

/-- **7b.** 位数 6：z(χ)·z(χ⁴)² は 1 の冪根（Part 178 のハッセ・ダベンポートの関係から出ていた
  z(ψL)·z(ψ)²（ψ = χ⁴ は位数 3、ψL = χ）が 1 の冪根になることを、付値だけで再現）。 -/
theorem sextic_hd_root (χ : MulChar (ZMod p) ℂ) (h6 : orderOf χ = 6) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) :
    ∃ N : ℕ, 0 < N ∧ ((gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) *
      (gaussSum (χ ^ 4) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ 2) ^ N = 1 := by
  set e : ℕ → ℤ := fun j => if j = 1 then 1 else if j = 4 then 2 else 0 with he
  have hI : Ico 1 6 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  have hprod : ∏ j ∈ Ico 1 (orderOf χ), (gaussSum (χ ^ j) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ e j
      = (gaussSum χ ψ / ((Real.sqrt p : ℝ) : ℂ)) * (gaussSum (χ ^ 4) ψ / ((Real.sqrt p : ℝ) : ℂ)) ^ 2 := by
    rw [h6, hI]
    simp [he]
  rw [← hprod]
  apply same_prime_sufficient χ hψ e
  rw [h6]
  apply crit_of_lt
  intro c hc hcop
  interval_cases c <;> first | (exact absurd hcop (by decide)) | (rw [hI]; simp [he])

end PAG.Part190

#print axioms PAG.Part190.exists_lift
#print axioms PAG.Part190.lift_chiA_pow
#print axioms PAG.Part190.hev_of_lift
#print axioms PAG.Part190.hsig_of_lift
#print axioms PAG.Part190.eval_repr
#print axioms PAG.Part190.vandermonde_solve
#print axioms PAG.Part190.int_dvd_of_padic
#print axioms PAG.Part190.coord_bound
#print axioms PAG.Part190.finite_of_bounded
#print axioms PAG.Part190.root_of_norm_eq_one
#print axioms PAG.Part190.exists_nodes
#print axioms PAG.Part190.det_ne_zero_complex
#print axioms PAG.Part190.det_isUnit_padic
#print axioms PAG.Part190.map_alphaA
#print axioms PAG.Part190.map_betaA
#print axioms PAG.Part190.prod_pair
#print axioms PAG.Part190.alpha_mul_alphaB
#print axioms PAG.Part190.beta_mul_betaB
#print axioms PAG.Part190.val_alpha_beta
#print axioms PAG.Part190.prod_zpow_div
#print axioms PAG.Part190.val_split
#print axioms PAG.Part190.norm_z
#print axioms PAG.Part190.V_mul_Vb
#print axioms PAG.Part190.padic_dvd_T
#print axioms PAG.Part190.map_alpha_eq
#print axioms PAG.Part190.map_U_div_V
#print axioms PAG.Part190.norm_prod_z
#print axioms PAG.Part190.map_betaA_ne_zero
#print axioms PAG.Part190.same_prime_sufficient
#print axioms PAG.Part190.same_prime_root_iff
#print axioms PAG.Part190.same_prime_root_iff_chain
#print axioms PAG.Part190.crit_of_lt
#print axioms PAG.Part190.mul_pred_mod
#print axioms PAG.Part190.inverse_pair_root_iff
#print axioms PAG.Part190.sextic_hd_root
