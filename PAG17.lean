/-
  PAG 2.0 Part 13（2026-10-18）
  1. P¹ 動径空間の貼り合わせ: 2×2 ブロックの和の直交性、貼り合わせ恒等式、A_S ⊔ A_N = ⊤ と A_S ⊓ A_N = 赤道
  2. 押し出し（ゼロ拡張）と引き戻しの畳み込み: ι_* f ⋆ ι_* g = ι_*(f ⋆ g)、π^* f ⋆ π^* g = |ker π| π^*(f ⋆ g)
  3. 引き戻しのフーリエ変換は双対部分群に台を持つ
  4. 一般殻の定理 A（積が原始的）: 押し出し・引き戻しと PAG16 の頂上殻の定理の合成
-/
import PAG16

namespace PAG.Part17

open Finset

/-! ## 1. P¹ 動径空間の貼り合わせ -/

section Glue

/-- 2×2 ブロックが (c, −c) の形なら、和 ε_{K−1} + ε_K は相手側と直交する。 -/
theorem block_sum_orth {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (B : M →ₗ[R] M →ₗ[R] R) (x y z : M) (c : R) (hx : B x z = c) (hy : B y z = -c) :
    B (x + y) z = 0 := by
  rw [map_add, LinearMap.add_apply, hx, hy, add_neg_cancel]

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **貼り合わせ恒等式**: s, n, u を南内部・北内部・赤道の指示関数とし、
ε^S_K = q⁻¹(s + u)、ε^N_K = q⁻¹(n + u)、P^S = (q/p)⁻¹ s、P^N = (q/p)⁻¹ n（q = p^K）とおくと
ε^S_K − ε^N_K = p⁻¹(P^S − P^N)。 -/
theorem glue_identity (p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (s n u : M) :
    q⁻¹ • (s + u) - q⁻¹ • (n + u) = p⁻¹ • ((q / p)⁻¹ • s - (q / p)⁻¹ • n) := by
  rw [smul_sub, smul_smul, smul_smul, inv_div, show p⁻¹ * (p / q) = q⁻¹ by field_simp,
    smul_add, smul_add]
  abel

/-- 赤道指示関数の復元: u = q ε^S_K − (q/p) P^S。 -/
theorem equator_from_south (p q : K) (hp : p ≠ 0) (hq : q ≠ 0) (s u : M) :
    q • (q⁻¹ • (s + u)) - (q / p) • ((q / p)⁻¹ • s) = u := by
  rw [smul_smul, smul_smul, mul_inv_cancel₀ hq, mul_inv_cancel₀ (div_ne_zero hq hp), one_smul,
    one_smul]
  abel

/-- 南の動径代数 A_S（北内部で 0 になる関数）。 -/
def AS {X : Type*} (Nn : Set X) : Submodule K (X → K) where
  carrier := {f | ∀ x ∈ Nn, f x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

/-- **A_S ⊔ A_N = 全体**（南内部と北内部が交わらなければ）。 -/
theorem AS_sup_AN {X : Type*} (S Nn : Set X) (hdisj : Disjoint S Nn) :
    AS (K := K) Nn ⊔ AS S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  have h1 : (fun x => if x ∈ Nn then 0 else f x) ∈ AS (K := K) Nn := fun x hx => by simp [hx]
  have h2 : (fun x => if x ∈ Nn then f x else 0) ∈ AS (K := K) S := fun x hx => by
    have : x ∉ Nn := fun h => Set.disjoint_left.mp hdisj hx h
    simp [this]
  have : f = (fun x => if x ∈ Nn then 0 else f x) + (fun x => if x ∈ Nn then f x else 0) := by
    funext x; by_cases hx : x ∈ Nn <;> simp [hx]
  rw [this]
  exact Submodule.add_mem_sup h1 h2

/-- **A_S ⊓ A_N = 赤道に台を持つ関数**（S, E, Nn が全体を覆い、E が S・Nn と交わらないとき）。 -/
theorem AS_inf_AN {X : Type*} (S E Nn : Set X) (hcover : ∀ x, x ∈ S ∨ x ∈ E ∨ x ∈ Nn)
    (hES : Disjoint E S) (hEN : Disjoint E Nn)
    (f : X → K) : f ∈ AS (K := K) Nn ⊓ AS S ↔ ∀ x, x ∉ E → f x = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ x hx
    rcases hcover x with h | h | h
    · exact h2 x h
    · exact absurd h hx
    · exact h1 x h
  · intro h
    exact ⟨fun x hx => h x (fun hE => Set.disjoint_left.mp hEN hE hx),
      fun x hx => h x (fun hE => Set.disjoint_left.mp hES hE hx)⟩

end Glue

/-! ## 2. 押し出しと引き戻しの畳み込み -/

section PushPull

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

/-- ゼロ拡張（押し出し）ι_* f = Function.extend ι f 0。 -/
noncomputable def push (ι : H →+ G) (f : H → ℂ) : G → ℂ := Function.extend ι f 0

theorem sum_push_mul (ι : H →+ G) (hι : Function.Injective ι) (f : H → ℂ) (h : G → ℂ) :
    ∑ z : G, push ι f z * h z = ∑ y : H, f y * h (ι y) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (univ.image ι)) (fun z _ hz => by
      have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.mpr ⟨a, mem_univ _, ha⟩)
      simp [push, Function.extend_apply' _ _ _ this]),
    Finset.sum_image (fun a _ b _ hab => hι hab)]
  exact sum_congr rfl (fun y _ => by rw [push, hι.extend_apply])

/-- **押し出しの畳み込み**: ι 単射なら ι_* f ⋆ ι_* g = ι_*(f ⋆ g)（係数なし）。 -/
theorem push_conv (ι : H →+ G) (hι : Function.Injective ι) (f g : H → ℂ) :
    PAG.Part15.conv (push ι f) (push ι g) = push ι (PAG.Part15.conv f g) := by
  funext x
  unfold PAG.Part15.conv
  rw [sum_push_mul ι hι f (fun z => push ι g (x - z))]
  unfold push
  by_cases hx : ∃ a, ι a = x
  · obtain ⟨a, rfl⟩ := hx
    rw [hι.extend_apply]
    refine sum_congr rfl (fun y _ => ?_)
    rw [← map_sub, hι.extend_apply]
  · rw [Function.extend_apply' _ _ _ hx]
    simp only [Pi.zero_apply]
    refine sum_eq_zero (fun y _ => ?_)
    have : ¬ ∃ a, ι a = x - ι y := fun ⟨a, ha⟩ => hx ⟨a + y, by rw [map_add, ha, sub_add_cancel]⟩
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, mul_zero]

/-- 全射準同型の各ファイバーは核と同じ大きさ。 -/
theorem sum_comp_surj [DecidableEq H] (π : G →+ H) (hπ : Function.Surjective π) (F : H → ℂ) :
    ∑ z : G, F (π z) = ((univ.filter (fun z : G => π z = 0)).card : ℂ) * ∑ h : H, F h := by
  classical
  rw [Finset.sum_comp, show univ.image π = univ from
    Finset.eq_univ_of_forall (fun h => Finset.mem_image.mpr (by
      obtain ⟨z, hz⟩ := hπ h; exact ⟨z, mem_univ _, hz⟩)), mul_sum]
  refine sum_congr rfl (fun h _ => ?_)
  rw [nsmul_eq_mul]
  congr 2
  exact AddMonoidHom.card_fiber_eq_of_mem_range π (hπ h) ⟨0, map_zero π⟩

/-- **引き戻しの畳み込み**: π 全射、q = |ker π| なら π^* f ⋆ π^* g = q π^*(f ⋆ g)。 -/
theorem conv_pullback [DecidableEq H] (π : G →+ H) (hπ : Function.Surjective π) (f g : H → ℂ) :
    PAG.Part15.conv (f ∘ π) (g ∘ π)
      = ((univ.filter (fun z : G => π z = 0)).card : ℂ) • (PAG.Part15.conv f g ∘ π) := by
  funext x
  unfold PAG.Part15.conv
  simp only [Function.comp, Pi.smul_apply, smul_eq_mul]
  have := sum_comp_surj π hπ (fun h => f h * g (π x - h))
  simpa [map_sub] using this

end PushPull

/-! ## 3. 引き戻しのフーリエ変換の台 -/

section Support

open ZMod

variable {M M' : ℕ} [NeZero M']

/-- **双対部分群への台**: M ∣ M'、(M : ZMod M') k ≠ 0 なら 𝓕(f ∘ π)(k) = 0。 -/
theorem dft_pullback_eq_zero (h : M ∣ M') (f : ZMod M → ℂ) (k : ZMod M')
    (hk : (M : ZMod M') * k ≠ 0) : 𝓕 (fun x => f (ZMod.castHom h (ZMod M) x)) k = 0 := by
  set S := 𝓕 (fun x => f (ZMod.castHom h (ZMod M) x)) k with hS
  have hshift : S = stdAddChar (-((M : ZMod M') * k)) * S := by
    rw [hS, dft_apply, mul_sum]
    refine (Fintype.sum_equiv (Equiv.addRight (M : ZMod M')) _ _ (fun x => ?_)).symm
    simp only [Equiv.coe_addRight, smul_eq_mul, map_add, map_natCast, ZMod.natCast_self, add_zero]
    rw [show -((x + (M : ZMod M')) * k) = -((M : ZMod M') * k) + -(x * k) by ring,
      AddChar.map_add_eq_mul]
    ring
  have hne : stdAddChar (-((M : ZMod M') * k)) ≠ 1 := by
    intro h1
    exact hk (neg_eq_zero.mp (ZMod.injective_stdAddChar (N := M')
      (h1.trans (AddChar.map_zero_eq_one _).symm)))
  have : (1 - stdAddChar (-((M : ZMod M') * k))) * S = 0 := by
    rw [sub_mul, one_mul, ← hshift, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0).symm hne
  · exact h0

end Support

/-! ## 4. 一般殻の定理 A（積が原始的） -/

section GeneralShell

variable {G H : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {p n : ℕ} [hp : Fact p.Prime]

/-- **一般殻の定理 A**: ι : ZMod p^(K−v) ↪ ZMod p^K（殻 v への埋め込み）、π : ZMod p^(K−v) ↠ ZMod p^c
（引き戻し）の一般形。H = ZMod p^(n+1)（c = n+1）、χ₁, χ₂, χ₁χ₂ 原始的なら
ι_*π^*χ₁ ⋆ ι_*π^*χ₂ = (q·J(χ₁,χ₂)) · ι_*π^*(χ₁χ₂)、q = |ker π|。 -/
theorem conv_shell_chars {L : Type*} [AddCommGroup L] [Fintype L]
    (ι : L →+ G) (hι : Function.Injective ι) (π : L →+ ZMod (p ^ (n + 1))) (hπ : Function.Surjective π)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    PAG.Part15.conv (push ι (χ₁ ∘ π)) (push ι (χ₂ ∘ π))
      = (((univ.filter (fun z : L => π z = 0)).card : ℂ) * PAG.Part7.J χ₁ χ₂) •
          push ι ((χ₁ * χ₂ : DirichletCharacter ℂ _) ∘ π) := by
  classical
  rw [push_conv ι hι, conv_pullback π hπ, PAG.Part16.conv_chars_eq_jacobi χ₁ χ₂ h₁ h₂ h₁₂]
  funext x
  by_cases hx : ∃ a, ι a = x
  · obtain ⟨a, rfl⟩ := hx
    simp only [push, hι.extend_apply, Pi.smul_apply, Function.comp, smul_eq_mul]
    ring
  · simp [push, Function.extend_apply' _ _ _ hx]

/-- 殻 v への埋め込み ι_v : ZMod p^(K−v) → ZMod p^K、x ↦ p^v x。 -/
noncomputable def shellEmb (K v : ℕ) (hv : v ≤ K) : ZMod (p ^ (K - v)) →+ ZMod (p ^ K) :=
  ZMod.lift (p ^ (K - v)) ⟨(p ^ v : ZMod (p ^ K)) • (Int.castAddHom (ZMod (p ^ K))), by
    simp only [AddMonoidHom.smul_apply, Int.castAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Int.cast_natCast, smul_eq_mul]
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← pow_add, Nat.add_sub_cancel' hv, ZMod.natCast_self]⟩

theorem shellEmb_apply (K v : ℕ) (hv : v ≤ K) (x : ZMod (p ^ (K - v))) :
    shellEmb (p := p) K v hv x = ((p ^ v * x.val : ℕ) : ZMod (p ^ K)) := by
  have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast]
  rw [shellEmb, ZMod.lift_coe]
  simp [Int.castAddHom]

/-- ι_v は単射。 -/
theorem shellEmb_injective (K v : ℕ) (hv : v ≤ K) : Function.Injective (shellEmb (p := p) K v hv) := by
  have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [shellEmb_apply, ZMod.natCast_eq_zero_iff] at hx
  have h1 : p ^ v * p ^ (K - v) ∣ p ^ v * x.val := by rw [← pow_add, Nat.add_sub_cancel' hv]; exact hx
  have h2 : p ^ (K - v) ∣ x.val := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos v) h1
  rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]; exact h2

/-- **具体的な一般殻の定理 A**（ZMod p^K、殻 v、導手 p^(n+1)、p^(n+1) ∣ p^(K−v)）:
ι_v,* π^*χ₁ ⋆ ι_v,* π^*χ₂ = (q J(χ₁,χ₂)) · ι_v,* π^*(χ₁χ₂)。 -/
theorem conv_shell_chars_zmod (K v : ℕ) (hv : v ≤ K) (hc : p ^ (n + 1) ∣ p ^ (K - v))
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1)))
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) (h₁₂ : (χ₁ * χ₂).IsPrimitive) :
    let π := (ZMod.castHom hc (ZMod (p ^ (n + 1)))).toAddMonoidHom
    let ι := shellEmb (p := p) K v hv
    PAG.Part15.conv (push ι (χ₁ ∘ π)) (push ι (χ₂ ∘ π))
      = (((univ.filter (fun z => π z = 0)).card : ℂ) * PAG.Part7.J χ₁ χ₂) •
          push ι ((χ₁ * χ₂ : DirichletCharacter ℂ _) ∘ π) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro π ι
  exact conv_shell_chars ι (shellEmb_injective K v hv) π (ZMod.ringHom_surjective _) χ₁ χ₂ h₁ h₂ h₁₂

/-- 正規化（|S_v|^(−1/2) 倍のケット）: B(a F₁, a F₂) = (a q J) · (a F₁₂)。 -/
theorem conv_normalized {X : Type*} [AddCommGroup X] [Fintype X] (a qJ : ℂ) (F₁ F₂ F₁₂ : X → ℂ)
    (h : PAG.Part15.conv F₁ F₂ = qJ • F₁₂) :
    PAG.Part15.conv (a • F₁) (a • F₂) = (a * qJ) • (a • F₁₂) := by
  rw [PAG.Part15.conv_smul_smul, h, smul_smul, smul_smul]; ring_nf

end GeneralShell

end PAG.Part17

#print axioms PAG.Part17.block_sum_orth
#print axioms PAG.Part17.glue_identity
#print axioms PAG.Part17.equator_from_south
#print axioms PAG.Part17.AS_sup_AN
#print axioms PAG.Part17.AS_inf_AN
#print axioms PAG.Part17.sum_push_mul
#print axioms PAG.Part17.push_conv
#print axioms PAG.Part17.sum_comp_surj
#print axioms PAG.Part17.conv_pullback
#print axioms PAG.Part17.dft_pullback_eq_zero
#print axioms PAG.Part17.conv_shell_chars
#print axioms PAG.Part17.shellEmb_apply
#print axioms PAG.Part17.shellEmb_injective
#print axioms PAG.Part17.conv_shell_chars_zmod
#print axioms PAG.Part17.conv_normalized
