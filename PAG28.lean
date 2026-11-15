/-
  PAG 2.0 Part 24（2026-10-19）
  1. 本来の射影直線 ProjLine(p^K) 上の関数空間と 2 チャート部分空間の直接同型、W と B_S, B_N の移植
  2. 定理 B の動径基底 e_u 展開と、球べき等元 ε_{w0} との比例
  3. 積の導手が下がる（v ≥ 1）とき、定理 A・鏡像定理 A の像は赤道で 0
-/
import PAG27

namespace PAG.Part28

open ZMod Finset PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part22 PAG.Part23 PAG.Part25 PAG.Part26 PAG.Part27

open Classical

variable {p : ℕ} [hp : Fact p.Prime]

instance neZeroPow (K : ℕ) : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

/-! ## 1. 関数空間の直接同型と作用素の移植 -/

section FunIso

variable (K : ℕ) (hK : 1 ≤ K)

/-- **関数空間の直接同型**: (ProjLine(p^K) → ℂ) ≃ₗ 貼り合わせ条件の部分空間。 -/
noncomputable def projFunEquiv : (ProjLine (p ^ K) → ℂ) ≃ₗ[ℂ] compatSub (p ^ K) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (projEquiv K hK)).trans (ptEquiv (p ^ K))

/-- 南成分: x ↦ Φ([x:1])。 -/
theorem projFun_eq (Φ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK Φ).1 = toP1 (Φ ∘ toProj K) := rfl

theorem projFun_south (Φ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.1 x = Φ (mk ⟨(x, 1), 0, 1, by simp⟩) := rfl

omit hp in
/-- 単数 y で [y⁻¹:1] = [1:y]。 -/
theorem mk_inv_eq {N : ℕ} {y : ZMod N} (hy : IsUnit y) :
    (mk ⟨(y⁻¹, 1), 0, 1, by simp⟩ : ProjLine N) = mk ⟨(1, y), 1, 0, by simp⟩ := by
  obtain ⟨u, rfl⟩ := hy
  apply mk_eq_mk u
  · show (1 : ZMod N) = u * (u : ZMod N)⁻¹
    rw [ZMod.inv_coe_unit, Units.mul_inv]
  · show (u : ZMod N) = u * 1
    rw [mul_one]

/-- 北成分: y ↦ Φ([1:y])（y が単数でも非単数でも）。 -/
theorem projFun_north (Φ : ProjLine (p ^ K) → ℂ) (y : ZMod (p ^ K)) :
    (projFunEquiv K hK Φ).1.2 y = Φ (mk ⟨(1, y), 1, 0, by simp⟩) := by
  rw [projFun_eq]
  simp only [toP1, Function.comp_apply]
  split_ifs with hy
  · exact congrArg Φ (mk_inv_eq hy)
  · rfl

/-- ProjLine 上の反転の引き戻し W_proj Φ = Φ ∘ Wproj。 -/
def Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : ProjLine N → ℂ := Φ ∘ Wproj

omit hp in
theorem Wpull_Wpull {N : ℕ} (Φ : ProjLine N → ℂ) : Wpull (Wpull Φ) = Φ := by
  funext q; simp [Wpull, Wproj_Wproj]

/-- **W_proj は 2 チャートの入れ替え W に対応**。 -/
theorem projFun_Wpull (Φ : ProjLine (p ^ K) → ℂ) :
    (projFunEquiv K hK (Wpull Φ)).1 = W (projFunEquiv K hK Φ).1 := by
  show toP1 ((Φ ∘ Wproj) ∘ toProj K) = W (toP1 (Φ ∘ toProj K))
  have : (Φ ∘ Wproj) ∘ toProj K = (Φ ∘ toProj K) ∘ Wpt := by
    funext z; simp [toProj_Wpt]
  rw [this, toP1_comp_Wpt]

/-- ProjLine 上の南の畳み込み。 -/
noncomputable def BSproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BS (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extS _⟩

/-- ProjLine 上の北の畳み込み。 -/
noncomputable def BNproj (Φ Ψ : ProjLine (p ^ K) → ℂ) : ProjLine (p ^ K) → ℂ :=
  (projFunEquiv K hK).symm
    ⟨BN (projFunEquiv K hK Φ).1 (projFunEquiv K hK Ψ).1, compat_extN _⟩

/-- B_S^proj は南チャートでの畳み込み: B_S^proj(Φ,Ψ)[x:1] = Σ_y Φ[y:1] Ψ[x−y:1]。 -/
theorem BSproj_south (Φ Ψ : ProjLine (p ^ K) → ℂ) (x : ZMod (p ^ K)) :
    BSproj K hK Φ Ψ (mk ⟨(x, 1), 0, 1, by simp⟩)
      = PAG.Part15.conv (fun z => Φ (mk ⟨(z, 1), 0, 1, by simp⟩))
          (fun z => Ψ (mk ⟨(z, 1), 0, 1, by simp⟩)) x := by
  have e := projFun_south K hK (BSproj K hK Φ Ψ) x
  rw [← e, BSproj, LinearEquiv.apply_symm_apply]
  rfl

/-- **B_N^proj = W_proj B_S^proj(W_proj ·, W_proj ·)**。 -/
theorem BNproj_eq (Φ Ψ : ProjLine (p ^ K) → ℂ) :
    BNproj K hK Φ Ψ = Wpull (BSproj K hK (Wpull Φ) (Wpull Ψ)) := by
  apply (projFunEquiv K hK).injective
  apply Subtype.ext
  rw [projFun_Wpull, BSproj, LinearEquiv.apply_symm_apply, BNproj, LinearEquiv.apply_symm_apply]
  simp only [projFun_Wpull]
  rfl

end FunIso

/-! ## 2. 定理 B の e_u 展開と ε_{w0} 比例 -/

section Radial

/-- 殻 u の指示関数（u < K）、u = K では球 p^K Z = {0}。 -/
noncomputable def shellInd (K u : ℕ) : ZMod (p ^ K) → ℂ :=
  if u < K then ball (p := p) K u - ball (p := p) K (u + 1) else ball (p := p) K K

omit hp in
/-- **望遠鏡和**: ball(m) = Σ_{u∈[m,K)} shellInd(u) + shellInd(K)（m ≤ K）。 -/
theorem ball_eq_sum_shellInd (K m : ℕ) (hm : m ≤ K) :
    ball (p := p) K m = ∑ u ∈ Ico m K, shellInd (p := p) K u + shellInd (p := p) K K := by
  have h1 : ∑ u ∈ Ico m K, shellInd (p := p) K u
      = ∑ u ∈ Ico m K, (ball (p := p) K u - ball (p := p) K (u + 1)) :=
    sum_congr rfl (fun u hu => by rw [shellInd, ite_eq_left_of_eq_true _ _ (eq_true (mem_Ico.mp hu).2)])
  have h2 : ∑ u ∈ Ico m K, (ball (p := p) K u - ball (p := p) K (u + 1))
      = ball (p := p) K m - ball (p := p) K K := by
    rw [sum_Ico_eq_sum_range]
    have := sum_range_sub' (fun k => ball (p := p) K (m + k)) (K - m)
    simp only [add_zero, Nat.add_sub_cancel' hm] at this
    rw [← this]
    refine sum_congr rfl (fun k _ => ?_)
    rw [add_assoc]
  rw [h1, h2, shellInd, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl K)), sub_add_cancel]

/-- 正規化動径基底 e_u = |S_u|^(−1/2) 1_{S_u}（u < K）、e_K = 1_{0}。 -/
noncomputable def eu (K u : ℕ) : ZMod (p ^ K) → ℂ :=
  if u < K then ((Real.sqrt (sz p K u) : ℝ) : ℂ)⁻¹ • shellInd (p := p) K u else shellInd (p := p) K K

theorem sqrt_sz_ne_zero (K u : ℕ) : ((Real.sqrt (sz p K u) : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < sz p K u := by
    unfold sz; exact_mod_cast Nat.mul_pos (pow_pos hp.out.pos _) (by have := hp.out.two_le; omega)
  exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'

theorem shellInd_eq_eu {K u : ℕ} (hu : u < K) :
    shellInd (p := p) K u = ((Real.sqrt (sz p K u) : ℝ) : ℂ) • eu (p := p) K u := by
  rw [eu, ite_eq_left_of_eq_true _ _ (eq_true hu), smul_smul, mul_inv_cancel₀ (sqrt_sz_ne_zero K u), one_smul]

/-- **cascade の e_u 展開**（c = n+1、w + c ≤ K）:
cascade = −√|S_{w+n}|/(p−1) e_{w+n} + Σ_{u∈[w+c,K)} √|S_u| e_u + e_K。 -/
theorem cascade_eu (K w n : ℕ) (hK : w + (n + 1) ≤ K) :
    cascade (p := p) K w n
      = (-(((Real.sqrt (sz p K (w + n)) : ℝ) : ℂ) * ((p : ℂ) - 1)⁻¹)) • eu (p := p) K (w + n)
        + ∑ u ∈ Ico (w + (n + 1)) K, ((Real.sqrt (sz p K u) : ℝ) : ℂ) • eu (p := p) K u
        + eu (p := p) K K := by
  have hs : ball (p := p) K (w + n) - ball (p := p) K (w + (n + 1))
      = ((Real.sqrt (sz p K (w + n)) : ℝ) : ℂ) • eu (p := p) K (w + n) := by
    rw [← shellInd_eq_eu (by omega), shellInd, ite_eq_left_of_eq_true _ _ (eq_true (by omega)), add_assoc]
  have hb : ball (p := p) K (w + (n + 1))
      = ∑ u ∈ Ico (w + (n + 1)) K, ((Real.sqrt (sz p K u) : ℝ) : ℂ) • eu (p := p) K u
        + eu (p := p) K K := by
    rw [ball_eq_sum_shellInd K _ hK, eu, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl K))]
    congr 1
    exact sum_congr rfl (fun u hu => shellInd_eq_eu (mem_Ico.mp hu).2)
  rw [cascade, hs, hb, smul_smul, neg_smul, mul_comm]
  abel

/-- **定理 B の e_u 展開形**。 -/
theorem thmB_eu (K w n : ℕ) (hK : w + (n + 1) ≤ K)
    (χ : DirichletCharacter ℂ (p ^ (n + 1))) (hχ : χ.IsPrimitive) :
    PAG.Part15.conv (ket K w (n + 1) hK χ) (ket K w (n + 1) hK ((χ⁻¹ : DirichletCharacter ℂ _) : ZMod _ → ℂ))
      = χ (-1) • ((-(((Real.sqrt (sz p K (w + n)) : ℝ) : ℂ) * ((p : ℂ) - 1)⁻¹)) • eu (p := p) K (w + n)
        + ∑ u ∈ Ico (w + (n + 1)) K, ((Real.sqrt (sz p K u) : ℝ) : ℂ) • eu (p := p) K u
        + eu (p := p) K K) := by
  rw [thmB_closed K w n hK χ hχ, ← cascade_eu K w n hK]
  rfl

/-- 球平均 P(u) = p^(−u) · 1_{p^(K−u) Z}。 -/
noncomputable def Pavg (K u : ℕ) : ZMod (p ^ K) → ℂ := ((p : ℂ) ^ u)⁻¹ • ball (p := p) K (K - u)

/-- **cascade = (p^K/|S_{w0}|) · ε_{w0}**（w0 = K − c − w の双対殻）。 -/
theorem cascade_eps (K w n : ℕ) (hK : w + (n + 1) ≤ K) :
    cascade (p := p) K w n
      = ((p : ℂ) ^ K / (sz p K (K - (n + 1) - w) : ℂ)) •
          PAG.Part14.epsBall (Pavg (p := p) K) K (K - (n + 1) - w) := by
  have hw0 : K - (n + 1) - w < K := by omega
  have e1 : K - (K - (n + 1) - w) = w + (n + 1) := by omega
  have e2 : K - (K - (n + 1) - w + 1) = w + n := by omega
  have hsz : (sz p K (K - (n + 1) - w) : ℂ) = (p : ℂ) ^ (w + n) * ((p : ℂ) - 1) := by
    unfold sz
    rw [show K - 1 - (K - (n + 1) - w) = w + n by omega]
    push_cast [Nat.cast_sub hp.out.one_lt.le]
    ring
  have hpK : (p : ℂ) ^ K = (p : ℂ) ^ (K - (n + 1) - w) * (p : ℂ) ^ (w + n) * p := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    intro h; apply this.ne'; exact_mod_cast (sub_eq_zero.mp h)
  rw [PAG.Part14.epsBall, ite_eq_left_of_eq_true _ _ (eq_true hw0), Pavg, Pavg, e1, e2, hsz, hpK]
  funext x
  simp only [cascade, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

end Radial

/-! ## 3. 導手降下（v ≥ 1）での赤道消滅 -/

section Descent

/-- **内部殻ケットは単数上で 0**（1 ≤ u）。 -/
theorem ket_eq_zero_of_isUnit (K u c' : ℕ) (h : u + c' ≤ K) (hu : 1 ≤ u) (ψ : ZMod (p ^ c') → ℂ)
    {x : ZMod (p ^ K)} (hx : IsUnit x) : ket K u c' h ψ x = 0 := by
  have hnd := (isUnit_iff_not_dvd (by omega) x).mp hx
  unfold ket
  rw [Pi.smul_apply, push_apply_not, smul_zero]
  intro hex
  apply hnd
  have := (mem_range_iff (p := p) K u (by omega) x).mp hex
  exact (dvd_pow_self p (by omega)).trans this

theorem kS_equator_zero (K u c' : ℕ) (h : u + c' ≤ K) (hu : 1 ≤ u) (ψ : DirichletCharacter ℂ (p ^ c'))
    {x : ZMod (p ^ K)} (hx : IsUnit x) : (kS K u c' h ψ).1 x = 0 ∧ (kS K u c' h ψ).2 x = 0 := by
  refine ⟨ket_eq_zero_of_isUnit K u c' h hu _ hx, ?_⟩
  unfold kS extS
  simp only [hx, ↓reduceIte]
  exact ket_eq_zero_of_isUnit K u c' h hu _ (inv_inv_of_unit hx).1

theorem kN_equator_zero (K u c' : ℕ) (h : u + c' ≤ K) (hu : 1 ≤ u) (ψ : DirichletCharacter ℂ (p ^ c'))
    {x : ZMod (p ^ K)} (hx : IsUnit x) : (kN K u c' h ψ).1 x = 0 ∧ (kN K u c' h ψ).2 x = 0 := by
  refine ⟨?_, ket_eq_zero_of_isUnit K u c' h hu _ hx⟩
  unfold kN extN
  simp only [hx, ↓reduceIte]
  exact ket_eq_zero_of_isUnit K u c' h hu _ (inv_inv_of_unit hx).1

/-- 定理 A の P¹ 版（南）: B_S(|w,χ₁⟩,|w,χ₂⟩) = √(p^K/|S_{w0}|) J̃ · |w+v, ψ⟩。 -/
theorem thmA_south (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    BS (kS K w (n + 1) hK χ₁) (kS K w (n + 1) hK χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        kS K (w + v) (n + 1 - v) (by omega) ψ := by
  unfold BS kS
  show extS (PAG.Part15.conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂)) = _
  rw [thmA_ket K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod, extS_smul]

/-- **導手降下での赤道消滅**: 1 ≤ v ≤ n なら、南の定理 A・北の鏡像定理 A の像は
赤道（単数）上で第 1・第 2 成分とも 0。 -/
theorem descent_equator_zero (K w n v : ℕ) (hv1 : 1 ≤ v) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x))
    {x : ZMod (p ^ K)} (hx : IsUnit x) :
    (BS (kS K w (n + 1) hK χ₁) (kS K w (n + 1) hK χ₂)).1 x = 0 ∧
    (BS (kS K w (n + 1) hK χ₁) (kS K w (n + 1) hK χ₂)).2 x = 0 ∧
    (BN (kN K w (n + 1) hK χ₁) (kN K w (n + 1) hK χ₂)).1 x = 0 ∧
    (BN (kN K w (n + 1) hK χ₁) (kN K w (n + 1) hK χ₂)).2 x = 0 := by
  have hS := kS_equator_zero K (w + v) (n + 1 - v) (by omega) (by omega) ψ hx
  have hN := kN_equator_zero K (w + v) (n + 1 - v) (by omega) (by omega) ψ hx
  rw [thmA_south K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod, mirror_thmA K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod]
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hS.1, hS.2, hN.1, hN.2, mul_zero,
    and_self]

end Descent

end PAG.Part28

#print axioms PAG.Part28.projFunEquiv
#print axioms PAG.Part28.projFun_eq
#print axioms PAG.Part28.projFun_south
#print axioms PAG.Part28.mk_inv_eq
#print axioms PAG.Part28.projFun_north
#print axioms PAG.Part28.Wpull_Wpull
#print axioms PAG.Part28.projFun_Wpull
#print axioms PAG.Part28.BSproj_south
#print axioms PAG.Part28.BNproj_eq
#print axioms PAG.Part28.ball_eq_sum_shellInd
#print axioms PAG.Part28.sqrt_sz_ne_zero
#print axioms PAG.Part28.shellInd_eq_eu
#print axioms PAG.Part28.cascade_eu
#print axioms PAG.Part28.thmB_eu
#print axioms PAG.Part28.cascade_eps
#print axioms PAG.Part28.ket_eq_zero_of_isUnit
#print axioms PAG.Part28.kS_equator_zero
#print axioms PAG.Part28.kN_equator_zero
#print axioms PAG.Part28.thmA_south
#print axioms PAG.Part28.descent_equator_zero
