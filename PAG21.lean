/-
  PAG 2.0 Part 17（2026-10-18）— 押し出しの合成則と、定理 A の最終形のケット表示
  ι_{w,*}((ι_{v,*} f) ∘ π) = ι_{w+v,*}(f ∘ π')
  （ι_u : ZMod p^(K−u) → ZMod p^K は x ↦ p^u x、π, π' は射影）
  これで定理 A の右辺が殻 w+v の標準ケット ket_{w+v}(ψ) そのものになる。
-/
import PAG20

namespace PAG.Part21

open ZMod Finset PAG.Part17 PAG.Part19

variable {p : ℕ} [hp : Fact p.Prime]

/-- castHom の値は val の剰余。 -/
theorem castHom_eq_natCast {m n : ℕ} (h : m ∣ n) (y : ZMod n) [NeZero n] :
    ZMod.castHom h (ZMod m) y = ((y.val : ℕ) : ZMod m) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

theorem push_apply_emb {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G)
    (hι : Function.Injective ι) (f : H → ℂ) (y : H) : push ι f (ι y) = f y := by
  rw [push, hι.extend_apply]

theorem push_apply_not {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G)
    (f : H → ℂ) (x : G) (hx : ¬ ∃ y, ι y = x) : push ι f x = 0 := by
  rw [push, Function.extend_apply' _ _ _ hx, Pi.zero_apply]

/-- **押し出しの合成則**: w + c ≤ K、v ≤ c のとき、任意の f について
ι_{w,*}((ι_{v,*} f) ∘ π) = ι_{w+v,*}(f ∘ π')。 -/
theorem push_comp (K w c v : ℕ) (hw : w + c ≤ K) (hv : v ≤ c) (f : ZMod (p ^ (c - v)) → ℂ) :
    push (shellEmb (p := p) K w (by omega))
        (push (shellEmb (p := p) c v hv) f ∘
          (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c))).toAddMonoidHom)
      = push (shellEmb (p := p) K (w + v) (by omega))
          (f ∘ (ZMod.castHom (pow_dvd_pow p (by omega : c - v ≤ K - (w + v))) (ZMod (p ^ (c - v)))).toAddMonoidHom) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - (w + v))) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (c - v)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hKw : p ^ K = p ^ w * p ^ (K - w) := by rw [← pow_add]; congr 1; omega
  have hKwv : p ^ K = p ^ (w + v) * p ^ (K - (w + v)) := by rw [← pow_add]; congr 1; omega
  have hKwv' : p ^ (K - w) = p ^ v * p ^ (K - (w + v)) := by rw [← pow_add]; congr 1; omega
  have hcv : p ^ c = p ^ v * p ^ (c - v) := by rw [← pow_add]; congr 1; omega
  have hι_w := shellEmb_injective (p := p) K w (by omega)
  have hι_v := shellEmb_injective (p := p) c v hv
  have hι_wv := shellEmb_injective (p := p) K (w + v) (by omega)
  funext x
  by_cases hx : ∃ s, shellEmb (p := p) K (w + v) (by omega) s = x
  · obtain ⟨s, rfl⟩ := hx
    -- y = p^v s ∈ ZMod p^(K−w)
    set y : ZMod (p ^ (K - w)) := ((p ^ v * s.val : ℕ) : ZMod (p ^ (K - w))) with hy
    have e1 : shellEmb (p := p) K (w + v) (by omega) s = shellEmb (p := p) K w (by omega) y := by
      rw [shellEmb_apply, shellEmb_apply, hy, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff', hKw,
        pow_add, mul_assoc]
      simp only [Nat.mul_mod_mul_left, Nat.mod_mod]
    set t : ZMod (p ^ (c - v)) := ((s.val : ℕ) : ZMod (p ^ (c - v))) with ht
    have e2 : (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c))) y
        = shellEmb (p := p) c v hv t := by
      rw [hy, map_natCast, shellEmb_apply, ht, ZMod.val_natCast, ZMod.natCast_eq_natCast_iff', hcv]
      simp only [Nat.mul_mod_mul_left, Nat.mod_mod]
    have e3 : (ZMod.castHom (pow_dvd_pow p (by omega : c - v ≤ K - (w + v))) (ZMod (p ^ (c - v)))) s = t := by
      rw [castHom_eq_natCast, ht]
    rw [push_apply_emb _ hι_wv]
    conv_lhs => rw [e1]
    rw [push_apply_emb _ hι_w]
    simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
    rw [e2, push_apply_emb _ hι_v, e3]
  · rw [push_apply_not _ _ _ hx]
    by_cases hy : ∃ y, shellEmb (p := p) K w (by omega) y = x
    · obtain ⟨y, rfl⟩ := hy
      rw [push_apply_emb _ hι_w]
      simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
      by_cases htt : ∃ t, shellEmb (p := p) c v hv t = ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)) y
      · exfalso
        obtain ⟨t, htv⟩ := htt
        rw [shellEmb_apply, castHom_eq_natCast, ZMod.natCast_eq_natCast_iff'] at htv
        -- p^v ∣ y.val
        have hdvd : p ^ v ∣ y.val := by
          have h1 : p ^ v ∣ (p ^ v * t.val) % p ^ c :=
            (Nat.dvd_mod_iff (pow_dvd_pow p hv)).mpr (dvd_mul_right _ _)
          rw [htv] at h1
          exact (Nat.dvd_mod_iff (pow_dvd_pow p hv)).mp h1
        obtain ⟨m, hm⟩ := hdvd
        apply hx
        refine ⟨((m : ℕ) : ZMod (p ^ (K - (w + v)))), ?_⟩
        rw [shellEmb_apply, shellEmb_apply, ZMod.val_natCast, hm, ZMod.natCast_eq_natCast_iff', hKwv,
          pow_add, mul_assoc, mul_assoc (p ^ w) (p ^ v)]
        simp only [Nat.mul_mod_mul_left, Nat.mod_mod]
      · rw [push_apply_not _ _ _ htt]
    · rw [push_apply_not _ _ _ hy]

/-- 殻 u の標準ケット（step30 の `P.ket(u, c, j)` に対応）: |S_u|^(−1/2) ι_{u,*}(χ ∘ π_u)。 -/
noncomputable def ket (K u c : ℕ) (huc : u + c ≤ K) (χ : ZMod (p ^ c) → ℂ) : ZMod (p ^ K) → ℂ :=
  have : NeZero (p ^ (K - u)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  (((Real.sqrt (sz p K u))⁻¹ : ℝ) : ℂ) •
    push (shellEmb (p := p) K u (by omega))
      (χ ∘ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - u)) (ZMod (p ^ c))).toAddMonoidHom)

/-- **定理 A（ケット表示の最終形）**:
B_cv(|w,χ₁⟩, |w,χ₂⟩) = √(p^K/|S_{w0}|) · J̃ · |w+v, ψ⟩、J̃ = τ₁τ₂/(τ(ψ)√(p^(c+v)))、c = n+1。 -/
theorem thmA_ket (K w n v : ℕ) (hv : v ≤ n) (hK : w + (n + 1) ≤ K)
    (χ₁ χ₂ : DirichletCharacter ℂ (p ^ (n + 1))) (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (ψ : DirichletCharacter ℂ (p ^ (n + 1 - v))) (hψ : ψ.IsPrimitive)
    (hprod : ∀ x, (χ₁ * χ₂) x = ψ (ZMod.castHom (pow_dvd_pow p (Nat.sub_le (n + 1) v)) _ x)) :
    PAG.Part15.conv (ket K w (n + 1) hK χ₁) (ket K w (n + 1) hK χ₂)
      = ((Real.sqrt ((p : ℝ) ^ K / (sz p K (K - (n + 1) - w) : ℝ)) : ℝ) *
          (gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar /
            (gaussSum ψ stdAddChar * ((Real.sqrt ((p : ℝ) ^ (n + 1 + v)) : ℝ) : ℂ))) : ℂ) •
        ket K (w + v) (n + 1 - v) (by omega) ψ := by
  have h := PAG.Part20.thmA_normalized K w n v hv hK χ₁ χ₂ h₁ h₂ ψ hψ hprod
  simp only at h
  unfold ket
  rw [h, push_comp K w (n + 1) v hK (by omega)]

end PAG.Part21

#print axioms PAG.Part21.castHom_eq_natCast
#print axioms PAG.Part21.push_apply_emb
#print axioms PAG.Part21.push_apply_not
#print axioms PAG.Part21.push_comp
#print axioms PAG.Part21.thmA_ket
