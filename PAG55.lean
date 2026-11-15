/-
  PAG 2.0 Part 51（2026-10-19）— 族 S は直交系、したがって一次独立（基底）
  S = 原始ケット ∪ 殻の指示関数 ∪ {δ₀}（PAG54）について
  1. S の相異なる 2 元は直交（内積 0）
  2. S の元はどれも 0 でない
  3. S は一次独立。PAG54 の完全性と合わせて S は ℂ^(Z/p^K) の基底
-/
import PAG54

namespace PAG.Part55

open ZMod Finset PAG.Part15 PAG.Part17 PAG.Part19 PAG.Part21 PAG.Part24 PAG.Part52 PAG.Part54

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## 内積の一般的な性質 -/

theorem ip_conj {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) : ip g f = starRingEnd ℂ (ip f g) := by
  simp only [ip, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

theorem ip_smul_left {N : ℕ} [NeZero N] (a : ℂ) (f g : ZMod N → ℂ) :
    ip (a • f) g = starRingEnd ℂ a * ip f g := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem ip_smul_right {N : ℕ} [NeZero N] (a : ℂ) (f g : ZMod N → ℂ) :
    ip f (a • g) = a * ip f g := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem ip_self_ne_zero {N : ℕ} [NeZero N] (f : ZMod N → ℂ) (hf : f ≠ 0) : ip f f ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf
  have e : ip f f = ((∑ y, Complex.normSq (f y) : ℝ) : ℂ) := by
    simp only [ip]; push_cast
    exact Finset.sum_congr rfl (fun y _ => by rw [mul_comm, Complex.mul_conj])
  rw [e]
  have hpos : 0 < ∑ y, Complex.normSq (f y) :=
    Finset.sum_pos' (fun y _ => Complex.normSq_nonneg _) ⟨x, mem_univ _, Complex.normSq_pos.mpr hx⟩
  exact_mod_cast hpos.ne'

theorem ip_delta {N : ℕ} [NeZero N] (g : ZMod N → ℂ) : ip (Pi.single 0 1) g = g 0 := by
  unfold ip
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (mem_univ _) h

/-! ## 押し出しの内積 -/

theorem conj_push {G H : Type*} [AddCommGroup G] [AddCommGroup H] (ι : H →+ G) (hι : Function.Injective ι)
    (f : H → ℂ) (z : G) :
    starRingEnd ℂ (push ι f z) = push ι (fun y => starRingEnd ℂ (f y)) z := by
  by_cases hz : ∃ y, ι y = z
  · obtain ⟨y, rfl⟩ := hz
    rw [PAG.Part21.push_apply_emb _ hι, PAG.Part21.push_apply_emb _ hι]
  · rw [PAG.Part21.push_apply_not _ _ _ hz, PAG.Part21.push_apply_not _ _ _ hz, map_zero]

/-- 同じ殻: ⟨ι_*f, ι_*g⟩ = Σ_y conj(f y)·g y。 -/
theorem ip_push_same (K w : ℕ) (hw : w ≤ K) (f g : ZMod (p ^ (K - w)) → ℂ) :
    ip (push (shellEmb (p := p) K w hw) f) (push (shellEmb (p := p) K w hw) g)
      = ∑ y, starRingEnd ℂ (f y) * g y := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hinj := shellEmb_injective (p := p) K w hw
  unfold ip
  simp_rw [conj_push _ hinj]
  rw [sum_push_mul _ hinj]
  exact Finset.sum_congr rfl (fun y _ => by rw [PAG.Part21.push_apply_emb _ hinj])

/-- 殻 w の点 ι_w(y) は殻 w' < w の点 ι_{w'}(p^(w−w')·y) でもある。 -/
theorem shellEmb_lower (K w w' : ℕ) (hw' : w' < w) (hw : w < K) (y : ZMod (p ^ (K - w))) :
    shellEmb (p := p) K w hw.le y
      = shellEmb (p := p) K w' (by omega) ((p ^ (w - w') * y.val : ℕ) : ZMod (p ^ (K - w'))) := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hlt : p ^ (w - w') * y.val < p ^ (K - w') := by
    have := ZMod.val_lt y
    calc p ^ (w - w') * y.val < p ^ (w - w') * p ^ (K - w) := Nat.mul_lt_mul_of_pos_left this (pow_pos hp.out.pos _)
      _ = p ^ (K - w') := by rw [← pow_add]; congr 1; omega
  rw [shellEmb_apply, shellEmb_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ← mul_assoc, ← pow_add]
  congr 3; omega

/-- 非単数で消える関数。 -/
def VanishNU {N : ℕ} (f : ZMod N → ℂ) : Prop := ∀ y, ¬ IsUnit y → f y = 0

/-- **異なる殻の押し出しは直交**（w' < w、どちらも非単数で消える）。 -/
theorem ip_push_lower (K w w' : ℕ) (hw' : w' < w) (hw : w < K)
    (f : ZMod (p ^ (K - w)) → ℂ) (g : ZMod (p ^ (K - w')) → ℂ) (hf : VanishNU f) (hg : VanishNU g) :
    ip (push (shellEmb (p := p) K w hw.le) f) (push (shellEmb (p := p) K w' (by omega)) g) = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hinj := shellEmb_injective (p := p) K w hw.le
  have hinj' := shellEmb_injective (p := p) K w' (by omega)
  unfold ip
  simp_rw [conj_push _ hinj]
  rw [sum_push_mul _ hinj]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hy : IsUnit y
  · rw [shellEmb_lower K w w' hw' hw y, PAG.Part21.push_apply_emb _ hinj', hg _ ?_, mul_zero]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_left]
    rintro ⟨h1, -⟩
    rw [Nat.coprime_pow_left_iff (by omega), Nat.coprime_pow_right_iff (by omega), Nat.coprime_self] at h1
    exact hp.out.one_lt.ne' h1
  · rw [hf y hy, map_zero, zero_mul]

theorem ip_push_ne (K w w' : ℕ) (hne : w ≠ w') (hw : w < K) (hw' : w' < K)
    (f : ZMod (p ^ (K - w)) → ℂ) (g : ZMod (p ^ (K - w')) → ℂ) (hf : VanishNU f) (hg : VanishNU g) :
    ip (push (shellEmb (p := p) K w hw.le) f) (push (shellEmb (p := p) K w' hw'.le) g) = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ip_conj, ip_push_lower K w' w h hw' g f hg hf, map_zero]
  · exact ip_push_lower K w w' h hw f g hf hg

/-! ## 族の元を押し出しとして書く -/

theorem ket_eq_push (K w c : ℕ) (h : w + c ≤ K) (ψ : DirichletCharacter ℂ (p ^ c)) :
    ket K w c h ψ = (((Real.sqrt (sz p K w))⁻¹ : ℝ) : ℂ) •
      push (shellEmb (p := p) K w (by omega))
        (fun y => ψ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)) y)) := rfl

theorem vanish_ket (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (ψ : DirichletCharacter ℂ (p ^ c)) :
    VanishNU (fun y : ZMod (p ^ (K - w)) => ψ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)) y)) :=
  fun _ hy => chi_cast_nonunit hc (by omega) ψ hy

theorem vanish_one (K w : ℕ) (hw : w < K) :
    VanishNU (((1 : DirichletCharacter ℂ (p ^ (K - w))) : ZMod (p ^ (K - w)) → ℂ)) := by
  have : Fact (1 < p ^ (K - w)) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  exact fun _ hy => MulChar.map_nonunit _ hy

/-- 同じ殻の原始ケットと殻の指示関数は直交（非自明な指標の和は 0）。 -/
theorem ip_ket_shellInd (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (hw : w < K)
    (ψ : DirichletCharacter ℂ (p ^ c)) (hψ : ψ.IsPrimitive) :
    ip (ket K w c h ψ) (shellInd K w hw) = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [ket_eq_push, ip_smul_left, shellInd, ip_push_same]
  have hterm : ∀ y : ZMod (p ^ (K - w)),
      starRingEnd ℂ (ψ (ZMod.castHom (pow_dvd_pow p (by omega : c ≤ K - w)) (ZMod (p ^ c)) y)) *
        (1 : DirichletCharacter ℂ (p ^ (K - w))) y
      = starRingEnd ℂ (DirichletCharacter.changeLevel (pow_dvd_pow p (by omega : c ≤ K - w)) ψ y) := by
    intro y
    rw [PAG.Part47.changeLevel_apply_cast (K := K - w) hc (by omega) ψ y]
    by_cases hy : IsUnit y
    · rw [MulChar.one_apply hy, mul_one]
    · rw [chi_cast_nonunit hc (by omega) ψ hy, map_zero, zero_mul]
  simp_rw [hterm]
  rw [← map_sum, MulChar.sum_eq_zero_of_ne_one, map_zero, mul_zero]
  intro h1
  rw [DirichletCharacter.changeLevel_eq_one_iff] at h1
  have hc1 := (DirichletCharacter.isPrimitive_def ψ).mp hψ
  have : NeZero (p ^ c) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [h1, DirichletCharacter.conductor_one] at hc1
  exact absurd hc1.symm (Nat.one_lt_pow (by omega) hp.out.one_lt).ne'

/-! ## 族の相異なる 2 元は直交 -/

theorem shellInd_zero (K w : ℕ) (hw : w < K) : shellInd (p := p) K w hw 0 = 0 := by
  have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (1 < p ^ (K - w)) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  rw [shellInd, ← map_zero (shellEmb (p := p) K w hw.le), PAG.Part21.push_apply_emb _ (shellEmb_injective K w hw.le)]
  exact vanish_one K w hw 0 not_isUnit_zero

theorem ne_zero_of_mem (K : ℕ) (v : ZMod (p ^ K) → ℂ) (hv : v ∈ family (p := p) K) : v ≠ 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases hv with ⟨w, c, h, hc, ψ, -, rfl⟩ | ⟨w, hw, rfl⟩ | rfl
  · intro h0
    have := congrFun h0 (shellEmb (p := p) K w (by omega) 1)
    rw [PAG.Part51.ket_own_shell, Pi.zero_apply] at this
    exact PAG.Part51.coef_ne_zero K w this
  · intro h0
    have : NeZero (p ^ (K - w)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    have e := congrFun h0 (shellEmb (p := p) K w hw.le 1)
    rw [shellInd, PAG.Part21.push_apply_emb _ (shellEmb_injective K w hw.le), MulChar.map_one, Pi.zero_apply] at e
    exact one_ne_zero e
  · intro h0
    have := congrFun h0 0
    simp at this

/-- ケットと別の族の元の内積（ケットを左に置く場合）。 -/
theorem ip_ket_other (K w c : ℕ) (hc : 1 ≤ c) (h : w + c ≤ K) (ψ : DirichletCharacter ℂ (p ^ c))
    (hψ : ψ.IsPrimitive) (v : ZMod (p ^ K) → ℂ) (hv : v ∈ family (p := p) K) (hne : ket K w c h ψ ≠ v) :
    ip (ket K w c h ψ) v = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases hv with ⟨w', c', h', hc', ψ', hψ', rfl⟩ | ⟨w', hw', rfl⟩ | rfl
  · obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', c' = n' + 1 := ⟨c' - 1, by omega⟩
    by_cases hl : w ≠ w' ∨ n ≠ n'
    · exact ip_ket_eq_zero_of_ne K w n w' n' h h' ψ ψ' hψ hψ' hl
    · rw [not_or, not_not, not_not] at hl
      obtain ⟨rfl, rfl⟩ := hl
      have : ψ ≠ ψ' := by rintro rfl; exact hne rfl
      exact ip_ket_eq_zero_of_char_ne K w n h ψ ψ' hψ hψ' this
  · by_cases hww : w = w'
    · subst hww; exact ip_ket_shellInd K w c hc h hw' ψ hψ
    · rw [ket_eq_push, ip_smul_left, shellInd]
      rw [ip_push_ne K w w' hww (by omega) hw' _ _ (vanish_ket K w c hc h ψ) (vanish_one K w' hw'), mul_zero]
  · rw [ip_conj, ip_delta, PAG.Part49.ket_apply_zero K w c hc h ψ, map_zero]

/-- **相異なる 2 元は直交**。 -/
theorem family_orthogonal (K : ℕ) (u v : ZMod (p ^ K) → ℂ) (hu : u ∈ family (p := p) K) (hv : v ∈ family (p := p) K)
    (hne : u ≠ v) :
    ip u v = 0 := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases hu with ⟨w, c, h, hc, ψ, hψ, rfl⟩ | ⟨w, hw, rfl⟩ | rfl
  · exact ip_ket_other K w c hc h ψ hψ v hv hne
  · rcases hv with ⟨w', c', h', hc', ψ', hψ', rfl⟩ | ⟨w', hw', rfl⟩ | rfl
    · rw [ip_conj, ip_ket_other K w' c' hc' h' ψ' hψ' _ (Or.inr (Or.inl ⟨w, hw, rfl⟩)) (Ne.symm hne), map_zero]
    · have hww : w ≠ w' := by rintro rfl; exact hne rfl
      rw [shellInd, shellInd]
      exact ip_push_ne K w w' hww hw hw' _ _ (vanish_one K w hw) (vanish_one K w' hw')
    · rw [ip_conj, ip_delta, shellInd_zero, map_zero]
  · rcases hv with ⟨w', c', h', hc', ψ', hψ', rfl⟩ | ⟨w', hw', rfl⟩ | rfl
    · rw [ip_delta, PAG.Part49.ket_apply_zero K w' c' hc' h' ψ']
    · rw [ip_delta, shellInd_zero]
    · exact absurd rfl hne

/-- ip の第 2 引数についての線形性（有限和）。 -/
theorem ip_sum_right {N : ℕ} [NeZero N] {ι : Type*} (s : Finset ι) (f : ZMod N → ℂ) (g : ι → ℂ)
    (v : ι → ZMod N → ℂ) : ip f (∑ i ∈ s, g i • v i) = ∑ i ∈ s, g i * ip f (v i) := by
  simp only [ip, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ => by ring))

/-- **一次独立性**。 -/
theorem family_linearIndependent (K : ℕ) :
    LinearIndependent ℂ (fun v : family (p := p) K => (v : ZMod (p ^ K) → ℂ)) := by
  have : NeZero (p ^ K) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [linearIndependent_iff']
  intro s g hg i hi
  have e := congrArg (ip (i : ZMod (p ^ K) → ℂ)) hg
  rw [ip_sum_right, Finset.sum_eq_single i] at e
  · have hz : ip (i : ZMod (p ^ K) → ℂ) 0 = 0 := by simp [ip]
    rw [hz] at e
    exact (mul_eq_zero.mp e).resolve_right (ip_self_ne_zero _ (ne_zero_of_mem (p := p) K i.1 i.2))
  · intro j _ hji
    rw [family_orthogonal (p := p) K i.1 j.1 i.2 j.2 (fun h => hji (Subtype.ext h).symm), mul_zero]
  · intro h; exact absurd hi h

/-- **基底**: 族 S は ℂ^(Z/p^K) の基底（一次独立かつ全体を張る）。 -/
noncomputable def familyBasis (K : ℕ) : Module.Basis (family (p := p) K) ℂ (ZMod (p ^ K) → ℂ) :=
  Module.Basis.mk (family_linearIndependent K) (by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, span_family_eq_top])

/-- 系: 族 S の元の個数は p^K。 -/
theorem card_family (K : ℕ) : Nat.card (family (p := p) K) = p ^ K := by
  have := Module.finrank_eq_nat_card_basis (familyBasis (p := p) K)
  rw [← this, Module.finrank_fintype_fun_eq_card, ZMod.card]

end PAG.Part55

#print axioms PAG.Part55.ip_conj
#print axioms PAG.Part55.ip_smul_left
#print axioms PAG.Part55.ip_smul_right
#print axioms PAG.Part55.ip_self_ne_zero
#print axioms PAG.Part55.ip_delta
#print axioms PAG.Part55.conj_push
#print axioms PAG.Part55.ip_push_same
#print axioms PAG.Part55.shellEmb_lower
#print axioms PAG.Part55.VanishNU
#print axioms PAG.Part55.ip_push_lower
#print axioms PAG.Part55.ip_push_ne
#print axioms PAG.Part55.ket_eq_push
#print axioms PAG.Part55.vanish_ket
#print axioms PAG.Part55.vanish_one
#print axioms PAG.Part55.ip_ket_shellInd
#print axioms PAG.Part55.shellInd_zero
#print axioms PAG.Part55.ne_zero_of_mem
#print axioms PAG.Part55.ip_ket_other
#print axioms PAG.Part55.family_orthogonal
#print axioms PAG.Part55.ip_sum_right
#print axioms PAG.Part55.family_linearIndependent
#print axioms PAG.Part55.familyBasis
#print axioms PAG.Part55.card_family
