/-
  PAG 2.0 Part 233（2026-10-31）— 非対角の行列単位の中国剰余定理による分解（位相とゲージ）
  行列単位 E^d_{χ→χ′} = Θ_{χ→χ′}·ι_d·P_χ（Part 223 の matUnit。Θ は Part 218 の twistFn、ι_d は Part 217 の layerInd）、
  χ_a ⊠ χ_b（Part 232 の charMul）、C・L・R（Part 228）。(c_a, d_a) ∈ S(a)、(c_b, d_b) ∈ S(b)、gcd(a, b) = 1、
  ψ_a = χ′_a χ_a⁻¹、ψ_b = χ′_b χ_b⁻¹、位相 λ = ψ_a(d_b)·ψ_b(d_a)、ゲージ g(χ_a, χ_b) = χ_a(d_b)·χ_b(d_a)
  0. 割り算：d ∣ a なら (n mod a)/d = (n/d) mod (a/d)。x が c_a c_b について d_a d_b の層なら
     (x mod a)/d_a ≡ d_b·(x/(d_a d_b)) (mod c_a)（b 側も同様）。d_b は法 c_a の単数なので λ ≠ 0
  1. ねじりの関数の分解：λ·(Θ^{ab}·ι^{ab})(x) = (Θ^a·ι^a)(x mod a)·(Θ^b·ι^b)(x mod b)（χ′χ⁻¹ = ψ_a ⊠ ψ_b：Part 232 の
     charMul_mul・charMul_inv・charMul_apply）。掛け算の作用素では λ·C(Θ^{ab}ι^{ab}) = L(Θ^aι^a)·R(Θ^bι^b)
  2. 行列単位の分解：λ·C(E^{d_a d_b}_{χ_a⊠χ_b → χ′_a⊠χ′_b}) = L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})（1 と Part 232 の
     crtConj_blockProjL）、C(E) = λ⁻¹·L(E)R(E)
  3. ゲージ：λ = g(χ′)/g(χ)（位相はゲージの比）、g(χ′)·C(E) = g(χ)·L(E)R(E)。法 c_a c_b の原始指標の組はすべてこの形。
     Ẽ = (g(χ′)/g(χ))·E（def gaugeUnit）は C(Ẽ) = L(E^a)·R(E^b)、C⁻¹(L(E^a)R(E^b)) = Ẽ を満たし、行列単位の関係
     Ẽ_{χ′→χ″}·Ẽ_{χ→χ′} = Ẽ_{χ→χ″}、Ẽ_{ψ→χ″}·Ẽ_{χ→χ′} = 0（ψ ≠ χ′）と Ẽ_{χ→χ} = E_{χ→χ} を満たす
-/
import PAG236

namespace PAG.Part237

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233 PAG.Part234
  PAG.Part235 PAG.Part236
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 割り算と単数 -/

/-- **0a.** d ∣ a なら (n mod a)/d = (n/d) mod (a/d)。 -/
theorem mod_div_eq_div_mod {n a d : ℕ} (hda : d ∣ a) : n % a / d = n / d % (a / d) := by
  obtain ⟨k, rfl⟩ := hda
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [Nat.mul_div_cancel_left k hd]
    exact Nat.mod_mul_right_div_self n d k

/-- **0b.** d_a ∣ a、c_a ∣ a/d_a、d_a d_b ∣ x なら (x mod a)/d_a ≡ d_b·(x/(d_a d_b))（mod c_a）。 -/
theorem crt_fst_div_cast {a b ca da db : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hda : da ∣ a)
    (hca : ca ∣ a / da) (hdb : 0 < db) {x : ZMod (a * b)} (hx : da * db ∣ x.val) :
    (((ZMod.chineseRemainder hab x).1.val / da : ℕ) : ZMod ca) =
      (db : ZMod ca) * ((x.val / (da * db) : ℕ) : ZMod ca) := by
  have hda0 : 0 < da := Nat.pos_of_dvd_of_pos hda (Nat.pos_of_ne_zero (NeZero.ne a))
  rw [crt_fst_val, mod_div_eq_div_mod hda, (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq (x.val / da) (a / da)).of_dvd hca)]
  obtain ⟨y, hy⟩ := hx
  rw [hy, Nat.mul_div_cancel_left y (Nat.mul_pos hda0 hdb), mul_assoc, Nat.mul_div_cancel_left _ hda0, Nat.cast_mul]

/-- **0c.** d_b ∣ b、c_b ∣ b/d_b、d_a d_b ∣ x なら (x mod b)/d_b ≡ d_a·(x/(d_a d_b))（mod c_b）。 -/
theorem crt_snd_div_cast {a b cb da db : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hdb : db ∣ b)
    (hcb : cb ∣ b / db) (hda : 0 < da) {x : ZMod (a * b)} (hx : da * db ∣ x.val) :
    (((ZMod.chineseRemainder hab x).2.val / db : ℕ) : ZMod cb) =
      (da : ZMod cb) * ((x.val / (da * db) : ℕ) : ZMod cb) := by
  have hdb0 : 0 < db := Nat.pos_of_dvd_of_pos hdb (Nat.pos_of_ne_zero (NeZero.ne b))
  rw [crt_snd_val, mod_div_eq_div_mod hdb, (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq (x.val / db) (b / db)).of_dvd hcb)]
  obtain ⟨y, hy⟩ := hx
  rw [hy, Nat.mul_div_cancel_left y (Nat.mul_pos hda hdb0), mul_comm da db, mul_assoc,
    Nat.mul_div_cancel_left _ hdb0, Nat.cast_mul]

/-- **0d.** gcd(a, b) = 1、c_a ∣ a、d_b ∣ b なら d_b は法 c_a の単数。 -/
theorem isUnit_cast_of_dvd {a b ca db : ℕ} (hab : Nat.Coprime a b) (hca : ca ∣ a) (hdb : db ∣ b) :
    IsUnit (db : ZMod ca) :=
  (ZMod.isUnit_iff_coprime db ca).mpr
    (Nat.Coprime.coprime_dvd_left hdb (Nat.Coprime.coprime_dvd_right hca hab.symm))

/-- **0e.** 指標 ψ_a（法 c_a）・ψ_b（法 c_b）について ψ_a(d_b)·ψ_b(d_a) ≠ 0（0d：単数での指標の値は 0 でない）。 -/
theorem phase_ne_zero {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ} (hca : ca ∣ a) (hcb : cb ∣ b)
    (hda : da ∣ a) (hdb : db ∣ b) (ψa : DirichletCharacter ℂ ca) (ψb : DirichletCharacter ℂ cb) :
    ψa (db : ZMod ca) * ψb (da : ZMod cb) ≠ 0 :=
  mul_ne_zero ((isUnit_cast_of_dvd hab hca hdb).map ψa).ne_zero
    ((isUnit_cast_of_dvd hab.symm hcb hda).map ψb).ne_zero

/-! ### 1. ねじりの関数の分解 -/

/-- **1a. ねじりの関数の分解** λ·(Θ^{ab}_{χ→χ′}·ι^{ab}_{d_a d_b})(x) = (Θ^a_{χ_a→χ′_a}·ι^a_{d_a})(x mod a)·(Θ^b_{χ_b→χ′_b}·ι^b_{d_b})(x mod b)（χ = χ_a ⊠ χ_b、χ′ = χ′_a ⊠ χ′_b。層の点では Part 218 の twistFn_apply、χ′χ⁻¹ = ψ_a ⊠ ψ_b、0b・0c。層の外では両辺 0：Part 231 の inLayer_mul_iff）。 -/
theorem twist_mul_layerInd_crt {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (χa χa' : DirichletCharacter ℂ ca) (χb χb' : DirichletCharacter ℂ cb) (x : ZMod (a * b)) :
    (χa' * χa⁻¹) (db : ZMod ca) * (χb' * χb⁻¹) (da : ZMod cb) *
        (twistFn (a * b) (ca * cb) (charMul χa χb) (charMul χa' χb') * layerInd (a * b) (ca * cb) (da * db)) x =
      (twistFn a ca χa χa' * layerInd a ca da) (ZMod.chineseRemainder hab x).1 *
        (twistFn b cb χb χb' * layerInd b cb db) (ZMod.chineseRemainder hab x).2 := by
  obtain ⟨hca, ha0, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, hb0, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  have hdaI : da ∈ layerIdx ca (a / ca) := ((mem_centerIdx _ _).mp hp).2.2
  have hdbI : db ∈ layerIdx cb (b / cb) := ((mem_centerIdx _ _).mp hq).2.2
  have hdI : da * db ∈ layerIdx (ca * cb) (a * b / (ca * cb)) :=
    ((mem_centerIdx _ _).mp (idxMul_mem_centerIdx hab hp hq)).2.2
  have hLa : 0 < a / ca :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hca) (Nat.pos_of_dvd_of_pos hca (Nat.pos_of_ne_zero ha0))
  have hLb : 0 < b / cb :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hcb) (Nat.pos_of_dvd_of_pos hcb (Nat.pos_of_ne_zero hb0))
  have hda0 : 0 < da := Nat.pos_of_dvd_of_pos hda hLa
  have hdb0 : 0 < db := Nat.pos_of_dvd_of_pos hdb hLb
  have hcda : ca * da ∣ a := Nat.mul_dvd_of_dvd_div hca hda
  have hcdb : cb * db ∣ b := Nat.mul_dvd_of_dvd_div hcb hdb
  have hiff := inLayer_mul_iff (n := x.val) hab hcda hcdb hda0 hdb0
  rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply]
  by_cases hx : InLayer (ca * cb) (da * db) x.val
  · have h1 : InLayer ca da (ZMod.chineseRemainder hab x).1.val := by
      rw [crt_fst_val]; exact (hiff.mp hx).1
    have h2 : InLayer cb db (ZMod.chineseRemainder hab x).2.val := by
      rw [crt_snd_val]; exact (hiff.mp hx).2
    have hxd : da * db ∣ x.val := ((inLayer_iff_dvd (Nat.mul_pos hda0 hdb0)).mp hx).1
    rw [twistFn_apply _ _ _ _ hdI hx, layerInd_apply_of_inLayer _ _ _ hx, twistFn_apply _ _ _ _ hdaI h1,
      layerInd_apply_of_inLayer _ _ _ h1, twistFn_apply _ _ _ _ hdbI h2, layerInd_apply_of_inLayer _ _ _ h2,
      mul_one, mul_one, mul_one, ← charMul_inv, ← charMul_mul, charMul_apply,
      ZMod.cast_natCast (dvd_mul_right ca cb), ZMod.cast_natCast (dvd_mul_left cb ca),
      crt_fst_div_cast hab (dvd_trans (dvd_mul_left da ca) hcda)
        (Nat.dvd_div_of_mul_dvd (by rw [mul_comm]; exact hcda)) hdb0 hxd,
      crt_snd_div_cast hab (dvd_trans (dvd_mul_left db cb) hcdb)
        (Nat.dvd_div_of_mul_dvd (by rw [mul_comm]; exact hcdb)) hda0 hxd,
      map_mul (χa' * χa⁻¹), map_mul (χb' * χb⁻¹)]
    ring
  · rw [layerInd_apply_of_not_inLayer _ _ _ hx, mul_zero, mul_zero]
    by_cases h1 : InLayer ca da (ZMod.chineseRemainder hab x).1.val
    · have h2 : ¬ InLayer cb db (ZMod.chineseRemainder hab x).2.val := by
        rw [crt_snd_val]
        rw [crt_fst_val] at h1
        exact fun h2 => hx (hiff.mpr ⟨h1, h2⟩)
      rw [layerInd_apply_of_not_inLayer _ _ _ h2, mul_zero, mul_zero]
    · rw [layerInd_apply_of_not_inLayer _ _ _ h1, mul_zero, zero_mul]

/-- **1b.** r·F(x) = G_a(x mod a)·G_b(x mod b) なら r·C(F·) = L(G_a·)·R(G_b·)（関数を掛ける作用素）。 -/
theorem smul_crtConj_mulLeft {a b : ℕ} (hab : Nat.Coprime a b) (r : ℂ) (F : ZMod (a * b) → ℂ) (Ga : ZMod a → ℂ)
    (Gb : ZMod b → ℂ)
    (h : ∀ x, r * F x = Ga (ZMod.chineseRemainder hab x).1 * Gb (ZMod.chineseRemainder hab x).2) :
    r • crtConj hab (LinearMap.mulLeft ℂ F) =
      leftOp b (LinearMap.mulLeft ℂ Ga) * rightOp a (LinearMap.mulLeft ℂ Gb) := by
  apply LinearMap.ext
  intro F'
  funext p
  show r * (F ((ZMod.chineseRemainder hab).symm p) *
      F' (ZMod.chineseRemainder hab ((ZMod.chineseRemainder hab).symm p))) = Ga p.1 * (Gb p.2 * F' (p.1, p.2))
  rw [← mul_assoc, h, RingEquiv.apply_symm_apply, mul_assoc]

/-- **1c.** λ·C(Θ^{ab}ι^{ab}·) = L(Θ^aι^a·)·R(Θ^bι^b·)（1a と 1b）。 -/
theorem smul_crtConj_twistLayer {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (χa χa' : DirichletCharacter ℂ ca) (χb χb' : DirichletCharacter ℂ cb) :
    ((χa' * χa⁻¹) (db : ZMod ca) * (χb' * χb⁻¹) (da : ZMod cb)) •
        crtConj hab (LinearMap.mulLeft ℂ
          (twistFn (a * b) (ca * cb) (charMul χa χb) (charMul χa' χb') * layerInd (a * b) (ca * cb) (da * db))) =
      leftOp b (LinearMap.mulLeft ℂ (twistFn a ca χa χa' * layerInd a ca da)) *
        rightOp a (LinearMap.mulLeft ℂ (twistFn b cb χb χb' * layerInd b cb db)) :=
  smul_crtConj_mulLeft hab _ _ _ _ (twist_mul_layerInd_crt hab hp hq χa χa' χb χb')

/-! ### 2. 行列単位の分解 -/

/-- **2a.** E^d_{χ→χ′} = (Θ_{χ→χ′}ι_d·)·P_χ（Part 223 の matUnit の定義）。 -/
theorem matUnit_eq_mul (N c d : ℕ) [NeZero N] [NeZero c] (χ χ' : DirichletCharacter ℂ c) :
    matUnit N c d χ χ' = LinearMap.mulLeft ℂ (twistFn N c χ χ' * layerInd N c d) * blockProjL N c χ := rfl

/-- **2b. 非対角の行列単位の分解** λ·C(E^{d_a d_b}_{χ_a⊠χ_b → χ′_a⊠χ′_b}) = L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})（χ_a, χ_b は原始的。1b・1a と Part 232 の crtConj_blockProjL）。 -/
theorem smul_crtConj_matUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    (χa' : DirichletCharacter ℂ ca) (χb' : DirichletCharacter ℂ cb) :
    ((χa' * χa⁻¹) (db : ZMod ca) * (χb' * χb⁻¹) (da : ZMod cb)) •
        crtConj hab (matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa' χb')) =
      leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb') := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  rw [matUnit_eq_mul, matUnit_eq_mul, matUnit_eq_mul, map_mul, ← smul_mul_assoc,
    smul_crtConj_mulLeft hab _ _ _ _ (twist_mul_layerInd_crt hab hp hq χa χa' χb χb'),
    crtConj_blockProjL hab hca hcb hχa hχb, leftOp_mul, rightOp_mul,
    mul_assoc, ← mul_assoc (rightOp a _), ← (leftOp_commute_rightOp _ _).eq, mul_assoc, mul_assoc]

/-- **2c.** C(E^{d_a d_b}_{χ_a⊠χ_b → χ′_a⊠χ′_b}) = λ⁻¹·L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})（2b と 0e）。 -/
theorem crtConj_matUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    (χa' : DirichletCharacter ℂ ca) (χb' : DirichletCharacter ℂ cb) :
    crtConj hab (matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa' χb')) =
      ((χa' * χa⁻¹) (db : ZMod ca) * (χb' * χb⁻¹) (da : ZMod cb))⁻¹ •
        (leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb')) := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  rw [← smul_crtConj_matUnit hab hp hq hχa hχb χa' χb',
    inv_smul_smul₀ (phase_ne_zero hab hca hcb (Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca))
      (Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)) _ _)]

/-! ### 3. ゲージ -/

/-- ゲージ g(χ_a, χ_b) = χ_a(d_b)·χ_b(d_a)（層 (d_a, d_b) ごとの、指標の組の関数）。 -/
noncomputable def gaugeFactor {ca cb : ℕ} (da db : ℕ) (χa : DirichletCharacter ℂ ca) (χb : DirichletCharacter ℂ cb) :
    ℂ :=
  χa (db : ZMod ca) * χb (da : ZMod cb)

/-- **3a.** g(χ_a, χ_b) ≠ 0（0e）。 -/
theorem gaugeFactor_ne_zero {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ} (hca : ca ∣ a) (hcb : cb ∣ b)
    (hda : da ∣ a) (hdb : db ∣ b) (χa : DirichletCharacter ℂ ca) (χb : DirichletCharacter ℂ cb) :
    gaugeFactor da db χa χb ≠ 0 :=
  phase_ne_zero hab hca hcb hda hdb χa χb

/-- **3b.** 位相はゲージの比：ψ_a(d_b)·ψ_b(d_a) = g(χ′_a, χ′_b)/g(χ_a, χ_b)（単数 u で χ(u)·χ⁻¹(u) = 1）。 -/
theorem phase_eq_div {a b : ℕ} (hab : Nat.Coprime a b) {ca da cb db : ℕ} (hca : ca ∣ a) (hcb : cb ∣ b)
    (hda : da ∣ a) (hdb : db ∣ b) (χa χa' : DirichletCharacter ℂ ca) (χb χb' : DirichletCharacter ℂ cb) :
    (χa' * χa⁻¹) (db : ZMod ca) * (χb' * χb⁻¹) (da : ZMod cb) =
      gaugeFactor da db χa' χb' / gaugeFactor da db χa χb := by
  have hua := isUnit_cast_of_dvd hab hca hdb
  have hub := isUnit_cast_of_dvd hab.symm hcb hda
  have h1 : χa (db : ZMod ca) * χa⁻¹ (db : ZMod ca) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hua]
  have h2 : χb (da : ZMod cb) * χb⁻¹ (da : ZMod cb) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hub]
  rw [eq_div_iff (gaugeFactor_ne_zero hab hca hcb hda hdb χa χb), gaugeFactor, gaugeFactor, MulChar.mul_apply,
    MulChar.mul_apply]
  linear_combination (χa' (db : ZMod ca) * χb' (da : ZMod cb) * (χb (da : ZMod cb) * χb⁻¹ (da : ZMod cb))) * h1 +
    (χa' (db : ZMod ca) * χb' (da : ZMod cb)) * h2

/-- **3c.** ゲージの形：g(χ′)·C(E^{d_a d_b}_{χ→χ′}) = g(χ)·L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})（2b と 3b）。 -/
theorem gauge_crtConj_matUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    (χa' : DirichletCharacter ℂ ca) (χb' : DirichletCharacter ℂ cb) :
    gaugeFactor da db χa' χb' • crtConj hab (matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa' χb')) =
      gaugeFactor da db χa χb • (leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb')) := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  have hda' : da ∣ a := Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca)
  have hdb' : db ∣ b := Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)
  rw [← smul_crtConj_matUnit hab hp hq hχa hχb χa' χb', smul_smul, phase_eq_div hab hca hcb hda' hdb',
    mul_div_cancel₀ _ (gaugeFactor_ne_zero hab hca hcb hda' hdb' χa χb)]

/-- **3d.** 法 c_a c_b の原始指標 χ, χ′ はすべて χ = χ_a ⊠ χ_b、χ′ = χ′_a ⊠ χ′_b（原始的）と書け、3c が成り立つ（Part 232 の exists_charMul_eq）。 -/
theorem exists_gauge_crtConj_matUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)]
    [Fintype (BlockIdx b)] (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χ χ' : DirichletCharacter ℂ (ca * cb)} (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive) :
    ∃ χa χa' : DirichletCharacter ℂ ca, ∃ χb χb' : DirichletCharacter ℂ cb,
      χa.IsPrimitive ∧ χa'.IsPrimitive ∧ χb.IsPrimitive ∧ χb'.IsPrimitive ∧
        charMul χa χb = χ ∧ charMul χa' χb' = χ' ∧
          gaugeFactor da db χa' χb' • crtConj hab (matUnit (a * b) (ca * cb) (da * db) χ χ') =
            gaugeFactor da db χa χb • (leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb')) := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  obtain ⟨χa, χb, ha, hb, rfl⟩ := exists_charMul_eq hcop hχ
  obtain ⟨χa', χb', ha', hb', rfl⟩ := exists_charMul_eq hcop hχ'
  exact ⟨χa, χa', χb, χb', ha, ha', hb, hb', rfl, rfl, gauge_crtConj_matUnit hab hp hq ha hb χa' χb'⟩

/-- ゲージで直した行列単位 Ẽ^{d_a d_b}_{χ→χ′} = (g(χ′)/g(χ))·E^{d_a d_b}_{χ_a⊠χ_b → χ′_a⊠χ′_b}。 -/
noncomputable def gaugeUnit (a b ca da cb db : ℕ) [NeZero a] [NeZero b] [NeZero ca] [NeZero cb]
    (χa χa' : DirichletCharacter ℂ ca) (χb χb' : DirichletCharacter ℂ cb) : Module.End ℂ (ZMod (a * b) → ℂ) :=
  (gaugeFactor da db χa' χb' / gaugeFactor da db χa χb) •
    matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa' χb')

/-- **3e.** C(Ẽ_{χ→χ′}) = L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})（位相なしで分かれる）。 -/
theorem crtConj_gaugeUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    (χa' : DirichletCharacter ℂ ca) (χb' : DirichletCharacter ℂ cb) :
    crtConj hab (gaugeUnit a b ca da cb db χa χa' χb χb') =
      leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb') := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  have hda' : da ∣ a := Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca)
  have hdb' : db ∣ b := Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)
  rw [gaugeUnit, map_smul, div_eq_inv_mul, mul_smul, gauge_crtConj_matUnit hab hp hq hχa hχb χa' χb',
    inv_smul_smul₀ (gaugeFactor_ne_zero hab hca hcb hda' hdb' χa χb)]

/-- **3f.** C⁻¹(L(E^{d_a}_{χ_a→χ′_a})·R(E^{d_b}_{χ_b→χ′_b})) = Ẽ_{χ→χ′}（行列単位の積の引き戻しはゲージで直した行列単位）。 -/
theorem crtConj_symm_tensor_matUnit {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)]
    [Fintype (BlockIdx b)] (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    (χa' : DirichletCharacter ℂ ca) (χb' : DirichletCharacter ℂ cb) :
    (crtConj hab).symm (leftOp b (matUnit a ca da χa χa') * rightOp a (matUnit b cb db χb χb')) =
      gaugeUnit a b ca da cb db χa χa' χb χb' := by
  rw [← crtConj_gaugeUnit hab hp hq hχa hχb χa' χb', AlgEquiv.symm_apply_apply]

/-- **3g.** Ẽ_{χ→χ} = E_{χ→χ}（対角では直す必要がない：Part 232 の crtConj_matUnit_self と合う）。 -/
theorem gaugeUnit_self {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca]
    [NeZero cb] (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (χa : DirichletCharacter ℂ ca) (χb : DirichletCharacter ℂ cb) :
    gaugeUnit a b ca da cb db χa χa χb χb = matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa χb) := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  rw [gaugeUnit, div_self (gaugeFactor_ne_zero hab hca hcb (Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca))
    (Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)) χa χb), one_smul]

/-- **3h.** 積の規則 Ẽ_{χ′→χ″}·Ẽ_{χ→χ′} = Ẽ_{χ→χ″}（χ′ は原始的。Part 223 の matUnit_mul_self と、ゲージの比の打ち消し）。 -/
theorem gaugeUnit_mul {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca]
    [NeZero cb] (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (χa χa' χa'' : DirichletCharacter ℂ ca) (χb χb' χb'' : DirichletCharacter ℂ cb)
    (hχa' : χa'.IsPrimitive) (hχb' : χb'.IsPrimitive) :
    gaugeUnit a b ca da cb db χa' χa'' χb' χb'' * gaugeUnit a b ca da cb db χa χa' χb χb' =
      gaugeUnit a b ca da cb db χa χa'' χb χb'' := by
  obtain ⟨hca, -, -, hda, -⟩ := (mem_centerIdx_iff_dvd a ca da).mp hp
  obtain ⟨hcb, -, -, hdb, -⟩ := (mem_centerIdx_iff_dvd b cb db).mp hq
  have hda' : da ∣ a := Nat.dvd_trans hda (Nat.div_dvd_of_dvd hca)
  have hdb' : db ∣ b := Nat.dvd_trans hdb (Nat.div_dvd_of_dvd hcb)
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  obtain ⟨hcN, -, -, -, hrad⟩ := (mem_centerIdx_iff_dvd (a * b) (ca * cb) (da * db)).mp (idxMul_mem_centerIdx hab hp hq)
  unfold gaugeUnit
  rw [smul_mul_smul_comm, matUnit_mul_self (a * b) (ca * cb) (da * db) hcN hrad _ _ _
    (isPrimitive_charMul hcop hχa' hχb'), div_mul_div_cancel₀ (gaugeFactor_ne_zero hab hca hcb hda' hdb' χa' χb')]

/-- **3i.** (ψ_a, ψ_b) ≠ (χ′_a, χ′_b) なら Ẽ_{ψ→χ″}·Ẽ_{χ→χ′} = 0（Part 223 の matUnit_mul_of_ne_char と Part 232 の charMul_injective）。 -/
theorem gaugeUnit_mul_of_ne {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    [NeZero ca] [NeZero cb] (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a)
    (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    (ψa χa'' χa χa' : DirichletCharacter ℂ ca) (ψb χb'' χb χb' : DirichletCharacter ℂ cb)
    (hψa : ψa.IsPrimitive) (hψb : ψb.IsPrimitive) (hχa' : χa'.IsPrimitive) (hχb' : χb'.IsPrimitive)
    (h : ¬ (ψa = χa' ∧ ψb = χb')) :
    gaugeUnit a b ca da cb db ψa χa'' ψb χb'' * gaugeUnit a b ca da cb db χa χa' χb χb' = 0 := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  obtain ⟨hcN, -, -, -, hrad⟩ := (mem_centerIdx_iff_dvd (a * b) (ca * cb) (da * db)).mp (idxMul_mem_centerIdx hab hp hq)
  unfold gaugeUnit
  rw [smul_mul_smul_comm, matUnit_mul_of_ne_char (a * b) (ca * cb) hcN (da * db) (da * db) hrad _ _ _ _
    (isPrimitive_charMul hcop hψa hψb) (isPrimitive_charMul hcop hχa' hχb') (fun e => h (charMul_injective hcop e)),
    smul_zero]

end PAG.Part237

#print axioms PAG.Part237.mod_div_eq_div_mod
#print axioms PAG.Part237.crt_fst_div_cast
#print axioms PAG.Part237.crt_snd_div_cast
#print axioms PAG.Part237.isUnit_cast_of_dvd
#print axioms PAG.Part237.phase_ne_zero
#print axioms PAG.Part237.twist_mul_layerInd_crt
#print axioms PAG.Part237.smul_crtConj_mulLeft
#print axioms PAG.Part237.smul_crtConj_twistLayer
#print axioms PAG.Part237.matUnit_eq_mul
#print axioms PAG.Part237.smul_crtConj_matUnit
#print axioms PAG.Part237.crtConj_matUnit
#print axioms PAG.Part237.gaugeFactor
#print axioms PAG.Part237.gaugeFactor_ne_zero
#print axioms PAG.Part237.phase_eq_div
#print axioms PAG.Part237.gauge_crtConj_matUnit
#print axioms PAG.Part237.exists_gauge_crtConj_matUnit
#print axioms PAG.Part237.gaugeUnit
#print axioms PAG.Part237.crtConj_gaugeUnit
#print axioms PAG.Part237.crtConj_symm_tensor_matUnit
#print axioms PAG.Part237.gaugeUnit_self
#print axioms PAG.Part237.gaugeUnit_mul
#print axioms PAG.Part237.gaugeUnit_mul_of_ne
