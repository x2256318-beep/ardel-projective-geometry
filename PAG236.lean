/-
  PAG 2.0 Part 232（2026-10-30）— 原始指標の中国剰余定理と、ブロックの射影・中心の極小べき等元の番号どおりの分解
  χ₁ ⊠ χ₂ = 法 mn の指標 x ↦ χ₁(x mod m)·χ₂(x mod n)（def charMul、Mathlib の changeLevel で法 mn に持ち上げた積）、
  ブロック V_{c,χ}（Part 215 の blockSpan）と射影 P_{c,χ}（Part 214 の blockProjL）、層の部分 W_{c,χ}(d)（Part 216 の layerPart）、
  中心の極小べき等元 z_{(c,d)}（Part 222 の centralElt）、行列単位 E^d_{χ→χ′}（Part 223 の matUnit）、C・L・R（Part 228）
  0. 指標の積：値は χ₁(x mod m)·χ₂(x mod n)（単数でない x も）、⊠ は積と逆を保つ。gcd(m, n) = 1 なら原始的な χ₁, χ₂ の積は
     原始的（導手は m でも n でも割り切れる：Mathlib の conductor・FactorsThrough）、(χ₁, χ₂) ↦ χ₁ ⊠ χ₂ は単射
     （Mathlib の factorsThrough_gcd）、原始指標の数の乗法性（Part 226 の primCount_mul）と合わせて
     Prim(m) × Prim(n) ≅ Prim(mn)（def primEquiv）。持ち上げの値は (χ_a ⊠ χ_b)_{ab}(u) = (χ_a)_a(u mod a)·(χ_b)_b(u mod b)
  1. 純テンソル f ⊗ g（def tens）：L(S)(f ⊗ g) = Sf ⊗ g、R(T)(f ⊗ g) = f ⊗ Tg。作用素は純テンソルでの値で決まり、
     ブロックの元どうしの純テンソルでの値で決まる（Σ_b P_b = 1）
  2. 中国剰余定理で戻した積 x ↦ f(x mod a)·g(x mod b)（def crtProd）：U_u は成分ごとに作用し、f ∈ V^a_{c_a,χ_a}、
     g ∈ V^b_{c_b,χ_b} なら積は V^{ab}_{c_a c_b, χ_a⊠χ_b} に入る（ブロックは U_u の固有空間：Part 214）。W(d) も同様
  3. 番号どおりの分解：C(P_{c_a c_b, χ_a⊠χ_b}) = L(P_{c_a,χ_a})·R(P_{c_b,χ_b})（法 c_a c_b の原始指標はすべてこの形）、
     C(z_{(c_a c_b, d_a d_b)}) = L(z_{(c_a,d_a)})·R(z_{(c_b,d_b)})、S(ab) の (c, d) では
     C(z_{(c,d)}) = L(z_{(gcd(c,a), gcd(d,a))})·R(z_{(gcd(c,b), gcd(d,b))})。W(d) への射影 ι_d·P_χ と
     対角の行列単位 E^d_{χ→χ} = ι_d·P_χ も C(E^{d_a d_b}_{χ→χ}) = L(E^{d_a}_{χ_a→χ_a})·R(E^{d_b}_{χ_b→χ_b})（χ = χ_a⊠χ_b）
-/
import PAG235

namespace PAG.Part236

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part231 PAG.Part232 PAG.Part233 PAG.Part234
  PAG.Part235
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 指標の積 -/

/-- 法 m の指標 χ₁ と法 n の指標 χ₂ の積 χ₁ ⊠ χ₂（両方を法 mn に持ち上げて掛けた法 mn の指標）。 -/
noncomputable def charMul {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    DirichletCharacter ℂ (m * n) :=
  DirichletCharacter.changeLevel (dvd_mul_right m n) χ₁ * DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂

/-- **0a.** mn ∣ N なら χ₁ ⊠ χ₂ の法 N への持ち上げは、χ₁・χ₂ の法 N への持ち上げの積。 -/
theorem changeLevel_charMul {m n N : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n)
    (h : m * n ∣ N) :
    DirichletCharacter.changeLevel h (charMul χ₁ χ₂) =
      DirichletCharacter.changeLevel ((dvd_mul_right m n).trans h) χ₁ *
        DirichletCharacter.changeLevel ((dvd_mul_left n m).trans h) χ₂ := by
  rw [charMul, map_mul, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]

/-- **0b.** 単数 u での値：(χ₁ ⊠ χ₂)(u) = χ₁(u mod m)·χ₂(u mod n)。 -/
theorem charMul_apply_unit {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n)
    (u : (ZMod (m * n))ˣ) :
    charMul χ₁ χ₂ (u : ZMod (m * n)) =
      χ₁ (ZMod.cast (u : ZMod (m * n))) * χ₂ (ZMod.cast (u : ZMod (m * n))) := by
  rw [charMul, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]

/-- **0c.** すべての x での値：(χ₁ ⊠ χ₂)(x) = χ₁(x mod m)·χ₂(x mod n)（x が単数でなければ x mod m か x mod n が単数でなく、両辺 0）。 -/
theorem charMul_apply {m n : ℕ} [NeZero m] [NeZero n] (χ₁ : DirichletCharacter ℂ m)
    (χ₂ : DirichletCharacter ℂ n) (x : ZMod (m * n)) :
    charMul χ₁ χ₂ x = χ₁ (ZMod.cast x) * χ₂ (ZMod.cast x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact charMul_apply_unit χ₁ χ₂ u
  · rw [MulChar.map_nonunit _ hx, ZMod.cast_eq_val, ZMod.cast_eq_val]
    by_cases h1 : x.val.Coprime m
    · have h2 : ¬ x.val.Coprime n := fun h2 =>
        hx (by rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]; exact Nat.Coprime.mul_right h1 h2)
      rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul]

/-- **0d.** ⊠ は積を保つ：(χ₁ψ₁) ⊠ (χ₂ψ₂) = (χ₁ ⊠ χ₂)(ψ₁ ⊠ ψ₂)。 -/
theorem charMul_mul {m n : ℕ} (χ₁ ψ₁ : DirichletCharacter ℂ m) (χ₂ ψ₂ : DirichletCharacter ℂ n) :
    charMul (χ₁ * ψ₁) (χ₂ * ψ₂) = charMul χ₁ χ₂ * charMul ψ₁ ψ₂ := by
  simp only [charMul, map_mul]
  exact mul_mul_mul_comm _ _ _ _

/-- **0e.** χ₁⁻¹ ⊠ χ₂⁻¹ = (χ₁ ⊠ χ₂)⁻¹。 -/
theorem charMul_inv {m n : ℕ} (χ₁ : DirichletCharacter ℂ m) (χ₂ : DirichletCharacter ℂ n) :
    charMul χ₁⁻¹ χ₂⁻¹ = (charMul χ₁ χ₂)⁻¹ := by
  simp only [charMul, map_inv, mul_inv]

/-- **0f.** 法 N の指標 χ が ψ₁（法 k、原始的）と ψ₂（法 l）の持ち上げの積で gcd(k, l) = 1 なら k ∣ χ の導手 f（ψ₁ の持ち上げ = χ·ψ₂⁻¹ は法 lcm(f, l) を経由するので k ∣ lcm(f, l) ∣ f·l）。 -/
theorem dvd_conductor_of_eq_mul {N k l : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hk : k ∣ N) (hl : l ∣ N)
    (ψ₁ : DirichletCharacter ℂ k) (ψ₂ : DirichletCharacter ℂ l) (hψ₁ : ψ₁.IsPrimitive) (hkl : Nat.Coprime k l)
    (h : χ = DirichletCharacter.changeLevel hk ψ₁ * DirichletCharacter.changeLevel hl ψ₂) :
    k ∣ χ.conductor := by
  subst h
  set χ := DirichletCharacter.changeLevel hk ψ₁ * DirichletCharacter.changeLevel hl ψ₂ with hχ
  have hd : χ.conductor ∣ N := χ.conductor_dvd_level
  have hL : Nat.lcm χ.conductor l ∣ N := Nat.lcm_dvd hd hl
  have hfac : (DirichletCharacter.changeLevel hk ψ₁).FactorsThrough (Nat.lcm χ.conductor l) := by
    refine ⟨hL, DirichletCharacter.changeLevel (Nat.dvd_lcm_left χ.conductor l) χ.primitiveCharacter *
      (DirichletCharacter.changeLevel (Nat.dvd_lcm_right χ.conductor l) ψ₂)⁻¹, ?_⟩
    rw [map_mul, map_inv, ← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans,
      DirichletCharacter.changeLevel_primitiveCharacter]
    exact (mul_inv_cancel_right _ _).symm
  have h1 : (DirichletCharacter.changeLevel hk ψ₁).conductor ∣ Nat.lcm χ.conductor l :=
    (DirichletCharacter.mem_conductorSet_iff_conductor_dvd _ hL).mp hfac
  rw [DirichletCharacter.conductor_changeLevel, (DirichletCharacter.isPrimitive_def ψ₁).mp hψ₁] at h1
  exact hkl.dvd_of_dvd_mul_right (h1.trans (Nat.lcm_dvd (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _)))

/-- **0g. gcd(m, n) = 1 なら原始指標の積は原始的**：χ₁ ⊠ χ₂ の導手は m でも n でも割り切れ（0f）、mn に等しい。 -/
theorem isPrimitive_charMul {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ : DirichletCharacter ℂ m} {χ₂ : DirichletCharacter ℂ n} (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive) :
    (charMul χ₁ χ₂).IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hm : m ∣ (charMul χ₁ χ₂).conductor :=
    dvd_conductor_of_eq_mul _ (dvd_mul_right m n) (dvd_mul_left n m) χ₁ χ₂ h₁ hmn rfl
  have hn : n ∣ (charMul χ₁ χ₂).conductor :=
    dvd_conductor_of_eq_mul _ (dvd_mul_left n m) (dvd_mul_right m n) χ₂ χ₁ h₂ hmn.symm (mul_comm _ _)
  exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_level _) (hmn.mul_dvd_of_dvd_of_dvd hm hn)

/-- **0h.** gcd(m, n) = 1 なら χ₁ ⊠ χ₂ = χ₁′ ⊠ χ₂′ ⇒ χ₁ = χ₁′、χ₂ = χ₂′（χ₁/χ₁′ と χ₂′/χ₂ の持ち上げが一致し、Mathlib の factorsThrough_gcd で χ₁/χ₁′ は法 gcd(m, n) = 1 を経由する）。 -/
theorem charMul_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ₁ χ₁' : DirichletCharacter ℂ m} {χ₂ χ₂' : DirichletCharacter ℂ n}
    (h : charMul χ₁ χ₂ = charMul χ₁' χ₂') : χ₁ = χ₁' ∧ χ₂ = χ₂' := by
  have e : DirichletCharacter.changeLevel (m.dvd_mul_right n) (χ₁ / χ₁') =
      DirichletCharacter.changeLevel (n.dvd_mul_left m) (χ₂' / χ₂) := by
    rw [map_div, map_div, div_eq_div_iff_mul_eq_mul, mul_comm (DirichletCharacter.changeLevel _ χ₂')]
    exact h
  have hf := DirichletCharacter.factorsThrough_gcd (χ₁ / χ₁') (χ₂' / χ₂) e
  rw [Nat.Coprime.gcd_eq_one hmn, DirichletCharacter.factorsThrough_one_iff, div_eq_one] at hf
  subst hf
  refine ⟨rfl, ?_⟩
  have h2 : DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂ =
      DirichletCharacter.changeLevel (dvd_mul_left n m) χ₂' := mul_left_cancel h
  exact DirichletCharacter.changeLevel_injective _ h2

/-- 原始指標の組 (χ₁, χ₂) ↦ χ₁ ⊠ χ₂（Part 223 の Prim）。 -/
noncomputable def primMul {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) (p : Prim m × Prim n) :
    Prim (m * n) :=
  ⟨charMul p.1.1 p.2.1, isPrimitive_charMul hmn p.1.2 p.2.2⟩

/-- **0i.** primMul は単射（0h）。 -/
theorem primMul_injective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Function.Injective (primMul hmn) := by
  rintro ⟨⟨χ₁, h₁⟩, ⟨χ₂, h₂⟩⟩ ⟨⟨χ₁', h₁'⟩, ⟨χ₂', h₂'⟩⟩ e
  obtain ⟨rfl, rfl⟩ := charMul_injective hmn (congrArg Subtype.val e)
  rfl

/-- **0j.** primMul は全単射（単射と #Prim(mn) = #Prim(m)·#Prim(n)：Part 226 の primCount_mul）。 -/
theorem primMul_bijective {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Function.Bijective (primMul hmn) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨primMul_injective hmn, ?_⟩
  have h := primCount_mul hmn
  simp only [primCount, Nat.card_eq_fintype_card] at h
  rw [Fintype.card_prod, h]

/-- **原始指標の中国剰余定理** Prim(m) × Prim(n) ≅ Prim(mn)（gcd(m, n) = 1）。 -/
noncomputable def primEquiv {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n) :
    Prim m × Prim n ≃ Prim (m * n) :=
  Equiv.ofBijective (primMul hmn) (primMul_bijective hmn)

/-- **0k.** gcd(m, n) = 1 なら法 mn の原始指標はすべて χ₁ ⊠ χ₂（χ₁, χ₂ は原始的）の形（0j）。 -/
theorem exists_charMul_eq {m n : ℕ} [NeZero m] [NeZero n] (hmn : Nat.Coprime m n)
    {χ : DirichletCharacter ℂ (m * n)} (hχ : χ.IsPrimitive) :
    ∃ χ₁ : DirichletCharacter ℂ m, ∃ χ₂ : DirichletCharacter ℂ n,
      χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧ charMul χ₁ χ₂ = χ := by
  obtain ⟨⟨⟨χ₁, h₁⟩, ⟨χ₂, h₂⟩⟩, e⟩ := (primMul_bijective hmn).2 ⟨χ, hχ⟩
  exact ⟨χ₁, χ₂, h₁, h₂, congrArg Subtype.val e⟩

/-- **0l.** c ∣ a なら (x mod a) mod c = x mod c。 -/
theorem cast_crt_fst {a b c : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hc : c ∣ a) (x : ZMod (a * b)) :
    (ZMod.cast (ZMod.chineseRemainder hab x).1 : ZMod c) = ZMod.cast x := by
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val, crt_fst_val]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq x.val a).of_dvd hc)

/-- **0m.** c ∣ b なら (x mod b) mod c = x mod c。 -/
theorem cast_crt_snd {a b c : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hc : c ∣ b) (x : ZMod (a * b)) :
    (ZMod.cast (ZMod.chineseRemainder hab x).2 : ZMod c) = ZMod.cast x := by
  rw [ZMod.cast_eq_val, ZMod.cast_eq_val, crt_snd_val]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr ((Nat.mod_modEq x.val b).of_dvd hc)

/-- **0n.** 持ち上げ：(χ_a ⊠ χ_b)_{ab}(u) = (χ_a)_a(u mod a)·(χ_b)_b(u mod b)（c_a ∣ a、c_b ∣ b。Part 206 の liftc）。 -/
theorem liftc_charMul {a b ca cb : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) (hca : ca ∣ a) (hcb : cb ∣ b)
    (χa : DirichletCharacter ℂ ca) (χb : DirichletCharacter ℂ cb) (u : (ZMod (a * b))ˣ) :
    liftc (charMul χa χb) (a * b) (u : ZMod (a * b)) =
      liftc χa a (unitFst hab u : ZMod a) * liftc χb b (unitSnd hab u : ZMod b) := by
  rw [liftc_of_dvd _ (mul_dvd_mul hca hcb), liftc_of_dvd _ hca, liftc_of_dvd _ hcb, changeLevel_charMul,
    MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, unitFst_val,
    unitSnd_val, cast_crt_fst hab hca, cast_crt_snd hab hcb]

/-! ### 1. 純テンソル -/

/-- 純テンソル (f ⊗ g)(x, y) = f(x)·g(y)（ℂ^{ℤ/a × ℤ/b} の元）。 -/
def tens {a b : ℕ} (f : ZMod a → ℂ) (g : ZMod b → ℂ) : ZMod a × ZMod b → ℂ := fun p => f p.1 * g p.2

/-- **1a.** f ⊗ g の値。 -/
theorem tens_apply {a b : ℕ} (f : ZMod a → ℂ) (g : ZMod b → ℂ) (p : ZMod a × ZMod b) :
    tens f g p = f p.1 * g p.2 := rfl

/-- **1b.** 0 ⊗ g = 0。 -/
theorem tens_zero_left {a b : ℕ} (g : ZMod b → ℂ) : tens (0 : ZMod a → ℂ) g = 0 :=
  funext fun _ => zero_mul _

/-- **1c.** f ⊗ 0 = 0。 -/
theorem tens_zero_right {a b : ℕ} (f : ZMod a → ℂ) : tens f (0 : ZMod b → ℂ) = 0 :=
  funext fun _ => mul_zero _

/-- **1d.** (Σ f_i) ⊗ g = Σ f_i ⊗ g。 -/
theorem tens_sum_left {a b : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ZMod a → ℂ) (g : ZMod b → ℂ) :
    tens (∑ i ∈ s, f i) g = ∑ i ∈ s, tens (f i) g := by
  funext p
  simp only [tens, Finset.sum_apply, Finset.sum_mul]

/-- **1e.** f ⊗ (Σ g_i) = Σ f ⊗ g_i。 -/
theorem tens_sum_right {a b : ℕ} {ι : Type*} (s : Finset ι) (f : ZMod a → ℂ) (g : ι → ZMod b → ℂ) :
    tens f (∑ i ∈ s, g i) = ∑ i ∈ s, tens f (g i) := by
  funext p
  simp only [tens, Finset.sum_apply, Finset.mul_sum]

/-- **1f.** L(S)(f ⊗ g) = Sf ⊗ g。 -/
theorem leftOp_tens {a : ℕ} (b : ℕ) (S : Module.End ℂ (ZMod a → ℂ)) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    leftOp b S (tens f g) = tens (S f) g := by
  funext p
  show S (fun x => f x * g p.2) p.1 = S f p.1 * g p.2
  have e : (fun x => f x * g p.2) = g p.2 • f := funext fun x => mul_comm (f x) (g p.2)
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **1g.** R(T)(f ⊗ g) = f ⊗ Tg。 -/
theorem rightOp_tens (a : ℕ) {b : ℕ} (T : Module.End ℂ (ZMod b → ℂ)) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    rightOp a T (tens f g) = tens f (T g) := by
  funext p
  show T (fun y => f p.1 * g y) p.2 = f p.1 * T g p.2
  have e : (fun y => f p.1 * g y) = f p.1 • g := rfl
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul]

/-- **1h.** L(SS′) = L(S)L(S′)。 -/
theorem leftOp_mul {a : ℕ} (b : ℕ) (S S' : Module.End ℂ (ZMod a → ℂ)) :
    leftOp b (S * S') = leftOp b S * leftOp b S' :=
  map_mul (leftHom a b) S S'

/-- **1i.** R(TT′) = R(T)R(T′)。 -/
theorem rightOp_mul (a : ℕ) {b : ℕ} (T T' : Module.End ℂ (ZMod b → ℂ)) :
    rightOp a (T * T') = rightOp a T * rightOp a T' :=
  map_mul (rightHom a b) T T'

/-- **1j.** δ_{(x,y)} = δ_x ⊗ δ_y。 -/
theorem single_eq_tens {a b : ℕ} (p : ZMod a × ZMod b) :
    (Pi.single p 1 : ZMod a × ZMod b → ℂ) = tens (Pi.single p.1 1) (Pi.single p.2 1) := by
  funext q
  rw [tens_apply]
  by_cases h1 : q.1 = p.1
  · by_cases h2 : q.2 = p.2
    · have hq : q = p := Prod.ext h1 h2
      rw [hq, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, mul_one]
    · have hq : q ≠ p := fun e => h2 (congrArg Prod.snd e)
      rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne h2, mul_zero]
  · have hq : q ≠ p := fun e => h1 (congrArg Prod.fst e)
    rw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne h1, zero_mul]

/-- **1k.** 純テンソルでの値が等しい作用素は等しい（1j）。 -/
theorem ext_tens {a b : ℕ} [NeZero a] [NeZero b] {M₁ M₂ : Module.End ℂ (ZMod a × ZMod b → ℂ)}
    (h : ∀ (f : ZMod a → ℂ) (g : ZMod b → ℂ), M₁ (tens f g) = M₂ (tens f g)) : M₁ = M₂ := by
  apply LinearMap.pi_ext'
  intro p
  apply LinearMap.ext_ring
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.coe_single, single_eq_tens, h]

/-- **1l.** ブロックの元どうしの純テンソル f ⊗ g（f ∈ V^a_p、g ∈ V^b_q）での値が等しい作用素は等しい（Σ_p P_p f = f：Part 220 の sum_blockProj）。 -/
theorem ext_tens_block {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    {M₁ M₂ : Module.End ℂ (ZMod a × ZMod b → ℂ)}
    (h : ∀ (p : BlockIdx a) (q : BlockIdx b) (f : ZMod a → ℂ) (g : ZMod b → ℂ),
      f ∈ blockSpan a p.1 p.2.1 → g ∈ blockSpan b q.1 q.2.1 → M₁ (tens f g) = M₂ (tens f g)) :
    M₁ = M₂ := by
  refine ext_tens (fun f g => ?_)
  have e : tens f g = ∑ p : BlockIdx a, ∑ q : BlockIdx b,
      tens (blockProj a p.1 p.2.1 f) (blockProj b q.1 q.2.1 g) := by
    conv_lhs => rw [← sum_blockProj a f, ← sum_blockProj b g]
    rw [tens_sum_left]
    exact Finset.sum_congr rfl (fun p _ => tens_sum_right _ _ _)
  rw [e, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl (fun q _ => h p q _ _ (blockProj_mem_span a p.1 p.2.1 f) (blockProj_mem_span b q.1 q.2.1 g))

/-! ### 2. 中国剰余定理で戻した積 -/

/-- 中国剰余定理で戻した積 x ↦ f(x mod a)·g(x mod b)（= crtLin⁻¹(f ⊗ g)）。 -/
noncomputable def crtProd {a b : ℕ} (hab : Nat.Coprime a b) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    ZMod (a * b) → ℂ :=
  (crtLin hab).symm (tens f g)

/-- **2a.** crtProd の値。 -/
theorem crtProd_apply {a b : ℕ} (hab : Nat.Coprime a b) (f : ZMod a → ℂ) (g : ZMod b → ℂ) (x : ZMod (a * b)) :
    crtProd hab f g x = f (ZMod.chineseRemainder hab x).1 * g (ZMod.chineseRemainder hab x).2 := rfl

/-- **2b.** crtLin(crtProd f g) = f ⊗ g。 -/
theorem crtLin_crtProd {a b : ℕ} (hab : Nat.Coprime a b) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    crtLin hab (crtProd hab f g) = tens f g :=
  LinearEquiv.apply_symm_apply _ _

/-- **2c.** C(T)(f ⊗ g) = crtLin(T(crtProd f g))。 -/
theorem crtConj_apply_tens {a b : ℕ} (hab : Nat.Coprime a b) (T : Module.End ℂ (ZMod (a * b) → ℂ))
    (f : ZMod a → ℂ) (g : ZMod b → ℂ) : crtConj hab T (tens f g) = crtLin hab (T (crtProd hab f g)) := rfl

/-- **2d.** crtProd (r·f) (s·g) = rs·crtProd f g。 -/
theorem crtProd_smul_smul {a b : ℕ} (hab : Nat.Coprime a b) (r s : ℂ) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    crtProd hab (r • f) (s • g) = (r * s) • crtProd hab f g := by
  funext x
  simp only [crtProd_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **2e.** U_u(crtProd f g) = crtProd (U_{u mod a} f) (U_{u mod b} g)。 -/
theorem dil_crtProd {a b : ℕ} (hab : Nat.Coprime a b) (u : (ZMod (a * b))ˣ) (f : ZMod a → ℂ) (g : ZMod b → ℂ) :
    dil u (crtProd hab f g) = crtProd hab (dil (unitFst hab u) f) (dil (unitSnd hab u) g) := by
  funext x
  rw [dil_apply, crtProd_apply, crtProd_apply, dil_apply, dil_apply, map_mul]
  rfl

/-- **2f. ブロックの積**：f ∈ V^a_{c_a,χ_a}、g ∈ V^b_{c_b,χ_b}（原始的）なら crtProd f g ∈ V^{ab}_{c_a c_b, χ_a⊠χ_b}（ブロックは U_u の固有空間：Part 214 の mem_span_iff_dil。2e、0n、0g）。 -/
theorem crtProd_mem_blockSpan {a b ca cb : ℕ} [NeZero a] [NeZero b] [NeZero ca] [NeZero cb]
    (hab : Nat.Coprime a b) (hca : ca ∣ a) (hcb : cb ∣ b) {χa : DirichletCharacter ℂ ca}
    {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive) {f : ZMod a → ℂ}
    {g : ZMod b → ℂ} (hf : f ∈ blockSpan a ca χa) (hg : g ∈ blockSpan b cb χb) :
    crtProd hab f g ∈ blockSpan (a * b) (ca * cb) (charMul χa χb) := by
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  unfold blockSpan at hf hg ⊢
  rw [mem_span_iff_dil a ca hca χa hχa] at hf
  rw [mem_span_iff_dil b cb hcb χb hχb] at hg
  rw [mem_span_iff_dil (a * b) (ca * cb) (mul_dvd_mul hca hcb) _ (isPrimitive_charMul hcop hχa hχb)]
  intro u
  rw [dil_crtProd, hf, hg, crtProd_smul_smul, liftc_charMul hab hca hcb]

/-- **2g.** 層の部分も同様：f ∈ W^a_{c_a,χ_a}(d_a)、g ∈ W^b_{c_b,χ_b}(d_b) なら crtProd f g ∈ W^{ab}_{c_a c_b, χ_a⊠χ_b}(d_a d_b)（Part 231 の layerInd_crt）。 -/
theorem crtProd_mem_layerPart {a b : ℕ} [NeZero a] [NeZero b] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive)
    {f : ZMod a → ℂ} {g : ZMod b → ℂ} (hf : f ∈ layerPart a ca χa da) (hg : g ∈ layerPart b cb χb db) :
    crtProd hab f g ∈ layerPart (a * b) (ca * cb) (charMul χa χb) (da * db) := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  rw [mem_layerPart] at hf hg ⊢
  refine ⟨crtProd_mem_blockSpan hab hca hcb hχa hχb hf.1 hg.1, fun x hx => ?_⟩
  have e := layerInd_crt hab hp hq x
  unfold layerInd at e
  rw [ite_eq_right hx] at e
  rw [crtProd_apply]
  by_cases h1 : InLayer ca da (ZMod.chineseRemainder hab x).1.val
  · by_cases h2 : InLayer cb db (ZMod.chineseRemainder hab x).2.val
    · rw [ite_eq_left h1, ite_eq_left h2, one_mul] at e
      exact absurd e zero_ne_one
    · rw [hg.2 _ h2, mul_zero]
  · rw [hf.2 _ h1, zero_mul]

/-! ### 3. 番号どおりの分解 -/

open Classical in
/-- **3a.** f ∈ V_{c,χ} なら P_{c′,χ′} f = [(c, χ) = (c′, χ′)]·f（Part 215・220）。 -/
theorem blockProj_eq_ite {N c c' : ℕ} [NeZero N] [NeZero c] [NeZero c'] (hcN : c ∣ N) (hc'N : c' ∣ N)
    {χ : DirichletCharacter ℂ c} {χ' : DirichletCharacter ℂ c'} (hχ : χ.IsPrimitive) (hχ' : χ'.IsPrimitive)
    {f : ZMod N → ℂ} (hf : f ∈ blockSpan N c χ) :
    blockProj N c' χ' f = if (⟨c, χ⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨c', χ'⟩ then f else 0 := by
  by_cases h : (⟨c, χ⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨c', χ'⟩
  · rw [ite_eq_left h]
    cases h
    exact blockProj_of_mem N c hcN χ hχ hf
  · rw [ite_eq_right h]
    exact blockProj_eq_zero_of_mem N c c' hcN hc'N χ χ' hχ hχ' h hf

/-- **3b.** (c′_a c′_b, χ′_a ⊠ χ′_b) = (c_a c_b, χ_a ⊠ χ_b) ⇔ (c′_a, χ′_a) = (c_a, χ_a) かつ (c′_b, χ′_b) = (c_b, χ_b)（c_a, c′_a ∣ a、c_b, c′_b ∣ b。Part 228 の mul_eq_mul_iff_of_coprime と 0h）。 -/
theorem sigma_charMul_eq_iff {a b ca cb ca' cb' : ℕ} [NeZero ca] [NeZero cb] [NeZero ca'] [NeZero cb']
    (hab : Nat.Coprime a b) (hca : ca ∣ a) (hcb : cb ∣ b) (hca' : ca' ∣ a) (hcb' : cb' ∣ b)
    (χa : DirichletCharacter ℂ ca) (χb : DirichletCharacter ℂ cb) (χa' : DirichletCharacter ℂ ca')
    (χb' : DirichletCharacter ℂ cb') :
    (⟨ca' * cb', charMul χa' χb'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨ca * cb, charMul χa χb⟩ ↔
      (⟨ca', χa'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨ca, χa⟩ ∧
        (⟨cb', χb'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨cb, χb⟩ := by
  constructor
  · intro e
    obtain ⟨rfl, rfl⟩ := (mul_eq_mul_iff_of_coprime hab hca' hcb' hca hcb).mp (Sigma.mk.inj e).1
    have hcop : Nat.Coprime ca' cb' := Nat.Coprime.coprime_dvd_right hcb' (Nat.Coprime.coprime_dvd_left hca' hab)
    obtain ⟨rfl, rfl⟩ := charMul_injective hcop (eq_of_heq (Sigma.mk.inj e).2)
    exact ⟨rfl, rfl⟩
  · rintro ⟨e1, e2⟩
    cases e1
    cases e2
    rfl

/-- **3c. ブロックの射影の分解** C(P_{c_a c_b, χ_a⊠χ_b}) = L(P_{c_a,χ_a})·R(P_{c_b,χ_b})（1l で純テンソルに帰着し、2f と 3a・3b）。 -/
theorem crtConj_blockProjL {a b ca cb : ℕ} [NeZero a] [NeZero b] [NeZero ca] [NeZero cb]
    [Fintype (BlockIdx a)] [Fintype (BlockIdx b)] (hab : Nat.Coprime a b) (hca : ca ∣ a) (hcb : cb ∣ b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive) :
    crtConj hab (blockProjL (a * b) (ca * cb) (charMul χa χb)) =
      leftOp b (blockProjL a ca χa) * rightOp a (blockProjL b cb χb) := by
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  apply ext_tens_block
  rintro ⟨⟨ca', hca'⟩, ⟨χa', hχa'⟩⟩ ⟨⟨cb', hcb'⟩, ⟨χb', hχb'⟩⟩ f g hf hg
  have hca'a : ca' ∣ a := Nat.dvd_of_mem_divisors hca'
  have hcb'b : cb' ∣ b := Nat.dvd_of_mem_divisors hcb'
  have : NeZero ca' := ⟨(Nat.pos_of_mem_divisors hca').ne'⟩
  have : NeZero cb' := ⟨(Nat.pos_of_mem_divisors hcb').ne'⟩
  have hcop' : Nat.Coprime ca' cb' := Nat.Coprime.coprime_dvd_right hcb'b (Nat.Coprime.coprime_dvd_left hca'a hab)
  have hG := crtProd_mem_blockSpan hab hca'a hcb'b hχa' hχb' hf hg
  have hiff := sigma_charMul_eq_iff hab hca hcb hca'a hcb'b χa χb χa' χb'
  rw [crtConj_apply_tens, Module.End.mul_apply, rightOp_tens, leftOp_tens, blockProjL_apply, blockProjL_apply,
    blockProjL_apply, blockProj_eq_ite (mul_dvd_mul hca'a hcb'b) (mul_dvd_mul hca hcb)
      (isPrimitive_charMul hcop' hχa' hχb') (isPrimitive_charMul hcop hχa hχb) hG,
    blockProj_eq_ite hca'a hca hχa' hχa hf, blockProj_eq_ite hcb'b hcb hχb' hχb hg]
  by_cases h1 : (⟨ca', χa'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨ca, χa⟩
  · by_cases h2 : (⟨cb', χb'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨cb, χb⟩
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2, crtLin_crtProd]
    · rw [ite_eq_right (fun e => h2 (hiff.mp e).2), ite_eq_right h2, map_zero, tens_zero_right]
  · rw [ite_eq_right (fun e => h1 (hiff.mp e).1), ite_eq_right h1, map_zero, tens_zero_left]

/-- **3d.** 法 c_a c_b の原始指標 χ はすべて χ_a ⊠ χ_b の形で、C(P_{c_a c_b, χ}) = L(P_{c_a,χ_a})·R(P_{c_b,χ_b})（0k と 3c）。 -/
theorem crtConj_blockProjL_exists {a b ca cb : ℕ} [NeZero a] [NeZero b] [NeZero ca] [NeZero cb]
    [Fintype (BlockIdx a)] [Fintype (BlockIdx b)] (hab : Nat.Coprime a b) (hca : ca ∣ a) (hcb : cb ∣ b)
    {χ : DirichletCharacter ℂ (ca * cb)} (hχ : χ.IsPrimitive) :
    ∃ χa : DirichletCharacter ℂ ca, ∃ χb : DirichletCharacter ℂ cb, χa.IsPrimitive ∧ χb.IsPrimitive ∧
      charMul χa χb = χ ∧
        crtConj hab (blockProjL (a * b) (ca * cb) χ) =
          leftOp b (blockProjL a ca χa) * rightOp a (blockProjL b cb χb) := by
  have hcop : Nat.Coprime ca cb := Nat.Coprime.coprime_dvd_right hcb (Nat.Coprime.coprime_dvd_left hca hab)
  obtain ⟨χa, χb, ha, hb, rfl⟩ := exists_charMul_eq hcop hχ
  exact ⟨χa, χb, ha, hb, rfl, crtConj_blockProjL hab hca hcb ha hb⟩

/-- **3e. 中心の極小べき等元の番号どおりの分解** C(z_{(c_a c_b, d_a d_b)}) = L(z_{(c_a,d_a)})·R(z_{(c_b,d_b)})（(c_a, d_a) ∈ S(a)、(c_b, d_b) ∈ S(b)。Part 222 の centralElt_apply_of_mem′、2f、Part 231 の layerInd_crt）。 -/
theorem crtConj_centralElt {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    [Fintype (BlockIdx (a * b))] (hab : Nat.Coprime a b) {ca da cb db : ℕ}
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b) :
    crtConj hab (centralElt (a * b) (ca * cb) (da * db)) =
      leftOp b (centralElt a ca da) * rightOp a (centralElt b cb db) := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  apply ext_tens_block
  rintro ⟨⟨ca', hca'⟩, ⟨χa', hχa'⟩⟩ ⟨⟨cb', hcb'⟩, ⟨χb', hχb'⟩⟩ f g hf hg
  have hca'a : ca' ∣ a := Nat.dvd_of_mem_divisors hca'
  have hcb'b : cb' ∣ b := Nat.dvd_of_mem_divisors hcb'
  have : NeZero ca' := ⟨(Nat.pos_of_mem_divisors hca').ne'⟩
  have : NeZero cb' := ⟨(Nat.pos_of_mem_divisors hcb').ne'⟩
  have hcop' : Nat.Coprime ca' cb' := Nat.Coprime.coprime_dvd_right hcb'b (Nat.Coprime.coprime_dvd_left hca'a hab)
  have hG := crtProd_mem_blockSpan hab hca'a hcb'b hχa' hχb' hf hg
  have hmem : ca' * cb' ∈ (a * b).divisors := Nat.mem_divisors.mpr ⟨mul_dvd_mul hca'a hcb'b, NeZero.ne _⟩
  have hiff := mul_eq_mul_iff_of_coprime hab hca'a hcb'b hca hcb
  rw [crtConj_apply_tens, Module.End.mul_apply, rightOp_tens, leftOp_tens,
    centralElt_apply_of_mem' a hca' χa' hχa' hf, centralElt_apply_of_mem' b hcb' χb' hχb' hg,
    centralElt_apply_of_mem' (a * b) hmem _ (isPrimitive_charMul hcop' hχa' hχb') hG]
  by_cases h1 : ca' = ca
  · by_cases h2 : cb' = cb
    · rw [ite_eq_left (hiff.mpr ⟨h1, h2⟩), ite_eq_left h1, ite_eq_left h2]
      funext p
      rw [crtLin_apply, Pi.mul_apply, crtProd_apply, RingEquiv.apply_symm_apply, layerInd_crt hab hp hq,
        RingEquiv.apply_symm_apply, tens_apply, Pi.mul_apply, Pi.mul_apply]
      ring
    · rw [ite_eq_right (fun e => h2 (hiff.mp e).2), ite_eq_right h2, map_zero, tens_zero_right]
  · rw [ite_eq_right (fun e => h1 (hiff.mp e).1), ite_eq_right h1, map_zero, tens_zero_left]

/-- **3f.** S(ab) の (c, d) について C(z_{(c,d)}) = L(z_{(gcd(c,a), gcd(d,a))})·R(z_{(gcd(c,b), gcd(d,b))})（Part 229 の idxSplit）。 -/
theorem crtConj_centralElt_split {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    [Fintype (BlockIdx (a * b))] (hab : Nat.Coprime a b) {c d : ℕ}
    (hr : (⟨c, d⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx (a * b)) :
    crtConj hab (centralElt (a * b) c d) =
      leftOp b (centralElt a (Nat.gcd c a) (Nat.gcd d a)) * rightOp a (centralElt b (Nat.gcd c b) (Nat.gcd d b)) := by
  have hpa : (⟨Nat.gcd c a, Nat.gcd d a⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a := (idxSplit_mem hab hr).1
  have hpb : (⟨Nat.gcd c b, Nat.gcd d b⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b := (idxSplit_mem hab hr).2
  have h := idxMul_idxSplit hab hr
  have hc : Nat.gcd c a * Nat.gcd c b = c := congrArg (fun s : Σ _ : ℕ, ℕ => s.1) h
  have hd : Nat.gcd d a * Nat.gcd d b = d := congrArg (fun s : Σ _ : ℕ, ℕ => s.2) h
  have e := crtConj_centralElt hab hpa hpb
  rw [hc, hd] at e
  exact e

/-- **3g.** W_{c,χ}(d) への射影 ι_d·P_χ も C(ι_{d_a d_b}·P_{χ_a⊠χ_b}) = L(ι_{d_a}·P_{χ_a})·R(ι_{d_b}·P_{χ_b})（Part 231 の crtConj_layerInd と 3c）。 -/
theorem crtConj_layerBlockProj {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive) :
    crtConj hab (LinearMap.mulLeft ℂ (layerInd (a * b) (ca * cb) (da * db)) *
        blockProjL (a * b) (ca * cb) (charMul χa χb)) =
      leftOp b (LinearMap.mulLeft ℂ (layerInd a ca da) * blockProjL a ca χa) *
        rightOp a (LinearMap.mulLeft ℂ (layerInd b cb db) * blockProjL b cb χb) := by
  have hca : ca ∣ a := ((mem_centerIdx_iff_dvd a ca da).mp hp).1
  have hcb : cb ∣ b := ((mem_centerIdx_iff_dvd b cb db).mp hq).1
  rw [map_mul, crtConj_layerInd hab hp hq, crtConj_blockProjL hab hca hcb hχa hχb, leftOp_mul, rightOp_mul,
    mul_assoc, ← mul_assoc (rightOp a _), ← (leftOp_commute_rightOp _ _).eq, mul_assoc, mul_assoc]

/-- **3h.** 対角の行列単位 E^d_{χ→χ} = ι_d·P_χ（d ∈ D(c)。Part 223 の twistFn_self_mul_layerInd）。 -/
theorem matUnit_self_eq (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) {d : ℕ}
    (hdI : d ∈ layerIdx c (N / c)) :
    matUnit N c d χ χ = LinearMap.mulLeft ℂ (layerInd N c d) * blockProjL N c χ := by
  unfold matUnit
  rw [twistFn_self_mul_layerInd N c χ hdI]
  rfl

/-- **3i.** C(E^{d_a d_b}_{χ_a⊠χ_b → χ_a⊠χ_b}) = L(E^{d_a}_{χ_a→χ_a})·R(E^{d_b}_{χ_b→χ_b})（3g と 3h）。 -/
theorem crtConj_matUnit_self {a b : ℕ} [NeZero a] [NeZero b] [Fintype (BlockIdx a)] [Fintype (BlockIdx b)]
    (hab : Nat.Coprime a b) {ca da cb db : ℕ} [NeZero ca] [NeZero cb]
    (hp : (⟨ca, da⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx a) (hq : (⟨cb, db⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx b)
    {χa : DirichletCharacter ℂ ca} {χb : DirichletCharacter ℂ cb} (hχa : χa.IsPrimitive) (hχb : χb.IsPrimitive) :
    crtConj hab (matUnit (a * b) (ca * cb) (da * db) (charMul χa χb) (charMul χa χb)) =
      leftOp b (matUnit a ca da χa χa) * rightOp a (matUnit b cb db χb χb) := by
  have hr : da * db ∈ layerIdx (ca * cb) (a * b / (ca * cb)) :=
    ((mem_centerIdx _ _).mp (idxMul_mem_centerIdx hab hp hq)).2.2
  have ha : da ∈ layerIdx ca (a / ca) := ((mem_centerIdx _ _).mp hp).2.2
  have hb : db ∈ layerIdx cb (b / cb) := ((mem_centerIdx _ _).mp hq).2.2
  rw [matUnit_self_eq (a * b) (ca * cb) (charMul χa χb) hr, matUnit_self_eq a ca χa ha, matUnit_self_eq b cb χb hb]
  exact crtConj_layerBlockProj hab hp hq hχa hχb

end PAG.Part236

#print axioms PAG.Part236.charMul
#print axioms PAG.Part236.changeLevel_charMul
#print axioms PAG.Part236.charMul_apply_unit
#print axioms PAG.Part236.charMul_apply
#print axioms PAG.Part236.charMul_mul
#print axioms PAG.Part236.charMul_inv
#print axioms PAG.Part236.dvd_conductor_of_eq_mul
#print axioms PAG.Part236.isPrimitive_charMul
#print axioms PAG.Part236.charMul_injective
#print axioms PAG.Part236.primMul
#print axioms PAG.Part236.primMul_injective
#print axioms PAG.Part236.primMul_bijective
#print axioms PAG.Part236.primEquiv
#print axioms PAG.Part236.exists_charMul_eq
#print axioms PAG.Part236.cast_crt_fst
#print axioms PAG.Part236.cast_crt_snd
#print axioms PAG.Part236.liftc_charMul
#print axioms PAG.Part236.tens
#print axioms PAG.Part236.tens_apply
#print axioms PAG.Part236.tens_zero_left
#print axioms PAG.Part236.tens_zero_right
#print axioms PAG.Part236.tens_sum_left
#print axioms PAG.Part236.tens_sum_right
#print axioms PAG.Part236.leftOp_tens
#print axioms PAG.Part236.rightOp_tens
#print axioms PAG.Part236.leftOp_mul
#print axioms PAG.Part236.rightOp_mul
#print axioms PAG.Part236.single_eq_tens
#print axioms PAG.Part236.ext_tens
#print axioms PAG.Part236.ext_tens_block
#print axioms PAG.Part236.crtProd
#print axioms PAG.Part236.crtProd_apply
#print axioms PAG.Part236.crtLin_crtProd
#print axioms PAG.Part236.crtConj_apply_tens
#print axioms PAG.Part236.crtProd_smul_smul
#print axioms PAG.Part236.dil_crtProd
#print axioms PAG.Part236.crtProd_mem_blockSpan
#print axioms PAG.Part236.crtProd_mem_layerPart
#print axioms PAG.Part236.blockProj_eq_ite
#print axioms PAG.Part236.sigma_charMul_eq_iff
#print axioms PAG.Part236.crtConj_blockProjL
#print axioms PAG.Part236.crtConj_blockProjL_exists
#print axioms PAG.Part236.crtConj_centralElt
#print axioms PAG.Part236.crtConj_centralElt_split
#print axioms PAG.Part236.crtConj_layerBlockProj
#print axioms PAG.Part236.matUnit_self_eq
#print axioms PAG.Part236.crtConj_matUnit_self
