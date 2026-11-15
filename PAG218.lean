/-
  PAG 2.0 Part 214（2026-10-28）— 単数倍の作用によるブロックの特徴づけと、殻の射影が生成する代数
  ブロック (c, χ)（χ は法 c の原始指標）、L = N/c。u, w は L の約数
  U_a f(x) = f(a·x)（a は法 N の単数、def dil）、χ_N = liftc χ N（χ を法 N へ持ち上げた指標、Part 206）
  k_u = |u, χ⟩_N（Part 210 の kblock）、P = P_{c,χ}（Part 211 の blockProj）
  E_s = ε_s ⋆（双対殻の射影、Part 201 の geps）、D_s = 1_{D_s}·（空間の殻の射影、dind）
  0. 準備：単数の上の指標の和 Σ_a ψ(a) = [ψ = 1]·φ(N)、χ̄_N = χ_N⁻¹、殻の埋め込みと掛け算
  1. U_a の性質：U_1 = 1、U_a U_b = U_{ab}、ユニタリ（⟨U_a f, U_a g⟩ = ⟨f, g⟩）
  2. ケットは U_a の固有ベクトル：U_a |u, χ⟩ = χ_N(a)·|u, χ⟩。ブロックの張る空間の元も同じ
  3. 射影の式：P_{c,χ} f = (1/φ(N))·Σ_a χ̄_N(a)·U_a f（指標の直交性）
  4. 系：ブロック = 固有空間 {f : U_a f = χ_N(a) f}。U_a とすべて可換な線形写像は P と可換。
     動径関数 r（Part 203）の積・畳み込みは P と可換（Part 212・213 の可換性は r = ε_s, 1_{D_s} の場合）。
     𝓕 U_a = U_{a⁻¹} 𝓕。動径関数の空間 = 自明な指標のブロック (1, 1) の張る空間
  5. 殻の射影の代数 A = ⟨E_s, D_s⟩（def shellAlg）：A の元は U_a と可換で、各ブロックを保つ。
     rad(N/c) ∣ c なら各 k_u は A のすべての元の固有ベクトル（ε_s ⋆ k_u = [s = L/u]·k_u、1_{D_s}·k_u = [s = u]·k_u）。
     特に N/c > 1 なら A のどの元も k_1 を k_{N/c} に写さない（ブロックの上で A は全行列環にならない）
-/
import PAG217

namespace PAG.Part218

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 0. 準備 -/

open Classical in
/-- **0a. 単数の上の指標の和**：法 N の指標 ψ について Σ_{a ∈ (ℤ/N)ˣ} ψ(a) = [ψ = 1]·φ(N)。 -/
theorem sum_units_char (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ∑ a : (ZMod N)ˣ, ψ (a : ZMod N) = if ψ = 1 then (Nat.totient N : ℂ) else 0 := by
  by_cases h : ψ = 1
  · rw [ite_eq_left h]
    subst h
    simp only [MulChar.one_apply_coe, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient,
      nsmul_eq_mul, mul_one]
  · rw [ite_eq_right h]
    obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp h
    refine eq_zero_of_mul_eq_self_left hb ?_
    rw [Finset.mul_sum]
    simp only [← map_mul, ← Units.val_mul]
    exact Fintype.sum_bijective _ (Group.mulLeft_bijective b) _ _ (fun _ => rfl)

/-- **0b.** c ∣ N なら liftc χ⁻¹ N = (liftc χ N)⁻¹（χ̄_N = χ_N⁻¹）。 -/
theorem liftc_inv (N : ℕ) {c : ℕ} (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) :
    liftc χ⁻¹ N = (liftc χ N)⁻¹ := by
  rw [liftc_of_dvd χ⁻¹ hcN, liftc_of_dvd χ hcN, map_inv]

/-- **0c.** 単数 a で χ_N(a)·χ̄_N(a) = 1。 -/
theorem liftc_mul_liftc_inv (N : ℕ) {c : ℕ} (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ) :
    liftc χ N (a : ZMod N) * liftc χ⁻¹ N (a : ZMod N) = 1 := by
  rw [← MulChar.mul_apply, liftc_inv N hcN χ, mul_inv_cancel, MulChar.one_apply_coe]

/-- **0d. 殻の埋め込みと掛け算**：b·ι_u(y) = ι_u(b̄·y)（u M = N、b̄ は b を法 M へ落としたもの）。 -/
theorem mul_memb (u M N : ℕ) [NeZero N] (h : u * M = N) (b : ZMod N) (y : ZMod M) :
    b * memb u M N h y = memb u M N h (ZMod.castHom (Dvd.intro_left u h) (ZMod M) b * y) := by
  have := neZero_of_mul h
  have hb : ZMod.castHom (Dvd.intro_left u h) (ZMod M) b = ((b.val : ℕ) : ZMod M) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val b]
    exact map_natCast _ _
  rw [hb, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-! ### 1. 単数倍の作用 -/

/-- 単数倍の作用 U_a f(x) = f(a·x)（a は法 N の単数）。線形写像として定義する。 -/
def dil {N : ℕ} (a : (ZMod N)ˣ) : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x => (a : ZMod N) * x)

/-- **1a.** (U_a f)(x) = f(a·x)。 -/
theorem dil_apply {N : ℕ} (a : (ZMod N)ˣ) (f : ZMod N → ℂ) (x : ZMod N) :
    dil a f x = f ((a : ZMod N) * x) := rfl

/-- **1b.** U_1 f = f。 -/
theorem dil_one {N : ℕ} (f : ZMod N → ℂ) : dil (1 : (ZMod N)ˣ) f = f := by
  funext x
  rw [dil_apply, Units.val_one, one_mul]

/-- **1c.** U_a (U_b f) = U_{ab} f。 -/
theorem dil_dil {N : ℕ} (a b : (ZMod N)ˣ) (f : ZMod N → ℂ) : dil a (dil b f) = dil (a * b) f := by
  funext x
  rw [dil_apply, dil_apply, dil_apply, Units.val_mul]
  congr 1
  ring

/-- **1d. ユニタリ**：⟨U_a f, U_a g⟩ = ⟨f, g⟩。 -/
theorem inner_dil {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (f g : ZMod N → ℂ) :
    ∑ x, starRingEnd ℂ (dil a f x) * dil a g x = ∑ x, starRingEnd ℂ (f x) * g x :=
  Fintype.sum_bijective _ (Units.mulLeft_bijective a) _ _ (fun _ => rfl)

/-! ### 2. ケットは単数倍の固有ベクトル -/

/-- **2a.** 各点の形：|u, χ⟩(a·x) = χ_N(a)·|u, χ⟩(x)（a は単数、χ は法 c のどの指標でもよい）。 -/
theorem gket_unit_mul (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ) (x : ZMod N) :
    gket u M N h c hc χ ((a : ZMod N) * x) = liftc χ N (a : ZMod N) * gket u M N h c hc χ x := by
  have hcN : c ∣ N := dvd_trans hc (Dvd.intro_left u h)
  have hcast : ZMod.castHom hc (ZMod c) (ZMod.castHom (Dvd.intro_left u h) (ZMod M) (a : ZMod N)) =
      ZMod.cast (a : ZMod N) := by
    rw [← ZMod.castHom_apply (h := hcN)]
    exact RingHom.congr_fun (ZMod.castHom_comp hc (Dvd.intro_left u h)) _
  rw [liftc_of_dvd χ hcN, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  by_cases hx : ∃ y, memb u M N h y = x
  · obtain ⟨y, rfl⟩ := hx
    rw [mul_memb u M N h, gket_memb, gket_memb, map_mul, map_mul, hcast]
    ring
  · have hx' : ¬ ∃ y, memb u M N h y = (a : ZMod N) * x := by
      rintro ⟨y, hy⟩
      apply hx
      refine ⟨ZMod.castHom (Dvd.intro_left u h) (ZMod M) ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * y, ?_⟩
      rw [← mul_memb u M N h, hy, ← mul_assoc, Units.inv_mul, one_mul]
    rw [gket_apply, gket_apply, ite_eq_right (fun hd => hx' ((exists_memb_iff u M N h _).mpr hd)),
      ite_eq_right (fun hd => hx ((exists_memb_iff u M N h _).mpr hd)), mul_zero]

/-- **2b. ケットは単数倍の固有ベクトル**：U_a |u, χ⟩ = χ_N(a)·|u, χ⟩。 -/
theorem dil_gket (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ) :
    dil a (gket u M N h c hc χ) = liftc χ N (a : ZMod N) • gket u M N h c hc χ := by
  funext x
  rw [dil_apply, gket_unit_mul, Pi.smul_apply, smul_eq_mul]

/-- **2c.** ケット基底の元：U_a k_j = χ_{j,N}(a)·k_j（χ_j は番号 j の指標）。 -/
theorem dil_ketFam (N : ℕ) [NeZero N] (j : KetIdx N) (a : (ZMod N)ˣ) :
    dil a (ketFam N j) = liftc j.2.2.1 N (a : ZMod N) • ketFam N j :=
  dil_gket _ _ N _ _ _ _ a

/-- **2d.** ブロックのケット：U_a k_w = χ_N(a)·k_w。 -/
theorem dil_kblock (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (w : ℕ) (a : (ZMod N)ˣ) :
    dil a (kblock N c χ w) = liftc χ N (a : ZMod N) • kblock N c χ w := by
  unfold kblock
  split_ifs with hw
  · exact dil_gket _ _ N _ c _ χ a
  · rw [map_zero, smul_zero]

/-- **2e.** ブロックの張る空間の元 f は U_a f = χ_N(a)·f を満たす。 -/
theorem dil_of_mem_span (N c : ℕ) [NeZero N] (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ)
    {f : ZMod N → ℂ} (hf : f ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w)) :
    dil a f = liftc χ N (a : ZMod N) • f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact dil_kblock N c χ w a
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul r x _ hx => rw [map_smul, hx, smul_comm]

/-! ### 3. 射影の式 -/

/-- 線形写像としてのブロックへの射影 P_{c,χ}。 -/
noncomputable def blockProjL (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) :
    (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ) where
  toFun := blockProj N c χ
  map_add' f g := by
    simp only [blockProj, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' r f := by
    simp only [blockProj, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by ring)

/-- **3a.** blockProjL は blockProj。 -/
theorem blockProjL_apply (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (f : ZMod N → ℂ) :
    blockProjL N c χ f = blockProj N c χ f := rfl

/-- **3b.** 番号 j のケットについて：χ̄_N·χ_{j,N} = 1 ⇔ j はブロック (c, χ) のケット（χ, χ_j は原始的）。 -/
theorem liftc_mul_eq_one_iff (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (j : KetIdx N) :
    liftc χ⁻¹ N * liftc j.2.2.1 N = 1 ↔ ketClass j = ⟨c, χ⟩ := by
  obtain ⟨⟨u', hu'⟩, ⟨c', hc'⟩, ⟨χ', hχ'⟩⟩ := j
  have hc'N : c' ∣ N :=
    Nat.dvd_of_mem_divisors ((mem_block_iff N u' c' (NeZero.ne N)).mp ⟨hu', hc'⟩).1
  show liftc χ⁻¹ N * liftc χ' N = 1 ↔ (⟨c', χ'⟩ : Σ c : ℕ, DirichletCharacter ℂ c) = ⟨c, χ⟩
  constructor
  · intro e
    have e' : liftc χ⁻¹ N = liftc χ'⁻¹ N := by
      rw [liftc_inv N hc'N χ']
      exact eq_inv_of_mul_eq_one_left e
    have hcc : c = c' := conductor_eq_of_liftc_eq N hcN hc'N χ χ' hχ hχ' e'
    subst hcc
    rw [eq_of_liftc_eq N hcN χ χ' e']
  · intro hcl
    obtain ⟨hcc, hχχ⟩ := Sigma.mk.inj_iff.mp hcl
    subst hcc
    rw [eq_of_heq hχχ, liftc_inv N hcN χ, inv_mul_cancel]

open Classical in
/-- **3c.** Σ_a χ̄_N(a)·U_a k_j = [j はブロック (c, χ) のケット]·φ(N)·k_j。 -/
theorem sum_dil_ketFam (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (j : KetIdx N) :
    ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) • dil a (ketFam N j) =
      (if ketClass j = ⟨c, χ⟩ then (Nat.totient N : ℂ) else 0) • ketFam N j := by
  simp only [dil_ketFam, smul_smul, ← Finset.sum_smul]
  congr 1
  simp only [← MulChar.mul_apply]
  rw [sum_units_char N]
  by_cases hj : ketClass j = ⟨c, χ⟩
  · rw [ite_eq_left ((liftc_mul_eq_one_iff N c hcN χ hχ j).mpr hj), ite_eq_left hj]
  · rw [ite_eq_right (fun e => hj ((liftc_mul_eq_one_iff N c hcN χ hχ j).mp e)), ite_eq_right hj]

/-- **3d. 射影の式（線形写像として）**：P_{c,χ} = (1/φ(N))·Σ_{a ∈ (ℤ/N)ˣ} χ̄_N(a)·U_a（χ 原始的）。 -/
theorem blockProjL_eq_sum_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    blockProjL N c χ = ((Nat.totient N : ℂ))⁻¹ • ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) • dil a := by
  classical
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  refine (ketBasis N).ext (fun j => ?_)
  rw [ketBasis_apply, blockProjL_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  rw [sum_dil_ketFam N c hcN χ hχ j, smul_smul]
  by_cases hj : ketClass j = ⟨c, χ⟩
  · rw [ite_eq_left hj, inv_mul_cancel₀ hφ, one_smul]
    rcases ketIdx_cases N c χ j with ⟨w, hw⟩ | hne
    · rw [hw]
      exact blockProj_kblock N c hcN χ hχ w
    · exact absurd hj hne
  · rw [ite_eq_right hj, mul_zero, zero_smul]
    exact blockProj_ketFam_of_ne N c hcN χ hχ j hj

/-- **3e. 射影の式**：P_{c,χ} f = (1/φ(N))·Σ_{a ∈ (ℤ/N)ˣ} χ̄_N(a)·U_a f（χ 原始的）。 -/
theorem blockProj_eq_sum_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    blockProj N c χ f = ((Nat.totient N : ℂ))⁻¹ • ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) • dil a f := by
  have e := LinearMap.congr_fun (blockProjL_eq_sum_dil N c hcN χ hχ) f
  rw [blockProjL_apply, LinearMap.smul_apply, LinearMap.sum_apply] at e
  simpa only [LinearMap.smul_apply] using e

/-! ### 4. 系 -/

/-- **4a.** U_a (P f) = χ_N(a)·P f。 -/
theorem dil_blockProj (N c : ℕ) [NeZero N] [NeZero c] (χ : DirichletCharacter ℂ c) (a : (ZMod N)ˣ)
    (f : ZMod N → ℂ) : dil a (blockProj N c χ f) = liftc χ N (a : ZMod N) • blockProj N c χ f :=
  dil_of_mem_span N c χ a (blockProj_mem_span N c χ f)

/-- **4b.** P と U_a は可換：P (U_a f) = U_a (P f)。 -/
theorem blockProj_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (a : (ZMod N)ˣ) (f : ZMod N → ℂ) :
    blockProj N c χ (dil a f) = dil a (blockProj N c χ f) := by
  rw [blockProj_eq_sum_dil N c hcN χ hχ, blockProj_eq_sum_dil N c hcN χ hχ, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul, dil_dil, dil_dil, mul_comm]

/-- **4c.** U_a とすべて可換な線形写像 T は P と可換：T (P f) = P (T f)。 -/
theorem comm_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (T : (ZMod N → ℂ) →ₗ[ℂ] (ZMod N → ℂ))
    (hT : ∀ (a : (ZMod N)ˣ) (g : ZMod N → ℂ), T (dil a g) = dil a (T g)) (f : ZMod N → ℂ) :
    T (blockProj N c χ f) = blockProj N c χ (T f) := by
  rw [blockProj_eq_sum_dil N c hcN χ hχ, blockProj_eq_sum_dil N c hcN χ hχ, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_smul, hT]

/-- **4d. ブロック = 固有空間**：f がブロックの張る空間に入る ⇔ すべての単数 a で U_a f = χ_N(a)·f。 -/
theorem mem_span_iff_dil (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (f : ZMod N → ℂ) :
    f ∈ Submodule.span ℂ (Set.range fun w : (N / c).divisors => kblock N c χ w) ↔
      ∀ a : (ZMod N)ˣ, dil a f = liftc χ N (a : ZMod N) • f := by
  constructor
  · intro hf a
    exact dil_of_mem_span N c χ a hf
  · intro hf
    have hφ : (Nat.totient N : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
    have h1 : ∀ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) * liftc χ N (a : ZMod N) = 1 := fun a => by
      rw [mul_comm, liftc_mul_liftc_inv N hcN χ a]
    have e : blockProj N c χ f = f := by
      rw [blockProj_eq_sum_dil N c hcN χ hχ]
      simp only [hf, smul_smul, h1, one_smul, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hφ, one_smul]
    rw [← e]
    exact blockProj_mem_span N c χ f

/-- **4e.** 動径関数 r の積は U_a と可換：U_a (r·f) = r·U_a f。 -/
theorem dil_radial_mul {N : ℕ} (r : ZMod N → ℂ) (hr : Radial r) (a : (ZMod N)ˣ) (f : ZMod N → ℂ) :
    dil a (r * f) = r * dil a f := by
  funext x
  simp only [dil_apply, Pi.mul_apply, hr a x]

/-- **4f.** 動径関数 r の畳み込みは U_a と可換：U_a (r ⋆ f) = r ⋆ U_a f。 -/
theorem dil_radial_conv {N : ℕ} [NeZero N] (r : ZMod N → ℂ) (hr : Radial r) (a : (ZMod N)ˣ)
    (f : ZMod N → ℂ) : dil a (PAG.Part15.conv r f) = PAG.Part15.conv r (dil a f) := by
  funext x
  simp only [dil_apply, PAG.Part15.conv]
  symm
  exact Fintype.sum_bijective (fun y => (a : ZMod N) * y) (Units.mulLeft_bijective a) _ _
    (fun y => by simp only [hr a y, mul_sub])

/-- **4g. 動径関数の積は射影と可換**：r·(P f) = P (r·f)（Part 213 の dind_mul_blockProj は r = 1_{D_s}）。 -/
theorem radial_mul_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (r : ZMod N → ℂ) (hr : Radial r) (f : ZMod N → ℂ) :
    r * blockProj N c χ f = blockProj N c χ (r * f) :=
  comm_blockProj N c hcN χ hχ (LinearMap.mulLeft ℂ r) (fun a g => (dil_radial_mul r hr a g).symm) f

/-- **4h. 動径関数の畳み込みは射影と可換**：r ⋆ (P f) = P (r ⋆ f)（Part 212 の geps_conv_blockProj は r = ε_s）。 -/
theorem radial_conv_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (r : ZMod N → ℂ) (hr : Radial r) (f : ZMod N → ℂ) :
    PAG.Part15.conv r (blockProj N c χ f) = blockProj N c χ (PAG.Part15.conv r f) :=
  comm_blockProj N c hcN χ hχ (PAG.Part15.convL r) (fun a g => (dil_radial_conv r hr a g).symm) f

/-- **4i. フーリエ変換と単数倍**：𝓕 (U_a f) = U_{a⁻¹} (𝓕 f)。 -/
theorem dft_dil {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : 𝓕 (dil a f) = dil a⁻¹ (𝓕 f) := by
  funext k
  rw [dil_apply, ZMod.dft_apply, ZMod.dft_apply]
  refine Fintype.sum_bijective (fun j => (a : ZMod N) * j) (Units.mulLeft_bijective a) _ _ (fun j => ?_)
  have e : (a : ZMod N) * j * (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * k) = j * k := by
    rw [show (a : ZMod N) * j * (((a⁻¹ : (ZMod N)ˣ) : ZMod N) * k) =
      j * k * ((a : ZMod N) * ((a⁻¹ : (ZMod N)ˣ) : ZMod N)) by ring, Units.mul_inv, mul_one]
  simp only [dil_apply, e]

/-- **4j.** 動径関数 ⇔ すべての U_a で不変。 -/
theorem radial_iff_dil {N : ℕ} (f : ZMod N → ℂ) : Radial f ↔ ∀ a : (ZMod N)ˣ, dil a f = f := by
  constructor
  · intro hf a
    funext x
    exact hf a x
  · intro hf a x
    exact congrFun (hf a) x

/-- **4k. 動径関数の空間は自明な指標のブロック**：Radial f ⇔ f ∈ span{|u, 1⟩_N : u ∣ N}（c = 1）。 -/
theorem radial_iff_mem_span (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    Radial f ↔ f ∈ Submodule.span ℂ
      (Set.range fun w : (N / 1).divisors => kblock N 1 (1 : DirichletCharacter ℂ 1) w) := by
  rw [mem_span_iff_dil N 1 (one_dvd N) 1 DirichletCharacter.isPrimitive_one_level_one f, radial_iff_dil]
  refine forall_congr' (fun a => ?_)
  rw [liftc_of_dvd _ (one_dvd N), map_one, MulChar.one_apply_coe, one_smul]

/-! ### 5. 殻の射影が生成する代数 -/

/-- 殻の射影が生成する代数 A = ⟨E_s, D_s⟩ ⊆ End(ℂ^{ℤ/N})（E_s = ε_s ⋆、D_s = 1_{D_s}·）。 -/
noncomputable def shellAlg (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (ZMod N → ℂ)) :=
  Algebra.adjoin ℂ (Set.range (fun s : ℕ => PAG.Part15.convL (geps N s)) ∪
    Set.range (fun s : ℕ => LinearMap.mulLeft ℂ (dind N s)))

/-- **5a.** A の元は U_a と可換。 -/
theorem shellAlg_comm_dil (N : ℕ) [NeZero N] {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N)
    (a : (ZMod N)ˣ) (f : ZMod N → ℂ) : T (dil a f) = dil a (T f) := by
  unfold shellAlg at hT
  induction hT using Algebra.adjoin_induction generalizing f with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact (dil_radial_conv (geps N s) (geps_radial N s) a f).symm
    · exact (dil_radial_mul (dind N s) (dind_radial N s) a f).symm
  | algebraMap r =>
    rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add x y _ _ hx hy =>
    rw [LinearMap.add_apply, LinearMap.add_apply, hx, hy, map_add]
  | mul x y _ _ hx hy =>
    rw [Module.End.mul_apply, Module.End.mul_apply, hy, hx]

/-- **5b.** A の元は各ブロックを保つ：T (P f) = P (T f)。 -/
theorem shellAlg_comm_blockProj (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N) (f : ZMod N → ℂ) :
    T (blockProj N c χ f) = blockProj N c χ (T f) :=
  comm_blockProj N c hcN χ hχ T (fun a g => shellAlg_comm_dil N hT a g) f

/-- **5c.** M の素因数がすべて c を割るなら 1_{D_s}·|u, χ⟩ = [s = u]·|u, χ⟩（χ は法 c のどの指標でもよい）。 -/
theorem dind_mul_gket_of_rad (u M N : ℕ) [NeZero N] (h : u * M = N) (c : ℕ) (hc : c ∣ M)
    (χ : DirichletCharacter ℂ c) (hrad : ∀ q : ℕ, q.Prime → q ∣ M → q ∣ c) (s : ℕ) :
    dind N s * gket u M N h c hc χ = if s = u then gket u M N h c hc χ else 0 := by
  have := neZero_of_mul h
  funext x
  rw [Pi.mul_apply]
  by_cases hx : ∃ y, memb u M N h y = x
  · obtain ⟨y, rfl⟩ := hx
    by_cases h0 : χ (ZMod.castHom hc (ZMod c) y) = 0
    · have hg : gket u M N h c hc χ (memb u M N h y) = 0 := by rw [gket_memb, h0, mul_zero]
      rw [hg, mul_zero]
      split_ifs <;> simp [hg]
    · have hunit : IsUnit (ZMod.castHom hc (ZMod c) y) := by
        by_contra hnu
        exact h0 (MulChar.map_nonunit χ hnu)
      have hy : ZMod.castHom hc (ZMod c) y = ((y.val : ℕ) : ZMod c) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val y]
        exact map_natCast _ _
      rw [hy] at hunit
      have hcop : Nat.Coprime y.val c := (ZMod.isUnit_iff_coprime y.val c).mp hunit
      have hcopM : Nat.Coprime M y.val := Nat.coprime_of_dvd (fun q hq hqM hqy => by
        have hq1 := Nat.dvd_gcd hqy (hrad q hq hqM)
        rw [Nat.Coprime.gcd_eq_one hcop] at hq1
        exact hq.one_lt.ne' (Nat.dvd_one.mp hq1))
      have hgcd : Nat.gcd N (memb u M N h y).val = u := by
        rw [memb_val, ← h, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hcopM, mul_one]
      have hd : dind N s (memb u M N h y) = if u = s then 1 else 0 := by
        simp only [dind, hgcd]
      rw [hd]
      by_cases hsu : s = u
      · subst hsu
        simp
      · simp [hsu, Ne.symm hsu]
  · have hg : gket u M N h c hc χ x = 0 := by
      rw [gket_apply, ite_eq_right (fun hd => hx ((exists_memb_iff u M N h x).mpr hd))]
    rw [hg, mul_zero]
    split_ifs <;> simp [hg]

/-- **5d.** rad(N/c) ∣ c のブロック：1_{D_s}·k_u = [s = u]·k_u（u ∣ N/c）。 -/
theorem dind_mul_kblock_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hrad : ∀ q : ℕ, q.Prime → q ∣ N / c → q ∣ c) {u : ℕ} (hu : u ∣ N / c) (s : ℕ) :
    dind N s * kblock N c χ u = if s = u then kblock N c χ u else 0 := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hc0 : 0 < c := Nat.pos_of_ne_zero (NeZero.ne c)
  have hL0 : 0 < N / c := Nat.div_pos (Nat.le_of_dvd hN0 hcN) hc0
  have hu0 : 0 < u := Nat.pos_of_dvd_of_pos hu hL0
  have e : N / u = c * (N / c / u) := by
    rw [Nat.div_eq_iff_eq_mul_left hu0 h1, mul_assoc, Nat.div_mul_cancel hu, Nat.mul_div_cancel' hcN]
  rw [kblock_of_dvd N c χ h1 h2]
  apply dind_mul_gket_of_rad
  intro q hq hqM
  rw [e] at hqM
  rcases (Nat.Prime.dvd_mul hq).mp hqM with hqc | hqk
  · exact hqc
  · exact hrad q hq (dvd_trans hqk (Nat.div_dvd_of_dvd hu))

/-- **5e.** rad(N/c) ∣ c のブロック：ε_s ⋆ k_u = [s = (N/c)/u]·k_u（u ∣ N/c、χ 原始的）。 -/
theorem geps_conv_kblock_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ N / c → q ∣ c) {u : ℕ} (hu : u ∣ N / c) (s : ℕ) :
    PAG.Part15.conv (geps N s) (kblock N c χ u) = if s = N / c / u then kblock N c χ u else 0 := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  rw [kblock_of_dvd N c χ h1 h2]
  have hru : ∀ q : ℕ, q.Prime → q ∣ u → q ∣ c := fun q hq hqu => hrad q hq (dvd_trans hqu hu)
  split_ifs with hs
  · rw [hs, ← div_div_swap N c u]
    exact geps_conv_gket_self u (N / u) N _ c h2 χ hχ hru
  · exact geps_conv_gket_ne u (N / u) N _ c h2 χ hχ hru s (fun e => hs (e.trans (div_div_swap N c u)))

/-- **5f.** ブロックのケットは 0 でない（u ∣ N/c）。 -/
theorem kblock_ne_zero (N c : ℕ) [NeZero N] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c) {u : ℕ}
    (hu : u ∣ N / c) : kblock N c χ u ≠ 0 := by
  obtain ⟨h1, h2⟩ := block_dvd hcN hu
  rw [kblock_of_dvd N c χ h1 h2]
  intro h0
  have hM := neZero_of_mul (Nat.mul_div_cancel' h1)
  have e := congrFun h0 (memb u (N / u) N (Nat.mul_div_cancel' h1) 1)
  rw [gket_memb, map_one, map_one, mul_one, Pi.zero_apply] at e
  have hpos : 0 < Real.sqrt (Nat.totient (N / u)) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (N / u))))
  have e' : (Real.sqrt (Nat.totient (N / u)))⁻¹ = 0 := by exact_mod_cast e
  exact inv_ne_zero hpos.ne' e'

/-- **5g. 分解するブロック**：rad(N/c) ∣ c なら、各 k_u（u ∣ N/c）は A のすべての元の固有ベクトル。 -/
theorem shellAlg_eigen_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ N / c → q ∣ c) {u : ℕ} (hu : u ∣ N / c)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N) :
    ∃ μ : ℂ, T (kblock N c χ u) = μ • kblock N c χ u := by
  unfold shellAlg at hT
  induction hT using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · refine ⟨if s = N / c / u then 1 else 0, ?_⟩
      rw [PAG.Part15.convL_apply, geps_conv_kblock_of_rad N c hcN χ hχ hrad hu s]
      split_ifs <;> simp
    · refine ⟨if s = u then 1 else 0, ?_⟩
      rw [LinearMap.mulLeft_apply, dind_mul_kblock_of_rad N c hcN χ hrad hu s]
      split_ifs <;> simp
  | algebraMap r => exact ⟨r, Module.algebraMap_end_apply _ _ _ r _⟩
  | add x y _ _ hx hy =>
    obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    exact ⟨μ + ν, by rw [LinearMap.add_apply, hμ, hν, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨μ, hμ⟩ := hx
    obtain ⟨ν, hν⟩ := hy
    exact ⟨ν * μ, by rw [Module.End.mul_apply, hν, map_smul, hμ, smul_smul]⟩

/-- **5h. 全行列環にならない**：rad(N/c) ∣ c かつ N/c > 1 なら、A のどの元も k_1 を k_{N/c} に写さない
（ブロックの上の線形写像 k_1 ↦ k_{N/c} は A の元の制限ではない）。 -/
theorem shellAlg_ne_of_rad (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) (hrad : ∀ q : ℕ, q.Prime → q ∣ N / c → q ∣ c) (hL : 1 < N / c)
    {T : Module.End ℂ (ZMod N → ℂ)} (hT : T ∈ shellAlg N) : T (kblock N c χ 1) ≠ kblock N c χ (N / c) := by
  intro e
  obtain ⟨μ, hμ⟩ := shellAlg_eigen_of_rad N c hcN χ hχ hrad (one_dvd (N / c)) hT
  rw [hμ] at e
  have h1 := dind_mul_kblock_of_rad N c hcN χ hrad (one_dvd (N / c)) (N / c)
  have h2 := dind_mul_kblock_of_rad N c hcN χ hrad (dvd_refl (N / c)) (N / c)
  rw [ite_eq_right hL.ne'] at h1
  rw [ite_eq_left rfl] at h2
  have h0 : kblock N c χ (N / c) = 0 := by
    rw [← h2, ← e, mul_smul_comm, h1, smul_zero]
  exact kblock_ne_zero N c hcN χ (dvd_refl (N / c)) h0

/-! ### 6. トレース：Menon の恒等式とその指標版 -/

/-- **6a.** P_{c,χ} のトレースはブロックの次元：tr P_{c,χ} = d(N/c)（ケット基底で数える）。 -/
theorem trace_blockProjL (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    LinearMap.trace ℂ (ZMod N → ℂ) (blockProjL N c χ) = ((N / c).divisors.card : ℂ) := by
  classical
  let _ := Fintype.ofFinite (KetIdx N)
  have hj : ∀ j : KetIdx N, (ketBasis N).repr (blockProj N c χ (ketFam N j)) j =
      if ketClass j = ⟨c, χ⟩ then 1 else 0 := by
    intro j
    by_cases hc : ketClass j = ⟨c, χ⟩
    · rw [ite_eq_left hc]
      rcases ketIdx_cases N c χ j with ⟨w, hw⟩ | hne
      · rw [hw, blockProj_kblock N c hcN χ hχ w, ← hw, ← ketBasis_apply, Module.Basis.repr_self,
          Finsupp.single_eq_same]
      · exact absurd hc hne
    · rw [ite_eq_right hc, blockProj_ketFam_of_ne N c hcN χ hχ j hc, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have hinj : Function.Injective (blockIdx N c hcN χ hχ) := by
    intro w w' e
    exact Subtype.ext (congrArg (fun j : KetIdx N => (j.1 : ℕ)) e)
  have himage : Finset.univ.filter (fun j : KetIdx N => ketClass j = ⟨c, χ⟩) =
      Finset.univ.image (blockIdx N c hcN χ hχ) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hc
      rcases ketIdx_cases N c χ j with ⟨w, hw⟩ | hne
      · exact ⟨w, ketFam_injective N ((ketFam_blockIdx N c hcN χ hχ w).trans hw.symm)⟩
      · exact absurd hc hne
    · rintro ⟨w, rfl⟩
      rfl
  rw [LinearMap.trace_eq_matrix_trace ℂ (ketBasis N), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, ketBasis_apply, blockProjL_apply, hj]
  rw [Finset.sum_boole, himage, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]

/-- **6b.** U_a のトレースは固定点の個数：tr U_a = #{x : a x = x}。 -/
theorem trace_dil {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    LinearMap.trace ℂ (ZMod N → ℂ) (dil a) =
      ((Finset.univ.filter (fun x : ZMod N => (a : ZMod N) * x = x)).card : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ZMod N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, dil_apply,
    Pi.single_apply]
  rw [Finset.sum_boole]

/-- **6c. 固定点の和**：Σ_{a ∈ (ℤ/N)ˣ} χ̄_N(a)·#{x : a x = x} = φ(N)·d(N/c)（χ は法 c の原始指標）。 -/
theorem sum_liftc_card_fix (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) *
        ((Finset.univ.filter (fun x : ZMod N => (a : ZMod N) * x = x)).card : ℂ) =
      (Nat.totient N : ℂ) * ((N / c).divisors.card : ℂ) := by
  have hφ : (Nat.totient N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  have e := congrArg (LinearMap.trace ℂ (ZMod N → ℂ)) (blockProjL_eq_sum_dil N c hcN χ hχ)
  rw [trace_blockProjL N c hcN χ hχ, map_smul, map_sum] at e
  simp only [map_smul, trace_dil, smul_eq_mul] at e
  rw [e, ← mul_assoc, mul_inv_cancel₀ hφ, one_mul]

/-- **6d. 固定点の個数**：#{x ∈ ℤ/N : a x = x} = gcd(N, (a − 1).val)。 -/
theorem card_fix_eq_gcd (N : ℕ) [NeZero N] (a : ZMod N) :
    (Finset.univ.filter (fun x : ZMod N => a * x = x)).card = Nat.gcd N (a - 1).val := by
  set b := a - 1 with hb
  have hker : ∀ x : ZMod N, a * x = x ↔ x ∈ (AddMonoidHom.mulLeft b).ker := by
    intro x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_mulLeft, hb, sub_mul, one_mul, sub_eq_zero]
  have hrange : (AddMonoidHom.mulLeft b).range = AddSubgroup.zmultiples b := by
    ext y
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(x.val : ℤ), ?_⟩
      rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
    · rintro ⟨k, rfl⟩
      exact ⟨(k : ZMod N), by rw [zsmul_eq_mul, mul_comm]⟩
  have hord : addOrderOf b = N / Nat.gcd N b.val := by
    conv_lhs => rw [← ZMod.natCast_zmod_val b]
    exact ZMod.addOrderOf_coe _ (NeZero.ne N)
  have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddMonoidHom.mulLeft b).ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (AddMonoidHom.mulLeft b)).toEquiv, hrange,
    Nat.card_zmultiples, Nat.card_zmod, hord] at hlag
  have hg : Nat.gcd N b.val ∣ N := Nat.gcd_dvd_left N b.val
  have hq : 0 < N / Nat.gcd N b.val :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hg)
      (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N)))
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.subtypeEquivRight hker)]
  refine Nat.eq_of_mul_eq_mul_left hq ?_
  rw [← hlag, Nat.div_mul_cancel hg]

/-- **6e. 指標つき Menon の恒等式**：Σ_{a ∈ (ℤ/N)ˣ} χ̄_N(a)·gcd(N, a − 1) = φ(N)·d(N/c)（χ は法 c の原始指標）。 -/
theorem menon_char (N c : ℕ) [NeZero N] [NeZero c] (hcN : c ∣ N) (χ : DirichletCharacter ℂ c)
    (hχ : χ.IsPrimitive) :
    ∑ a : (ZMod N)ˣ, liftc χ⁻¹ N (a : ZMod N) * (Nat.gcd N ((a : ZMod N) - 1).val : ℂ) =
      (Nat.totient N : ℂ) * ((N / c).divisors.card : ℂ) := by
  rw [← sum_liftc_card_fix N c hcN χ hχ]
  simp only [card_fix_eq_gcd]

/-- **6f. Menon の恒等式**：Σ_{a ∈ (ℤ/N)ˣ} gcd(N, a − 1) = φ(N)·d(N)。 -/
theorem menon (N : ℕ) [NeZero N] :
    ∑ a : (ZMod N)ˣ, Nat.gcd N ((a : ZMod N) - 1).val = Nat.totient N * N.divisors.card := by
  have e := menon_char N 1 (one_dvd N) 1 DirichletCharacter.isPrimitive_one_level_one
  simp only [inv_one, liftc_of_dvd _ (one_dvd N), map_one, MulChar.one_apply_coe, one_mul, Nat.div_one] at e
  exact_mod_cast e

end PAG.Part218

#print axioms PAG.Part218.sum_units_char
#print axioms PAG.Part218.liftc_inv
#print axioms PAG.Part218.liftc_mul_liftc_inv
#print axioms PAG.Part218.mul_memb
#print axioms PAG.Part218.dil
#print axioms PAG.Part218.dil_apply
#print axioms PAG.Part218.dil_one
#print axioms PAG.Part218.dil_dil
#print axioms PAG.Part218.inner_dil
#print axioms PAG.Part218.gket_unit_mul
#print axioms PAG.Part218.dil_gket
#print axioms PAG.Part218.dil_ketFam
#print axioms PAG.Part218.dil_kblock
#print axioms PAG.Part218.dil_of_mem_span
#print axioms PAG.Part218.blockProjL
#print axioms PAG.Part218.blockProjL_apply
#print axioms PAG.Part218.liftc_mul_eq_one_iff
#print axioms PAG.Part218.sum_dil_ketFam
#print axioms PAG.Part218.blockProjL_eq_sum_dil
#print axioms PAG.Part218.blockProj_eq_sum_dil
#print axioms PAG.Part218.dil_blockProj
#print axioms PAG.Part218.blockProj_dil
#print axioms PAG.Part218.comm_blockProj
#print axioms PAG.Part218.mem_span_iff_dil
#print axioms PAG.Part218.dil_radial_mul
#print axioms PAG.Part218.dil_radial_conv
#print axioms PAG.Part218.radial_mul_blockProj
#print axioms PAG.Part218.radial_conv_blockProj
#print axioms PAG.Part218.dft_dil
#print axioms PAG.Part218.radial_iff_dil
#print axioms PAG.Part218.radial_iff_mem_span
#print axioms PAG.Part218.shellAlg
#print axioms PAG.Part218.shellAlg_comm_dil
#print axioms PAG.Part218.shellAlg_comm_blockProj
#print axioms PAG.Part218.dind_mul_gket_of_rad
#print axioms PAG.Part218.dind_mul_kblock_of_rad
#print axioms PAG.Part218.geps_conv_kblock_of_rad
#print axioms PAG.Part218.kblock_ne_zero
#print axioms PAG.Part218.shellAlg_eigen_of_rad
#print axioms PAG.Part218.shellAlg_ne_of_rad
#print axioms PAG.Part218.trace_blockProjL
#print axioms PAG.Part218.trace_dil
#print axioms PAG.Part218.sum_liftc_card_fix
#print axioms PAG.Part218.card_fix_eq_gcd
#print axioms PAG.Part218.menon_char
#print axioms PAG.Part218.menon
