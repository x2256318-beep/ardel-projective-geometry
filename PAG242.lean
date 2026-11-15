/-
  PAG 2.0 Part 238（2026-11-05）— 素冪 q^k の場合の A・A′ の具体的な形と、素冪ごとのテンソル積の形
  N = q^k（q は素数）で、中心の番号の集合 S、層の大きさ n_p、原始指標の数 m(c) を具体的に書き、
  Part 225・223 の行列環への分解（shellAlgMatrixEquiv・fullCommMatrixEquiv）を具体的な形にする。
  Part 237 の素因数ごとの同型（piPrimeEquiv）と合わせて、一般の N を素冪の場合の積として書く。
  1. 道具：成分を切り離す同型（piSplitAlgEquiv）、1 × 1 行列 ≅ ℂ（matUniqueEquiv）、
     成分ごとの同型の PiTensorProduct（tpCongr、Part 237 の tpLift で作る）
  2. 基準の番号 p₀ = (1, 1)（baseIdx）：W_{p₀} = 動径関数の空間（mem_refLayer_base_iff）、dim = d(N)（finrank_refLayer_base）、
     制限 A_N → End(動径関数) は全射（radialHom_surjective）。どの N でも A は動径関数の空間に M_{d(N)}(ℂ) として作用する
  3. S(q^k) = {(1, 1)} ∪ {(q^γ, q^δ) : 1 ≤ γ、γ + δ ≤ k、(q, γ) ≠ (2, 1)}（mem_centerIdx_primePow）、
     n_(1,1) = k + 1、ほかは n_p = 1（card_layerDivs_primePow）、#S = 1 + k(k+1)/2 − [q = 2]k（card_centerIdx_primePow）
  4. A_{q^k} ≅ M_{k+1}(ℂ) × ℂ^{S′}（shellAlgPrimePowEquiv、S′ = S \ {(1, 1)}）、A′_N ≅ ℂ × Π_{p ∈ S′} M_{m(c_p)}(ℂ)
     （fullCommSplitEquiv）、次元の系
  5. 一般の N：A_N ≅ ⨂_{p ∣ N} (M_{v_p(N)+1}(ℂ) × ℂ^{S′(p^{v_p(N)})})（shellAlgPrimeTensorEquiv）、A′_N・Z_N も素冪ごとの
     テンソル積（fullCommPrimeTensorEquiv・centerAlgPrimeTensorEquiv）、End(ℂ^{ℤ/N}) ≅ ⨂_{p ∣ N} End(ℂ^{ℤ/p^{v_p(N)}})
     （endTensorEquiv、因子は End そのもの。Part 237 の endPiEquiv の因子は ⊤ の型だった）、純テンソルの行き先（局所作用素の積）
-/
import PAG241

namespace PAG.Part242

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241
open scoped TensorProduct

/-! ### 1. 道具：成分を切り離す同型、1 × 1 行列、PiTensorProduct の成分ごとの同型 -/

/-- 番号 i₀ の成分を切り離す：Π_i B_i ≅ B_{i₀} × Π_{i ≠ i₀} B_i（代数の同型）。 -/
def piSplitAlgEquiv {ι : Type*} [DecidableEq ι] (i₀ : ι) (B : ι → Type*) [∀ i, Semiring (B i)]
    [∀ i, Algebra ℂ (B i)] : (Π i, B i) ≃ₐ[ℂ] B i₀ × Π i : {i // i ≠ i₀}, B i :=
  { Equiv.piSplitAt i₀ B with
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

/-- **1a.** 切り離した値。 -/
theorem piSplitAlgEquiv_apply {ι : Type*} [DecidableEq ι] (i₀ : ι) (B : ι → Type*) [∀ i, Semiring (B i)]
    [∀ i, Algebra ℂ (B i)] (f : Π i, B i) :
    piSplitAlgEquiv i₀ B f = (f i₀, fun j : {i // i ≠ i₀} => f j) := rfl

/-- 1 × 1 行列の代数 ≅ ℂ（番号の型がただ 1 つの元を持つ）。 -/
noncomputable def matUniqueEquiv (m : Type*) [Unique m] [Fintype m] [DecidableEq m] :
    Matrix m m ℂ ≃ₐ[ℂ] ℂ :=
  AlgEquiv.ofLinearEquiv
    { toFun := fun M => M default default
      invFun := fun r => Matrix.of fun _ _ => r
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun M => by
        ext i j
        rw [Subsingleton.elim i default, Subsingleton.elim j default]
        rfl
      right_inv := fun _ => rfl }
    (Matrix.one_apply_eq default)
    (fun M M' => by
      show (M * M') default default = M default default * M' default default
      rw [Matrix.mul_apply, Fintype.sum_unique])

/-- **1b.** 値は (default, default) 成分。 -/
theorem matUniqueEquiv_apply (m : Type*) [Unique m] [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) :
    matUniqueEquiv m M = M default default := rfl

section TPC

variable {ι : Type*} [DecidableEq ι] {A B : ι → Type*} [∀ i, Semiring (A i)]
  [∀ i, Algebra ℂ (A i)] [∀ i, Semiring (B i)] [∀ i, Algebra ℂ (B i)]

/-- **1c.** 異なる番号の 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1 は可換。 -/
theorem commute_singleAlgHom {i j : ι} (hij : i ≠ j) (x : A i) (y : A j) :
    Commute (PiTensorProduct.singleAlgHom (R := ℂ) (A := A) i x) (PiTensorProduct.singleAlgHom j y) := by
  rw [PiTensorProduct.singleAlgHom_apply, PiTensorProduct.singleAlgHom_apply]
  exact Commute.tprod (Pi.mulSingle_commute hij x y)

/-- **1c′.** 成分ごとの同型と 1 ⊗ ⋯ ⊗ x ⊗ ⋯ ⊗ 1 の合成は、像が可換な族（Part 237 の CommFam）。 -/
theorem commFam_single_equiv (e : ∀ i, A i ≃ₐ[ℂ] B i) :
    CommFam (fun i => (PiTensorProduct.singleAlgHom (R := ℂ) (A := B) i).comp (e i).toAlgHom) :=
  fun _ _ hij _ _ => commute_singleAlgHom hij _ _

variable [Fintype ι]

/-- 成分ごとの代数の同型 e_i : A_i ≅ B_i から ⨂_i A_i ≅ ⨂_i B_i（Part 237 の tpLift で作る）。 -/
noncomputable def tpCongr (e : ∀ i, A i ≃ₐ[ℂ] B i) : (⨂[ℂ] i, A i) ≃ₐ[ℂ] ⨂[ℂ] i, B i :=
  AlgEquiv.ofAlgHom
    (tpLift (fun i => (PiTensorProduct.singleAlgHom i).comp (e i).toAlgHom) (commFam_single_equiv e))
    (tpLift (fun i => (PiTensorProduct.singleAlgHom i).comp (e i).symm.toAlgHom)
      (commFam_single_equiv fun i => (e i).symm))
    (PiTensorProduct.algHom_ext fun i => AlgHom.ext fun b => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, tpLift_single]
      exact congrArg _ ((e i).apply_symm_apply b))
    (PiTensorProduct.algHom_ext fun i => AlgHom.ext fun a => by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, tpLift_single]
      exact congrArg _ ((e i).symm_apply_apply a))

/-- **1d.** 純テンソルの行き先：⊗_i x_i ↦ ⊗_i e_i(x_i)。 -/
theorem tpCongr_tprod (e : ∀ i, A i ≃ₐ[ℂ] B i) (x : ∀ i, A i) :
    tpCongr e (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (fun i => e i (x i)) := by
  show tpLift _ _ (PiTensorProduct.tprod ℂ x) = _
  rw [tpLift_tprod, tpProd]
  symm
  calc PiTensorProduct.tprod ℂ (fun i => e i (x i))
      = PiTensorProduct.tprod ℂ (Finset.univ.noncommProd (fun i => Pi.mulSingle i (e i (x i)))
          (pwComm (fun i j hij => Pi.mulSingle_commute hij _ _) _)) :=
        (congrArg (PiTensorProduct.tprod ℂ) (Finset.noncommProd_mulSingle (fun i => e i (x i)))).symm
    _ = Finset.univ.noncommProd (fun i => PiTensorProduct.tprod ℂ (Pi.mulSingle i (e i (x i))))
          (pwComm (fun i j hij => Commute.tprod (Pi.mulSingle_commute hij _ _)) _) :=
        PiTensorProduct.tprod_noncommProd _ _ _
    _ = _ := Finset.noncommProd_congr rfl (fun i _ => rfl) _

/-- **1e.** 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1 の行き先。 -/
theorem tpCongr_single (e : ∀ i, A i ≃ₐ[ℂ] B i) (i : ι) (a : A i) :
    tpCongr e (PiTensorProduct.singleAlgHom i a) = PiTensorProduct.singleAlgHom i (e i a) :=
  tpLift_single _ _ i a

end TPC

/-! ### 2. 基準の番号 (1, 1) と動径関数の成分（一般の N） -/

/-- **2a.** (1, 1) ∈ S(N)。 -/
theorem one_mem_centerIdx (N : ℕ) [NeZero N] : (⟨1, 1⟩ : Σ _ : ℕ, ℕ) ∈ centerIdx N := by
  rw [mem_centerIdx]
  refine ⟨Nat.mem_divisors.mpr ⟨one_dvd N, NeZero.ne N⟩, ?_, ?_⟩
  · show 0 < primCount 1
    rw [primCount_one]
    exact one_pos
  · rw [mem_layerIdx]
    exact ⟨Nat.mem_divisors.mpr ⟨one_dvd _, by rw [Nat.div_one]; exact NeZero.ne N⟩, fun _ _ h => h⟩

/-- 基準の番号 p₀ = (1, 1)（導手 1、層 1）。 -/
def baseIdx (N : ℕ) [NeZero N] : centerIdx N := ⟨⟨1, 1⟩, one_mem_centerIdx N⟩

/-- 残りの番号 S′ = S \ {(1, 1)}。 -/
abbrev restIdx (N : ℕ) [NeZero N] : Type := {p : centerIdx N // p ≠ baseIdx N}

/-- **2b.** 導手 1・層 1 の層の約数はすべての約数：S_1 = {v ∣ L}。 -/
theorem layerDivs_one_one (L : ℕ) : layerDivs 1 1 L = L.divisors := by
  classical
  ext v
  unfold layerDivs
  rw [Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, v, (one_mul v).symm, Nat.coprime_one_right v⟩⟩

/-- **2c.** n_{p₀} = dim W_{p₀} = d(N)（約数の個数）。 -/
theorem finrank_refLayer_base (N : ℕ) [NeZero N] :
    Module.finrank ℂ (refLayer N (baseIdx N)) = N.divisors.card := by
  rw [finrank_refLayer]
  show (layerDivs 1 1 (N / 1)).card = _
  rw [layerDivs_one_one, Nat.div_one]

/-- **2d.** 法 1 の指標で、層 1 の成分 W_{1,χ}(1) は動径関数の空間。 -/
theorem mem_layerPart_one_one (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ 1) (f : ZMod N → ℂ) :
    f ∈ layerPart N 1 χ 1 ↔ Radial f := by
  obtain rfl : χ = 1 := DirichletCharacter.level_one χ
  rw [mem_layerPart, radial_iff_mem_span]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun x hx => absurd ⟨x.val, (one_mul _).symm, Nat.coprime_one_right _⟩ hx⟩

/-- **2e.** W_{p₀} = 動径関数の空間（単数倍で不変な関数）。 -/
theorem mem_refLayer_base_iff (N : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    f ∈ refLayer N (baseIdx N) ↔ Radial f :=
  mem_layerPart_one_one N _ f

/-- 動径関数の空間への制限 A_N → End(W_{p₀})（W_{p₀} = 動径関数の空間、dim = d(N)）。 -/
noncomputable def radialHom (N : ℕ) [NeZero N] :
    shellAlg N →ₐ[ℂ] Module.End ℂ (refLayer N (baseIdx N)) :=
  (Pi.evalAlgHom ℂ (fun p : centerIdx N => Module.End ℂ (refLayer N p)) (baseIdx N)).comp
    (shellAlgEquiv N).toAlgHom

/-- **2f.** radialHom は制限：(radialHom T) g = T g。 -/
theorem radialHom_apply (N : ℕ) [NeZero N] (T : shellAlg N) (g : refLayer N (baseIdx N)) :
    (radialHom N T g : ZMod N → ℂ) = (T : Module.End ℂ (ZMod N → ℂ)) g := rfl

/-- **2g.** 制限 A_N → End(動径関数) は全射（A は動径関数の空間に全行列環 M_{d(N)}(ℂ) として作用する）。 -/
theorem radialHom_surjective (N : ℕ) [NeZero N] : Function.Surjective (radialHom N) := by
  classical
  intro S
  obtain ⟨T, hT⟩ := (shellAlgEquiv N).surjective
    (Pi.single (M := fun p : centerIdx N => Module.End ℂ (refLayer N p)) (baseIdx N) S)
  refine ⟨T, ?_⟩
  show (shellAlgEquiv N T) (baseIdx N) = S
  rw [hT, Pi.single_eq_same]

/-! ### 3. 素冪 q^k の番号の集合 S(q^k) と層の大きさ -/

/-- **3a.** S(q^k) の具体形：(c, d) = (1, 1)、または (q^γ, q^δ)（1 ≤ γ、γ + δ ≤ k、(q, γ) ≠ (2, 1)）。 -/
theorem mem_centerIdx_primePow {q : ℕ} (hq : q.Prime) (k : ℕ) (p : Σ _ : ℕ, ℕ) :
    p ∈ centerIdx (q ^ k) ↔ (p.1 = 1 ∧ p.2 = 1) ∨
      ∃ γ δ : ℕ, 1 ≤ γ ∧ γ + δ ≤ k ∧ ¬ (q = 2 ∧ γ = 1) ∧ p.1 = q ^ γ ∧ p.2 = q ^ δ := by
  obtain ⟨c, d⟩ := p
  have hqk : q ^ k ≠ 0 := pow_ne_zero _ hq.ne_zero
  rw [mem_centerIdx]
  show c ∈ (q ^ k).divisors ∧ 0 < primCount c ∧ d ∈ layerIdx c (q ^ k / c) ↔ _
  constructor
  · rintro ⟨hc, hm, hd⟩
    obtain ⟨γ, hγk, rfl⟩ := (Nat.dvd_prime_pow hq).mp (Nat.dvd_of_mem_divisors hc)
    rw [Nat.pow_div hγk hq.pos, mem_layerIdx] at hd
    obtain ⟨hdL, hrad⟩ := hd
    obtain ⟨δ, hδ, rfl⟩ := (Nat.dvd_prime_pow hq).mp (Nat.dvd_of_mem_divisors hdL)
    rcases Nat.eq_zero_or_pos γ with rfl | hγ
    · left
      have hδ0 : δ = 0 := by
        by_contra hδ0
        have h1 := hrad q hq (dvd_pow_self q hδ0)
        rw [pow_zero] at h1
        exact hq.one_lt.ne' (Nat.dvd_one.mp h1)
      subst hδ0
      exact ⟨pow_zero q, pow_zero q⟩
    · right
      refine ⟨γ, δ, hγ, by omega, ?_, rfl, rfl⟩
      exact (primCount_prime_pow_pos_iff hq hγ).mp hm
  · rintro (⟨rfl, rfl⟩ | ⟨γ, δ, hγ, hγδ, hq2, rfl, rfl⟩)
    · refine ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hqk⟩, by rw [primCount_one]; exact one_pos, ?_⟩
      rw [mem_layerIdx]
      exact ⟨Nat.mem_divisors.mpr ⟨one_dvd _, by rw [Nat.div_one]; exact hqk⟩, fun _ _ h => h⟩
    · refine ⟨Nat.mem_divisors.mpr ⟨pow_dvd_pow q (by omega), hqk⟩,
        (primCount_prime_pow_pos_iff hq hγ).mpr hq2, ?_⟩
      rw [Nat.pow_div (by omega) hq.pos, mem_layerIdx]
      refine ⟨Nat.mem_divisors.mpr ⟨pow_dvd_pow q (by omega), pow_ne_zero _ hq.ne_zero⟩, ?_⟩
      intro r hr hrd
      have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow hrd)
      rw [hrq]
      exact dvd_pow_self q (by omega)

/-- **3b.** S(q^k) では c = 1 なら d = 1。 -/
theorem snd_eq_one_of_fst_eq_one {q : ℕ} (hq : q.Prime) (k : ℕ) {p : Σ _ : ℕ, ℕ}
    (hp : p ∈ centerIdx (q ^ k)) (h1 : p.1 = 1) : p.2 = 1 := by
  rcases (mem_centerIdx_primePow hq k p).mp hp with ⟨-, h⟩ | ⟨γ, δ, hγ, -, -, hc, -⟩
  · exact h
  · exfalso
    rw [h1] at hc
    have := Nat.one_lt_pow (by omega : γ ≠ 0) hq.one_lt
    omega

/-- **3c.** 層の大きさ：n_(c,d) = k + 1（c = 1）、1（c ≠ 1）。 -/
theorem card_layerDivs_primePow {q : ℕ} (hq : q.Prime) (k : ℕ) {p : Σ _ : ℕ, ℕ}
    (hp : p ∈ centerIdx (q ^ k)) :
    (layerDivs p.1 p.2 (q ^ k / p.1)).card = if p.1 = 1 then k + 1 else 1 := by
  obtain ⟨hc, -, hd⟩ := (mem_centerIdx (q ^ k) p).mp hp
  have hqk : q ^ k ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hcN := Nat.dvd_of_mem_divisors hc
  have hc0 : p.1 ≠ 0 := ne_zero_of_dvd_ne_zero hqk hcN
  have hL : q ^ k / p.1 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hqk) hcN) (Nat.pos_of_ne_zero hc0)).ne'
  rw [card_layerDivs hL hd]
  split_ifs with h1
  · rw [h1, Nat.div_one]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.primeFactors_prime_pow (by omega) hq]
      rw [Finset.filter_true_of_mem (fun r hr h => by
          rw [Finset.mem_singleton] at hr
          rw [hr] at h
          exact hq.one_lt.ne' (Nat.dvd_one.mp h)),
        Finset.prod_singleton, Nat.factorization_pow, Finsupp.smul_apply, hq.factorization_self,
        smul_eq_mul, mul_one]
  · refine Finset.prod_eq_one fun r hr => ?_
    exfalso
    rw [Finset.mem_filter] at hr
    obtain ⟨hr1, hr2⟩ := hr
    have hrp := Nat.prime_of_mem_primeFactors hr1
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hrp hq).mp
      (hrp.dvd_of_dvd_pow (dvd_trans (Nat.dvd_of_mem_primeFactors hr1) (Nat.div_dvd_of_dvd hcN)))
    obtain ⟨γ, -, hγ⟩ := (Nat.dvd_prime_pow hq).mp hcN
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      exact h1 (by rw [hγ, pow_zero])
    exact hr2 (by rw [hrq, hγ]; exact dvd_pow_self q hγ0)

/-- **3d.** #S(q^k) = 1 + k(k+1)/2 − [q = 2]k（k ≥ 1）。 -/
theorem card_centerIdx_primePow {q : ℕ} (hq : q.Prime) {k : ℕ} (hk : 1 ≤ k) :
    (centerIdx (q ^ k)).card = 1 + k * (k + 1) / 2 - (if q = 2 then k else 0) := by
  have : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have h1 : (centerIdx (q ^ k)).card = Module.finrank ℂ (fullCommCenter (q ^ k)) := by
    rw [center_eq_span, finrank_span_eq_card (centralElt_linearIndependent _), Fintype.card_coe]
  rw [h1, finrank_fullCommCenter_eq_prod, Nat.primeFactors_prime_pow (by omega) hq,
    Finset.prod_singleton, Nat.factorization_pow, Finsupp.smul_apply, hq.factorization_self,
    smul_eq_mul, mul_one]

/-- **3e.** dim W_{p₀} = k + 1（N = q^k）。 -/
theorem finrank_refLayer_base_primePow {q : ℕ} (hq : q.Prime) (k : ℕ) [NeZero (q ^ k)] :
    Module.finrank ℂ (refLayer (q ^ k) (baseIdx (q ^ k))) = k + 1 := by
  rw [finrank_refLayer_base, Nat.divisors_prime_pow hq, Finset.card_map, Finset.card_range]

/-- **3f.** p ≠ p₀ なら dim W_p = 1（N = q^k）。 -/
theorem finrank_refLayer_rest {q : ℕ} (hq : q.Prime) (k : ℕ) [NeZero (q ^ k)] (p : restIdx (q ^ k)) :
    Module.finrank ℂ (refLayer (q ^ k) p.1) = 1 := by
  rw [finrank_refLayer, card_layerDivs_primePow hq k p.1.2]
  split_ifs with h1
  · exfalso
    apply p.2
    exact Subtype.ext (Sigma.ext h1 (heq_of_eq (snd_eq_one_of_fst_eq_one hq k p.1.2 h1)))
  · rfl

/-- **3g.** #S′(q^k) = k(k+1)/2 − [q = 2]k（k ≥ 1）。 -/
theorem card_restIdx_primePow {q : ℕ} (hq : q.Prime) {k : ℕ} (hk : 1 ≤ k) [NeZero (q ^ k)] :
    Fintype.card (restIdx (q ^ k)) = k * (k + 1) / 2 - (if q = 2 then k else 0) := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_coe,
    card_centerIdx_primePow hq hk]
  have hP : 2 * k ≤ k * (k + 1) := by nlinarith
  generalize k * (k + 1) = P at hP ⊢
  split_ifs <;> omega

/-! ### 4. 素冪の A・A′ の具体的な形 -/

/-- 法 1 の原始指標はただ 1 つ（自明な指標）。 -/
noncomputable instance uniquePrimOne : Unique (Prim 1) where
  default := ⟨1, DirichletCharacter.isPrimitive_one_level_one⟩
  uniq χ := Subtype.ext (DirichletCharacter.level_one χ.1)

/-- **主定理 1.** A_{q^k} ≅ M_{k+1}(ℂ) × ℂ^{S′}（動径関数の全行列環と、1 次元の成分のスカラー）。 -/
noncomputable def shellAlgPrimePowEquiv {q : ℕ} (hq : q.Prime) (k : ℕ) [NeZero (q ^ k)] :
    shellAlg (q ^ k) ≃ₐ[ℂ] Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ × (restIdx (q ^ k) → ℂ) :=
  (shellAlgMatrixEquiv (q ^ k)).trans <|
    (piSplitAlgEquiv (baseIdx (q ^ k)) _).trans <|
      AlgEquiv.prodCongr
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (finrank_refLayer_base_primePow hq k)))
        (AlgEquiv.piCongrRight fun p =>
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (finrank_refLayer_rest hq k p))).trans
            (matUniqueEquiv (Fin 1)))

/-- **主定理 2.** A′_N ≅ ℂ × Π_{p ∈ S′} M_{m(c_p)}(ℂ)（(1, 1) の成分は ℂ。N = q^k では S′ は 3a の (q^γ, q^δ)、
  成分は M_{m(q^γ)}(ℂ)）。 -/
noncomputable def fullCommSplitEquiv (N : ℕ) [NeZero N] :
    fullCommAlg N ≃ₐ[ℂ] ℂ × (Π p : restIdx N, Matrix (Prim p.1.1.1) (Prim p.1.1.1) ℂ) :=
  (fullCommMatrixEquiv N).symm.trans <|
    (piSplitAlgEquiv (baseIdx N) _).trans <|
      AlgEquiv.prodCongr (matUniqueEquiv (Prim 1)) AlgEquiv.refl

/-- **4a.** dim A_{q^k} = (k + 1)² + #S′。 -/
theorem finrank_shellAlg_primePow {q : ℕ} (hq : q.Prime) (k : ℕ) [NeZero (q ^ k)] :
    Module.finrank ℂ (shellAlg (q ^ k)) = (k + 1) ^ 2 + Fintype.card (restIdx (q ^ k)) := by
  rw [(shellAlgPrimePowEquiv hq k).toLinearEquiv.finrank_eq, Module.finrank_prod,
    Module.finrank_matrix, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Module.finrank_self]
  ring

/-- **4b.** dim A′_N = 1 + Σ_{p ∈ S′} m(c_p)²。 -/
theorem finrank_fullComm_split (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommAlg N) = 1 + ∑ p : restIdx N, Fintype.card (Prim p.1.1.1) ^ 2 := by
  rw [(fullCommSplitEquiv N).toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_self,
    Module.finrank_pi_fintype]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, sq]

/-! ### 5. 一般の N：素冪ごとのテンソル積 -/

/-- **主定理 3.** A_N ≅ ⨂_{p ∣ N} (M_{v_p(N)+1}(ℂ) × ℂ^{S′(p^{v_p(N)})})（Part 237 の piPrimeEquiv と主定理 1）。 -/
noncomputable def shellAlgPrimeTensorEquiv (N : ℕ) [NeZero N] :
    shellAlg N ≃ₐ[ℂ] ⨂[ℂ] p : N.primeFactors,
      (Matrix (Fin (N.factorization p + 1)) (Fin (N.factorization p + 1)) ℂ ×
        (restIdx ((p : ℕ) ^ N.factorization p) → ℂ)) :=
  (piPrimeEquiv shellAlg crtMul_shellAlg N).symm.trans
    (tpCongr fun p => shellAlgPrimePowEquiv (Nat.prime_of_mem_primeFactors p.2) (N.factorization p))

/-- **主定理 4.** A′_N ≅ ⨂_{p ∣ N} (ℂ × Π_{r ∈ S′(p^{v_p(N)})} M_{m(c_r)}(ℂ))。 -/
noncomputable def fullCommPrimeTensorEquiv (N : ℕ) [NeZero N] :
    fullCommAlg N ≃ₐ[ℂ] ⨂[ℂ] p : N.primeFactors,
      (ℂ × (Π r : restIdx ((p : ℕ) ^ N.factorization p), Matrix (Prim r.1.1.1) (Prim r.1.1.1) ℂ)) :=
  (piPrimeEquiv fullCommAlg crtMul_fullCommAlg N).symm.trans
    (tpCongr fun p => fullCommSplitEquiv ((p : ℕ) ^ N.factorization p))

/-- **主定理 5.** Z_N ≅ ⨂_{p ∣ N} ℂ^{S(p^{v_p(N)})}（A′ の中心。#S(p^k) = 1 + k(k+1)/2 − [p = 2]k は 3d）。 -/
noncomputable def centerAlgPrimeTensorEquiv (N : ℕ) [NeZero N] :
    centerAlg N ≃ₐ[ℂ] ⨂[ℂ] p : N.primeFactors, (centerIdx ((p : ℕ) ^ N.factorization p) → ℂ) :=
  (piPrimeEquiv centerAlg crtMul_centerAlg N).symm.trans
    (tpCongr fun p => (centerAlgEquiv ((p : ℕ) ^ N.factorization p)).symm)

/-- **主定理 6.** ⨂_{p ∣ N} End(ℂ^{ℤ/p^{v_p(N)}}) ≅ End(ℂ^{ℤ/N})（因子は End そのもの。Part 237 の endPiEquiv の因子 ⊤ を
  tpCongr と Subalgebra.topEquiv で End に付け替えたもの）。 -/
noncomputable def endTensorEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, Module.End ℂ (ZMod ((p : ℕ) ^ N.factorization p) → ℂ)) ≃ₐ[ℂ]
      Module.End ℂ (ZMod N → ℂ) :=
  (tpCongr fun p : N.primeFactors =>
    (Subalgebra.topEquiv (R := ℂ) (A := Module.End ℂ (ZMod ((p : ℕ) ^ N.factorization p) → ℂ))).symm).trans
    (endPiEquiv N)

/-- **5a.** End の場合の純テンソルの行き先：⊗_p S_p ↦ Π_p ι^N_{p^{v_p}}(S_p)（S_p は End(ℂ^{ℤ/p^{v_p}}) の任意の元）。 -/
theorem endTensorEquiv_tprod (N : ℕ) [NeZero N]
    (S : ∀ p : N.primeFactors, Module.End ℂ (ZMod ((p : ℕ) ^ N.factorization p) → ℂ)) :
    endTensorEquiv N (PiTensorProduct.tprod ℂ S) =
      Finset.univ.noncommProd (fun p : N.primeFactors => locOp N ((p : ℕ) ^ N.factorization p)
        (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) (S p))
        (pwComm (fun p q hpq => commute_locOp_pp N p.2 q.2 (fun e => hpq (Subtype.ext e)) _ _) _) := by
  have h2 : endTensorEquiv N (PiTensorProduct.tprod ℂ S) = endPiEquiv N ((tpCongr fun p : N.primeFactors =>
      (Subalgebra.topEquiv (R := ℂ) (A := Module.End ℂ (ZMod ((p : ℕ) ^ N.factorization p) → ℂ))).symm)
        (PiTensorProduct.tprod ℂ S)) := rfl
  rw [h2, tpCongr_tprod]
  exact endPiEquiv_tprod N _

/-- **5b.** 逆向きの純テンソルの行き先：⊗_p x_p ↦ Π_p ι^N_{p^{v_p}}(A_{p^{v_p}} の元)。 -/
theorem shellAlgPrimeTensorEquiv_symm_tprod (N : ℕ) [NeZero N]
    (x : ∀ p : N.primeFactors, Matrix (Fin (N.factorization p + 1)) (Fin (N.factorization p + 1)) ℂ ×
      (restIdx ((p : ℕ) ^ N.factorization p) → ℂ)) :
    ((shellAlgPrimeTensorEquiv N).symm (PiTensorProduct.tprod ℂ x) : Module.End ℂ (ZMod N → ℂ)) =
      Finset.univ.noncommProd (fun p : N.primeFactors => locOp N ((p : ℕ) ^ N.factorization p)
        (Nat.ordProj_dvd N p) (coprime_ordProj N p.2)
        ((shellAlgPrimePowEquiv (Nat.prime_of_mem_primeFactors p.2) (N.factorization p)).symm (x p)))
        (pwComm (fun p q hpq => commute_locOp_pp N p.2 q.2 (fun e => hpq (Subtype.ext e)) _ _) _) := by
  have h : (tpCongr fun p : N.primeFactors =>
      shellAlgPrimePowEquiv (Nat.prime_of_mem_primeFactors p.2) (N.factorization p)).symm
      (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ (fun p : N.primeFactors =>
        (shellAlgPrimePowEquiv (Nat.prime_of_mem_primeFactors p.2) (N.factorization p)).symm (x p)) := by
    rw [AlgEquiv.symm_apply_eq, tpCongr_tprod]
    simp only [AlgEquiv.apply_symm_apply]
  have h2 : (shellAlgPrimeTensorEquiv N).symm (PiTensorProduct.tprod ℂ x) =
      piPrimeEquiv shellAlg crtMul_shellAlg N ((tpCongr fun p : N.primeFactors =>
        shellAlgPrimePowEquiv (Nat.prime_of_mem_primeFactors p.2) (N.factorization p)).symm
          (PiTensorProduct.tprod ℂ x)) := rfl
  rw [h2, h]
  exact piPrimeEquiv_tprod shellAlg crtMul_shellAlg N _

end PAG.Part242

#print axioms PAG.Part242.piSplitAlgEquiv
#print axioms PAG.Part242.piSplitAlgEquiv_apply
#print axioms PAG.Part242.matUniqueEquiv
#print axioms PAG.Part242.matUniqueEquiv_apply
#print axioms PAG.Part242.commute_singleAlgHom
#print axioms PAG.Part242.commFam_single_equiv
#print axioms PAG.Part242.tpCongr
#print axioms PAG.Part242.tpCongr_tprod
#print axioms PAG.Part242.tpCongr_single
#print axioms PAG.Part242.one_mem_centerIdx
#print axioms PAG.Part242.baseIdx
#print axioms PAG.Part242.restIdx
#print axioms PAG.Part242.layerDivs_one_one
#print axioms PAG.Part242.finrank_refLayer_base
#print axioms PAG.Part242.mem_layerPart_one_one
#print axioms PAG.Part242.mem_refLayer_base_iff
#print axioms PAG.Part242.radialHom
#print axioms PAG.Part242.radialHom_apply
#print axioms PAG.Part242.radialHom_surjective
#print axioms PAG.Part242.mem_centerIdx_primePow
#print axioms PAG.Part242.snd_eq_one_of_fst_eq_one
#print axioms PAG.Part242.card_layerDivs_primePow
#print axioms PAG.Part242.card_centerIdx_primePow
#print axioms PAG.Part242.finrank_refLayer_base_primePow
#print axioms PAG.Part242.finrank_refLayer_rest
#print axioms PAG.Part242.card_restIdx_primePow
#print axioms PAG.Part242.uniquePrimOne
#print axioms PAG.Part242.shellAlgPrimePowEquiv
#print axioms PAG.Part242.fullCommSplitEquiv
#print axioms PAG.Part242.finrank_shellAlg_primePow
#print axioms PAG.Part242.finrank_fullComm_split
#print axioms PAG.Part242.shellAlgPrimeTensorEquiv
#print axioms PAG.Part242.fullCommPrimeTensorEquiv
#print axioms PAG.Part242.centerAlgPrimeTensorEquiv
#print axioms PAG.Part242.endTensorEquiv
#print axioms PAG.Part242.endTensorEquiv_tprod
#print axioms PAG.Part242.shellAlgPrimeTensorEquiv_symm_tprod
