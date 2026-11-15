/-
  PAG 2.0 Part 237（2026-11-04）— 有限個の積を PiTensorProduct の形で：⨂_{p ∣ N} X_{p^{v_p(N)}} ≅ X_N
  Part 236 の積は 2 因子を右から重ねた形（tensAlg）だった。ここでは Mathlib の PiTensorProduct（⨂[ℂ] i, A_i）で、
  番号の付け方によらない形に書く。
  1. 一般論：異なる番号の像が可換な代数準同型の族 φ_i : A_i → B（CommFam）から準同型 ⨂_i A_i → B（tpLift、
     ⊗_i x_i ↦ Π_i φ_i(x_i)、積は Finset.noncommProd）。A_i への制限は φ_i（tpLift_single）で、それで一意（eq_tpLift）、
     像 = ⨆_i range φ_i（range_tpLift）、dim ⨂_i A_i = Π_i dim A_i（finrank_tp）。部分代数 T が φ_i の像で生成され
     dim T = Π_i dim A_i なら ⨂_i A_i ≅ T（tpEquiv）
  2. 位置によらない局所作用素 ι^N_a（locOp。a ∣ N、gcd(a, N/a) = 1）：ℤ/N ≅ ℤ/a × ℤ/(N/a)（crtE）で第 1 座標に作用させたもの。
     陽な式 (ι^N_a(S)F)(x) = S(y ↦ F(lift(x, y)))(x mod a)（locOp_apply）、法の付け替えと両立（endCongr_locOp）
  3. リストの局所作用素（Part 236 の locHom）は位置によらない：ι_k = ι^N_{a_k}（locHom_eq_locOp）。並べ方を変えても
     同じ法・同じ因子なら一致（locHom_congr、prodList_perm）
  4. リストの形：⨂_k X_{a_k} ≅ X_N（piTensEquiv。純テンソルは局所作用素の積に写る）
  5. 素因数で番号をつけた形：互いに素な a, b の ι^N_a と ι^N_b は可換（commute_locOp）、
     X_N = ⨆_{p ∣ N} ι^N_{p^{v_p}}(X_{p^{v_p}})（eq_iSup_ppFam）、⨂_{p ∣ N} X_{p^{v_p(N)}} ≅ X_N（piPrimeEquiv。
     局所作用素で一意に決まる piPrimeEquiv_unique）、局所の基底の積は X_N の基底（ppBasis・ppBasis_apply）
  6. A・A′・Z・dilComm・End 全体の場合（shellAlgPiEquiv・fullCommAlgPiEquiv・centerAlgPiEquiv・dilCommAlgPiEquiv・endPiEquiv）
-/
import PAG240
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

namespace PAG.Part241

open PAG.Part218 PAG.Part226 PAG.Part232 PAG.Part233 PAG.Part234 PAG.Part235 PAG.Part240
open scoped TensorProduct

/-! ### 1. 像が可換な準同型の族と PiTensorProduct からの準同型 -/

section TP

/-- 可換性の仮定の形の付け替え（Finset.noncommProd に渡す形）。 -/
theorem pwComm {κ M : Type*} [Monoid M] {f : κ → M} (h : ∀ i j, i ≠ j → Commute (f i) (f j))
    (s : Finset κ) : (s : Set κ).Pairwise (Function.onFun Commute f) :=
  fun i _ j _ hij => h i j hij

variable {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra ℂ (A i)]
  {B : Type*} [Semiring B] [Algebra ℂ B]

/-- 異なる番号の像が可換な代数準同型の族。 -/
def CommFam (φ : ∀ i, A i →ₐ[ℂ] B) : Prop :=
  ∀ i j, i ≠ j → ∀ (x : A i) (y : A j), Commute (φ i x) (φ j y)

variable [Fintype ι]

/-- 積 Π_i φ_i(x_i)（像が可換なので順序によらない）。 -/
noncomputable def tpProd (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (x : ∀ i, A i) : B :=
  Finset.univ.noncommProd (fun i => φ i (x i)) (pwComm (fun i j hij => hφ i j hij (x i) (x j)) _)

/-- **1a.** 番号 i の因子を先頭に出す：Π = φ_i(x_i)·Π_{j ≠ i}。 -/
theorem tpProd_eq_mul_erase [DecidableEq ι] (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ)
    (x : ∀ i, A i) (i : ι) :
    tpProd φ hφ x = φ i (x i) * (Finset.univ.erase i).noncommProd (fun j => φ j (x j))
      (pwComm (fun j k hjk => hφ j k hjk (x j) (x k)) _) :=
  (Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) (fun j => φ j (x j)) _).symm

/-- **1b.** 1 か所を取り替えた族の積。 -/
theorem tpProd_update [DecidableEq ι] (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (m : ∀ i, A i)
    (i : ι) (v : A i) :
    tpProd φ hφ (Function.update m i v) = φ i v * (Finset.univ.erase i).noncommProd
      (fun j => φ j (m j)) (pwComm (fun j k hjk => hφ j k hjk (m j) (m k)) _) := by
  rw [tpProd_eq_mul_erase φ hφ _ i, Function.update_self]
  congr 1
  exact Finset.noncommProd_congr rfl
    (fun j hj => by simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]) _

/-- 多重線形写像 x ↦ Π_i φ_i(x_i)。 -/
noncomputable def tpProdML (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) : MultilinearMap ℂ A B where
  toFun := tpProd φ hφ
  map_update_add' m i x y := by
    rw [tpProd_update, tpProd_update, tpProd_update, map_add, add_mul]
  map_update_smul' m i c x := by
    rw [tpProd_update, tpProd_update, map_smul, smul_mul_assoc]

/-- **1c.** Π_i φ_i(1) = 1。 -/
theorem tpProd_one (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) : tpProd φ hφ 1 = 1 := by
  unfold tpProd
  rw [Finset.noncommProd_eq_pow_card Finset.univ (fun i => φ i ((1 : ∀ i, A i) i)) _ 1
    (fun i _ => by simp only [Pi.one_apply, map_one]), one_pow]

/-- **1d.** 積を保つ。 -/
theorem tpProd_mul (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (x y : ∀ i, A i) :
    tpProd φ hφ (x * y) = tpProd φ hφ x * tpProd φ hφ y := by
  refine Eq.trans ?_ (Finset.noncommProd_mul_distrib (s := Finset.univ) (fun i => φ i (x i))
    (fun i => φ i (y i)) (fun i _ j _ hij => hφ i j hij (x i) (x j))
    (fun i _ j _ hij => hφ i j hij (y i) (y j)) (fun i _ j _ hij => hφ i j hij (y i) (x j)))
  exact Finset.noncommProd_congr rfl (fun i _ => by simp only [Pi.mul_apply, map_mul]) _

/-- **1c′.** 多重線形写像の形の 1c。 -/
theorem tpProdML_one (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) : tpProdML φ hφ 1 = 1 :=
  tpProd_one φ hφ

/-- **1d′.** 多重線形写像の形の 1d。 -/
theorem tpProdML_mul (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (x y : ∀ i, A i) :
    tpProdML φ hφ (x * y) = tpProdML φ hφ x * tpProdML φ hφ y :=
  tpProd_mul φ hφ x y

/-- 像が可換な準同型の族から得られる準同型 ⨂_i A_i → B（⊗_i x_i ↦ Π_i φ_i(x_i)）。 -/
noncomputable def tpLift (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) : (⨂[ℂ] i, A i) →ₐ[ℂ] B :=
  PiTensorProduct.liftAlgHom (tpProdML φ hφ) (tpProdML_one φ hφ) (tpProdML_mul φ hφ)

/-- **1e.** 純テンソルの行き先：⊗_i x_i ↦ Π_i φ_i(x_i)。 -/
theorem tpLift_tprod (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (x : ∀ i, A i) :
    tpLift φ hφ (PiTensorProduct.tprod ℂ x) = tpProd φ hφ x := by
  rw [tpLift, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod]
  rfl

/-- **1f.** 1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1 ↦ φ_i(a)。 -/
theorem tpLift_single [DecidableEq ι] (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (i : ι) (a : A i) :
    tpLift φ hφ (PiTensorProduct.singleAlgHom i a) = φ i a := by
  rw [PiTensorProduct.singleAlgHom_apply, tpLift_tprod, tpProd_eq_mul_erase φ hφ _ i]
  have h1 : ∀ j ∈ Finset.univ.erase i, φ j ((MonoidHom.mulSingle A i a) j) = 1 := fun j hj => by
    rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), map_one]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 h1, one_pow, mul_one, MonoidHom.mulSingle_apply,
    Pi.mulSingle_eq_same]

/-- **1g.** 一意性：各 A_i への制限が φ_i になる準同型 ⨂_i A_i → B は tpLift だけ
  （番号の付け方は使わない）。 -/
theorem eq_tpLift [DecidableEq ι] (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ)
    (F : (⨂[ℂ] i, A i) →ₐ[ℂ] B) (hF : ∀ i (a : A i), F (PiTensorProduct.singleAlgHom i a) = φ i a) :
    F = tpLift φ hφ :=
  PiTensorProduct.algHom_ext fun i =>
    AlgHom.ext fun a => (hF i a).trans (tpLift_single φ hφ i a).symm

/-- **1h.** 像 = φ_i の像が生成する部分代数：range = ⨆_i range φ_i。 -/
theorem range_tpLift (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) :
    (tpLift φ hφ).range = ⨆ i, (φ i).range := by
  classical
  apply le_antisymm
  · intro y hy
    obtain ⟨z, rfl⟩ := (AlgHom.mem_range _).mp hy
    clear hy
    induction z using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      rw [map_smul, tpLift_tprod]
      refine Subalgebra.smul_mem _ ?_ r
      exact Submonoid.noncommProd_mem (⨆ i, (φ i).range).toSubmonoid Finset.univ
        (fun i => φ i (x i)) _
        (fun i _ => (le_iSup (fun i => (φ i).range) i) (AlgHom.mem_range_self (φ i) (x i)))
    | add x y hx hy =>
      rw [map_add]
      exact Subalgebra.add_mem _ hx hy
  · refine iSup_le fun i => ?_
    intro y hy
    obtain ⟨a, rfl⟩ := (AlgHom.mem_range _).mp hy
    exact ⟨PiTensorProduct.singleAlgHom i a, tpLift_single φ hφ i a⟩

end TP

section TPR

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Ring (A i)] [∀ i, Algebra ℂ (A i)]
  {B : Type*} [Ring B] [Algebra ℂ B]

/-- 有限次元の積は有限次元。 -/
instance finiteDimensional_tp [∀ i, FiniteDimensional ℂ (A i)] :
    FiniteDimensional ℂ (⨂[ℂ] i, A i) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun i => Module.finBasis ℂ (A i))

/-- **1i.** dim ⨂_i A_i = Π_i dim A_i。 -/
theorem finrank_tp [∀ i, FiniteDimensional ℂ (A i)] :
    Module.finrank ℂ (⨂[ℂ] i, A i) = ∏ i, Module.finrank ℂ (A i) := by
  classical
  rw [Module.finrank_eq_card_basis (Basis.piTensorProduct fun i => Module.finBasis ℂ (A i)),
    Fintype.card_pi]
  simp only [Fintype.card_fin]

/-- **1j.** 像の次元が Π dim A_i なら、像への制限は全単射。 -/
theorem tpLift_rangeRestrict_bijective [∀ i, FiniteDimensional ℂ (A i)] [FiniteDimensional ℂ B]
    (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ)
    (hdim : Module.finrank ℂ (tpLift φ hφ).range = ∏ i, Module.finrank ℂ (A i)) :
    Function.Bijective (tpLift φ hφ).rangeRestrict := by
  refine ⟨?_, (tpLift φ hφ).rangeRestrict_surjective⟩
  have hs : Function.Surjective (tpLift φ hφ).rangeRestrict.toLinearMap :=
    (tpLift φ hφ).rangeRestrict_surjective
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_tp.trans hdim.symm)).mpr hs

/-- **主定理（一般形）.** 部分代数 T が φ_i の像で生成され、dim T = Π_i dim A_i なら ⨂_i A_i ≅ T。 -/
noncomputable def tpEquiv [∀ i, FiniteDimensional ℂ (A i)] [FiniteDimensional ℂ B]
    (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (T : Subalgebra ℂ B) (hT : T = ⨆ i, (φ i).range)
    (hdim : Module.finrank ℂ T = ∏ i, Module.finrank ℂ (A i)) : (⨂[ℂ] i, A i) ≃ₐ[ℂ] T :=
  (AlgEquiv.ofBijective (tpLift φ hφ).rangeRestrict
    (tpLift_rangeRestrict_bijective φ hφ (by rw [range_tpLift, ← hT]; exact hdim))).trans
    (Subalgebra.equivOfEq _ _ ((range_tpLift φ hφ).trans hT.symm))

/-- **1k.** tpEquiv の純テンソルの行き先。 -/
theorem tpEquiv_tprod [∀ i, FiniteDimensional ℂ (A i)] [FiniteDimensional ℂ B]
    (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (T : Subalgebra ℂ B) (hT : T = ⨆ i, (φ i).range)
    (hdim : Module.finrank ℂ T = ∏ i, Module.finrank ℂ (A i)) (x : ∀ i, A i) :
    (tpEquiv φ hφ T hT hdim (PiTensorProduct.tprod ℂ x) : B) = tpProd φ hφ x :=
  tpLift_tprod φ hφ x

/-- **1l.** tpEquiv(1 ⊗ ⋯ ⊗ a ⊗ ⋯ ⊗ 1) = φ_i(a)。 -/
theorem tpEquiv_single [DecidableEq ι] [∀ i, FiniteDimensional ℂ (A i)] [FiniteDimensional ℂ B]
    (φ : ∀ i, A i →ₐ[ℂ] B) (hφ : CommFam φ) (T : Subalgebra ℂ B) (hT : T = ⨆ i, (φ i).range)
    (hdim : Module.finrank ℂ T = ∏ i, Module.finrank ℂ (A i)) (i : ι) (a : A i) :
    (tpEquiv φ hφ T hT hdim (PiTensorProduct.singleAlgHom i a) : B) = φ i a :=
  tpLift_single φ hφ i a

end TPR

/-! ### 2. 位置によらない局所作用素 -/

/-- 法の付け替え End(ℂ^{ℤ/M}) ≅ End(ℂ^{ℤ/N})（M = N）。 -/
noncomputable def endCongr {M N : ℕ} (h : M = N) :
    Module.End ℂ (ZMod M → ℂ) ≃ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) := by
  subst h; exact AlgEquiv.refl

/-- **2a.** 同じ法なら付け替えは恒等。 -/
theorem endCongr_rfl (M : ℕ) (T : Module.End ℂ (ZMod M → ℂ)) : endCongr (rfl : M = M) T = T := rfl

/-- 中国剰余定理 ℤ/N ≅ ℤ/a × ℤ/(N/a)（a ∣ N、gcd(a, N/a) = 1）。 -/
noncomputable def crtE (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) :
    ZMod N ≃+* ZMod a × ZMod (N / a) :=
  (ZMod.ringEquivCongr (Nat.mul_div_cancel' hd).symm).trans (ZMod.chineseRemainder hc)

/-- **2b.** 第 1 成分は x mod a。 -/
theorem crtE_fst (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) (x : ZMod N) :
    (crtE N a hd hc x).1 = ZMod.castHom hd (ZMod a) x := by
  have e : (RingHom.fst (ZMod a) (ZMod (N / a))).comp (crtE N a hd hc).toRingHom =
      ZMod.castHom hd (ZMod a) := RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod N →+* ZMod a => f x) e

/-- **2c.** c ∣ N/a なら（第 2 成分）mod c = x mod c。 -/
theorem castHom_crtE_snd (N a c : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) (hcd : c ∣ N / a)
    (x : ZMod N) : ZMod.castHom hcd (ZMod c) (crtE N a hd hc x).2 =
      ZMod.castHom (dvd_trans hcd (Nat.div_dvd_of_dvd hd)) (ZMod c) x := by
  have e : ((ZMod.castHom hcd (ZMod c)).comp (RingHom.snd (ZMod a) (ZMod (N / a)))).comp
      (crtE N a hd hc).toRingHom = ZMod.castHom (dvd_trans hcd (Nat.div_dvd_of_dvd hd)) (ZMod c) :=
    RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod N →+* ZMod c => f x) e

/-- 局所の持ち上げ：x の a 成分を y に取り替えた ℤ/N の元。 -/
noncomputable def liftF (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) (x : ZMod N)
    (y : ZMod a) : ZMod N :=
  (crtE N a hd hc).symm (y, (crtE N a hd hc x).2)

/-- **2d.** 持ち上げの a 成分は y。 -/
theorem castHom_liftF (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) (x : ZMod N)
    (y : ZMod a) : ZMod.castHom hd (ZMod a) (liftF N a hd hc x y) = y := by
  rw [← crtE_fst N a hd hc, liftF, RingEquiv.apply_symm_apply]

/-- **2e.** c ∣ N/a なら持ち上げの mod c は x と同じ。 -/
theorem castHom_liftF_of_dvd (N a c : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a))
    (hcd : c ∣ N / a) (x : ZMod N) (y : ZMod a) :
    ZMod.castHom (dvd_trans hcd (Nat.div_dvd_of_dvd hd)) (ZMod c) (liftF N a hd hc x y) =
      ZMod.castHom (dvd_trans hcd (Nat.div_dvd_of_dvd hd)) (ZMod c) x := by
  rw [← castHom_crtE_snd N a c hd hc hcd, ← castHom_crtE_snd N a c hd hc hcd, liftF,
    RingEquiv.apply_symm_apply]

/-- ℂ^{ℤ/N} ≅ ℂ^{ℤ/a × ℤ/(N/a)}（中国剰余定理による付け替え）。 -/
noncomputable def crtLinN (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) :
    (ZMod N → ℂ) ≃ₗ[ℂ] (ZMod a × ZMod (N / a) → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ (crtE N a hd hc).symm.toEquiv

/-- 位置によらない局所作用素 ι^N_a：End(ℂ^{ℤ/a}) → End(ℂ^{ℤ/N})（a ∣ N、gcd(a, N/a) = 1。
  ℤ/N ≅ ℤ/a × ℤ/(N/a) で第 1 座標に作用させたもの）。 -/
noncomputable def locOp (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a)) :
    Module.End ℂ (ZMod a → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  ((crtLinN N a hd hc).conjAlgEquiv ℂ).symm.toAlgHom.comp (leftHom a (N / a))

/-- **2f.** ι^N_a の値：(ι^N_a(S)F)(x) = S(y ↦ F(x の a 成分を y にしたもの))(x mod a)。 -/
theorem locOp_apply (N a : ℕ) (hd : a ∣ N) (hc : Nat.Coprime a (N / a))
    (S : Module.End ℂ (ZMod a → ℂ)) (F : ZMod N → ℂ) (x : ZMod N) :
    locOp N a hd hc S F x = S (fun y => F (liftF N a hd hc x y)) (ZMod.castHom hd (ZMod a) x) := by
  rw [← crtE_fst N a hd hc x]
  rfl

/-- **2g.** 法の付け替えと両立：M = N、a = b なら ι^N_b ∘ (付け替え) = (付け替え) ∘ ι^M_a。 -/
theorem endCongr_locOp {M N a b : ℕ} (hMN : M = N) (hab : a = b) (hd : a ∣ M)
    (hc : Nat.Coprime a (M / a)) (hd' : b ∣ N) (hc' : Nat.Coprime b (N / b))
    (S : Module.End ℂ (ZMod a → ℂ)) :
    endCongr hMN (locOp M a hd hc S) = locOp N b hd' hc' (endCongr hab S) := by
  subst hMN; subst hab; rfl

/-! ### 3. リストの局所作用素は位置によらない -/

/-- **3a.** gcd(a_k, N/a_k) = 1。 -/
theorem coprime_get_div : ∀ (l : List ℕ+) (_ : CoprimeList l) (k : Fin l.length),
    Nat.Coprime ((l.get k : ℕ+) : ℕ) (prodList l / ((l.get k : ℕ+) : ℕ))
  | a :: l, h, ⟨0, _⟩ => by
    show Nat.Coprime (a : ℕ) ((a : ℕ) * prodList l / (a : ℕ))
    rw [Nat.mul_div_cancel_left _ a.pos]
    exact h.head
  | b :: l, h, ⟨k + 1, hk⟩ => by
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have ih := coprime_get_div l h.tail ⟨k, hk'⟩
    have hd := get_dvd_prodList l ⟨k, hk'⟩
    show Nat.Coprime ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ) ((b : ℕ) * prodList l / ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ))
    rw [Nat.mul_div_assoc _ hd]
    exact Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right hd h.head).symm ih

/-- **3b.** j ≠ k なら gcd(a_j, a_k) = 1。 -/
theorem coprime_get_get (l : List ℕ+) (h : CoprimeList l) {j k : Fin l.length} (hjk : j ≠ k) :
    Nat.Coprime ((l.get j : ℕ+) : ℕ) ((l.get k : ℕ+) : ℕ) := by
  rcases lt_or_gt_of_ne (fun e : j.val = k.val => hjk (Fin.ext e)) with hlt | hlt
  · exact List.pairwise_iff_getElem.mp h j k j.2 k.2 hlt
  · exact (List.pairwise_iff_getElem.mp h k j k.2 j.2 hlt).symm

/-- **3c.** j ≠ k なら a_j ∣ N/a_k。 -/
theorem get_dvd_div (l : List ℕ+) (h : CoprimeList l) {j k : Fin l.length} (hjk : j ≠ k) :
    ((l.get j : ℕ+) : ℕ) ∣ prodList l / ((l.get k : ℕ+) : ℕ) := by
  have hdk := get_dvd_prodList l k
  have hdj := get_dvd_prodList l j
  rw [← Nat.mul_div_cancel' hdk] at hdj
  exact (coprime_get_get l h hjk).dvd_of_dvd_mul_left hdj

/-- **3d.** リストの持ち上げ lift_k は位置によらない持ち上げ（法 N、因子 a_k）に等しい。 -/
theorem liftL_eq_liftF (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length) (x : ZMod (prodList l))
    (y : ZMod ((l.get k : ℕ+) : ℕ)) :
    liftL l h k x y = liftF (prodList l) ((l.get k : ℕ+) : ℕ) (get_dvd_prodList l k)
      (coprime_get_div l h k) x y := by
  apply eq_of_castHom_eq l h
  intro j
  by_cases hjk : j = k
  · subst hjk
    rw [castHom_liftL, castHom_liftF]
  · rw [castHom_liftL_of_ne l h hjk, castHom_liftF_of_dvd (prodList l) ((l.get k : ℕ+) : ℕ)
      ((l.get j : ℕ+) : ℕ) (get_dvd_prodList l k) (coprime_get_div l h k) (get_dvd_div l h hjk)]

/-- **3e.** リストの局所作用素 ι_k = 位置によらない ι^N_{a_k}（N = prodList l）。 -/
theorem locHom_eq_locOp (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length) :
    locHom l h k = locOp (prodList l) ((l.get k : ℕ+) : ℕ) (get_dvd_prodList l k)
      (coprime_get_div l h k) := by
  refine AlgHom.ext fun S => LinearMap.ext fun F => funext fun x => ?_
  rw [locHom_apply, locOp_apply]
  simp only [liftL_eq_liftF]

/-- **3f.** 並べ替えたリストの積は同じ。 -/
theorem prodList_perm {l l' : List ℕ+} (h : l.Perm l') : prodList l = prodList l' := by
  rw [prodList_eq_prod, prodList_eq_prod]
  exact (h.map _).prod_eq

/-- **3g.** 局所作用素はリストの並べ方によらない：積が等しく同じ因子なら、法の付け替えで一致する。 -/
theorem locHom_congr (l l' : List ℕ+) (h : CoprimeList l) (h' : CoprimeList l') (k : Fin l.length)
    (k' : Fin l'.length) (hN : prodList l = prodList l')
    (hk : ((l.get k : ℕ+) : ℕ) = ((l'.get k' : ℕ+) : ℕ))
    (S : Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ)) :
    endCongr hN (locHom l h k S) = locHom l' h' k' (endCongr hk S) := by
  rw [locHom_eq_locOp, locHom_eq_locOp]
  exact endCongr_locOp hN hk _ _ _ _ S

/-! ### 4. ⨂_k X_{a_k} ≅ X_N（リスト） -/

section Fam

variable (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))

/-- 局所の族 ι_k|_{X_{a_k}}。 -/
noncomputable def locFam (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length) :
    ↥(X ((l.get k : ℕ+) : ℕ)) →ₐ[ℂ] Module.End ℂ (ZMod (prodList l) → ℂ) :=
  (locHom l h k).comp (X ((l.get k : ℕ+) : ℕ)).val

/-- **4a.** 局所の族の像は可換。 -/
theorem commFam_locFam (l : List ℕ+) (h : CoprimeList l) : CommFam (locFam X l h) :=
  fun _ _ hjk x y => by
    simp only [locFam, AlgHom.comp_apply, Subalgebra.coe_val]
    exact locHom_commute l h hjk _ _

/-- **4b.** 像は ι_k(X_{a_k})。 -/
theorem range_locFam (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length) :
    (locFam X l h k).range = (X ((l.get k : ℕ+) : ℕ)).map (locHom l h k) := by
  rw [locFam, AlgHom.range_comp, Subalgebra.range_val]

/-- **主定理（リスト）.** ⨂_k X_{a_k} ≅ X_N（N = Π a_k、⊗_k x_k ↦ Π_k ι_k(x_k)）。 -/
noncomputable def piTensEquiv (hX : CRTMul X) (l : List ℕ+) (h : CoprimeList l) :
    (⨂[ℂ] k : Fin l.length, ↥(X ((l.get k : ℕ+) : ℕ))) ≃ₐ[ℂ] ↥(X (prodList l)) :=
  tpEquiv (A := fun k => ↥(X ((l.get k : ℕ+) : ℕ))) (B := Module.End ℂ (ZMod (prodList l) → ℂ))
    (locFam X l h) (by exact commFam_locFam X l h) (X (prodList l))
    (by simp only [range_locFam]; exact eq_iSup_map_locHom X hX l h)
    (by rw [finrank_prodList X hX l h, ← Fin.prod_univ_fun_getElem]; rfl)

/-- **4c.** 純テンソルは局所作用素の積に写る。 -/
theorem piTensEquiv_tprod (hX : CRTMul X) (l : List ℕ+) (h : CoprimeList l)
    (S : ∀ k : Fin l.length, ↥(X ((l.get k : ℕ+) : ℕ))) :
    (piTensEquiv X hX l h (PiTensorProduct.tprod ℂ S) : Module.End ℂ (ZMod (prodList l) → ℂ)) =
      Finset.univ.noncommProd (fun k => locHom l h k (S k))
        (pwComm (fun _ _ hjk => locHom_commute l h hjk _ _) _) :=
  tpLift_tprod (locFam X l h) (commFam_locFam X l h) S

/-- **4d.** 1 ⊗ ⋯ ⊗ s ⊗ ⋯ ⊗ 1 ↦ ι_k(s)。 -/
theorem piTensEquiv_single (hX : CRTMul X) (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length)
    (s : ↥(X ((l.get k : ℕ+) : ℕ))) :
    (piTensEquiv X hX l h (PiTensorProduct.singleAlgHom k s) :
      Module.End ℂ (ZMod (prodList l) → ℂ)) = locHom l h k s :=
  tpLift_single (locFam X l h) (commFam_locFam X l h) k s

/-! ### 5. 素因数で番号をつけた形 ⨂_{p ∣ N} X_{p^{v_p(N)}} ≅ X_N -/

/-- **5a.** gcd(p^{v_p(N)}, N/p^{v_p(N)}) = 1。 -/
theorem coprime_ordProj (N : ℕ) {p : ℕ} (hp : p ∈ N.primeFactors) :
    Nat.Coprime (p ^ N.factorization p) (N / p ^ N.factorization p) :=
  (Nat.coprime_ordCompl (Nat.prime_of_mem_primeFactors hp) (Nat.mem_primeFactors.mp hp).2.2).pow_left _

/-- **5b.** p ∣ N なら p^{v_p(N)} は素冪のリストにある。 -/
theorem mem_ppList (N : ℕ) {p : ℕ} (hp : p ∈ N.primeFactors) : ppow N p ∈ ppList N :=
  List.mem_map.mpr ⟨p, (Finset.mem_sort _).mpr hp, rfl⟩

/-- **5c.** 素冪のリストの元は p^{v_p(N)}（p ∣ N）。 -/
theorem exists_of_mem_ppList (N : ℕ) {a : ℕ+} (ha : a ∈ ppList N) :
    ∃ p ∈ N.primeFactors, ppow N p = a := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact ⟨p, (Finset.mem_sort _).mp hp, rfl⟩

/-- **5d.** 付け替え（因子）：a = b なら ι^N_a(X_a) = ι^N_b(X_b)。 -/
theorem map_locOp_congr {N a b : ℕ} [NeZero a] [NeZero b] (hab : a = b) (hd : a ∣ N)
    (hc : Nat.Coprime a (N / a)) (hd' : b ∣ N) (hc' : Nat.Coprime b (N / b)) :
    (X a).map (locOp N a hd hc) = (X b).map (locOp N b hd' hc') := by
  subst hab; rfl

/-- **5e.** 付け替え（法）：M = N なら X_M = ⨆ ι^M_{a_k}(X_{a_k}) から X_N = ⨆ ι^N_{a_k}(X_{a_k})。 -/
theorem iSup_map_locOp_transport {M N : ℕ} [NeZero M] [NeZero N] (hMN : M = N) {κ : Type*}
    (a : κ → ℕ) [∀ k, NeZero (a k)] (hd : ∀ k, a k ∣ M) (hc : ∀ k, Nat.Coprime (a k) (M / a k))
    (hd' : ∀ k, a k ∣ N) (hc' : ∀ k, Nat.Coprime (a k) (N / a k))
    (H : X M = ⨆ k, (X (a k)).map (locOp M (a k) (hd k) (hc k))) :
    X N = ⨆ k, (X (a k)).map (locOp N (a k) (hd' k) (hc' k)) := by
  subst hMN; exact H

end Fam

/-- **5f.** 付け替え（可換性）：M = N、a = a′、b = b′ のとき、ι^M_a と ι^M_b の可換性から ι^N_{a′} と ι^N_{b′} の可換性。 -/
theorem commute_locOp_transport {M N a b a' b' : ℕ} (hMN : M = N) (ha : a = a') (hb : b = b')
    (hda : a ∣ M) (hca : Nat.Coprime a (M / a)) (hdb : b ∣ M) (hcb : Nat.Coprime b (M / b))
    (hda' : a' ∣ N) (hca' : Nat.Coprime a' (N / a')) (hdb' : b' ∣ N)
    (hcb' : Nat.Coprime b' (N / b'))
    (H : ∀ S T, Commute (locOp M a hda hca S) (locOp M b hdb hcb T)) :
    ∀ S T, Commute (locOp N a' hda' hca' S) (locOp N b' hdb' hcb' T) := by
  subst hMN; subst ha; subst hb; exact H

/-- **5g.** リストの 2 つの位置の局所作用素の可換性を、法 N（= prodList l）と因子 a, b の言葉に付け替える。 -/
theorem commute_locOp_of_list (l : List ℕ+) (h : CoprimeList l) {N : ℕ} (hN : prodList l = N)
    {j k : Fin l.length} (hjk : j ≠ k) {a b : ℕ} (ha : ((l.get j : ℕ+) : ℕ) = a)
    (hb : ((l.get k : ℕ+) : ℕ) = b) (hda : a ∣ N) (hca : Nat.Coprime a (N / a)) (hdb : b ∣ N)
    (hcb : Nat.Coprime b (N / b)) (S : Module.End ℂ (ZMod a → ℂ))
    (T : Module.End ℂ (ZMod b → ℂ)) :
    Commute (locOp N a hda hca S) (locOp N b hdb hcb T) := by
  have H : ∀ S T, Commute
      (locOp (prodList l) ((l.get j : ℕ+) : ℕ) (get_dvd_prodList l j) (coprime_get_div l h j) S)
      (locOp (prodList l) ((l.get k : ℕ+) : ℕ) (get_dvd_prodList l k) (coprime_get_div l h k) T) := by
    intro S T
    rw [← locHom_eq_locOp l h j, ← locHom_eq_locOp l h k]
    exact locHom_commute l h hjk S T
  exact commute_locOp_transport hN ha hb _ _ _ _ _ _ _ _ H S T

/-- **5h.** 互いに素な a, b（a, b ∣ N、gcd(a, N/a) = gcd(b, N/b) = 1）なら ι^N_a(S) と ι^N_b(T) は可換
  （3 項のリスト [a, b, N/(ab)] の局所作用素の可換性から付け替える）。 -/
theorem commute_locOp (N a b : ℕ) [NeZero N] (hda : a ∣ N) (hca : Nat.Coprime a (N / a))
    (hdb : b ∣ N) (hcb : Nat.Coprime b (N / b)) (hab : Nat.Coprime a b)
    (S : Module.End ℂ (ZMod a → ℂ)) (T : Module.End ℂ (ZMod b → ℂ)) :
    Commute (locOp N a hda hca S) (locOp N b hdb hcb T) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have ha : 0 < a := Nat.pos_of_dvd_of_pos hda hN
  have hb : 0 < b := Nat.pos_of_dvd_of_pos hdb hN
  have hdab : a * b ∣ N := hab.mul_dvd_of_dvd_of_dvd hda hdb
  have hc : 0 < N / (a * b) := Nat.div_pos (Nat.le_of_dvd hN hdab) (Nat.mul_pos ha hb)
  have hN' : a * b * (N / (a * b)) = N := Nat.mul_div_cancel' hdab
  have e1 : N / a = b * (N / (a * b)) :=
    Nat.div_eq_of_eq_mul_left ha (by
      calc N = a * b * (N / (a * b)) := hN'.symm
        _ = b * (N / (a * b)) * a := by ring)
  have e2 : N / b = a * (N / (a * b)) :=
    Nat.div_eq_of_eq_mul_left hb (by
      calc N = a * b * (N / (a * b)) := hN'.symm
        _ = a * (N / (a * b)) * b := by ring)
  have hac : Nat.Coprime a (N / (a * b)) := by
    rw [e1] at hca; exact hca.coprime_mul_left_right
  have hbc : Nat.Coprime b (N / (a * b)) := by
    rw [e2] at hcb; exact hcb.coprime_mul_left_right
  have hl : CoprimeList [Nat.toPNat a ha, Nat.toPNat b hb, Nat.toPNat (N / (a * b)) hc] := by
    refine List.pairwise_cons.mpr ⟨?_, List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hab
      · rcases List.mem_singleton.mp hy with rfl
        exact hac
    · intro y hy
      rcases List.mem_singleton.mp hy with rfl
      exact hbc
  have hprod : prodList [Nat.toPNat a ha, Nat.toPNat b hb, Nat.toPNat (N / (a * b)) hc] = N := by
    show a * (b * (N / (a * b) * 1)) = N
    rw [Nat.mul_one, ← Nat.mul_assoc, hN']
  exact commute_locOp_of_list _ hl hprod (j := ⟨0, by simp⟩) (k := ⟨1, by simp⟩)
    (fun e => Nat.zero_ne_one (congrArg Fin.val e)) rfl rfl hda hca hdb hcb S T

/-- **5i.** p ≠ q（p, q ∣ N）なら ι^N_{p^{v_p}}(S) と ι^N_{q^{v_q}}(T) は可換。 -/
theorem commute_locOp_pp (N : ℕ) [NeZero N] {p q : ℕ} (hp : p ∈ N.primeFactors)
    (hq : q ∈ N.primeFactors) (hpq : p ≠ q) (S : Module.End ℂ (ZMod (p ^ N.factorization p) → ℂ))
    (T : Module.End ℂ (ZMod (q ^ N.factorization q) → ℂ)) :
    Commute (locOp N (p ^ N.factorization p) (Nat.ordProj_dvd N p) (coprime_ordProj N hp) S)
      (locOp N (q ^ N.factorization q) (Nat.ordProj_dvd N q) (coprime_ordProj N hq) T) :=
  commute_locOp N _ _ _ _ _ _ (Nat.Coprime.pow _ _ ((Nat.coprime_primes
    (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)) S T

section Fam2

variable (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))

/-- 素因数ごとの局所の族 ι^N_{p^{v_p(N)}}|_{X_{p^{v_p(N)}}}（番号は p ∣ N）。 -/
noncomputable def ppFam (N : ℕ) [NeZero N] (p : N.primeFactors) :
    ↥(X ((p : ℕ) ^ N.factorization p)) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  (locOp N ((p : ℕ) ^ N.factorization p) (Nat.ordProj_dvd N p) (coprime_ordProj N p.2)).comp
    (X ((p : ℕ) ^ N.factorization p)).val

/-- **5j.** 素因数ごとの局所の族の像は可換。 -/
theorem commFam_ppFam (N : ℕ) [NeZero N] : CommFam (ppFam X N) := fun p q hpq x y => by
  simp only [ppFam, AlgHom.comp_apply, Subalgebra.coe_val]
  exact commute_locOp_pp N p.2 q.2 (fun e => hpq (Subtype.ext e)) _ _

/-- **5k.** 像は ι^N_{p^{v_p}}(X_{p^{v_p}})。 -/
theorem range_ppFam (N : ℕ) [NeZero N] (p : N.primeFactors) :
    (ppFam X N p).range = (X ((p : ℕ) ^ N.factorization p)).map
      (locOp N ((p : ℕ) ^ N.factorization p) (Nat.ordProj_dvd N p) (coprime_ordProj N p.2)) := by
  rw [ppFam, AlgHom.range_comp, Subalgebra.range_val]

/-- **5l.** X_N = ⨆_{p ∣ N} ι^N_{p^{v_p}}(X_{p^{v_p}})。 -/
theorem eq_iSup_ppFam (hX : CRTMul X) (N : ℕ) [NeZero N] : X N = ⨆ p, (ppFam X N p).range := by
  have H0 : X (prodList (ppList N)) = ⨆ k, (X (((ppList N).get k : ℕ+) : ℕ)).map
      (locOp (prodList (ppList N)) (((ppList N).get k : ℕ+) : ℕ) (get_dvd_prodList _ k)
        (coprime_get_div _ (coprimeList_ppList N) k)) := by
    refine (eq_iSup_map_locHom X hX (ppList N) (coprimeList_ppList N)).trans ?_
    simp only [locHom_eq_locOp]
  have H := iSup_map_locOp_transport X (prodList_ppList N)
    (fun k => (((ppList N).get k : ℕ+) : ℕ))
    (fun k => get_dvd_prodList _ k) (fun k => coprime_get_div _ (coprimeList_ppList N) k)
    (fun k => (get_dvd_prodList _ k).trans (dvd_of_eq (prodList_ppList N)))
    (fun k => by
      have := coprime_get_div _ (coprimeList_ppList N) k
      rwa [prodList_ppList N] at this) H0
  rw [H]
  apply le_antisymm
  · refine iSup_le fun k => ?_
    obtain ⟨p, hp, hpk⟩ := exists_of_mem_ppList N (List.get_mem _ k)
    refine le_trans (le_of_eq ?_) (le_iSup _ (⟨p, hp⟩ : N.primeFactors))
    rw [range_ppFam]
    exact map_locOp_congr X (congrArg PNat.val hpk).symm _ _ _ _
  · refine iSup_le fun p => ?_
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp (mem_ppList N p.2)
    refine le_trans (le_of_eq ?_) (le_iSup _ k)
    rw [range_ppFam]
    exact map_locOp_congr X (congrArg PNat.val hk).symm _ _ _ _

/-- **5m.** dim X_N = Π_{p ∣ N} dim X_{p^{v_p(N)}}（番号は N.primeFactors）。 -/
theorem finrank_pp (hX : CRTMul X) (N : ℕ) [NeZero N] :
    Module.finrank ℂ (X N) =
      ∏ p : N.primeFactors, Module.finrank ℂ (X ((p : ℕ) ^ N.factorization p)) := by
  rw [finrank_eq_prod_primeFactors X hX N]
  exact (Finset.prod_coe_sort N.primeFactors
    (fun p => Module.finrank ℂ (X (p ^ N.factorization p)))).symm

/-- **主定理（素因数）.** ⨂_{p ∣ N} X_{p^{v_p(N)}} ≅ X_N（⊗_p x_p ↦ Π_p ι^N_{p^{v_p}}(x_p)、番号の付け方によらない）。 -/
noncomputable def piPrimeEquiv (hX : CRTMul X) (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(X ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ] ↥(X N) :=
  tpEquiv (A := fun p : N.primeFactors => ↥(X ((p : ℕ) ^ N.factorization p)))
    (B := Module.End ℂ (ZMod N → ℂ)) (ppFam X N) (by exact commFam_ppFam X N) (X N)
    (by exact eq_iSup_ppFam X hX N) (by exact finrank_pp X hX N)

/-- **5n.** 純テンソルの行き先。 -/
theorem piPrimeEquiv_tprod (hX : CRTMul X) (N : ℕ) [NeZero N]
    (S : ∀ p : N.primeFactors, ↥(X ((p : ℕ) ^ N.factorization p))) :
    (piPrimeEquiv X hX N (PiTensorProduct.tprod ℂ S) : Module.End ℂ (ZMod N → ℂ)) =
      Finset.univ.noncommProd (fun p : N.primeFactors => locOp N ((p : ℕ) ^ N.factorization p)
        (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) (S p))
        (pwComm (fun p q hpq => commute_locOp_pp N p.2 q.2 (fun e => hpq (Subtype.ext e)) _ _) _) :=
  tpLift_tprod (ppFam X N) (commFam_ppFam X N) S

/-- **5o.** 1 ⊗ ⋯ ⊗ s ⊗ ⋯ ⊗ 1（p の位置）↦ ι^N_{p^{v_p}}(s)。 -/
theorem piPrimeEquiv_single (hX : CRTMul X) (N : ℕ) [NeZero N] (p : N.primeFactors)
    (s : ↥(X ((p : ℕ) ^ N.factorization p))) :
    (piPrimeEquiv X hX N (PiTensorProduct.singleAlgHom p s) : Module.End ℂ (ZMod N → ℂ)) =
      locOp N ((p : ℕ) ^ N.factorization p) (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) s :=
  tpLift_single (ppFam X N) (commFam_ppFam X N) p s

/-- **5p.** 一意性：⨂_{p ∣ N} X_{p^{v_p}} からの準同型で、p の位置の 1 ⊗ ⋯ ⊗ s ⊗ ⋯ ⊗ 1 を ι^N_{p^{v_p}}(s) に
  写すものは piPrimeEquiv だけ（番号の付け方を使わない特徴づけ）。 -/
theorem piPrimeEquiv_unique (hX : CRTMul X) (N : ℕ) [NeZero N]
    (F : (⨂[ℂ] p : N.primeFactors, ↥(X ((p : ℕ) ^ N.factorization p))) →ₐ[ℂ]
      Module.End ℂ (ZMod N → ℂ))
    (hF : ∀ (p : N.primeFactors) (s : ↥(X ((p : ℕ) ^ N.factorization p))),
      F (PiTensorProduct.singleAlgHom p s) =
        locOp N ((p : ℕ) ^ N.factorization p) (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) s)
    (z : ⨂[ℂ] p : N.primeFactors, ↥(X ((p : ℕ) ^ N.factorization p))) :
    F z = (piPrimeEquiv X hX N z : Module.End ℂ (ZMod N → ℂ)) := by
  rw [eq_tpLift (ppFam X N) (commFam_ppFam X N) F hF]
  rfl

/-- 局所の基底の積による X_N の基底（b_p は X_{p^{v_p}} の基底）。 -/
noncomputable def ppBasis (hX : CRTMul X) (N : ℕ) [NeZero N] {κ : N.primeFactors → Type*}
    (b : ∀ p : N.primeFactors, Module.Basis (κ p) ℂ ↥(X ((p : ℕ) ^ N.factorization p))) :
    Module.Basis (∀ p, κ p) ℂ ↥(X N) :=
  (Basis.piTensorProduct b).map (piPrimeEquiv X hX N).toLinearEquiv

/-- **5q.** 基底の元は局所の基底の積：b(q) = Π_p ι^N_{p^{v_p}}(b_p(q_p))。 -/
theorem ppBasis_apply (hX : CRTMul X) (N : ℕ) [NeZero N] {κ : N.primeFactors → Type*}
    (b : ∀ p : N.primeFactors, Module.Basis (κ p) ℂ ↥(X ((p : ℕ) ^ N.factorization p)))
    (q : ∀ p, κ p) :
    (ppBasis X hX N b q : Module.End ℂ (ZMod N → ℂ)) =
      Finset.univ.noncommProd (fun p : N.primeFactors => locOp N ((p : ℕ) ^ N.factorization p)
        (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) (b p (q p)))
        (pwComm (fun p p' hpp' => commute_locOp_pp N p.2 p'.2 (fun e => hpp' (Subtype.ext e)) _ _) _) := by
  rw [ppBasis, Module.Basis.map_apply, Basis.piTensorProduct_apply]
  exact piPrimeEquiv_tprod X hX N _

end Fam2

/-! ### 6. 具体的な族 -/

/-- **6a.** A_N ≅ ⨂_{p ∣ N} A_{p^{v_p(N)}}（殻の射影が生成する代数）。 -/
noncomputable def shellAlgPiEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(shellAlg ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ] ↥(shellAlg N) :=
  piPrimeEquiv shellAlg crtMul_shellAlg N

/-- **6b.** A′_N ≅ ⨂_{p ∣ N} A′_{p^{v_p(N)}}（A の可換子）。 -/
noncomputable def fullCommAlgPiEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(fullCommAlg ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ]
      ↥(fullCommAlg N) :=
  piPrimeEquiv fullCommAlg crtMul_fullCommAlg N

/-- **6c.** Z_N ≅ ⨂_{p ∣ N} Z_{p^{v_p(N)}}（A′ の中心）。 -/
noncomputable def centerAlgPiEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(centerAlg ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ] ↥(centerAlg N) :=
  piPrimeEquiv centerAlg crtMul_centerAlg N

/-- **6d.** dilComm_N ≅ ⨂_{p ∣ N} dilComm_{p^{v_p(N)}}（A と単数倍の可換子）。 -/
noncomputable def dilCommAlgPiEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(dilCommAlg ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ]
      ↥(dilCommAlg N) :=
  piPrimeEquiv dilCommAlg crtMul_dilCommAlg N

/-- **6e.** End(ℂ^{ℤ/N}) ≅ ⨂_{p ∣ N} End(ℂ^{ℤ/p^{v_p(N)}})（因子は End 全体 = topAlg）。 -/
noncomputable def endPiEquiv (N : ℕ) [NeZero N] :
    (⨂[ℂ] p : N.primeFactors, ↥(topAlg ((p : ℕ) ^ N.factorization p))) ≃ₐ[ℂ]
      Module.End ℂ (ZMod N → ℂ) :=
  (piPrimeEquiv topAlg crtMul_topAlg N).trans Subalgebra.topEquiv

/-- **6f.** End の場合の純テンソルの行き先：⊗_p S_p ↦ Π_p ι^N_{p^{v_p}}(S_p)。 -/
theorem endPiEquiv_tprod (N : ℕ) [NeZero N]
    (S : ∀ p : N.primeFactors, ↥(topAlg ((p : ℕ) ^ N.factorization p))) :
    endPiEquiv N (PiTensorProduct.tprod ℂ S) =
      Finset.univ.noncommProd (fun p : N.primeFactors => locOp N ((p : ℕ) ^ N.factorization p)
        (Nat.ordProj_dvd N p) (coprime_ordProj N p.2) (S p))
        (pwComm (fun p q hpq => commute_locOp_pp N p.2 q.2 (fun e => hpq (Subtype.ext e)) _ _) _) :=
  piPrimeEquiv_tprod topAlg crtMul_topAlg N S

end PAG.Part241

#print axioms PAG.Part241.pwComm
#print axioms PAG.Part241.CommFam
#print axioms PAG.Part241.tpProd
#print axioms PAG.Part241.tpProd_eq_mul_erase
#print axioms PAG.Part241.tpProd_update
#print axioms PAG.Part241.tpProdML
#print axioms PAG.Part241.tpProd_one
#print axioms PAG.Part241.tpProd_mul
#print axioms PAG.Part241.tpProdML_one
#print axioms PAG.Part241.tpProdML_mul
#print axioms PAG.Part241.tpLift
#print axioms PAG.Part241.tpLift_tprod
#print axioms PAG.Part241.tpLift_single
#print axioms PAG.Part241.eq_tpLift
#print axioms PAG.Part241.range_tpLift
#print axioms PAG.Part241.finiteDimensional_tp
#print axioms PAG.Part241.finrank_tp
#print axioms PAG.Part241.tpLift_rangeRestrict_bijective
#print axioms PAG.Part241.tpEquiv
#print axioms PAG.Part241.tpEquiv_tprod
#print axioms PAG.Part241.tpEquiv_single
#print axioms PAG.Part241.endCongr
#print axioms PAG.Part241.endCongr_rfl
#print axioms PAG.Part241.crtE
#print axioms PAG.Part241.crtE_fst
#print axioms PAG.Part241.castHom_crtE_snd
#print axioms PAG.Part241.liftF
#print axioms PAG.Part241.castHom_liftF
#print axioms PAG.Part241.castHom_liftF_of_dvd
#print axioms PAG.Part241.crtLinN
#print axioms PAG.Part241.locOp
#print axioms PAG.Part241.locOp_apply
#print axioms PAG.Part241.endCongr_locOp
#print axioms PAG.Part241.coprime_get_div
#print axioms PAG.Part241.coprime_get_get
#print axioms PAG.Part241.get_dvd_div
#print axioms PAG.Part241.liftL_eq_liftF
#print axioms PAG.Part241.locHom_eq_locOp
#print axioms PAG.Part241.prodList_perm
#print axioms PAG.Part241.locHom_congr
#print axioms PAG.Part241.locFam
#print axioms PAG.Part241.commFam_locFam
#print axioms PAG.Part241.range_locFam
#print axioms PAG.Part241.piTensEquiv
#print axioms PAG.Part241.piTensEquiv_tprod
#print axioms PAG.Part241.piTensEquiv_single
#print axioms PAG.Part241.coprime_ordProj
#print axioms PAG.Part241.mem_ppList
#print axioms PAG.Part241.exists_of_mem_ppList
#print axioms PAG.Part241.map_locOp_congr
#print axioms PAG.Part241.iSup_map_locOp_transport
#print axioms PAG.Part241.commute_locOp_transport
#print axioms PAG.Part241.commute_locOp_of_list
#print axioms PAG.Part241.commute_locOp
#print axioms PAG.Part241.commute_locOp_pp
#print axioms PAG.Part241.ppFam
#print axioms PAG.Part241.commFam_ppFam
#print axioms PAG.Part241.range_ppFam
#print axioms PAG.Part241.eq_iSup_ppFam
#print axioms PAG.Part241.finrank_pp
#print axioms PAG.Part241.piPrimeEquiv
#print axioms PAG.Part241.piPrimeEquiv_tprod
#print axioms PAG.Part241.piPrimeEquiv_single
#print axioms PAG.Part241.piPrimeEquiv_unique
#print axioms PAG.Part241.ppBasis
#print axioms PAG.Part241.ppBasis_apply
#print axioms PAG.Part241.shellAlgPiEquiv
#print axioms PAG.Part241.fullCommAlgPiEquiv
#print axioms PAG.Part241.centerAlgPiEquiv
#print axioms PAG.Part241.dilCommAlgPiEquiv
#print axioms PAG.Part241.endPiEquiv
#print axioms PAG.Part241.endPiEquiv_tprod
