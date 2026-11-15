/-
  PAG 2.0 Part 236（2026-10-31）— 有限個の互いに素な法の積：中国剰余定理の繰り返しと X_N ≅ X_{a₁} ⊗ (X_{a₂} ⊗ (⋯ ⊗ ℂ))
  互いに素な法のリスト l = [a₁, …, a_r]（ℕ+）、N = a₁·(a₂·(⋯·(a_r·1)))。中国剰余定理 ℤ/(a·P) ≅ ℤ/a × ℤ/P（Part 228 の C = crtConj、
  L・R）を先頭から繰り返す。
  0. 法のリストと積（prodList）、互いに素の条件（CoprimeList）、a_k ∣ N
  1. 局所作用素 ι_k（locHom）：ι_0(S) = C⁻¹(L(S))、ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))。単射、j ≠ k なら可換、ι_k(M_g) = M_{g∘(mod a_k)}、
     陽な式 (ι_k(S)F)(x) = S(y ↦ F(lift_k(x, y)))(x mod a_k)。lift_k(x, y) は第 k 座標が y、ほかの座標が x と同じ点で、ℤ/N の元は座標で決まる
  2. 中国剰余定理で分かれる部分代数の族 X（CRTMul：C(X_{ab}) = L(X_a) ⊔ R(X_b)）：ι_k(X_{a_k}) ⊆ X_N、X_N = ⨆_k ι_k(X_{a_k})、
     dim X_N = Π_k dim X_{a_k}、X_1 = ⊥
  3. 繰り返しのテンソル積 tensAlg と代数の同型 tensEquiv：X_{a₁} ⊗ (X_{a₂} ⊗ (⋯ ⊗ ℂ)) ≅ X_N、純テンソルは局所作用素の積に写る
  4. A（Part 228）・A′・Z（Part 229）・dilComm（Part 231）・End 全体（Part 230 の可換子の分解から）は CRTMul
  5. 素冪のリスト（素数の昇順）：X_N ≅ ⊗_{q^k ∥ N} X_{q^k}（ppEquiv）、End(ℂ^{ℤ/N}) ≅ ⊗ End(ℂ^{ℤ/q^k})（endPPEquiv）、
     dim X_N = Π_{q ∣ N} dim X_{q^{v_q(N)}}
-/
import PAG239

namespace PAG.Part240

open PAG.Part218 PAG.Part226 PAG.Part232 PAG.Part233 PAG.Part234 PAG.Part235
open scoped TensorProduct

/-! ### 0. 法のリスト -/

/-- 法のリスト l = [a₁, …, a_r]（ℕ+ の元）の積 a₁·(a₂·(⋯·(a_r·1)))。
  型の添字に現れるので、暗黙の引数の照合で展開されるようにする（`implicit_reducible`）。 -/
@[implicit_reducible] def prodList : List ℕ+ → ℕ
  | [] => 1
  | a :: l => (a : ℕ) * prodList l

/-- **0a.** 空のリストの積は 1。 -/
theorem prodList_nil : prodList [] = 1 := rfl

/-- **0b.** prodList (a :: l) = a·prodList l。 -/
theorem prodList_cons (a : ℕ+) (l : List ℕ+) : prodList (a :: l) = (a : ℕ) * prodList l := rfl

/-- **0c.** 積は正。 -/
theorem prodList_pos : ∀ l : List ℕ+, 0 < prodList l
  | [] => Nat.one_pos
  | a :: l => Nat.mul_pos a.pos (prodList_pos l)

/-- 積は 0 でない（インスタンス）。 -/
instance neZero_prodList (l : List ℕ+) : NeZero (prodList l) := ⟨(prodList_pos l).ne'⟩

/-- **0d.** prodList l は ℕ の積 (l.map (↑)).prod。 -/
theorem prodList_eq_prod : ∀ l : List ℕ+, prodList l = (l.map (fun a : ℕ+ => (a : ℕ))).prod
  | [] => rfl
  | a :: l => by rw [prodList_cons, prodList_eq_prod l, List.map_cons, List.prod_cons]

/-- リストの法が互いに素（すべての組）。 -/
def CoprimeList (l : List ℕ+) : Prop := l.Pairwise (fun a b : ℕ+ => Nat.Coprime (a : ℕ) (b : ℕ))

/-- **0e.** a がリストのすべての法と互いに素なら、積とも互いに素。 -/
theorem coprime_prodList {a : ℕ+} : ∀ {l : List ℕ+}, (∀ b ∈ l, Nat.Coprime (a : ℕ) (b : ℕ)) →
    Nat.Coprime (a : ℕ) (prodList l)
  | [], _ => Nat.coprime_one_right _
  | b :: l, h => Nat.Coprime.mul_right (h b (by simp)) (coprime_prodList fun c hc => h c (by simp [hc]))

/-- **0f.** 先頭の法と残りの積は互いに素。 -/
theorem CoprimeList.head {a : ℕ+} {l : List ℕ+} (h : CoprimeList (a :: l)) :
    Nat.Coprime (a : ℕ) (prodList l) :=
  coprime_prodList (List.pairwise_cons.mp h).1

/-- **0g.** 残りのリストも互いに素。 -/
theorem CoprimeList.tail {a : ℕ+} {l : List ℕ+} (h : CoprimeList (a :: l)) : CoprimeList l :=
  (List.pairwise_cons.mp h).2

/-- **0h.** k 番目の法は積を割り切る。 -/
theorem get_dvd_prodList : ∀ (l : List ℕ+) (k : Fin l.length), ((l.get k : ℕ+) : ℕ) ∣ prodList l
  | _ :: _, ⟨0, _⟩ => dvd_mul_right _ _
  | b :: l, ⟨k + 1, hk⟩ => dvd_mul_of_dvd_right (get_dvd_prodList l ⟨k, Nat.lt_of_succ_lt_succ hk⟩) (b : ℕ)

/-! ### 1. 局所作用素 -/

/-- 局所作用素 ι_k：End(ℂ^{ℤ/a_k}) → End(ℂ^{ℤ/N})（N = prodList l、代数の準同型）。
  ι_0(S) = C⁻¹(L(S))、ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))（C は Part 228 の crtConj、ι′ は残りのリストのもの）。 -/
noncomputable def locHom : (l : List ℕ+) → CoprimeList l → (k : Fin l.length) →
    Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ) →ₐ[ℂ] Module.End ℂ (ZMod (prodList l) → ℂ)
  | a :: l, h, ⟨0, _⟩ => (crtConj h.head).symm.toAlgHom.comp (leftHom (a : ℕ) (prodList l))
  | a :: l, h, ⟨k + 1, hk⟩ => (crtConj h.head).symm.toAlgHom.comp
      ((rightHom (a : ℕ) (prodList l)).comp (locHom l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩))

/-- **1a.** ι_0(S) = C⁻¹(L(S))。 -/
theorem locHom_zero (a : ℕ+) (l : List ℕ+) (h : CoprimeList (a :: l)) (S : Module.End ℂ (ZMod (a : ℕ) → ℂ)) :
    locHom (a :: l) h 0 S = (crtConj h.head).symm (leftOp (prodList l) S) := rfl

/-- **1b.** ι_{k+1}(T) = C⁻¹(R(ι′_k(T)))。 -/
theorem locHom_succ (a : ℕ+) (l : List ℕ+) (h : CoprimeList (a :: l)) (k : Fin l.length)
    (T : Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ)) :
    locHom (a :: l) h k.succ T = (crtConj h.head).symm (rightOp (a : ℕ) (locHom l h.tail k T)) := rfl

/-- **1c.** ι_k は単射。 -/
theorem locHom_injective : ∀ (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length),
    Function.Injective (locHom l h k)
  | a :: l, h, ⟨0, _⟩ => by
    intro S T hST
    exact leftHom_injective (a : ℕ) (prodList l) ((crtConj h.head).symm.injective hST)
  | a :: l, h, ⟨k + 1, hk⟩ => by
    intro S T hST
    exact locHom_injective l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (rightHom_injective (a : ℕ) (prodList l) ((crtConj h.head).symm.injective hST))

/-- **1d.** j ≠ k なら ι_j(S) と ι_k(T) は可換。 -/
theorem locHom_commute : ∀ (l : List ℕ+) (h : CoprimeList l) {j k : Fin l.length} (_ : j ≠ k)
    (S : Module.End ℂ (ZMod ((l.get j : ℕ+) : ℕ) → ℂ)) (T : Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ)),
    Commute (locHom l h j S) (locHom l h k T)
  | _ :: _, _, ⟨0, _⟩, ⟨0, _⟩, hjk, _, _ => (hjk rfl).elim
  | a :: l, h, ⟨0, _⟩, ⟨k + 1, hk⟩, _, S, T => by
    exact (leftOp_commute_rightOp S (locHom l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩ T)).map (crtConj h.head).symm
  | a :: l, h, ⟨j + 1, hj⟩, ⟨0, _⟩, _, S, T => by
    exact ((leftOp_commute_rightOp T (locHom l h.tail ⟨j, Nat.lt_of_succ_lt_succ hj⟩ S)).map
      (crtConj h.head).symm).symm
  | a :: l, h, ⟨j + 1, hj⟩, ⟨k + 1, hk⟩, hjk, S, T => by
    have hne : (⟨j, Nat.lt_of_succ_lt_succ hj⟩ : Fin l.length) ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := by
      intro e
      apply hjk
      rw [Fin.mk.injEq] at e ⊢
      omega
    exact ((locHom_commute l h.tail hne S T).map (rightHom (a : ℕ) (prodList l))).map (crtConj h.head).symm

/-- **1e.** C の第 1 成分は x mod a。 -/
theorem crt_fst_eq_castHom {a b : ℕ} (hab : Nat.Coprime a b) (x : ZMod (a * b)) :
    (ZMod.chineseRemainder hab x).1 = ZMod.castHom (dvd_mul_right a b) (ZMod a) x := by
  have e : (RingHom.fst (ZMod a) (ZMod b)).comp (ZMod.chineseRemainder hab).toRingHom =
      ZMod.castHom (dvd_mul_right a b) (ZMod a) := RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod (a * b) →+* ZMod a => f x) e

/-- **1f.** c ∣ b なら (C の第 2 成分) mod c = x mod c。 -/
theorem castHom_crt_snd {a b c : ℕ} (hab : Nat.Coprime a b) (hc : c ∣ b) (x : ZMod (a * b)) :
    ZMod.castHom hc (ZMod c) (ZMod.chineseRemainder hab x).2 =
      ZMod.castHom (dvd_trans hc (dvd_mul_left b a)) (ZMod c) x := by
  have e : ((ZMod.castHom hc (ZMod c)).comp (RingHom.snd (ZMod a) (ZMod b))).comp
      (ZMod.chineseRemainder hab).toRingHom = ZMod.castHom (dvd_trans hc (dvd_mul_left b a)) (ZMod c) :=
    RingHom.ext_zmod _ _
  exact congrArg (fun f : ZMod (a * b) →+* ZMod c => f x) e

/-- **1g.** 掛け算の作用素：ι_k(M_g) = M_{g ∘ (mod a_k)}。 -/
theorem locHom_mulLeft : ∀ (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length)
    (g : ZMod ((l.get k : ℕ+) : ℕ) → ℂ),
    locHom l h k (LinearMap.mulLeft ℂ g) =
      LinearMap.mulLeft ℂ (fun x => g (ZMod.castHom (get_dvd_prodList l k) _ x))
  | a :: l, h, ⟨0, _⟩, g => by
    show (crtConj h.head).symm (leftOp (prodList l) (LinearMap.mulLeft ℂ (g : ZMod (a : ℕ) → ℂ))) =
      LinearMap.mulLeft ℂ (fun x => g (ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ)) x))
    rw [AlgEquiv.symm_apply_eq]
    apply LinearMap.ext
    intro F
    funext p
    obtain ⟨y, rfl⟩ := (ZMod.chineseRemainder h.head).surjective p
    show g (ZMod.chineseRemainder h.head y).1 * F ((ZMod.chineseRemainder h.head y).1,
        (ZMod.chineseRemainder h.head y).2) =
      g (ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ))
          ((ZMod.chineseRemainder h.head).symm (ZMod.chineseRemainder h.head y))) *
        F (ZMod.chineseRemainder h.head ((ZMod.chineseRemainder h.head).symm (ZMod.chineseRemainder h.head y)))
    rw [RingEquiv.symm_apply_apply, ← crt_fst_eq_castHom h.head y]
  | a :: l, h, ⟨k + 1, hk⟩, g => by
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have hd := get_dvd_prodList l ⟨k, hk'⟩
    show (crtConj h.head).symm (rightOp (a : ℕ)
      (locHom l h.tail ⟨k, hk'⟩ (LinearMap.mulLeft ℂ (g : ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ) → ℂ)))) =
        LinearMap.mulLeft ℂ (fun x => g (ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ)))
          (ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ)) x))
    rw [locHom_mulLeft l h.tail ⟨k, hk'⟩ g, AlgEquiv.symm_apply_eq]
    apply LinearMap.ext
    intro F
    funext p
    obtain ⟨y, rfl⟩ := (ZMod.chineseRemainder h.head).surjective p
    show g (ZMod.castHom hd (ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ)) (ZMod.chineseRemainder h.head y).2) *
        F ((ZMod.chineseRemainder h.head y).1, (ZMod.chineseRemainder h.head y).2) =
      g (ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ))
          ((ZMod.chineseRemainder h.head).symm (ZMod.chineseRemainder h.head y))) *
        F (ZMod.chineseRemainder h.head ((ZMod.chineseRemainder h.head).symm (ZMod.chineseRemainder h.head y)))
    rw [RingEquiv.symm_apply_apply, castHom_crt_snd h.head hd y]

/-- 第 k 座標を y に取り替えた点 lift_k(x, y) ∈ ℤ/N（中国剰余定理を先頭から繰り返して戻す）。 -/
def liftL : (l : List ℕ+) → CoprimeList l → (k : Fin l.length) → ZMod (prodList l) →
    ZMod ((l.get k : ℕ+) : ℕ) → ZMod (prodList l)
  | _ :: _, h, ⟨0, _⟩, x, y => (ZMod.chineseRemainder h.head).symm (y, (ZMod.chineseRemainder h.head x).2)
  | _ :: l, h, ⟨k + 1, hk⟩, x, y => (ZMod.chineseRemainder h.head).symm
      ((ZMod.chineseRemainder h.head x).1,
        liftL l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩ (ZMod.chineseRemainder h.head x).2 y)

/-- **1h.** ι_k(S) の値：(ι_k(S) F)(x) = S(y ↦ F(lift_k(x, y)))(x mod a_k)（k 番目の座標にだけ S が作用する）。 -/
theorem locHom_apply : ∀ (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length)
    (S : Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ)) (F : ZMod (prodList l) → ℂ) (x : ZMod (prodList l)),
    locHom l h k S F x = S (fun y => F (liftL l h k x y)) (ZMod.castHom (get_dvd_prodList l k) _ x)
  | a :: l, h, ⟨0, _⟩, S, F, x => by
    show S (fun u => F ((ZMod.chineseRemainder h.head).symm (u, (ZMod.chineseRemainder h.head x).2)))
        (ZMod.chineseRemainder h.head x).1 =
      S (fun y => F ((ZMod.chineseRemainder h.head).symm (y, (ZMod.chineseRemainder h.head x).2)))
        (ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ)) x)
    rw [crt_fst_eq_castHom h.head]
  | a :: l, h, ⟨k + 1, hk⟩, S, F, x => by
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have hd := get_dvd_prodList l ⟨k, hk'⟩
    show locHom l h.tail ⟨k, hk'⟩ S
        (fun v => F ((ZMod.chineseRemainder h.head).symm ((ZMod.chineseRemainder h.head x).1, v)))
        (ZMod.chineseRemainder h.head x).2 =
      S (fun y => F ((ZMod.chineseRemainder h.head).symm ((ZMod.chineseRemainder h.head x).1,
          liftL l h.tail ⟨k, hk'⟩ (ZMod.chineseRemainder h.head x).2 y)))
        (ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ)) x)
    rw [locHom_apply l h.tail ⟨k, hk'⟩ S, castHom_crt_snd h.head hd x]
    rfl

/-- **1i.** lift_k(x, y) の第 k 座標（mod a_k）は y。 -/
theorem castHom_liftL : ∀ (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length) (x : ZMod (prodList l))
    (y : ZMod ((l.get k : ℕ+) : ℕ)), ZMod.castHom (get_dvd_prodList l k) _ (liftL l h k x y) = y
  | a :: l, h, ⟨0, _⟩, x, y => by
    show ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ))
      ((ZMod.chineseRemainder h.head).symm (y, (ZMod.chineseRemainder h.head x).2)) = y
    rw [← crt_fst_eq_castHom h.head, RingEquiv.apply_symm_apply]
  | a :: l, h, ⟨k + 1, hk⟩, x, y => by
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have hd := get_dvd_prodList l ⟨k, hk'⟩
    show ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨k, hk'⟩ : ℕ+) : ℕ))
      ((ZMod.chineseRemainder h.head).symm ((ZMod.chineseRemainder h.head x).1,
        liftL l h.tail ⟨k, hk'⟩ (ZMod.chineseRemainder h.head x).2 y)) = y
    rw [← castHom_crt_snd h.head hd, RingEquiv.apply_symm_apply]
    exact castHom_liftL l h.tail ⟨k, hk'⟩ _ y

/-- **1j.** j ≠ k なら lift_k(x, y) の第 j 座標は x の第 j 座標。 -/
theorem castHom_liftL_of_ne : ∀ (l : List ℕ+) (h : CoprimeList l) {j k : Fin l.length} (_ : j ≠ k)
    (x : ZMod (prodList l)) (y : ZMod ((l.get k : ℕ+) : ℕ)),
    ZMod.castHom (get_dvd_prodList l j) (ZMod ((l.get j : ℕ+) : ℕ)) (liftL l h k x y) =
      ZMod.castHom (get_dvd_prodList l j) (ZMod ((l.get j : ℕ+) : ℕ)) x
  | _ :: _, _, ⟨0, _⟩, ⟨0, _⟩, hjk, _, _ => (hjk rfl).elim
  | a :: l, h, ⟨0, _⟩, ⟨k + 1, hk⟩, _, x, y => by
    show ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ))
      ((ZMod.chineseRemainder h.head).symm ((ZMod.chineseRemainder h.head x).1,
        liftL l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩ (ZMod.chineseRemainder h.head x).2 y)) =
      ZMod.castHom (dvd_mul_right (a : ℕ) (prodList l)) (ZMod (a : ℕ)) x
    rw [← crt_fst_eq_castHom h.head, ← crt_fst_eq_castHom h.head, RingEquiv.apply_symm_apply]
  | a :: l, h, ⟨j + 1, hj⟩, ⟨0, _⟩, _, x, y => by
    have hj' : j < l.length := Nat.lt_of_succ_lt_succ hj
    have hd := get_dvd_prodList l ⟨j, hj'⟩
    show ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨j, hj'⟩ : ℕ+) : ℕ))
      ((ZMod.chineseRemainder h.head).symm (y, (ZMod.chineseRemainder h.head x).2)) =
      ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨j, hj'⟩ : ℕ+) : ℕ)) x
    rw [← castHom_crt_snd h.head hd, ← castHom_crt_snd h.head hd, RingEquiv.apply_symm_apply]
  | a :: l, h, ⟨j + 1, hj⟩, ⟨k + 1, hk⟩, hjk, x, y => by
    have hj' : j < l.length := Nat.lt_of_succ_lt_succ hj
    have hk' : k < l.length := Nat.lt_of_succ_lt_succ hk
    have hd := get_dvd_prodList l ⟨j, hj'⟩
    have hne : (⟨j, hj'⟩ : Fin l.length) ≠ ⟨k, hk'⟩ := by
      intro e
      apply hjk
      rw [Fin.mk.injEq] at e ⊢
      omega
    show ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨j, hj'⟩ : ℕ+) : ℕ))
      ((ZMod.chineseRemainder h.head).symm ((ZMod.chineseRemainder h.head x).1,
        liftL l h.tail ⟨k, hk'⟩ (ZMod.chineseRemainder h.head x).2 y)) =
      ZMod.castHom (dvd_trans hd (dvd_mul_left (prodList l) (a : ℕ))) (ZMod ((l.get ⟨j, hj'⟩ : ℕ+) : ℕ)) x
    rw [← castHom_crt_snd h.head hd, ← castHom_crt_snd h.head hd, RingEquiv.apply_symm_apply]
    exact castHom_liftL_of_ne l h.tail hne _ y

/-- **1k.** ℤ/N の元はすべての座標（mod a_k）で決まる（中国剰余定理の単射性を繰り返したもの）。 -/
theorem eq_of_castHom_eq : ∀ (l : List ℕ+) (_ : CoprimeList l) (u v : ZMod (prodList l)),
    (∀ k : Fin l.length, ZMod.castHom (get_dvd_prodList l k) (ZMod ((l.get k : ℕ+) : ℕ)) u =
      ZMod.castHom (get_dvd_prodList l k) (ZMod ((l.get k : ℕ+) : ℕ)) v) →
      u = v
  | [], _, u, v, _ => by
    have h1 : u.val < 1 := ZMod.val_lt u
    have h2 : v.val < 1 := ZMod.val_lt v
    exact ZMod.val_injective _ (by omega)
  | a :: l, h, u, v, huv => by
    apply (ZMod.chineseRemainder h.head).injective
    refine Prod.ext ?_ ?_
    · rw [crt_fst_eq_castHom, crt_fst_eq_castHom]
      exact huv 0
    · refine eq_of_castHom_eq l h.tail _ _ fun k => ?_
      rw [castHom_crt_snd h.head (get_dvd_prodList l k), castHom_crt_snd h.head (get_dvd_prodList l k)]
      exact huv k.succ

/-! ### 2. 中国剰余定理で分かれる部分代数の族 -/

/-- 中国剰余定理で分かれる部分代数の族：gcd(a, b) = 1 なら C(X_{ab}) = L(X_a) ⊔ R(X_b)。 -/
def CRTMul (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ))) : Prop :=
  ∀ (a b : ℕ) [NeZero a] [NeZero b] (hab : Nat.Coprime a b),
    (X (a * b)).map (crtConj hab).toAlgHom = (X a).map (leftHom a b) ⊔ (X b).map (rightHom a b)

/-- **2a.** C⁻¹(C(Y)) = Y。 -/
theorem map_symm_map_crtConj {a b : ℕ} (hab : Nat.Coprime a b)
    (Y : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ))) :
    (Y.map (crtConj hab).toAlgHom).map (crtConj hab).symm.toAlgHom = Y := by
  have e : (crtConj hab).symm.toAlgHom.comp (crtConj hab).toAlgHom = AlgHom.id ℂ _ :=
    AlgHom.ext fun T => (crtConj hab).symm_apply_apply T
  rw [Subalgebra.map_map, e, Subalgebra.map_id]

/-- **2b.** End(ℂ^{ℤ/1}) の部分代数はスカラーだけ（= ⊥）。 -/
theorem eq_bot_of_one (S : Subalgebra ℂ (Module.End ℂ (ZMod 1 → ℂ))) : S = ⊥ := by
  refine le_bot_iff.mp (fun T _ => Algebra.mem_bot.mpr ⟨T (fun _ => 1) 0, ?_⟩)
  apply LinearMap.ext
  intro f
  funext x
  have hx : x = 0 := Subsingleton.elim x 0
  have hf : f = f 0 • (fun _ => (1 : ℂ)) := by
    funext y
    rw [Subsingleton.elim y 0, Pi.smul_apply, smul_eq_mul, mul_one]
  subst hx
  rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply, smul_eq_mul]
  conv_rhs => rw [hf]
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **2c.** ι_k(X_{a_k}) ⊆ X_N。 -/
theorem map_locHom_le (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ))) (hX : CRTMul X) :
    ∀ (l : List ℕ+) (h : CoprimeList l) (k : Fin l.length),
    (X ((l.get k : ℕ+) : ℕ)).map (locHom l h k) ≤ X (prodList l)
  | a :: l, h, ⟨0, _⟩ => by
    have key := hX (a : ℕ) (prodList l) h.head
    show (X (a : ℕ)).map ((crtConj h.head).symm.toAlgHom.comp (leftHom (a : ℕ) (prodList l))) ≤
      X ((a : ℕ) * prodList l)
    rw [← Subalgebra.map_map]
    calc _ ≤ ((X ((a : ℕ) * prodList l)).map (crtConj h.head).toAlgHom).map (crtConj h.head).symm.toAlgHom :=
          Subalgebra.map_mono (le_sup_left.trans key.ge)
      _ = X ((a : ℕ) * prodList l) := map_symm_map_crtConj h.head _
  | a :: l, h, ⟨k + 1, hk⟩ => by
    have key := hX (a : ℕ) (prodList l) h.head
    have ih := map_locHom_le X hX l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    show (X ((l.get ⟨k, Nat.lt_of_succ_lt_succ hk⟩ : ℕ+) : ℕ)).map ((crtConj h.head).symm.toAlgHom.comp
      ((rightHom (a : ℕ) (prodList l)).comp (locHom l h.tail ⟨k, Nat.lt_of_succ_lt_succ hk⟩))) ≤
        X ((a : ℕ) * prodList l)
    rw [← Subalgebra.map_map, ← Subalgebra.map_map]
    calc _ ≤ ((X (prodList l)).map (rightHom (a : ℕ) (prodList l))).map (crtConj h.head).symm.toAlgHom :=
          Subalgebra.map_mono (Subalgebra.map_mono ih)
      _ ≤ ((X ((a : ℕ) * prodList l)).map (crtConj h.head).toAlgHom).map (crtConj h.head).symm.toAlgHom :=
          Subalgebra.map_mono (le_sup_right.trans key.ge)
      _ = X ((a : ℕ) * prodList l) := map_symm_map_crtConj h.head _

/-- **2d.** X_N = ⨆_k ι_k(X_{a_k})（局所の像が X_N を生成する）。 -/
theorem eq_iSup_map_locHom (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (h : CoprimeList l),
    X (prodList l) = ⨆ k : Fin l.length, (X ((l.get k : ℕ+) : ℕ)).map (locHom l h k)
  | [], _ => by
    refine (eq_bot_of_one _).trans (iSup_eq_bot.mpr fun k => ?_).symm
    exact Fin.elim0 k
  | a :: l, h => by
    refine le_antisymm ?_ (iSup_le fun k => map_locHom_le X hX (a :: l) h k)
    have key := hX (a : ℕ) (prodList l) h.head
    have ih := eq_iSup_map_locHom X hX l h.tail
    show X ((a : ℕ) * prodList l) ≤ _
    rw [← map_symm_map_crtConj h.head (X ((a : ℕ) * prodList l)), key, Algebra.map_sup]
    refine sup_le ?_ ?_
    · refine le_iSup_of_le (0 : Fin (l.length + 1)) (le_of_eq ?_)
      rw [Subalgebra.map_map]
      rfl
    · rw [Subalgebra.map_le, Subalgebra.map_le, ih]
      refine iSup_le fun j => ?_
      rw [← Subalgebra.map_le, ← Subalgebra.map_le, Subalgebra.map_map, Subalgebra.map_map]
      exact le_iSup_of_le j.succ le_rfl

/-- **2e.** dim X_N = Π_k dim X_{a_k}。 -/
theorem finrank_prodList (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (_ : CoprimeList l),
    Module.finrank ℂ (X (prodList l)) = (l.map (fun a : ℕ+ => Module.finrank ℂ (X (a : ℕ)))).prod
  | [], _ => by
    show Module.finrank ℂ (X 1) = 1
    rw [eq_bot_of_one (X 1), Subalgebra.finrank_bot]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, ← finrank_prodList X hX l h.tail]
    show Module.finrank ℂ (X ((a : ℕ) * prodList l)) = _
    rw [← finrank_map_crtConj_gen h.head (X ((a : ℕ) * prodList l)), hX (a : ℕ) (prodList l) h.head,
      finrank_sup_map]

/-! ### 3. 繰り返しのテンソル積 -/

/-- 半環と ℂ 代数の構造をもつ型の入れ物（繰り返しのテンソル積を再帰で作るため）。 -/
structure BundledAlg where
  /-- 台の型 -/
  carrier : Type
  [instSemiring : Semiring carrier]
  [instAlgebra : Algebra ℂ carrier]

attribute [instance] BundledAlg.instSemiring BundledAlg.instAlgebra

/-- 繰り返しのテンソル積 X_{a₁} ⊗ (X_{a₂} ⊗ (⋯ ⊗ (X_{a_r} ⊗ ℂ)))。 -/
noncomputable def tensAlg (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ))) :
    List ℕ+ → BundledAlg
  | [] => ⟨ℂ⟩
  | a :: l => ⟨TensorProduct ℂ (X (a : ℕ)) (tensAlg X l).carrier⟩

/-- **代数の同型** 繰り返しのテンソル積 ≅ X_N（N = prodList l。2 因子の同型（Part 229 の crtTensorEquiv）を繰り返す）。 -/
noncomputable def tensEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (_ : CoprimeList l), (tensAlg X l).carrier ≃ₐ[ℂ] X (prodList l)
  | [], _ => (Algebra.botEquiv ℂ (Module.End ℂ (ZMod 1 → ℂ))).symm.trans
      (Subalgebra.equivOfEq _ _ (eq_bot_of_one (X 1)).symm)
  | a :: l, h => (Algebra.TensorProduct.congr AlgEquiv.refl (tensEquiv X hX l h.tail)).trans
      (crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l)) (X ((a : ℕ) * prodList l))
        (hX (a : ℕ) (prodList l) h.head))

/-- **3a.** 純テンソルの値：Θ(S ⊗ z) = ι_0(S)·C⁻¹(R(Θ′(z)))。 -/
theorem tensEquiv_tmul (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) (a : ℕ+) (l : List ℕ+) (h : CoprimeList (a :: l)) (S : X (a : ℕ))
    (z : (tensAlg X l).carrier) :
    ((tensEquiv X hX (a :: l) h (S ⊗ₜ[ℂ] z : TensorProduct ℂ (X (a : ℕ)) (tensAlg X l).carrier) :
        X (prodList (a :: l))) : Module.End ℂ (ZMod (prodList (a :: l)) → ℂ)) =
      locHom (a :: l) h 0 (S : Module.End ℂ (ZMod (a : ℕ) → ℂ)) *
        @id (Module.End ℂ (ZMod (prodList (a :: l)) → ℂ)) ((crtConj h.head).symm (rightOp (a : ℕ)
          ((tensEquiv X hX l h.tail z : X (prodList l)) : Module.End ℂ (ZMod (prodList l) → ℂ)))) := by
  have e : ((tensEquiv X hX (a :: l) h (S ⊗ₜ[ℂ] z : TensorProduct ℂ (X (a : ℕ)) (tensAlg X l).carrier) :
      X (prodList (a :: l))) : Module.End ℂ (ZMod (prodList (a :: l)) → ℂ)) =
      ((crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l)) (X ((a : ℕ) * prodList l))
        (hX (a : ℕ) (prodList l) h.head) (S ⊗ₜ[ℂ] (tensEquiv X hX l h.tail z)) : X ((a : ℕ) * prodList l)) :
          Module.End ℂ (ZMod ((a : ℕ) * prodList l) → ℂ)) := by
    show ((crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l)) (X ((a : ℕ) * prodList l))
      (hX (a : ℕ) (prodList l) h.head) ((Algebra.TensorProduct.congr AlgEquiv.refl (tensEquiv X hX l h.tail))
        (S ⊗ₜ[ℂ] z)) : X ((a : ℕ) * prodList l)) : Module.End ℂ (ZMod ((a : ℕ) * prodList l) → ℂ)) = _
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    rfl
  rw [e, ← (crtConj h.head).symm_apply_apply ((crtTensorEquiv h.head (X (a : ℕ)) (X (prodList l))
    (X ((a : ℕ) * prodList l)) (hX (a : ℕ) (prodList l) h.head) (S ⊗ₜ[ℂ] (tensEquiv X hX l h.tail z)) :
      X ((a : ℕ) * prodList l)) : Module.End ℂ (ZMod ((a : ℕ) * prodList l) → ℂ)),
    crtConj_crtTensorEquiv_tmul, map_mul]
  rfl

/-- 純テンソル S₀ ⊗ (S₁ ⊗ (⋯ ⊗ (S_{r−1} ⊗ 1)))。 -/
noncomputable def tprodL (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ))) :
    ∀ (l : List ℕ+), (∀ k : Fin l.length, X ((l.get k : ℕ+) : ℕ)) → (tensAlg X l).carrier
  | [], _ => 1
  | a :: l, S => (S ⟨0, Nat.succ_pos _⟩ ⊗ₜ[ℂ] tprodL X l (fun k => S ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) :
      TensorProduct ℂ (X (a : ℕ)) (tensAlg X l).carrier)

/-- **3b.** Θ(S₀ ⊗ (S₁ ⊗ ⋯)) = ι_0(S₀)·ι_1(S₁)⋯ι_{r−1}(S_{r−1})（局所作用素の積）。 -/
theorem tensEquiv_tprodL (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) : ∀ (l : List ℕ+) (h : CoprimeList l) (S : ∀ k : Fin l.length, X ((l.get k : ℕ+) : ℕ)),
    (tensEquiv X hX l h (tprodL X l S) : Module.End ℂ (ZMod (prodList l) → ℂ)) =
      (List.ofFn (fun k => locHom l h k (S k : Module.End ℂ (ZMod ((l.get k : ℕ+) : ℕ) → ℂ)))).prod
  | [], h, S => by
    rw [List.ofFn_zero, List.prod_nil, show tprodL X [] S = 1 from rfl, map_one]
    rfl
  | a :: l, h, S => by
    rw [List.ofFn_succ, List.prod_cons]
    show (tensEquiv X hX (a :: l) h (S ⟨0, Nat.succ_pos _⟩ ⊗ₜ[ℂ]
      tprodL X l (fun k => S ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) :
        TensorProduct ℂ (X (a : ℕ)) (tensAlg X l).carrier) : Module.End ℂ (ZMod (prodList (a :: l)) → ℂ)) = _
    rw [tensEquiv_tmul, tensEquiv_tprodL X hX l h.tail (fun k => S ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)]
    have hφ := map_list_prod ((crtConj h.head).symm.toAlgHom.comp (rightHom (a : ℕ) (prodList l)))
      (List.ofFn (fun k => locHom l h.tail k (S ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩).val))
    rw [List.map_ofFn] at hφ
    exact congrArg₂ (· * ·) rfl hφ

/-! ### 4. A・A′・Z・dilComm・End -/

/-- **4a.** A は中国剰余定理で分かれる（Part 228）。 -/
theorem crtMul_shellAlg : CRTMul shellAlg := fun _ _ _ _ hab => map_crtConj_shellAlg hab

/-- **4b.** A′ も（Part 229）。 -/
theorem crtMul_fullCommAlg : CRTMul fullCommAlg := fun _ _ _ _ hab => map_crtConj_fullComm hab

/-- **4c.** 中心 Z も（Part 229）。 -/
theorem crtMul_centerAlg : CRTMul centerAlg := fun _ _ _ _ hab => map_crtConj_center hab

/-- **4d.** dilComm も（Part 231）。 -/
theorem crtMul_dilCommAlg : CRTMul dilCommAlg := fun _ _ _ _ hab => map_crtConj_dilComm hab

/-- End(ℂ^{ℤ/n}) 全体（部分代数 ⊤）。 -/
def topAlg (n : ℕ) [NeZero n] : Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)) := ⊤

/-- **4e.** End 全体も：C(⊤) = L(⊤) ⊔ R(⊤)（Part 230 の可換子の分解で B = B′ = スカラー）。 -/
theorem crtMul_topAlg : CRTMul topAlg := by
  intro a b _ _ hab
  have h1 := centralizer_sup_map (a := a) (b := b) ⊥ ⊥
  rw [Algebra.map_bot, Algebra.map_bot, sup_bot_eq, centralizer_bot_eq_top, centralizer_bot_eq_top,
    centralizer_bot_eq_top] at h1
  show (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod (a * b) → ℂ))).map (crtConj hab).toAlgHom =
    (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod a → ℂ))).map (leftHom a b) ⊔
      (⊤ : Subalgebra ℂ (Module.End ℂ (ZMod b → ℂ))).map (rightHom a b)
  rw [← h1]
  exact eq_top_iff.mpr fun T _ =>
    Subalgebra.mem_map.mpr ⟨(crtConj hab).symm T, Algebra.mem_top, (crtConj hab).apply_symm_apply T⟩

/-! ### 5. 素冪への分解 -/

/-- p^{v_p(N)} は 0 でない（インスタンス）。 -/
instance neZero_ordProj (N p : ℕ) : NeZero (p ^ N.factorization p) := ⟨(Nat.ordProj_pos N p).ne'⟩

/-- q^{v_q(N)}（ℕ+ の元として）。 -/
def ppow (N p : ℕ) : ℕ+ := ⟨p ^ N.factorization p, Nat.ordProj_pos N p⟩

/-- **5a.** ppow の値。 -/
theorem ppow_coe (N p : ℕ) : (ppow N p : ℕ) = p ^ N.factorization p := rfl

/-- N の素冪のリスト [q₁^{k₁}, …, q_r^{k_r}]（素数の昇順）。 -/
noncomputable def ppList (N : ℕ) : List ℕ+ := (N.primeFactors.sort (· ≤ ·)).map (ppow N)

/-- **5b.** 素冪のリストは互いに素。 -/
theorem coprimeList_ppList (N : ℕ) : CoprimeList (ppList N) := by
  unfold CoprimeList ppList
  rw [List.pairwise_map]
  refine (Finset.sort_nodup N.primeFactors (· ≤ ·)).pairwise_of_forall_ne fun p hp q hq hpq => ?_
  rw [Finset.mem_sort] at hp hq
  exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq)).mpr hpq)

/-- **5c.** 素冪のリストの積は N。 -/
theorem prodList_ppList (N : ℕ) [NeZero N] : prodList (ppList N) = N := by
  rw [prodList_eq_prod, ppList, List.map_map]
  have h := List.prod_toFinset (fun p => p ^ N.factorization p) (Finset.sort_nodup N.primeFactors (· ≤ ·))
  rw [Finset.sort_toFinset] at h
  exact h.symm.trans (Nat.prod_factorization_pow_eq_self (NeZero.ne N))

/-- 法が等しいときの付け替え X_M ≅ X_N（M = N）。 -/
noncomputable def substEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    {M N : ℕ} [NeZero M] [NeZero N] (h : M = N) : X M ≃ₐ[ℂ] X N := by
  subst h
  exact AlgEquiv.refl

/-- **代数の同型** X_N ≅ X_{q₁^{k₁}} ⊗ (X_{q₂^{k₂}} ⊗ (⋯ ⊗ ℂ))（素冪のリスト）。 -/
noncomputable def ppEquiv (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) (N : ℕ) [NeZero N] : (tensAlg X (ppList N)).carrier ≃ₐ[ℂ] X N :=
  (tensEquiv X hX (ppList N) (coprimeList_ppList N)).trans (substEquiv X (prodList_ppList N))

/-- **5d.** dim X_N = Π_{q ∣ N} dim X_{q^{v_q(N)}}。 -/
theorem finrank_eq_prod_primeFactors (X : ∀ (n : ℕ) [NeZero n], Subalgebra ℂ (Module.End ℂ (ZMod n → ℂ)))
    (hX : CRTMul X) (N : ℕ) [NeZero N] :
    Module.finrank ℂ (X N) = ∏ p ∈ N.primeFactors, Module.finrank ℂ (X (p ^ N.factorization p)) := by
  rw [← (substEquiv X (prodList_ppList N)).toLinearEquiv.finrank_eq,
    finrank_prodList X hX (ppList N) (coprimeList_ppList N), ppList, List.map_map]
  have h := List.prod_toFinset (fun p => Module.finrank ℂ (X (p ^ N.factorization p)))
    (Finset.sort_nodup N.primeFactors (· ≤ ·))
  rw [Finset.sort_toFinset] at h
  rw [h]
  rfl

/-- **代数の同型** End(ℂ^{ℤ/N}) ≅ End(ℂ^{ℤ/q₁^{k₁}}) ⊗ (End(ℂ^{ℤ/q₂^{k₂}}) ⊗ (⋯ ⊗ ℂ))（4e と 5 から）。 -/
noncomputable def endPPEquiv (N : ℕ) [NeZero N] :
    (tensAlg topAlg (ppList N)).carrier ≃ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  (ppEquiv topAlg crtMul_topAlg N).trans Subalgebra.topEquiv

/-- **5e.** dim A_N = Π_{q ∣ N} dim A_{q^{v_q(N)}}（A = 殻の射影が生成する代数）。 -/
theorem finrank_shellAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (shellAlg N) = ∏ p ∈ N.primeFactors, Module.finrank ℂ (shellAlg (p ^ N.factorization p)) :=
  finrank_eq_prod_primeFactors shellAlg crtMul_shellAlg N

/-- **5f.** dim A′_N = Π_{q ∣ N} dim A′_{q^{v_q(N)}}。 -/
theorem finrank_fullCommAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullCommAlg N) =
      ∏ p ∈ N.primeFactors, Module.finrank ℂ (fullCommAlg (p ^ N.factorization p)) :=
  finrank_eq_prod_primeFactors fullCommAlg crtMul_fullCommAlg N

/-- **5g.** dim Z_N = Π_{q ∣ N} dim Z_{q^{v_q(N)}}。 -/
theorem finrank_centerAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (centerAlg N) = ∏ p ∈ N.primeFactors, Module.finrank ℂ (centerAlg (p ^ N.factorization p)) :=
  finrank_eq_prod_primeFactors centerAlg crtMul_centerAlg N

/-- **5h.** dim dilComm_N = Π_{q ∣ N} dim dilComm_{q^{v_q(N)}}。 -/
theorem finrank_dilCommAlg_eq_prod (N : ℕ) [NeZero N] :
    Module.finrank ℂ (dilCommAlg N) =
      ∏ p ∈ N.primeFactors, Module.finrank ℂ (dilCommAlg (p ^ N.factorization p)) :=
  finrank_eq_prod_primeFactors dilCommAlg crtMul_dilCommAlg N

end PAG.Part240

#print axioms PAG.Part240.prodList
#print axioms PAG.Part240.prodList_nil
#print axioms PAG.Part240.prodList_cons
#print axioms PAG.Part240.prodList_pos
#print axioms PAG.Part240.neZero_prodList
#print axioms PAG.Part240.prodList_eq_prod
#print axioms PAG.Part240.CoprimeList
#print axioms PAG.Part240.coprime_prodList
#print axioms PAG.Part240.CoprimeList.head
#print axioms PAG.Part240.CoprimeList.tail
#print axioms PAG.Part240.get_dvd_prodList
#print axioms PAG.Part240.locHom
#print axioms PAG.Part240.locHom_zero
#print axioms PAG.Part240.locHom_succ
#print axioms PAG.Part240.locHom_injective
#print axioms PAG.Part240.locHom_commute
#print axioms PAG.Part240.crt_fst_eq_castHom
#print axioms PAG.Part240.castHom_crt_snd
#print axioms PAG.Part240.locHom_mulLeft
#print axioms PAG.Part240.liftL
#print axioms PAG.Part240.locHom_apply
#print axioms PAG.Part240.castHom_liftL
#print axioms PAG.Part240.castHom_liftL_of_ne
#print axioms PAG.Part240.eq_of_castHom_eq
#print axioms PAG.Part240.CRTMul
#print axioms PAG.Part240.map_symm_map_crtConj
#print axioms PAG.Part240.eq_bot_of_one
#print axioms PAG.Part240.map_locHom_le
#print axioms PAG.Part240.eq_iSup_map_locHom
#print axioms PAG.Part240.finrank_prodList
#print axioms PAG.Part240.BundledAlg
#print axioms PAG.Part240.tensAlg
#print axioms PAG.Part240.tensEquiv
#print axioms PAG.Part240.tensEquiv_tmul
#print axioms PAG.Part240.tprodL
#print axioms PAG.Part240.tensEquiv_tprodL
#print axioms PAG.Part240.crtMul_shellAlg
#print axioms PAG.Part240.crtMul_fullCommAlg
#print axioms PAG.Part240.crtMul_centerAlg
#print axioms PAG.Part240.crtMul_dilCommAlg
#print axioms PAG.Part240.topAlg
#print axioms PAG.Part240.crtMul_topAlg
#print axioms PAG.Part240.neZero_ordProj
#print axioms PAG.Part240.ppow
#print axioms PAG.Part240.ppow_coe
#print axioms PAG.Part240.ppList
#print axioms PAG.Part240.coprimeList_ppList
#print axioms PAG.Part240.prodList_ppList
#print axioms PAG.Part240.substEquiv
#print axioms PAG.Part240.ppEquiv
#print axioms PAG.Part240.finrank_eq_prod_primeFactors
#print axioms PAG.Part240.endPPEquiv
#print axioms PAG.Part240.finrank_shellAlg_eq_prod
#print axioms PAG.Part240.finrank_fullCommAlg_eq_prod
#print axioms PAG.Part240.finrank_centerAlg_eq_prod
#print axioms PAG.Part240.finrank_dilCommAlg_eq_prod
