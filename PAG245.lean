/-
  PAG 2.0 Part 241（2026-11-05）— ラマヌジャン和の閉じた式（フォン・シュテルネックの式）と、空間全体の ⟨D_s, E_N⟩ ≅ M_{d(N)}(ℂ) × ℂ^{S′}
  Part 239 で数値だけだった空間全体の次元 d(N)² + d(N) − 1 − [2 ∣ N] と、Part 240 の残る問いだった閉じた式を Lean にする。
  1. c_q(n) は gcd(q, n) だけで決まり（ramSum_gcd）、c_q(n)·φ(q/g) = μ(q/g)·φ(q)（g = gcd(q, n)、ramSum_mul_totient）。
     両辺は q について乗法的なので素冪で確かめる。系：c_q(n) = μ(q/g)·φ(q)/φ(q/g)（ramSum_eq_div）、
     c_q(n) ≠ 0 ⇔ q/g が平方因子をもたない（ramSum_ne_zero_iff_squarefree）、(q, n) = 1 なら μ(q)、q ∣ n なら φ(q)。
     Part 239 の行列 C(u, t) の閉じた式（ramMat_eq_closed）
  2. E_N = Φ([E_N])（E_N は角の代数に入る、convL_geps_self_eq）。Q_s = D_s − P_{s,s}（shellDev）は
     Q_s P_{u,v} = P_{u,v} Q_s = 0、Q_s Q_t = [s = t]·Q_s を満たし、Q_s = 0 ⇔ φ(N/s) = 1（N/s = 1, 2）
  3. Ψ(M, b) = Σ M_{st} P_{s,t} + Σ_{s ∈ S′} b_s Q_s（S′ = {s ∣ N : φ(N/s) ≠ 1}）は単射な代数準同型
     M_{d(N)}(ℂ) × ℂ^{S′} → End(ℂ^{ℤ/N}) で、像は ⟨D_u, E_N⟩ そのもの（ウェダーバーン分解 wholeAlgEquiv）。
     dim ⟨D_u, E_N⟩ = d(N)² + #S′ = d(N)² + d(N) − 1 − [2 ∣ N]（finrank_oneEAlg_self_sub）
  4. 中心：⟨D_u, E_N⟩ の元が中心に入る ⇔ c·P + Σ_{s ∈ S′} b_s Q_s の形（mem_center_oneEAlg_iff）。
     その形の作用素の空間は 1 + #S′ = d(N) − [2 ∣ N] 次元（finrank_range_centerMap）
-/
import PAG244

namespace PAG.Part245

open Complex Finset PAG.Part199 PAG.Part200 PAG.Part202 PAG.Part203 PAG.Part205 PAG.Part206 PAG.Part207
  PAG.Part208 PAG.Part209 PAG.Part210 PAG.Part211 PAG.Part212 PAG.Part213 PAG.Part214 PAG.Part215 PAG.Part216
  PAG.Part217 PAG.Part218 PAG.Part219 PAG.Part220 PAG.Part221 PAG.Part222 PAG.Part223 PAG.Part224 PAG.Part225
  PAG.Part226 PAG.Part227 PAG.Part228 PAG.Part229 PAG.Part230 PAG.Part240 PAG.Part241 PAG.Part242 PAG.Part243
  PAG.Part244
open ZMod (stdAddChar)
open scoped ZMod

/-! ### 1. ラマヌジャン和の閉じた式（フォン・シュテルネックの式） -/

/-- **1a.** c_q(n) は gcd(q, n) だけで決まる：c_q(n) = c_q(gcd(q, n))。 -/
theorem ramSum_gcd (n q : ℕ) : ramSum n q = ramSum (Nat.gcd q n) q := by
  rw [ramSum_apply, ramSum_apply]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hd : q / e ∣ q := Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he)
  have hiff : (q / e ∣ n) ↔ (q / e ∣ Nat.gcd q n) := by
    rw [Nat.dvd_gcd_iff]
    exact ⟨fun h => ⟨hd, h⟩, fun h => h.2⟩
  congr 1
  exact if_congr hiff rfl rfl

/-- **1b.** 周期性：c_q(n mod q) = c_q(n)。 -/
theorem ramSum_mod (n q : ℕ) : ramSum (n % q) q = ramSum n q := by
  rw [ramSum_gcd (n % q) q, ramSum_gcd n q, Nat.gcd_comm q (n % q), ← Nat.gcd_rec]

/-- **1c.** (q, n) = 1 なら c_q(n) = μ(q)。 -/
theorem ramSum_of_coprime {q n : ℕ} (h : Nat.Coprime q n) : ramSum n q = ArithmeticFunction.moebius q := by
  rw [ramSum_gcd, show Nat.gcd q n = 1 from h, ramSum_one]

/-- q ↦ φ(q / gcd(q, n))。 -/
noncomputable def totientDivGcd (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun q => (Nat.totient (q / Nat.gcd q n) : ℤ), by simp⟩

/-- q ↦ μ(q / gcd(q, n))。 -/
noncomputable def moebiusDivGcd (n : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun q => ArithmeticFunction.moebius (q / Nat.gcd q n), by simp⟩

/-- **1d.** totientDivGcd の値。 -/
theorem totientDivGcd_apply (n q : ℕ) : totientDivGcd n q = (Nat.totient (q / Nat.gcd q n) : ℤ) := rfl

/-- **1e.** moebiusDivGcd の値。 -/
theorem moebiusDivGcd_apply (n q : ℕ) :
    moebiusDivGcd n q = ArithmeticFunction.moebius (q / Nat.gcd q n) := rfl

/-- **1f.** 互いに素な a, b で gcd(ab, n) = gcd(a, n)·gcd(b, n)。 -/
theorem gcd_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    Nat.gcd (a * b) n = Nat.gcd a n * Nat.gcd b n := by
  rw [Nat.gcd_comm, Nat.Coprime.gcd_mul n h, Nat.gcd_comm n a, Nat.gcd_comm n b]

/-- **1g.** 互いに素な a, b で ab/gcd(ab, n) = (a/gcd(a, n))·(b/gcd(b, n))。 -/
theorem mul_div_gcd_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    a * b / Nat.gcd (a * b) n = (a / Nat.gcd a n) * (b / Nat.gcd b n) := by
  rw [gcd_mul_of_coprime h n, Nat.div_mul_div_comm (Nat.gcd_dvd_left a n) (Nat.gcd_dvd_left b n)]

/-- **1h.** 互いに素な a, b で a/gcd(a, n) と b/gcd(b, n) は互いに素。 -/
theorem coprime_div_gcd_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (n : ℕ) :
    Nat.Coprime (a / Nat.gcd a n) (b / Nat.gcd b n) :=
  (h.coprime_div_left (Nat.gcd_dvd_left a n)).coprime_div_right (Nat.gcd_dvd_left b n)

/-- **1i.** q ↦ φ(q / gcd(q, n)) は乗法的。 -/
theorem isMultiplicative_totientDivGcd (n : ℕ) : (totientDivGcd n).IsMultiplicative := by
  refine ⟨?_, fun {a b} h => ?_⟩
  · rw [totientDivGcd_apply, Nat.gcd_one_left, Nat.div_one, Nat.totient_one, Nat.cast_one]
  · rw [totientDivGcd_apply, totientDivGcd_apply, totientDivGcd_apply, mul_div_gcd_of_coprime h n,
      Nat.totient_mul (coprime_div_gcd_of_coprime h n), Nat.cast_mul]

/-- **1j.** q ↦ μ(q / gcd(q, n)) は乗法的。 -/
theorem isMultiplicative_moebiusDivGcd (n : ℕ) : (moebiusDivGcd n).IsMultiplicative := by
  refine ⟨?_, fun {a b} h => ?_⟩
  · rw [moebiusDivGcd_apply, Nat.gcd_one_left, Nat.div_one, ArithmeticFunction.moebius_apply_one]
  · rw [moebiusDivGcd_apply, moebiusDivGcd_apply, moebiusDivGcd_apply, mul_div_gcd_of_coprime h n]
    exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (coprime_div_gcd_of_coprime h n)

/-- **1k.** 素冪の場合：c_{p^i}(n)·φ(p^i/g) = μ(p^i/g)·φ(p^i)（g = gcd(p^i, n)）。 -/
theorem ramSum_mul_totient_primePow {p : ℕ} (hp : p.Prime) (i n : ℕ) :
    ramSum n (p ^ i) * (Nat.totient (p ^ i / Nat.gcd (p ^ i) n) : ℤ) =
      ArithmeticFunction.moebius (p ^ i / Nat.gcd (p ^ i) n) * (Nat.totient (p ^ i) : ℤ) := by
  obtain ⟨j, hji, hg⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p ^ i) n)
  have hpj : p ^ j ∣ n := hg ▸ Nat.gcd_dvd_right (p ^ i) n
  have hnot : j < i → ¬ p ^ (j + 1) ∣ n := by
    intro hlt hdvd
    have h1 : p ^ (j + 1) ∣ Nat.gcd (p ^ i) n := Nat.dvd_gcd (Nat.pow_dvd_pow p hlt) hdvd
    rw [hg] at h1
    have h2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
    omega
  have hdiv : p ^ i / Nat.gcd (p ^ i) n = p ^ (i - j) := by
    rw [hg, Nat.pow_div hji hp.pos]
  rw [hdiv]
  rcases Nat.lt_or_ge j i with hlt | hge
  · have hi : 1 ≤ i := by omega
    rw [ramSum_primePow hp hi n]
    by_cases hj : j + 1 = i
    · have hn1 : ¬ p ^ i ∣ n := by
        rw [← hj]
        exact hnot hlt
      have hn2 : p ^ (i - 1) ∣ n := by
        rw [show i - 1 = j by omega]
        exact hpj
      rw [ite_eq_right hn1, ite_eq_left hn2, show i - j = 1 by omega, pow_one, Nat.totient_prime hp,
        ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime_pow hp (by omega : 0 < i), Nat.cast_mul]
      ring
    · have hn1 : ¬ p ^ i ∣ n := fun h => hnot hlt (dvd_trans (Nat.pow_dvd_pow p (by omega)) h)
      have hn2 : ¬ p ^ (i - 1) ∣ n := fun h => hnot hlt (dvd_trans (Nat.pow_dvd_pow p (by omega)) h)
      rw [ite_eq_right hn1, ite_eq_right hn2, ArithmeticFunction.moebius_apply_prime_pow hp (by omega),
        ite_eq_right (by omega : ¬ (i - j = 1))]
      simp
  · have hji' : j = i := le_antisymm hji hge
    have hpi : p ^ i ∣ n := hji' ▸ hpj
    rw [hji', Nat.sub_self, pow_zero, Nat.totient_one, ArithmeticFunction.moebius_apply_one]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp [(isMultiplicative_ramSum n).map_one]
    · rw [ramSum_primePow hp hpos n, ite_eq_left hpi,
        ite_eq_left (dvd_trans (Nat.pow_dvd_pow p (Nat.sub_le i 1)) hpi), Nat.totient_prime_pow hp hpos]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow]
      ring

/-- **1l.** フォン・シュテルネックの式（整数の形）：c_q(n)·φ(q/g) = μ(q/g)·φ(q)（g = gcd(q, n)）。 -/
theorem ramSum_mul_totient (n q : ℕ) :
    ramSum n q * (Nat.totient (q / Nat.gcd q n) : ℤ) =
      ArithmeticFunction.moebius (q / Nat.gcd q n) * (Nat.totient q : ℤ) := by
  have h := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    ((ramSum n).pmul (totientDivGcd n)) ((isMultiplicative_ramSum n).pmul (isMultiplicative_totientDivGcd n))
    ((moebiusDivGcd n).pmul totientAF) ((isMultiplicative_moebiusDivGcd n).pmul totientAF_isMultiplicative)).mpr
    (fun p i hp => by
      simp only [ArithmeticFunction.pmul_apply, totientDivGcd_apply, moebiusDivGcd_apply, totientAF_apply]
      exact ramSum_mul_totient_primePow hp i n)
  have hq := congrArg (fun f : ArithmeticFunction ℤ => f q) h
  simp only [ArithmeticFunction.pmul_apply, totientDivGcd_apply, moebiusDivGcd_apply, totientAF_apply] at hq
  exact hq

/-- **1m.** q ≠ 0 なら q/gcd(q, n) ≥ 1。 -/
theorem div_gcd_pos {q : ℕ} (hq : q ≠ 0) (n : ℕ) : 0 < q / Nat.gcd q n :=
  Nat.div_pos (Nat.gcd_le_left n (Nat.pos_of_ne_zero hq)) (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hq))

/-- **1n.** 閉じた式：c_q(n) = μ(q/g)·φ(q)/φ(q/g)（q ≠ 0、g = gcd(q, n)）。 -/
theorem ramSum_eq_div {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    (ramSum n q : ℂ) = (ArithmeticFunction.moebius (q / Nat.gcd q n) : ℂ) * (Nat.totient q : ℂ) /
      (Nat.totient (q / Nat.gcd q n) : ℂ) := by
  have hφ : (Nat.totient (q / Nat.gcd q n) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (div_gcd_pos hq n)).ne'
  rw [eq_div_iff hφ]
  exact_mod_cast ramSum_mul_totient n q

/-- **1o.** c_q(n) ≠ 0 ⇔ q/gcd(q, n) が平方因子をもたない（q ≠ 0）。 -/
theorem ramSum_ne_zero_iff_squarefree {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    ramSum n q ≠ 0 ↔ Squarefree (q / Nat.gcd q n) := by
  rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
  have h := ramSum_mul_totient n q
  have h1 : (Nat.totient (q / Nat.gcd q n) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (div_gcd_pos hq n)).ne'
  have h2 : (Nat.totient q : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)).ne'
  constructor
  · intro hc hμ
    rw [hμ, zero_mul] at h
    exact mul_ne_zero hc h1 h
  · intro hμ hc
    rw [hc, zero_mul] at h
    exact mul_ne_zero hμ h2 h.symm

/-- **1p.** q ∣ n なら c_q(n) = φ(q)。 -/
theorem ramSum_of_dvd {q n : ℕ} (h : q ∣ n) : ramSum n q = (Nat.totient q : ℤ) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have e := ramSum_mul_totient n q
  rw [Nat.gcd_eq_left h, Nat.div_self hq, Nat.totient_one, ArithmeticFunction.moebius_apply_one, Nat.cast_one,
    mul_one, one_mul] at e
  exact e

/-- **1q.** ラマヌジャンの行列の閉じた式：C(u, t) = μ(q/g)·φ(q)/φ(q/g)（q = N/t、g = gcd(q, u)）。 -/
theorem ramMat_eq_closed (N : ℕ) [NeZero N] (u t : N.divisors) :
    ramMat N u t = (ArithmeticFunction.moebius ((N / t) / Nat.gcd (N / t) u) : ℂ) * (Nat.totient (N / t) : ℂ) /
      (Nat.totient ((N / t) / Nat.gcd (N / t) u) : ℂ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have ht : (t : ℕ) ∣ N := Nat.dvd_of_mem_divisors t.2
  rw [ramMat_eq_ramSum]
  exact ramSum_eq_div (Nat.div_pos (Nat.le_of_dvd hN ht) (Nat.pos_of_dvd_of_pos ht hN)).ne' u

/-! ### 2. E_N と、殻の上の平均を引く作用素 Q_s = D_s − P_{s,s} -/

/-- **2a.** Φ(M + M′) = Φ(M) + Φ(M′)（Φ(M) = Σ M_{st} P_{s,t}）。 -/
theorem radialMatOp_add (N : ℕ) [NeZero N] (M M' : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N (M + M') = radialMatOp N M + radialMatOp N M' := by
  simp only [radialMatOp, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

/-- **2b.** Φ(cM) = c·Φ(M)。 -/
theorem radialMatOp_smul (N : ℕ) [NeZero N] (c : ℂ) (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N (c • M) = c • radialMatOp N M := by
  simp only [radialMatOp, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- **2c.** Φ(0) = 0。 -/
theorem radialMatOp_zero (N : ℕ) [NeZero N] : radialMatOp N 0 = 0 := by
  simp only [radialMatOp, Matrix.zero_apply, zero_smul, Finset.sum_const_zero]

/-- **2d.** Φ(c·E_{st}) = c·P_{s,t}。 -/
theorem radialMatOp_single (N : ℕ) [NeZero N] (s t : N.divisors) (c : ℂ) :
    radialMatOp N (Matrix.single s t c) = c • shellTrans N s t := by
  have h : ∀ s' t' : N.divisors, Matrix.single s t c s' t' • shellTrans N s' t' =
      if s = s' then (if t = t' then c • shellTrans N s' t' else 0) else 0 := by
    intro s' t'
    rw [Matrix.single, Matrix.of_apply]
    by_cases h1 : s = s'
    · by_cases h2 : t = t'
      · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h1, ite_eq_left h2]
      · rw [ite_eq_right (fun h => h2 h.2), ite_eq_left h1, ite_eq_right h2, zero_smul]
    · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1, zero_smul]
  simp only [radialMatOp, h, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]

/-- **2e.** E_N は角の代数に入る：E_N = Φ([E_N])（E_N の像は定数関数で、P はそれを動かさない）。 -/
theorem convL_geps_self_eq (N : ℕ) [NeZero N] :
    PAG.Part15.convL (geps N N) = radialMatOp N (LinearMap.toMatrix (radialBasis N) (radialBasis N)
      (radialHom N ⟨PAG.Part15.convL (geps N N), PAG.Part232.convL_geps_mem N N⟩)) := by
  rw [← shellAvg_mul_eq]
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply]
  symm
  apply shellAvg_apply_of_radial
  intro a x
  show PAG.Part15.conv (geps N N) f ((a : ZMod N) * x) = PAG.Part15.conv (geps N N) f x
  rw [conv_geps_self]

/-- 殻の上の平均を引く作用素 Q_s = D_s − P_{s,s}：Q_s f = 1_{D_s}·(f − D_s の上の f の平均)。 -/
noncomputable def shellDev (N s : ℕ) [NeZero N] : Module.End ℂ (ZMod N → ℂ) :=
  LinearMap.mulLeft ℂ (dind N s) - shellTrans N s s

/-- **2f.** Q_s f = 1_{D_s}·f − (D_s の上の f の平均)·1_{D_s}。 -/
theorem shellDev_apply (N s : ℕ) [NeZero N] (f : ZMod N → ℂ) :
    shellDev N s f = dind N s * f - ((∑ y, dind N s y * f y) / (Nat.totient (N / s) : ℂ)) • dind N s := by
  rw [shellDev, LinearMap.sub_apply, LinearMap.mulLeft_apply, shellTrans_apply]

/-- **2g.** D_s P_{u,v} = [s = u]·P_{s,v}。 -/
theorem mulLeft_dind_mul_shellTrans (N s u v : ℕ) [NeZero N] :
    LinearMap.mulLeft ℂ (dind N s) * shellTrans N u v = if s = u then shellTrans N s v else 0 := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, LinearMap.mulLeft_apply, shellTrans_apply, mul_smul_comm, dind_mul]
  by_cases h : s = u
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, shellTrans_apply]
  · rw [ite_eq_right h, ite_eq_right h, smul_zero, LinearMap.zero_apply]

/-- **2h.** P_{u,v} D_s = [v = s]·P_{u,v}。 -/
theorem shellTrans_mul_mulLeft_dind (N u v s : ℕ) [NeZero N] :
    shellTrans N u v * LinearMap.mulLeft ℂ (dind N s) = if v = s then shellTrans N u v else 0 := by
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, LinearMap.mulLeft_apply, shellTrans_apply]
  have e : ∑ y, dind N v y * (dind N s * f) y = if v = s then ∑ y, dind N v y * f y else 0 := by
    by_cases hvs : v = s
    · subst hvs
      rw [ite_eq_left rfl]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Pi.mul_apply, ← mul_assoc, ← Pi.mul_apply (dind N v) (dind N v) y, dind_mul, ite_eq_left rfl]
    · rw [ite_eq_right hvs]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [Pi.mul_apply, ← mul_assoc, ← Pi.mul_apply (dind N v) (dind N s) y, dind_mul, ite_eq_right hvs,
        Pi.zero_apply, zero_mul]
  rw [e]
  by_cases hvs : v = s
  · rw [ite_eq_left hvs, ite_eq_left hvs, shellTrans_apply]
  · rw [ite_eq_right hvs, ite_eq_right hvs, zero_div, zero_smul, LinearMap.zero_apply]

/-- **2i.** Q_s P_{u,v} = 0（s ∣ N）。 -/
theorem shellDev_mul_shellTrans (N s u v : ℕ) [NeZero N] (hs : s ∣ N) :
    shellDev N s * shellTrans N u v = 0 := by
  rw [shellDev, sub_mul, mulLeft_dind_mul_shellTrans, shellTrans_mul N s s u v hs, sub_self]

/-- **2j.** P_{u,v} Q_s = 0（v ∣ N）。 -/
theorem shellTrans_mul_shellDev (N u v s : ℕ) [NeZero N] (hv : v ∣ N) :
    shellTrans N u v * shellDev N s = 0 := by
  rw [shellDev, mul_sub, shellTrans_mul_mulLeft_dind, shellTrans_mul N u v s s hv]
  by_cases h : v = s
  · subst h
    rw [ite_eq_left rfl, sub_self]
  · rw [ite_eq_right h, ite_eq_right h, sub_self]

/-- **2k.** Q_s Q_t = [s = t]·Q_s（s ∣ N）。 -/
theorem shellDev_mul_shellDev (N s t : ℕ) [NeZero N] (hs : s ∣ N) :
    shellDev N s * shellDev N t = if s = t then shellDev N s else 0 := by
  have hDD : LinearMap.mulLeft ℂ (dind N s) * LinearMap.mulLeft ℂ (dind N t) =
      if s = t then LinearMap.mulLeft ℂ (dind N s) else 0 := by
    apply LinearMap.ext
    intro f
    rw [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, dind_mul]
    split_ifs <;> simp
  rw [shellDev, shellDev, sub_mul, mul_sub, mul_sub, hDD, mulLeft_dind_mul_shellTrans,
    shellTrans_mul_mulLeft_dind, shellTrans_mul N s s t t hs]
  by_cases h : s = t
  · subst h
    simp only [↓reduceIte]
    abel
  · simp only [h, ↓reduceIte, sub_zero]

/-- **2l.** (Q_t δ_s)(s) = [s = t]·(1 − 1/φ(N/s))（s ∣ N）。 -/
theorem shellDev_single_apply (N t s : ℕ) [NeZero N] (hs : s ∣ N) :
    shellDev N t (Pi.single (s : ZMod N) 1) (s : ZMod N) =
      if s = t then 1 - ((Nat.totient (N / s) : ℂ))⁻¹ else 0 := by
  rw [shellDev_apply]
  have hsum : ∑ y, dind N t y * (Pi.single (s : ZMod N) (1 : ℂ) : ZMod N → ℂ) y = dind N t (s : ZMod N) := by
    rw [Finset.sum_eq_single (s : ZMod N)]
    · rw [Pi.single_eq_same, mul_one]
    · intro y _ hy
      rw [Pi.single_eq_of_ne hy, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hsum, Pi.single_eq_same, mul_one,
    dind_natCast t hs]
  by_cases h : s = t
  · subst h
    simp only [↓reduceIte]
    ring
  · simp only [h, ↓reduceIte]
    ring

/-- **2m.** Q_s = 0 ⇔ φ(N/s) = 1（s ∣ N。Mathlib の `Nat.totient_eq_one_iff` で N/s = 1, 2）。 -/
theorem shellDev_eq_zero_iff (N s : ℕ) [NeZero N] (hs : s ∣ N) :
    shellDev N s = 0 ↔ Nat.totient (N / s) = 1 := by
  constructor
  · intro h
    have e := shellDev_single_apply N s s hs
    rw [h, LinearMap.zero_apply, Pi.zero_apply, ite_eq_left rfl] at e
    have h' : ((Nat.totient (N / s) : ℂ))⁻¹ = 1 := by linear_combination e
    exact_mod_cast inv_eq_one.mp h'
  · intro hφ
    apply LinearMap.ext
    intro f
    funext x
    rw [shellDev_apply, LinearMap.zero_apply, Pi.zero_apply, hφ, Nat.cast_one, div_one]
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx : Nat.gcd N x.val = s
    · have huniq : ∀ y : ZMod N, Nat.gcd N y.val = s → y = x := by
        intro y hy
        have hcard := card_dsh N s hs
        rw [hφ] at hcard
        exact Finset.card_le_one.mp hcard.le y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩) x
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
      have hdx : dind N s x = 1 := by
        show (if Nat.gcd N x.val = s then (1 : ℂ) else 0) = 1
        exact ite_eq_left hx
      have hsum : ∑ y, dind N s y * f y = f x := by
        rw [Finset.sum_eq_single x]
        · rw [hdx, one_mul]
        · intro y _ hy
          have hdy : dind N s y = 0 := by
            show (if Nat.gcd N y.val = s then (1 : ℂ) else 0) = 0
            exact ite_eq_right (fun h => hy (huniq y h))
          rw [hdy, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ x) h
      rw [hsum, hdx]
      ring
    · have hdx : dind N s x = 0 := by
        show (if Nat.gcd N x.val = s then (1 : ℂ) else 0) = 0
        exact ite_eq_right hx
      rw [hdx]
      ring

/-! ### 3. 空間全体の ⟨D_s, E_N⟩ ≅ M_{d(N)}(ℂ) × ℂ^{S′} -/

/-- 0 でない Q_s の番号 S′ = {s ∣ N : φ(N/s) ≠ 1}。 -/
def devSet (N : ℕ) : Finset ℕ := N.divisors.filter (fun s => Nat.totient (N / s) ≠ 1)

/-- **3a.** S′ の元は N の約数。 -/
theorem dvd_of_mem_devSet {N : ℕ} (s : devSet N) : (s : ℕ) ∣ N :=
  Nat.dvd_of_mem_divisors (Finset.mem_filter.mp s.2).1

/-- **3b.** #{s ∣ N : φ(N/s) = 1} = 1 + [2 ∣ N]（s = N と、N が偶数なら s = N/2）。 -/
theorem card_filter_totient_eq_one (N : ℕ) [NeZero N] :
    (N.divisors.filter (fun s => Nat.totient (N / s) = 1)).card = 1 + if 2 ∣ N then 1 else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  have key : ∀ s, s ∈ N.divisors.filter (fun s => Nat.totient (N / s) = 1) ↔ s = N ∨ (2 ∣ N ∧ s = N / 2) := by
    intro s
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.totient_eq_one_iff]
    constructor
    · rintro ⟨⟨hs, -⟩, h | h⟩
      · exact Or.inl (Nat.eq_of_dvd_of_div_eq_one hs h)
      · right
        have e : N = 2 * s := by
          have := Nat.div_mul_cancel hs
          rw [h] at this
          omega
        exact ⟨⟨s, e⟩, by rw [e, Nat.mul_div_cancel_left s two_pos]⟩
    · rintro (rfl | ⟨h2, rfl⟩)
      · exact ⟨⟨dvd_rfl, hN⟩, Or.inl (Nat.div_self (Nat.pos_of_ne_zero hN))⟩
      · exact ⟨⟨Nat.div_dvd_of_dvd h2, hN⟩, Or.inr (Nat.div_div_self h2 hN)⟩
  by_cases h2 : 2 ∣ N
  · have hne : N ≠ N / 2 := by
      have := Nat.pos_of_ne_zero hN
      omega
    have e : N.divisors.filter (fun s => Nat.totient (N / s) = 1) = {N, N / 2} := by
      ext s
      rw [key, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [e, Finset.card_pair hne, ite_eq_left h2]
  · have e : N.divisors.filter (fun s => Nat.totient (N / s) = 1) = {N} := by
      ext s
      rw [key, Finset.mem_singleton]
      tauto
    rw [e, Finset.card_singleton, ite_eq_right h2]

/-- **3c.** #S′ + 1 + [2 ∣ N] = d(N)。 -/
theorem card_devSet (N : ℕ) [NeZero N] :
    (devSet N).card + 1 + (if 2 ∣ N then 1 else 0) = N.divisors.card := by
  calc (devSet N).card + 1 + (if 2 ∣ N then 1 else 0)
      = (N.divisors.filter (fun s => Nat.totient (N / s) = 1)).card + (devSet N).card := by
        rw [card_filter_totient_eq_one]
        ring
    _ = N.divisors.card := Finset.card_filter_add_card_filter_not _

/-- **3d.** Σ_{s ∈ S′} Q_s = Σ_{s ∣ N} Q_s（φ(N/s) = 1 の項は 0）。 -/
theorem sum_devSet_shellDev (N : ℕ) [NeZero N] :
    ∑ s : devSet N, shellDev N s = ∑ s ∈ N.divisors, shellDev N s := by
  rw [Finset.sum_coe_sort (devSet N) (fun s => shellDev N s), devSet]
  apply Finset.sum_filter_of_ne
  intro s hs hne hφ
  exact hne ((shellDev_eq_zero_iff N s (Nat.dvd_of_mem_divisors hs)).mpr hφ)

/-- **3e.** P + Σ_{s ∈ S′} Q_s = 1。 -/
theorem shellAvg_add_sum_shellDev (N : ℕ) [NeZero N] :
    shellAvg N + ∑ s : devSet N, shellDev N s = 1 := by
  rw [sum_devSet_shellDev, shellAvg, ← Finset.sum_add_distrib, ← PAG.Part232.sum_mulLeft_dind N]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [shellDev]
  abel

/-- **3f.** Φ(M) Q_s = 0。 -/
theorem radialMatOp_mul_shellDev (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) (s : ℕ) :
    radialMatOp N M * shellDev N s = 0 := by
  rw [radialMatOp, Finset.sum_mul]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [smul_mul_assoc, shellTrans_mul_shellDev N u v s (Nat.dvd_of_mem_divisors v.2), smul_zero]

/-- **3g.** Q_s Φ(M) = 0（s ∣ N）。 -/
theorem shellDev_mul_radialMatOp (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) {s : ℕ} (hs : s ∣ N) :
    shellDev N s * radialMatOp N M = 0 := by
  rw [radialMatOp, Finset.mul_sum]
  refine Finset.sum_eq_zero (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero (fun v _ => ?_)
  rw [mul_smul_comm, shellDev_mul_shellTrans N s u v hs, smul_zero]

/-- **3h.** S′ を番号にした形：Q_s Q_t = [s = t]·Q_s。 -/
theorem shellDev_mul_shellDev_devSet (N : ℕ) [NeZero N] (s t : devSet N) :
    shellDev N s * shellDev N t = if s = t then shellDev N s else 0 := by
  rw [shellDev_mul_shellDev N s t (dvd_of_mem_devSet s)]
  by_cases h : s = t
  · rw [ite_eq_left (congrArg Subtype.val h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (Subtype.ext e)), ite_eq_right h]

/-- Ψ(M, b) = Σ M_{st} P_{s,t} + Σ_{s ∈ S′} b_s Q_s（線形写像）。 -/
noncomputable def wholeMap (N : ℕ) [NeZero N] :
    (Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) →ₗ[ℂ] Module.End ℂ (ZMod N → ℂ) where
  toFun p := radialMatOp N p.1 + ∑ s : devSet N, p.2 s • shellDev N s
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, radialMatOp_add]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
      radialMatOp_smul, RingHom.id_apply, smul_add]

/-- **3i.** Ψ の値。 -/
theorem wholeMap_apply (N : ℕ) [NeZero N] (p : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    wholeMap N p = radialMatOp N p.1 + ∑ s : devSet N, p.2 s • shellDev N s := rfl

/-- **3j.** Ψ(1, 1) = 1。 -/
theorem wholeMap_one (N : ℕ) [NeZero N] : wholeMap N 1 = 1 := by
  rw [wholeMap_apply, Prod.fst_one, Prod.snd_one, radialMatOp_one_eq]
  simp only [Pi.one_apply, one_smul]
  exact shellAvg_add_sum_shellDev N

/-- **3k.** Ψ は積を保つ：Ψ(M, b)Ψ(M′, b′) = Ψ(MM′, bb′)。 -/
theorem wholeMap_mul (N : ℕ) [NeZero N] (p q : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    wholeMap N (p * q) = wholeMap N p * wholeMap N q := by
  have h1 : radialMatOp N p.1 * ∑ t : devSet N, q.2 t • shellDev N t = 0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero (fun t _ => by rw [mul_smul_comm, radialMatOp_mul_shellDev, smul_zero])
  have h2 : (∑ s : devSet N, p.2 s • shellDev N s) * radialMatOp N q.1 = 0 := by
    rw [Finset.sum_mul]
    exact Finset.sum_eq_zero (fun s _ => by
      rw [smul_mul_assoc, shellDev_mul_radialMatOp N q.1 (dvd_of_mem_devSet s), smul_zero])
  have h3 : (∑ s : devSet N, p.2 s • shellDev N s) * (∑ t : devSet N, q.2 t • shellDev N t) =
      ∑ s : devSet N, (p.2 s * q.2 s) • shellDev N s := by
    rw [Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [smul_mul_smul_comm, shellDev_mul_shellDev_devSet, smul_ite, smul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  rw [wholeMap_apply, wholeMap_apply, wholeMap_apply, add_mul, mul_add, mul_add, h1, h2, h3,
    Prod.fst_mul, Prod.snd_mul, radialMatOp_mul]
  simp only [Pi.mul_apply, add_zero, zero_add]

/-- 代数準同型 Ψ : M_{d(N)}(ℂ) × ℂ^{S′} → End(ℂ^{ℤ/N})。 -/
noncomputable def wholeHom (N : ℕ) [NeZero N] :
    (Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) →ₐ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  AlgHom.ofLinearMap (wholeMap N) (wholeMap_one N) (wholeMap_mul N)

/-- **3l.** wholeHom の値。 -/
theorem wholeHom_apply (N : ℕ) [NeZero N] (p : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    wholeHom N p = wholeMap N p := rfl

/-- **3m.** P Ψ(M, b) = Φ(M)。 -/
theorem shellAvg_mul_wholeMap (N : ℕ) [NeZero N] (p : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    shellAvg N * wholeMap N p = radialMatOp N p.1 := by
  have h0 : shellAvg N * ∑ s : devSet N, p.2 s • shellDev N s = 0 := by
    rw [← radialMatOp_one_eq, Finset.mul_sum]
    exact Finset.sum_eq_zero (fun s _ => by rw [mul_smul_comm, radialMatOp_mul_shellDev, smul_zero])
  rw [wholeMap_apply, mul_add, shellAvg_mul_radialMatOp, h0, add_zero]

/-- **3n.** Ψ は単射。 -/
theorem wholeMap_injective (N : ℕ) [NeZero N] : Function.Injective (wholeMap N) := by
  refine (injective_iff_map_eq_zero (wholeMap N)).mpr (fun p hp => ?_)
  have hM : p.1 = 0 := by
    have e := shellAvg_mul_wholeMap N p
    rw [hp, mul_zero] at e
    exact radialMatOp_injective N (e.symm.trans (radialMatOp_zero N).symm)
  have hb : p.2 = 0 := by
    funext s
    have e := congrArg (fun T : Module.End ℂ (ZMod N → ℂ) =>
      T (Pi.single ((s : ℕ) : ZMod N) 1) ((s : ℕ) : ZMod N)) hp
    simp only [wholeMap_apply, hM, radialMatOp_zero, zero_add, LinearMap.zero_apply, Pi.zero_apply,
      LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [Finset.sum_eq_single s] at e
    · rw [shellDev_single_apply N s s (dvd_of_mem_devSet s), ite_eq_left rfl] at e
      have hφ1 : Nat.totient (N / s) ≠ 1 := (Finset.mem_filter.mp s.2).2
      have hφ : (1 : ℂ) - ((Nat.totient (N / s) : ℂ))⁻¹ ≠ 0 := by
        intro h
        have h' : ((Nat.totient (N / s) : ℂ))⁻¹ = 1 := by linear_combination -h
        exact hφ1 (by exact_mod_cast inv_eq_one.mp h')
      exact (mul_eq_zero.mp e).resolve_right hφ
    · intro t _ hts
      rw [shellDev_single_apply N t s (dvd_of_mem_devSet s),
        ite_eq_right (fun e => hts (Subtype.ext e).symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ s) h
  exact Prod.ext hM hb

/-- **3o.** P_{s,t} ∈ ⟨D_u, E_N⟩。 -/
theorem shellTrans_mem_oneEAlg (N s t : ℕ) [NeZero N] : shellTrans N s t ∈ oneEAlg N N :=
  Subalgebra.smul_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _
    (Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)) (Algebra.subset_adjoin (Or.inr (Set.mem_singleton _))))
    (Algebra.subset_adjoin (Or.inl ⟨t, rfl⟩))) _

/-- **3p.** Φ(M) ∈ ⟨D_u, E_N⟩。 -/
theorem radialMatOp_mem_oneEAlg (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M ∈ oneEAlg N N :=
  Subalgebra.sum_mem _ (fun s _ => Subalgebra.sum_mem _ (fun t _ =>
    Subalgebra.smul_mem _ (shellTrans_mem_oneEAlg N s t) _))

/-- **3q.** Q_s ∈ ⟨D_u, E_N⟩。 -/
theorem shellDev_mem_oneEAlg (N s : ℕ) [NeZero N] : shellDev N s ∈ oneEAlg N N :=
  Subalgebra.sub_mem _ (Algebra.subset_adjoin (Or.inl ⟨s, rfl⟩)) (shellTrans_mem_oneEAlg N s s)

/-- **3r.** Φ(M) は Ψ の像に入る。 -/
theorem radialMatOp_mem_range (N : ℕ) [NeZero N] (M : Matrix N.divisors N.divisors ℂ) :
    radialMatOp N M ∈ (wholeHom N).range := by
  refine (AlgHom.mem_range _).mpr ⟨(M, 0), ?_⟩
  rw [wholeHom_apply, wholeMap_apply]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]

/-- **3s.** Q_s は Ψ の像に入る（s ∣ N）。 -/
theorem shellDev_mem_range (N s : ℕ) [NeZero N] (hs : s ∣ N) : shellDev N s ∈ (wholeHom N).range := by
  by_cases hφ : Nat.totient (N / s) = 1
  · rw [(shellDev_eq_zero_iff N s hs).mpr hφ]
    exact Subalgebra.zero_mem _
  · have hmem : s ∈ devSet N := Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hs, NeZero.ne N⟩, hφ⟩
    refine (AlgHom.mem_range _).mpr ⟨(0, Pi.single ⟨s, hmem⟩ 1), ?_⟩
    rw [wholeHom_apply, wholeMap_apply]
    dsimp only
    rw [radialMatOp_zero, zero_add, Finset.sum_eq_single ⟨s, hmem⟩]
    · rw [Pi.single_eq_same, one_smul]
    · intro t _ ht
      rw [Pi.single_eq_of_ne ht, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **3t.** D_u は Ψ の像に入る（u ∤ N なら D_u = 0）。 -/
theorem mulLeft_dind_mem_range (N u : ℕ) [NeZero N] : LinearMap.mulLeft ℂ (dind N u) ∈ (wholeHom N).range := by
  by_cases hu : u ∣ N
  · have hdec : LinearMap.mulLeft ℂ (dind N u) = shellTrans N u u + shellDev N u := by
      rw [shellDev]
      abel
    have hu' : u ∈ N.divisors := Nat.mem_divisors.mpr ⟨hu, NeZero.ne N⟩
    have hP : shellTrans N u u = radialMatOp N (Matrix.single ⟨u, hu'⟩ ⟨u, hu'⟩ 1) := by
      rw [radialMatOp_single, one_smul]
    rw [hdec, hP]
    exact Subalgebra.add_mem _ (radialMatOp_mem_range N _) (shellDev_mem_range N u hu)
  · rw [PAG.Part232.dind_eq_zero_of_not_dvd hu, LinearMap.mulLeft_zero_eq_zero]
    exact Subalgebra.zero_mem _

/-- **3u.** Ψ の像は ⟨D_u, E_N⟩ そのもの。 -/
theorem range_wholeHom (N : ℕ) [NeZero N] : (wholeHom N).range = oneEAlg N N := by
  apply le_antisymm
  · intro T hT
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hT
    rw [wholeHom_apply, wholeMap_apply]
    exact Subalgebra.add_mem _ (radialMatOp_mem_oneEAlg N p.1)
      (Subalgebra.sum_mem _ (fun s _ => Subalgebra.smul_mem _ (shellDev_mem_oneEAlg N s) _))
  · apply Algebra.adjoin_le
    rintro _ (⟨u, rfl⟩ | h)
    · exact mulLeft_dind_mem_range N u
    · rw [Set.mem_singleton_iff.mp h, convL_geps_self_eq]
      exact radialMatOp_mem_range N _

/-- 代数の同型 M_{d(N)}(ℂ) × ℂ^{S′} ≃ ⟨D_u, E_N⟩（ウェダーバーン分解）。 -/
noncomputable def wholeAlgEquiv (N : ℕ) [NeZero N] :
    (Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) ≃ₐ[ℂ] oneEAlg N N :=
  (AlgEquiv.ofInjective (wholeHom N) (wholeMap_injective N)).trans
    (Subalgebra.equivOfEq _ _ (range_wholeHom N))

/-- **3v.** wholeAlgEquiv の値は Ψ(M, b)。 -/
theorem wholeAlgEquiv_apply (N : ℕ) [NeZero N] (p : Matrix N.divisors N.divisors ℂ × (devSet N → ℂ)) :
    (wholeAlgEquiv N p : Module.End ℂ (ZMod N → ℂ)) = wholeMap N p := rfl

/-- **3w.** ⟨D_u, E_N⟩ は Ψ の像（部分空間として）。 -/
theorem toSubmodule_oneEAlg_self (N : ℕ) [NeZero N] :
    Subalgebra.toSubmodule (oneEAlg N N) = LinearMap.range (wholeMap N) := by
  ext T
  rw [Subalgebra.mem_toSubmodule, ← range_wholeHom, AlgHom.mem_range, LinearMap.mem_range]
  rfl

/-- **3x.** dim ⟨D_u, E_N⟩ = d(N)² + #S′。 -/
theorem finrank_oneEAlg_self (N : ℕ) [NeZero N] :
    Module.finrank ℂ (oneEAlg N N) = N.divisors.card ^ 2 + (devSet N).card := by
  have h1 : Module.finrank ℂ (Subalgebra.toSubmodule (oneEAlg N N)) = N.divisors.card ^ 2 + (devSet N).card := by
    rw [toSubmodule_oneEAlg_self, LinearMap.finrank_range_of_inj (wholeMap_injective N), Module.finrank_prod,
      Module.finrank_matrix, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
      Fintype.card_coe, mul_one, sq]
  exact (Subalgebra.finrank_toSubmodule _).symm.trans h1

/-- **3y.** dim ⟨D_u, E_N⟩ + 1 + [2 ∣ N] = d(N)² + d(N)。 -/
theorem finrank_oneEAlg_self_add (N : ℕ) [NeZero N] :
    Module.finrank ℂ (oneEAlg N N) + 1 + (if 2 ∣ N then 1 else 0) = N.divisors.card ^ 2 + N.divisors.card := by
  rw [finrank_oneEAlg_self, ← card_devSet N]
  ring

/-- **3z.** dim ⟨D_u, E_N⟩ = d(N)² + d(N) − 1 − [2 ∣ N]。 -/
theorem finrank_oneEAlg_self_sub (N : ℕ) [NeZero N] :
    Module.finrank ℂ (oneEAlg N N) = N.divisors.card ^ 2 + N.divisors.card - 1 - (if 2 ∣ N then 1 else 0) := by
  have h := finrank_oneEAlg_self_add N
  generalize Module.finrank ℂ (oneEAlg N N) = r at h ⊢
  generalize (if 2 ∣ N then 1 else 0) = k at h ⊢
  generalize N.divisors.card ^ 2 + N.divisors.card = m at h ⊢
  omega

/-! ### 4. 中心：Z(⟨D_u, E_N⟩) = {c·P + Σ_{s ∈ S′} b_s Q_s}（1 + #S′ 次元） -/

/-- **4a.** Ψ(c·1, b) = c·P + Σ_{s ∈ S′} b_s Q_s。 -/
theorem wholeMap_smul_one (N : ℕ) [NeZero N] (c : ℂ) (b : devSet N → ℂ) :
    wholeMap N (c • 1, b) = c • shellAvg N + ∑ s : devSet N, b s • shellDev N s := by
  rw [wholeMap_apply]
  dsimp only
  rw [radialMatOp_smul, radialMatOp_one_eq]

/-- **4b.** ⟨D_u, E_N⟩ の元 T が中心に入る ⇔ T = c·P + Σ_{s ∈ S′} b_s Q_s。 -/
theorem mem_center_oneEAlg_iff (N : ℕ) [NeZero N] (T : oneEAlg N N) :
    T ∈ Subalgebra.center ℂ (oneEAlg N N) ↔
      ∃ (c : ℂ) (b : devSet N → ℂ),
        (T : Module.End ℂ (ZMod N → ℂ)) = c • shellAvg N + ∑ s : devSet N, b s • shellDev N s := by
  have hrange : ∀ S : oneEAlg N N, ∃ p, wholeMap N p = (S : Module.End ℂ (ZMod N → ℂ)) := by
    intro S
    have hS : (S : Module.End ℂ (ZMod N → ℂ)) ∈ (wholeHom N).range := by
      rw [range_wholeHom]
      exact S.2
    exact (AlgHom.mem_range _).mp hS
  rw [Subalgebra.mem_center_iff]
  obtain ⟨p, hp⟩ := hrange T
  constructor
  · intro hT
    have hcomm : ∀ X : Matrix N.divisors N.divisors ℂ, X * p.1 = p.1 * X := by
      intro X
      have hX : wholeMap N (X, 0) ∈ oneEAlg N N := by
        rw [← range_wholeHom]
        exact (AlgHom.mem_range _).mpr ⟨(X, 0), rfl⟩
      have e : wholeMap N (X, 0) * (T : Module.End ℂ (ZMod N → ℂ)) =
          (T : Module.End ℂ (ZMod N → ℂ)) * wholeMap N (X, 0) :=
        congrArg Subtype.val (hT ⟨wholeMap N (X, 0), hX⟩)
      rw [← hp, ← wholeMap_mul, ← wholeMap_mul] at e
      have e2 := congrArg Prod.fst (wholeMap_injective N e)
      simpa only [Prod.fst_mul] using e2
    have hM : p.1 ∈ Set.center (Matrix N.divisors N.divisors ℂ) := Semigroup.mem_center_iff.mpr hcomm
    rw [Matrix.center_eq_range] at hM
    obtain ⟨c, hc⟩ := hM
    refine ⟨c, p.2, ?_⟩
    have hp1 : p.1 = c • (1 : Matrix N.divisors N.divisors ℂ) := by
      rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [← hp, ← wholeMap_smul_one, ← hp1]
  · rintro ⟨c, b, hTc⟩ S
    obtain ⟨q, hq⟩ := hrange S
    apply Subtype.ext
    show (S : Module.End ℂ (ZMod N → ℂ)) * (T : Module.End ℂ (ZMod N → ℂ)) =
      (T : Module.End ℂ (ZMod N → ℂ)) * (S : Module.End ℂ (ZMod N → ℂ))
    rw [hTc, ← wholeMap_smul_one, ← hq, ← wholeMap_mul, ← wholeMap_mul]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    · simp only [Prod.snd_mul, mul_comm]

/-- (c, b) ↦ c·P + Σ_{s ∈ S′} b_s Q_s（中心の元の形、線形写像）。 -/
noncomputable def centerMap (N : ℕ) [NeZero N] : (ℂ × (devSet N → ℂ)) →ₗ[ℂ] Module.End ℂ (ZMod N → ℂ) :=
  (wholeMap N).comp
    (LinearMap.prodMap (LinearMap.toSpanSingleton ℂ _ (1 : Matrix N.divisors N.divisors ℂ)) LinearMap.id)

/-- **4c.** centerMap の値。 -/
theorem centerMap_apply (N : ℕ) [NeZero N] (c : ℂ) (b : devSet N → ℂ) :
    centerMap N (c, b) = c • shellAvg N + ∑ s : devSet N, b s • shellDev N s := by
  rw [centerMap, LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply,
    wholeMap_smul_one]

/-- **4d.** centerMap は単射（P, Q_s (s ∈ S′) は一次独立）。 -/
theorem centerMap_injective (N : ℕ) [NeZero N] : Function.Injective (centerMap N) := by
  refine (wholeMap_injective N).comp ?_
  rintro ⟨c, b⟩ ⟨c', b'⟩ h
  simp only [LinearMap.prodMap_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have i0 : N.divisors := ⟨N, Nat.mem_divisors_self N (NeZero.ne N)⟩
  have hc : c = c' := by
    have := congrFun (congrFun h1 i0) i0
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using this
  rw [hc, h2]

/-- **4e.** ⟨D_u, E_N⟩ の元 T が中心に入る ⇔ T は centerMap の像に入る。 -/
theorem mem_center_oneEAlg_iff_range (N : ℕ) [NeZero N] (T : oneEAlg N N) :
    T ∈ Subalgebra.center ℂ (oneEAlg N N) ↔ (T : Module.End ℂ (ZMod N → ℂ)) ∈ LinearMap.range (centerMap N) := by
  rw [mem_center_oneEAlg_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨c, b, h⟩
    exact ⟨(c, b), by rw [centerMap_apply, h]⟩
  · rintro ⟨⟨c, b⟩, h⟩
    exact ⟨c, b, by rw [← h, centerMap_apply]⟩

/-- **4f.** 中心の元の形の作用素の空間の次元は 1 + #S′（ウェダーバーン成分の個数）。 -/
theorem finrank_range_centerMap (N : ℕ) [NeZero N] :
    Module.finrank ℂ (LinearMap.range (centerMap N)) = 1 + (devSet N).card := by
  rw [LinearMap.finrank_range_of_inj (centerMap_injective N), Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

/-- **4g.** その次元に [2 ∣ N] を足すと d(N)（1 + #S′ = d(N) − [2 ∣ N]）。 -/
theorem finrank_range_centerMap_add (N : ℕ) [NeZero N] :
    Module.finrank ℂ (LinearMap.range (centerMap N)) + (if 2 ∣ N then 1 else 0) = N.divisors.card := by
  rw [finrank_range_centerMap, ← card_devSet N]
  ring

end PAG.Part245

#print axioms PAG.Part245.ramSum_gcd
#print axioms PAG.Part245.ramSum_mod
#print axioms PAG.Part245.ramSum_of_coprime
#print axioms PAG.Part245.totientDivGcd
#print axioms PAG.Part245.moebiusDivGcd
#print axioms PAG.Part245.totientDivGcd_apply
#print axioms PAG.Part245.moebiusDivGcd_apply
#print axioms PAG.Part245.gcd_mul_of_coprime
#print axioms PAG.Part245.mul_div_gcd_of_coprime
#print axioms PAG.Part245.coprime_div_gcd_of_coprime
#print axioms PAG.Part245.isMultiplicative_totientDivGcd
#print axioms PAG.Part245.isMultiplicative_moebiusDivGcd
#print axioms PAG.Part245.ramSum_mul_totient_primePow
#print axioms PAG.Part245.ramSum_mul_totient
#print axioms PAG.Part245.div_gcd_pos
#print axioms PAG.Part245.ramSum_eq_div
#print axioms PAG.Part245.ramSum_ne_zero_iff_squarefree
#print axioms PAG.Part245.ramSum_of_dvd
#print axioms PAG.Part245.ramMat_eq_closed
#print axioms PAG.Part245.radialMatOp_add
#print axioms PAG.Part245.radialMatOp_smul
#print axioms PAG.Part245.radialMatOp_zero
#print axioms PAG.Part245.radialMatOp_single
#print axioms PAG.Part245.convL_geps_self_eq
#print axioms PAG.Part245.shellDev
#print axioms PAG.Part245.shellDev_apply
#print axioms PAG.Part245.mulLeft_dind_mul_shellTrans
#print axioms PAG.Part245.shellTrans_mul_mulLeft_dind
#print axioms PAG.Part245.shellDev_mul_shellTrans
#print axioms PAG.Part245.shellTrans_mul_shellDev
#print axioms PAG.Part245.shellDev_mul_shellDev
#print axioms PAG.Part245.shellDev_single_apply
#print axioms PAG.Part245.shellDev_eq_zero_iff
#print axioms PAG.Part245.devSet
#print axioms PAG.Part245.dvd_of_mem_devSet
#print axioms PAG.Part245.card_filter_totient_eq_one
#print axioms PAG.Part245.card_devSet
#print axioms PAG.Part245.sum_devSet_shellDev
#print axioms PAG.Part245.shellAvg_add_sum_shellDev
#print axioms PAG.Part245.radialMatOp_mul_shellDev
#print axioms PAG.Part245.shellDev_mul_radialMatOp
#print axioms PAG.Part245.shellDev_mul_shellDev_devSet
#print axioms PAG.Part245.wholeMap
#print axioms PAG.Part245.wholeMap_apply
#print axioms PAG.Part245.wholeMap_one
#print axioms PAG.Part245.wholeMap_mul
#print axioms PAG.Part245.wholeHom
#print axioms PAG.Part245.wholeHom_apply
#print axioms PAG.Part245.shellAvg_mul_wholeMap
#print axioms PAG.Part245.wholeMap_injective
#print axioms PAG.Part245.shellTrans_mem_oneEAlg
#print axioms PAG.Part245.radialMatOp_mem_oneEAlg
#print axioms PAG.Part245.shellDev_mem_oneEAlg
#print axioms PAG.Part245.radialMatOp_mem_range
#print axioms PAG.Part245.shellDev_mem_range
#print axioms PAG.Part245.mulLeft_dind_mem_range
#print axioms PAG.Part245.range_wholeHom
#print axioms PAG.Part245.wholeAlgEquiv
#print axioms PAG.Part245.wholeAlgEquiv_apply
#print axioms PAG.Part245.toSubmodule_oneEAlg_self
#print axioms PAG.Part245.finrank_oneEAlg_self
#print axioms PAG.Part245.finrank_oneEAlg_self_add
#print axioms PAG.Part245.finrank_oneEAlg_self_sub
#print axioms PAG.Part245.wholeMap_smul_one
#print axioms PAG.Part245.mem_center_oneEAlg_iff
#print axioms PAG.Part245.centerMap
#print axioms PAG.Part245.centerMap_apply
#print axioms PAG.Part245.centerMap_injective
#print axioms PAG.Part245.mem_center_oneEAlg_iff_range
#print axioms PAG.Part245.finrank_range_centerMap
#print axioms PAG.Part245.finrank_range_centerMap_add
