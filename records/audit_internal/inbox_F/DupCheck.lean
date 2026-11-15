import PAG260
/-! 内部の重複の確認（Part 257 の着手前）。Part 256（PAG260）の 2 つの定理が、
第 II 期の定理（Part 189 ＝ PAG193、Part 190 ＝ PAG194）からそのまま出ることを確かめる。
新しい定理ではない。証明は既存の定理を当てるだけ。 -/
open DirichletCharacter

namespace PAG.DupCheck257

variable {M N : ℕ} [NeZero M] [NeZero N]

/-- Part 256 の `gaussSum_prodChar` は Part 189 の `gaussSum_mul_coprime` そのもの。 -/
theorem dup_gaussSum (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (PAG.Part260.prodChar χ₁ χ₂) (ZMod.stdAddChar (N := M * N)) =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ (ZMod.stdAddChar (N := M)) * gaussSum χ₂ (ZMod.stdAddChar (N := N)) :=
  PAG.Part193.gaussSum_mul_coprime h χ₁ χ₂

/-- Part 256 の `isPrimitive_prodChar` は Part 190 の `isPrimitive_mul` そのもの。 -/
theorem dup_isPrimitive (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (PAG.Part260.prodChar χ₁ χ₂).IsPrimitive :=
  PAG.Part194.isPrimitive_mul h χ₁ χ₂ h1 h2

/-- 逆向き：Part 256 の定理から Part 189 の文も出る（同じ文であることの確認）。 -/
theorem dup_gaussSum_rev (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (χ₁.changeLevel (dvd_mul_right M N) * χ₂.changeLevel (dvd_mul_left N M)) (ZMod.stdAddChar (N := M * N))
      = χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ (ZMod.stdAddChar (N := M)) * gaussSum χ₂ (ZMod.stdAddChar (N := N)) :=
  PAG.Part260.gaussSum_prodChar h χ₁ χ₂

#print axioms dup_gaussSum
#print axioms dup_isPrimitive
#print axioms dup_gaussSum_rev

end PAG.DupCheck257
