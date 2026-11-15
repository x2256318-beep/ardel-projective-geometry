theorem S1 (x : ZMod M × ZMod N) :
    ((Ψ1 M N x : ZMod (M * N)).cast : ZMod M) = x.1 * (N : ZMod M)
theorem S2 (x : ZMod M × ZMod N) :
    ((Ψ1 M N x : ZMod (M * N)).cast : ZMod N) = x.2 * (M : ZMod N)
theorem S3 (h : M.Coprime N) : Function.Bijective (Ψ1 M N)
theorem S4 (x : ZMod M × ZMod N) :
    stdAddChar (Ψ1 M N x) = stdAddChar x.1 * stdAddChar x.2
theorem S5 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (a : ZMod (M * N)) :
    Φ1 χ₁ χ₂ a = χ₁ (a.cast : ZMod M) * χ₂ (a.cast : ZMod N)
theorem S6 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    gaussSum (Φ1 χ₁ χ₂) stdAddChar =
      χ₁ (N : ZMod M) * χ₂ (M : ZMod N) * gaussSum χ₁ stdAddChar * gaussSum χ₂ stdAddChar
theorem S7 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    Φ1 χ₁ χ₂ (-1) = χ₁ (-1) * χ₂ (-1)
theorem S8 {χ₁ : DirichletCharacter ℂ M} {χ₂ : DirichletCharacter ℂ N}
    (h1 : χ₁.Odd) (h2 : χ₂.Odd) : Θ1 χ₁ χ₂ = -1
theorem S9 {χ₁ : DirichletCharacter ℂ M} (χ₂ : DirichletCharacter ℂ N)
    (h1 : χ₁.Even) : Θ1 χ₁ χ₂ = 1
theorem S10 (χ₁ : DirichletCharacter ℂ M) {χ₂ : DirichletCharacter ℂ N}
    (h2 : χ₂.Even) : Θ1 χ₁ χ₂ = 1
theorem S11 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N) :
    Ξ2 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * Ξ2 χ₁ * Ξ2 χ₂
theorem S12 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    Ξ1 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ1 χ₁ * Ξ1 χ₂)
theorem S13 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    (Φ1 χ₁ χ₂).IsPrimitive
theorem S14 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    Ξ3 (Φ1 χ₁ χ₂) =
      Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ3 χ₁ * Ξ3 χ₂)
theorem S15 (h : M.Coprime N) {χ₁ : DirichletCharacter ℂ M}
    {χ₂ : DirichletCharacter ℂ N} (h1 : χ₁.IsPrimitive) (h2 : χ₂.IsPrimitive) :
    Ξ4 (Ξ5 (Φ1 χ₁ χ₂)) =
      (Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) *
        (Ξ3 χ₁ * Ξ3 χ₂)) •
        Ξ5 (Φ1 χ₁ χ₂)
theorem S16 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) (w1 : Ξ1 χ₁ = 1)
    (w2 : Ξ1 χ₂ = 1) (w12 : Ξ1 (Φ1 χ₁ χ₂) = 1) :
    Θ1 χ₁ χ₂ * (χ₁ (N : ZMod M) * χ₂ (M : ZMod N)) = 1
theorem S17 : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Odd
theorem S18 :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      Ξ1 (Φ1 χ₁ χ₂) ≠ Ξ1 χ₁ * Ξ1 χ₂
theorem S19 :
    ∃ (χ₁ : DirichletCharacter ℂ 3) (χ₂ : DirichletCharacter ℂ 5), χ₁.IsPrimitive ∧ χ₂.IsPrimitive ∧
      Ξ3 (Φ1 χ₁ χ₂) ≠ Ξ3 χ₁ * Ξ3 χ₂
theorem S20 {n : ℕ} (χ : DirichletCharacter ℂ n) (a : (ZMod n)ˣ) : ‖χ a‖ = 1
theorem S21 (h : M.Coprime N) (χ₁ : DirichletCharacter ℂ M)
    (χ₂ : DirichletCharacter ℂ N) :
    ‖χ₁ (N : ZMod M) * χ₂ (M : ZMod N)‖ = 1
theorem S22 (χ₁ : DirichletCharacter ℂ M) (χ₂ : DirichletCharacter ℂ N)
    (u : (ZMod (M * N))ˣ) :
    Ξ5 (Φ1 χ₁ χ₂) u =
      Ξ5 χ₁ (ZMod.unitsMap (dvd_mul_right M N) u) *
        Ξ5 χ₂ (ZMod.unitsMap (dvd_mul_left N M) u)
