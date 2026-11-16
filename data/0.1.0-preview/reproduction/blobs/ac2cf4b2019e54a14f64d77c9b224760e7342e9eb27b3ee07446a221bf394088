module

public import dep.CoarseDeGiorgi.Statements.AlphaParam
public import dep.CoarseDeGiorgi.Statements.GammaLoc
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.ParamTheta
public import dep.CoarseDeGiorgi.Statements.RBoundaryParam
public import dep.CoarseDeGiorgi.Statements.RStarParam
public import dep.CoarseDeGiorgi.Statements.SigmaUpper

@[expose] public section

namespace CoarseDeGiorgi

/-- `γ₃ := max{ 1 + 1/p + ((1-t) + 1/r) r_∂^* + 2 γ₁ σ / θ , 2 (1-t) r^* / r }`
(`e.recurrence.exponent`): the power of `(ρ₂ - ρ₁)⁻¹` in the two-level recurrence (Proposition `p.two.level.recurrence`). -/
noncomputable def gammaRec (d : ℕ) (p q s t : ℝ) : ℝ :=
  max (1 + 1 / p + (alphaParam t + 1 / paramR q) * rBoundaryParam (d := d) q t +
      2 * gammaLoc p q t * sigmaUpper d p s / paramTheta d p q s t)
    (2 * alphaParam t * rStarParam (d := d) q t / paramR q)

end CoarseDeGiorgi
