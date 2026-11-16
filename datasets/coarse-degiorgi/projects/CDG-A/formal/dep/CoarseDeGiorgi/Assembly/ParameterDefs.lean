module

public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Sobolev.WeakDerivatives
public import dep.Homogenization.CoarseGraining.Definitions
public import dep.Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import dep.CoarseDeGiorgi.Statements.AlphaParam
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.ParamTheta
public import dep.CoarseDeGiorgi.Statements.RBoundaryParam
public import dep.CoarseDeGiorgi.Statements.RStarParam

/-!
Auxiliary exponents used by implementation lemmas; they are not named in the paper.
`sigmaParam` is `σ + σ_* - t` in the notation of `e.intro.parameters`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def betaParam {d : ℕ} (q : ℝ) : ℝ := ((d : ℝ) - 1) / (2 * q)

noncomputable def sigmaParam {d : ℕ} (p q s : ℝ) : ℝ :=
  s + (((d : ℝ) - 1) / 2) * (1 / p + 1 / q)

noncomputable def gammaOneParam {d : ℕ} (q t : ℝ) : ℝ :=
  max (alphaParam t) ((d : ℝ) / (2 * q))

noncomputable def gammaTwoParam {d : ℕ} (p q t : ℝ) : ℝ :=
  gammaOneParam (d := d) q t + 1 + 1 / (2 * p) + 1 / (2 * q)

noncomputable def kappaParam {d : ℕ} (p q s t : ℝ) : ℝ :=
  2 * gammaTwoParam (d := d) p q t *
    (alphaParam t - betaParam (d := d) q) / paramTheta d p q s t

end CoarseDeGiorgi
