module

public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Sobolev.WeakDerivatives
public import dep.Homogenization.CoarseGraining.Definitions
public import dep.Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import dep.CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import dep.CoarseDeGiorgi.Statements.MemH1a
public import dep.CoarseDeGiorgi.Statements.AlphaParam
public import dep.CoarseDeGiorgi.Statements.AuxCube
public import dep.CoarseDeGiorgi.Statements.FracNorm
public import dep.CoarseDeGiorgi.Statements.H1aWeightedNorm
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.SpatialMomentRange

public import dep.CoarseDeGiorgi.LowerFractional.CubeFinal

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- Proposition `p.lower.fractional`: for every triadic cube `Q = auxCube m z ⊆ □₀` (the cube `3^{-m} z + □_{1-m}`; the inclusion
forces `m ≥ 1`, i.e. the paper's `n = m - 1 ∈ ℕ₀`) the embedding
`H¹_a(Q) ⊂ W^{1-t,r}(Q)` is continuous. -/
theorem lower_fractional_embedding {d : ℕ} (hd : 3 ≤ d)
    (p q s t : ℝ) (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (hrange : spatialMomentRange a ha p q s t) (m : ℤ) (z : Fin d → ℤ)
    (hQ : auxCube m z ⊆ originCube 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ w : Vec d → ℝ, ∀ G : Vec d → Vec d,
        MemH1a a (auxCube m z) w G →
        fracNorm (auxCube m z) (alphaParam t) (paramR q) w ≤
          C * h1aWeightedNorm a (auxCube m z) w G
:=
  LowerFractional.lower_fractional_embedding_of_reconstruction LowerFractional.cube_reconstruction hd p q s t a ha hrange m z hQ

end CoarseDeGiorgi
