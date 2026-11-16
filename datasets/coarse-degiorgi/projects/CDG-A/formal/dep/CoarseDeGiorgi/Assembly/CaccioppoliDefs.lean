module

public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Sobolev.WeakDerivatives
public import dep.Homogenization.CoarseGraining.Definitions
public import dep.Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import dep.CoarseDeGiorgi.Statements.IsWeightedCoeffOn
public import dep.CoarseDeGiorgi.Statements.IsWeightedSubsolution
public import dep.CoarseDeGiorgi.Statements.MemH1a
public import dep.CoarseDeGiorgi.Statements.MemH1a0
public import dep.CoarseDeGiorgi.Statements.SimplexIndex
public import dep.CoarseDeGiorgi.Statements.AlphaParam
public import dep.CoarseDeGiorgi.Statements.AuxAverage
public import dep.CoarseDeGiorgi.Statements.AuxCube
public import dep.CoarseDeGiorgi.Assembly.ParameterDefs
public import dep.CoarseDeGiorgi.Statements.Contrast
public import dep.CoarseDeGiorgi.Statements.FracNorm
public import dep.CoarseDeGiorgi.Statements.GridOffset
public import dep.CoarseDeGiorgi.Statements.H1aWeightedNorm
public import dep.CoarseDeGiorgi.Statements.LowerCellAverage
public import dep.CoarseDeGiorgi.Statements.LowerMoment
public import dep.CoarseDeGiorgi.Statements.LowerResponseInv
public import dep.CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import dep.CoarseDeGiorgi.Statements.LocallyBoundedAbove
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.ParamTheta
public import dep.CoarseDeGiorgi.Statements.PositivePart
public import dep.CoarseDeGiorgi.Statements.PositiveTruncationGradient
public import dep.CoarseDeGiorgi.Statements.RBoundaryParam
public import dep.CoarseDeGiorgi.Statements.RStarParam
public import dep.CoarseDeGiorgi.Statements.Simplex
public import dep.CoarseDeGiorgi.Statements.SimplexCell
public import dep.CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import dep.CoarseDeGiorgi.Statements.SimplexCellNonempty
public import dep.CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import dep.CoarseDeGiorgi.Statements.SpatialMomentRange
public import dep.CoarseDeGiorgi.Statements.Triangulation
public import dep.CoarseDeGiorgi.Statements.TriangulationCard
public import dep.CoarseDeGiorgi.Statements.TwoLevelQuantity
public import dep.CoarseDeGiorgi.Statements.UpperCellAverage
public import dep.CoarseDeGiorgi.Statements.UpperMoment
public import dep.CoarseDeGiorgi.Statements.UpperResponse
public import dep.CoarseDeGiorgi.Statements.UpperResponseOnCell
public import dep.CoarseDeGiorgi.Statements.UpperResponseExistsUnique
public import dep.CoarseDeGiorgi.Statements.LowerResponseExistsUnique
public import dep.CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.Assembly.Aliases

/-! Compatibility aliases for `Statements/` definitions. -/

abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

end CoarseDeGiorgi.Assembly.Aliases
