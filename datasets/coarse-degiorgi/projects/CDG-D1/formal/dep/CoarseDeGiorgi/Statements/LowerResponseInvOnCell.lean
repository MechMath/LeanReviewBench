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
public import dep.CoarseDeGiorgi.Statements.SimplexIndex
public import dep.CoarseDeGiorgi.Statements.LowerResponseInv
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.SimplexCell
public import dep.CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import dep.CoarseDeGiorgi.Statements.SimplexCellNonempty
public import dep.CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def lowerResponseInvOnCell {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (η : SimplexIndex d k) : Mat d :=
  lowerResponseInv a (simplexCell k η)
    (simplexCell_isOpenBoundedConvexDomain k η)
    (simplexCell_nonempty k η)
    (weightedCoeffOn_simplexCell k a ha η)

end CoarseDeGiorgi
