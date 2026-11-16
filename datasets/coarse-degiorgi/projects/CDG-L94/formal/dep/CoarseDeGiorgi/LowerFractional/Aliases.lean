module

public import dep.CoarseDeGiorgi.Statements.LowerResponseExistsUnique
public import dep.CoarseDeGiorgi.Statements.UpperResponseExistsUnique
public import dep.CoarseDeGiorgi.Statements.SimplexIndex
public import dep.CoarseDeGiorgi.Statements.AlphaParam
public import dep.CoarseDeGiorgi.Statements.AuxCube
public import dep.CoarseDeGiorgi.Statements.AuxAverage
public import dep.CoarseDeGiorgi.Assembly.ParameterDefs
public import dep.CoarseDeGiorgi.Statements.Contrast
public import dep.CoarseDeGiorgi.Statements.FracNorm
public import dep.CoarseDeGiorgi.Statements.GridOffset
public import dep.CoarseDeGiorgi.Statements.H1aWeightedNorm
public import dep.CoarseDeGiorgi.Statements.LowerCellAverage
public import dep.CoarseDeGiorgi.Statements.LowerMoment
public import dep.CoarseDeGiorgi.Statements.LowerResponseInv
public import dep.CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.ParamTheta
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
public import dep.CoarseDeGiorgi.Statements.UpperCellAverage
public import dep.CoarseDeGiorgi.Statements.UpperMoment
public import dep.CoarseDeGiorgi.Statements.UpperResponse
public import dep.CoarseDeGiorgi.Statements.UpperResponseOnCell
public import dep.CoarseDeGiorgi.Statements.WeightedCoeffOnSimplexCell
public import dep.CoarseDeGiorgi.Moments.Cells
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi.LowerFractional.Aliases

/-! Compatibility aliases for the `Statements/` definitions. The response
uniqueness and geometric facts below are direct exports of the stated theorems. -/




noncomputable abbrev lowerResponseInv {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d := CoarseDeGiorgi.lowerResponseInv a V hV hV₀ ha

abbrev simplex {d : ℕ} (n : ℤ) (π : Equiv.Perm (Fin d)) (z : Vec d) : Set (Vec d) :=
  CoarseDeGiorgi.simplex n π z



abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

abbrev SimplexIndex (d k : ℕ) := CoarseDeGiorgi.SimplexIndex d k

abbrev simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  CoarseDeGiorgi.simplexCell k η


theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) :=
  CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain k η

theorem simplexCell_nonempty {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (simplexCell k η).Nonempty := CoarseDeGiorgi.simplexCell_nonempty k η














end CoarseDeGiorgi.LowerFractional.Aliases
