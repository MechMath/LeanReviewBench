module

public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Sobolev.WeakDerivatives
public import dep.Homogenization.CoarseGraining.Definitions
public import dep.Homogenization.Geometry.TriadicCube
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import dep.CoarseDeGiorgi.Statements.SimplexIndex
public import dep.CoarseDeGiorgi.Statements.Contrast
public import dep.CoarseDeGiorgi.Statements.GridOffset
public import dep.CoarseDeGiorgi.Statements.LowerCellAverage
public import dep.CoarseDeGiorgi.Statements.LowerMoment
public import dep.CoarseDeGiorgi.Statements.LowerResponseInv
public import dep.CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.ParamR
public import dep.CoarseDeGiorgi.Statements.ParamTheta
public import dep.CoarseDeGiorgi.Statements.PositivePart
public import dep.CoarseDeGiorgi.Statements.Simplex
public import dep.CoarseDeGiorgi.Statements.SimplexCell
public import dep.CoarseDeGiorgi.Statements.SimplexCellIsOpenBoundedConvexDomain
public import dep.CoarseDeGiorgi.Statements.SimplexCellNonempty
public import dep.CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import dep.CoarseDeGiorgi.Statements.Triangulation
public import dep.CoarseDeGiorgi.Statements.TriangulationCard
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

namespace CoarseDeGiorgi.Assembly.ClassicalMomentsImpl

/-! Compatibility aliases for `Statements/` definitions. -/

noncomputable abbrev lowerResponseInv {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d := CoarseDeGiorgi.lowerResponseInv a V hV hV₀ ha

noncomputable abbrev triangulation {d : ℕ} (k : ℕ) :
    Finset ((Fin d → ℤ) × Equiv.Perm (Fin d)) := CoarseDeGiorgi.triangulation k

abbrev originCube {d : ℕ} (ρ : ℝ) : Set (Vec d) := CoarseDeGiorgi.originCube ρ

abbrev SimplexIndex (d k : ℕ) := CoarseDeGiorgi.SimplexIndex d k

abbrev simplexCell {d : ℕ} (k : ℕ) (η : SimplexIndex d k) : Set (Vec d) :=
  CoarseDeGiorgi.simplexCell k η

theorem triangulation_card {d : ℕ} (k : ℕ) :
    (triangulation (d := d) k).card = Nat.factorial d * 3 ^ (k * d) :=
  CoarseDeGiorgi.triangulation_card k

theorem simplexCell_isOpenBoundedConvexDomain {d : ℕ} (k : ℕ)
    (η : SimplexIndex d k) : IsOpenBoundedConvexDomain (simplexCell k η) :=
  CoarseDeGiorgi.simplexCell_isOpenBoundedConvexDomain k η

theorem simplexCell_nonempty {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    (simplexCell k η).Nonempty := CoarseDeGiorgi.simplexCell_nonempty k η

theorem weightedCoeffOn_simplexCell {d : ℕ} (k : ℕ)
    (a : CoeffField d) (ha : IsWeightedCoeffOn (originCube 1) a)
    (η : SimplexIndex d k) : IsWeightedCoeffOn (simplexCell k η) a :=
  CoarseDeGiorgi.weightedCoeffOn_simplexCell k a ha η

noncomputable abbrev upperResponseOnCell {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (η : SimplexIndex d k) : Mat d :=
  CoarseDeGiorgi.upperResponseOnCell k a ha η

noncomputable abbrev lowerResponseInvOnCell {d : ℕ} (k : ℕ) (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (η : SimplexIndex d k) : Mat d :=
  CoarseDeGiorgi.lowerResponseInvOnCell k a ha η

noncomputable abbrev upperCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (p : ℝ) : ℝ :=
  CoarseDeGiorgi.upperCellAverage a ha k p

noncomputable abbrev lowerCellAverage {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (k : ℕ) (q : ℝ) : ℝ :=
  CoarseDeGiorgi.lowerCellAverage a ha k q

noncomputable abbrev upperMoment {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s p : ℝ) (_hs : 0 < s) (_hp : 1 ≤ p) : ℝ≥0∞ :=
  CoarseDeGiorgi.upperMoment a ha s p _hs _hp

noncomputable abbrev lowerMoment {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (t q : ℝ) (_ht : 0 < t) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  CoarseDeGiorgi.lowerMoment a ha t q _ht _hq

noncomputable abbrev contrast {d : ℕ} (a : CoeffField d)
    (ha : IsWeightedCoeffOn (originCube 1) a) (s t p q : ℝ)
    (_hs : 0 < s) (_ht : 0 < t) (_hp : 1 ≤ p) (_hq : 1 ≤ q) : ℝ≥0∞ :=
  CoarseDeGiorgi.contrast a ha s t p q _hs _ht _hp _hq

end CoarseDeGiorgi.Assembly.ClassicalMomentsImpl
