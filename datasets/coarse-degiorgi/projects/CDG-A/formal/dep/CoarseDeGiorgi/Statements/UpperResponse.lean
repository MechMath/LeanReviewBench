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
public import dep.CoarseDeGiorgi.Statements.UpperResponseExistsUnique

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

noncomputable def upperResponse {d : ℕ} (a : CoeffField d) (V : Set (Vec d))
    (hV : IsOpenBoundedConvexDomain V) (hV₀ : V.Nonempty)
    (ha : IsWeightedCoeffOn V a) : Mat d :=
  Classical.choose (upperResponse_existsUnique hV hV₀ ha).exists

end CoarseDeGiorgi
