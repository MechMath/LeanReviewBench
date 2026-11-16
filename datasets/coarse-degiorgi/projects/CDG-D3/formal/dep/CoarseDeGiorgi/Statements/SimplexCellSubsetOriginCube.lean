module

public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Sobolev.WeakDerivatives
public import dep.Homogenization.CoarseGraining.Definitions
public import dep.Homogenization.Geometry.TriadicCube
public import Mathlib.Data.EReal.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import dep.CoarseDeGiorgi.Statements.SimplexIndex
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.SimplexCell
public import dep.CoarseDeGiorgi.Moments.Cells

@[expose] public section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

theorem simplexCell_subset_originCube {d : ℕ} (k : ℕ) (η : SimplexIndex d k) :
    simplexCell k η ⊆ originCube 1 :=
  CoarseDeGiorgi.Moments.simplexCell_subset_originCube k η

end CoarseDeGiorgi
