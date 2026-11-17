module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.CoarseDeGiorgi.Statements.CubeFaceMeasure
public import dep.CoarseDeGiorgi.Statements.FaceCoordinateMeasures
public import dep.CoarseDeGiorgi.Statements.SurfaceMeasure
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.Fractional.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace CoarseDeGiorgi.Foundations.FracGeometry

open Homogenization MeasureTheory

open scoped BigOperators ENNReal

noncomputable section

/-- Compatibility name for the surface measure, the sum of the face measures. -/
abbrev surfaceMeasure {d : ℕ} (τ : ℝ) : Measure (Vec d) :=
  CoarseDeGiorgi.surfaceMeasure τ

variable {d : ℕ}

/-- Compatibility access to the coordinate-face measure for Fubini arguments. -/
abbrev faceMeasure (τ : ℝ) (i : Fin d) (positive : Bool) : Measure (Vec d) :=
  CoarseDeGiorgi.cubeFaceMeasure τ i positive

private instance faceCoordinateMeasures_finite (τ : ℝ) (i : Fin d) (positive : Bool)
    (j : Fin d) : IsFiniteMeasure (CoarseDeGiorgi.faceCoordinateMeasures τ i positive j) := sorry

private instance cubeFaceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (CoarseDeGiorgi.cubeFaceMeasure τ i positive) := sorry

instance faceMeasure_finite (τ : ℝ) (i : Fin d) (positive : Bool) :
    IsFiniteMeasure (faceMeasure τ i positive) := sorry

/-- The surface measure (sum of face measures) is finite, even at an inadmissible radius. -/
instance surfaceMeasure_finite (τ : ℝ) : IsFiniteMeasure (surfaceMeasure (d := d) τ) := sorry

end

end CoarseDeGiorgi.Foundations.FracGeometry
