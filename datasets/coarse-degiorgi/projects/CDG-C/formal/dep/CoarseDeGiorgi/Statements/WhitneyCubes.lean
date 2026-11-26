module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import dep.CoarseDeGiorgi.Statements.ClosedReferenceCube
public import dep.CoarseDeGiorgi.Statements.ClosedTriadicCube
public import dep.CoarseDeGiorgi.Statements.FivefoldClosedTriadicCube
public import dep.CoarseDeGiorgi.Statements.TriadicCenter
public import dep.CoarseDeGiorgi.Statements.WhitneyAdmissible
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

open Homogenization MeasureTheory

open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

noncomputable section

def whitneyCubes {d : ℕ} (τ : ℝ) : Set (TriadicCube d) :=
  {D | whitneyAdmissible τ D ∧
    ∀ E, whitneyAdmissible τ E → closedTriadicCube D ⊆ closedTriadicCube E → E = D}

end

end CoarseDeGiorgi
