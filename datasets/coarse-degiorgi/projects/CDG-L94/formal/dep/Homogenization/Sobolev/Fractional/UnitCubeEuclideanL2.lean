module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.Euclidean
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.BoundedMeasurableDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.CubeMetric
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedDomainCube
public import dep.Homogenization.Multiscale.NormalizedNorms

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-- The bounded measurable realization of the unit centered cube. -/
noncomputable def unitCenteredCubeDomain (d : ℕ) : BoundedMeasurableDomain d :=
  cubeBoundedMeasurableDomain (originCube d 0)

/-- A Euclidean `L²` vector field on the unit centered cube.  The witness uses
the Euclidean Hilbert realization, so it supplies the explicit `euclideanNorm`
`L²` fact without a finite-real fallback. -/
structure UnitCubeEuclideanL2Field (d : ℕ) where
  /-- The represented vector field. -/
  toField : Vec d → Vec d
  euclideanMemL2 :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) (2 : ℝ≥0∞)
      (unitCenteredCubeDomain d).normalizedVolume

namespace UnitCubeEuclideanL2Field

instance {d : ℕ} : CoeFun (UnitCubeEuclideanL2Field d) (fun _ => Vec d → Vec d) where
  coe F := F.toField

end UnitCubeEuclideanL2Field

end

end Homogenization
