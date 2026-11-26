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
public import dep.Homogenization.Sobolev.Fractional.UnitCubeEuclideanL2

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

structure FiniteLpExponent where
  exponent : ℝ≥0∞
  one_lt : 1 < exponent
  lt_top : exponent < ∞

namespace FiniteLpExponent

end FiniteLpExponent

structure CubeEuclideanLpField {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) where
  toField : Vec d → Vec d
  euclideanMemLp :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) p.exponent
      (normalizedCubeMeasure Q)

namespace CubeEuclideanLpField

instance {d : ℕ} {Q : TriadicCube d} {p : FiniteLpExponent} :
    CoeFun (CubeEuclideanLpField Q p) (fun _ => Vec d → Vec d) where
  coe F := F.toField

end CubeEuclideanLpField

end

end Homogenization
