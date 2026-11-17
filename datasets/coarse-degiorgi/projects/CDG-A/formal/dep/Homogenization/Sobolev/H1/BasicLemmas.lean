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
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
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
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.H1.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace Homogenization

open scoped ENNReal

theorem memL2On_mono {d : ℕ} {U V : Set (Vec d)} {u : Vec d → ℝ}
    (hVU : V ⊆ U) (hu : MemL2On U u) : MemL2On V u := sorry

theorem gradMemL2On_mono {d : ℕ} {U V : Set (Vec d)} {Du : Vec d → Vec d}
    (hVU : V ⊆ U) (hDu : GradMemL2On U Du) : GradMemL2On V Du := sorry

theorem HasWeakPartialDerivOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi := sorry

theorem HasWeakGradientOn.restrict {d : ℕ} {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du := sorry

namespace H1Function

theorem grad_memVectorL2 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemVectorL2 U u.grad := sorry

def restrict {d : ℕ} {U V : Set (Vec d)} (u : H1Function U)
    (hVopen : IsOpen V) (hVU : V ⊆ U) : H1Function V :=
  { toFun := u.toFun
    grad := u.grad
    memL2 := memL2On_mono hVU u.memL2
    gradMemL2 := gradMemL2On_mono hVU u.gradMemL2
    hasWeakGradient := u.hasWeakGradient.restrict hVopen hVU }

end H1Function

namespace H10Function

end H10Function

end Homogenization
