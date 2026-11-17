module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
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
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Geometry.ConvexDomain
public import dep.Homogenization.Geometry.CubeMeasure
public import dep.Homogenization.Geometry.Domain
public import dep.Homogenization.Geometry.TriadicCube
public import dep.Homogenization.Multiscale.CubeAverage
public import dep.Homogenization.Multiscale.NormalizedNorms
public import dep.Homogenization.Sobolev.H1.BasicLemmas
public import dep.Homogenization.Sobolev.H1.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.W1p.BasicLemmas
public import dep.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import dep.Homogenization.Sobolev.W1p.Definitions
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace Homogenization

namespace H1Function

instance {d : ℕ} {U : Set (Vec d)} : Zero (H1Function U) where
  zero :=
    { toFun := 0
      grad := 0
      memL2 := sorry
      gradMemL2 := sorry
      hasWeakGradient := sorry }

instance {d : ℕ} {U : Set (Vec d)} : SMul ℝ (H1Function U) where
  smul c u :=
    { toFun := fun x => c * u x
      grad := fun x => c • u.grad x
      memL2 := u.memL2.const_mul c
      gradMemL2 := sorry
      hasWeakGradient := sorry
      }

instance {d : ℕ} {U : Set (Vec d)} : Neg (H1Function U) where
  neg u := (-1 : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : Add (H1Function U) where
  add u v :=
    { toFun := fun x => u x + v x
      grad := fun x => u.grad x + v.grad x
      memL2 := u.memL2.add v.memL2
      gradMemL2 := sorry
      hasWeakGradient := sorry
      }

instance {d : ℕ} {U : Set (Vec d)} : Sub (H1Function U) where
  sub u v := u + (-v)

instance {d : ℕ} {U : Set (Vec d)} : SMul ℕ (H1Function U) where
  smul n u := (n : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : SMul ℤ (H1Function U) where
  smul n u := (n : ℝ) • u

theorem toFunGrad_injective {d : ℕ} {U : Set (Vec d)} :
    Function.Injective (fun u : H1Function U => (u.toFun, u.grad)) := sorry

instance {d : ℕ} {U : Set (Vec d)} : AddCommGroup (H1Function U) :=
  Function.Injective.addCommGroup
    (fun u : H1Function U => (u.toFun, u.grad))
    toFunGrad_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => sorry)
    (fun _ _ => sorry)
    (fun u n => sorry)
    (fun u n => sorry)

noncomputable def toFunGradAddMonoidHom {d : ℕ} {U : Set (Vec d)} :
    H1Function U →+ ((Vec d → ℝ) × (Vec d → Vec d)) where
  toFun := fun u => (u.toFun, u.grad)
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance {d : ℕ} {U : Set (Vec d)} : Module ℝ (H1Function U) :=
  Function.Injective.module ℝ
    toFunGradAddMonoidHom
    (toFunGrad_injective (d := d) (U := U))
    (fun _ _ => rfl)

end H1Function

end Homogenization
