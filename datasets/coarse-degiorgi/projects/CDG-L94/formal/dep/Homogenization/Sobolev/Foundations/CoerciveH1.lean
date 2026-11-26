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
public import dep.Homogenization.Sobolev.H1.Algebra.H10Function
public import dep.Homogenization.Sobolev.H1.Algebra.H1Function
public import dep.Homogenization.Sobolev.H1.BasicLemmas
public import dep.Homogenization.Sobolev.H1.Definitions
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.W1p.BasicLemmas
public import dep.Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import dep.Homogenization.Sobolev.W1p.Definitions
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

namespace Homogenization

/-- Mean-zero `H¹(U)` functions, represented by a chosen `H¹` witness together
with the zero-average condition. -/
structure H1MeanZeroFunction {d : ℕ} (U : Set (Vec d)) where
  toH1Function : H1Function U
  meanZero : MeanZeroOn U toH1Function.toFun

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

instance : Coe (H1MeanZeroFunction U) (H1Function U) where
  coe u := u.toH1Function

instance : CoeFun (H1MeanZeroFunction U) (fun _ => Vec d → ℝ) where
  coe u := u.toH1Function

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

instance : Zero (H1MeanZeroFunction U) where
  zero :=
    { toH1Function := 0
      meanZero := sorry }

instance : Add (H1MeanZeroFunction U) where
  add u v :=
    { toH1Function := u.toH1Function + v.toH1Function
      meanZero := sorry }

instance : SMul ℝ (H1MeanZeroFunction U) where
  smul c u :=
    { toH1Function := c • u.toH1Function
      meanZero := sorry }

instance : Neg (H1MeanZeroFunction U) where
  neg u := (-1 : ℝ) • u

instance : Sub (H1MeanZeroFunction U) where
  sub u v := u + (-v)

instance : SMul ℕ (H1MeanZeroFunction U) where
  smul n u := (n : ℝ) • u

instance : SMul ℤ (H1MeanZeroFunction U) where
  smul n u := (n : ℝ) • u

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem toH1Function_injective :
    Function.Injective (fun u : H1MeanZeroFunction U => (u : H1Function U)) := sorry

instance : AddCommGroup (H1MeanZeroFunction U) :=
  Function.Injective.addCommGroup
    (fun u : H1MeanZeroFunction U => (u : H1Function U))
    toH1Function_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => rfl)
    (fun _ _ => rfl)
    (fun u n => sorry)
    (fun u n => sorry)

noncomputable def toH1FunctionAddMonoidHom :
    H1MeanZeroFunction U →+ H1Function U where
  toFun := fun u => u.toH1Function
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℝ (H1MeanZeroFunction U) :=
  Function.Injective.module ℝ
    toH1FunctionAddMonoidHom
    toH1Function_injective
    (fun _ _ => rfl)

end H1MeanZeroFunction

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²(U)` realization of an `H¹` function. -/
noncomputable def toScalarL2 (u : H1Function U) : ScalarL2 U :=
  Homogenization.toScalarL2 u.memL2

/-- The vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToVectorL2 (u : H1Function U) : VectorL2 U :=
  Homogenization.toVectorL2 u.grad_memVectorL2

/-- The Hilbert-vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToHilbertVectorL2 (u : H1Function U) : HilbertVectorL2 U :=
  Homogenization.toHilbertVectorL2OfVecField u.grad_memVectorL2

end H1Function

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²(U)` realization of a mean-zero `H¹` function. -/
noncomputable def toScalarL2 (u : H1MeanZeroFunction U) : ScalarL2 U :=
  u.toH1Function.toScalarL2

/-- The vector `L²(U; ℝ^d)` realization of the weak gradient. -/
noncomputable def gradToVectorL2 (u : H1MeanZeroFunction U) : VectorL2 U :=
  u.toH1Function.gradToVectorL2

/-- The Hilbert-vector `L²(U; ℝ^d)` realization of a mean-zero `H¹`
function's weak gradient. -/
noncomputable def gradToHilbertVectorL2 (u : H1MeanZeroFunction U) : HilbertVectorL2 U :=
  u.toH1Function.gradToHilbertVectorL2

end H1MeanZeroFunction

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²` norm of a mean-zero `H¹` function. -/
noncomputable def valueL2Norm (u : H1MeanZeroFunction U) : ℝ :=
  ‖u.toScalarL2‖

/-- The gradient-only `L²` norm which is the future coercive norm on the
mean-zero layer. -/
noncomputable def gradientL2Norm (u : H1MeanZeroFunction U) : ℝ :=
  ‖u.gradToVectorL2‖

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    Norm (H1MeanZeroFunction U) where
  norm u := u.gradientL2Norm

theorem seminormedSpaceCore [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    SeminormedSpace.Core ℝ (H1MeanZeroFunction U) := sorry

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    SeminormedAddCommGroup (H1MeanZeroFunction U) :=
  SeminormedAddCommGroup.ofCore (𝕜 := ℝ) seminormedSpaceCore

noncomputable instance [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    NormedSpace ℝ (H1MeanZeroFunction U) where
  norm_smul_le c u := sorry

end H1MeanZeroFunction

/-- Bundled coercive estimate on the mean-zero `H¹` layer. -/
structure H1CoerciveEstimate {d : ℕ} (U : Set (Vec d)) where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  bound :
    ∀ u : H1MeanZeroFunction U,
      u.valueL2Norm ≤ constant * u.gradientL2Norm

namespace H1CoerciveEstimate

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

end H1CoerciveEstimate

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

end H1MeanZeroFunction

end Homogenization
