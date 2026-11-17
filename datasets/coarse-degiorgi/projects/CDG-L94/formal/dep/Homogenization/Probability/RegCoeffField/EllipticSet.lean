module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Instances.Matrix
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.BlockMatrix
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Probability.RegCoeffField
public import dep.Homogenization.Probability.RegCoeffField.Sigma
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

namespace Homogenization

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The matrix-entry space `Mat d = Fin d → Fin d → ℝ` carries the product Borel
structure: its carrier σ-algebra `instMatMeasurableSpace` agrees with the Borel
σ-algebra of the product topology.  Transferred from the genuine pi type.

Named distinctly from the raw-`CoeffField` layer's `instBorelSpaceMat`
(`Ch04.Internal.CoarseObservableMeasurability.Basic`) so that the carrier and raw
layers coexist in a single import closure; both witness the same (defeq) product
Borel structure and are found by instance resolution, never by name. -/
instance instBorelSpaceMatEntry : BorelSpace (Mat d) := sorry

end

end Homogenization
