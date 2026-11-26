module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Parity
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Derivative
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.RamanujanFormula
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.RingTheory.Binomial
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Field
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import dep.SpherePacking.MagicFunction.IntegralParametrisations
public import dep.SpherePacking.MagicFunction.a.Basic
public import dep.SpherePacking.MagicFunction.a.Phi
public import dep.SpherePacking.ModularForms.Delta
public import dep.SpherePacking.ModularForms.E2
public import dep.SpherePacking.ModularForms.Eisenstein
public import dep.SpherePacking.ModularForms.FG
public import dep.SpherePacking.ModularForms.IsCuspForm
public import dep.SpherePacking.ModularForms.JacobiTheta.Basic
public import dep.SpherePacking.ModularForms.JacobiTheta.Defs
public import dep.SpherePacking.ModularForms.JacobiTheta.Derivative
public import dep.SpherePacking.ModularForms.JacobiTheta.JacobiIdentity
public import dep.SpherePacking.ModularForms.JacobiTheta.MDifferentiable
public import dep.SpherePacking.ModularForms.ResToImagAxis
public import dep.SpherePacking.ModularForms.SlashActionAuxil

@[expose] public section

open MagicFunction.Parametrisations MagicFunction.a.RealIntegrals MagicFunction.a.RadialFunctions

open Complex Real Set MeasureTheory MeasureTheory.Measure Filter intervalIntegral

open scoped Function UpperHalfPlane

namespace MagicFunction.a.IntegralEstimates.I₆

variable (r : ℝ)

section Setup

noncomputable def g : ℝ → ℝ → ℂ := fun r t ↦ I
  * φ₀'' (I * t)
  * cexp (-π * r * t)

end Setup

section Bounding

section Bounding_Integrand

end Bounding_Integrand

section Integrability

end Integrability

section Bounding_Integral

theorem I₆'_bounding (r : ℝ) (hr : 0 ≤ r) : ∃ C₁ > 0,
    ‖I₆' r‖ ≤ ∫ t in Ici (1 : ℝ), C₁ * rexp (-2 * π * t) * rexp (-π * r * t) := sorry

end Bounding_Integral

end Bounding

section Higher_iteratedFDerivs

end Higher_iteratedFDerivs

noncomputable section Schwartz_Decay

open SchwartzMap

section Zeroth_Derivative

end Zeroth_Derivative

section Higher_iteratedFDerivs

end Higher_iteratedFDerivs

end Schwartz_Decay

end I₆

end IntegralEstimates

end a

end MagicFunction
