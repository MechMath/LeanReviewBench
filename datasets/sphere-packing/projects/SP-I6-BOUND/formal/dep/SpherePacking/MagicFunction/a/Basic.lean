module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
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
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import dep.SpherePacking.MagicFunction.IntegralParametrisations
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

local notation "V" => EuclideanSpace ℝ (Fin 8)

open Set Complex Real MagicFunction.Parametrisations

open scoped UpperHalfPlane

noncomputable section Integrands

variable (r : ℝ)

namespace MagicFunction.a.ComplexIntegrands

def Φ₁' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₂' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z + 1)) * (z + 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₃' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₄' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / (z - 1)) * (z - 1) ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₅' : ℂ → ℂ := fun z ↦ φ₀'' (-1 / z) * z ^ 2 * cexp (π * I * r * (z : ℂ))

def Φ₆' : ℂ → ℂ := fun z ↦ φ₀'' (z) * cexp (π * I * r * (z : ℂ))

section Def

end Def

end MagicFunction.a.ComplexIntegrands

namespace MagicFunction.a.RealIntegrands

open MagicFunction.a.ComplexIntegrands

def Φ₁ : ℝ → ℂ := fun t ↦ I * Φ₁' r (z₁' t)

def Φ₂ : ℝ → ℂ := fun t ↦ Φ₂' r (z₂' t)

def Φ₃ : ℝ → ℂ := fun t ↦ I * Φ₃' r (z₃' t)

def Φ₄ : ℝ → ℂ := fun t ↦ -1 * Φ₄' r (z₄' t)

def Φ₅ : ℝ → ℂ := fun t ↦ I * Φ₅' r (z₅' t)

def Φ₆ : ℝ → ℂ := fun t ↦ I * Φ₆' r (z₆' t)

section Def

end Def

end MagicFunction.a.RealIntegrands

end Integrands

namespace MagicFunction.a.RealIntegrals

noncomputable section Real_Input

open MagicFunction.a.RealIntegrands

def I₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₁ x t

def I₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₂ x t

def I₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₃ x t

def I₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Φ₄ x t

def I₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Φ₅ x t

def I₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Φ₆ x t

def a' : ℝ → ℂ := fun x ↦ I₁' x + I₂' x + I₃' x + I₄' x + I₅' x + I₆' x

end Real_Input

end MagicFunction.a.RealIntegrals

open MagicFunction.a.RealIntegrals

namespace MagicFunction.a.RadialFunctions

noncomputable section Vector_Input

def I₆ : V → ℂ := fun x ↦ I₆' (‖x‖ ^ 2)

def a : V → ℂ := fun x ↦ a' (‖x‖ ^ 2)

end Vector_Input

open intervalIntegral

section Eq

open MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

end Eq

end MagicFunction.a.RadialFunctions
