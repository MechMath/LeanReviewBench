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
public import dep.SpherePacking.MagicFunction.b.Psi
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

namespace MagicFunction.b.ComplexIntegrands

def Ψ₁' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₂' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₃' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₄' : ℂ → ℂ := fun z ↦ (ψT' z) * cexp (π * I * r * z)

def Ψ₅' : ℂ → ℂ := fun z ↦ (ψI' z) * cexp (π * I * r * z)

def Ψ₆' : ℂ → ℂ := fun z ↦ (ψS' z) * cexp (π * I * r * z)

section Def

end Def

end MagicFunction.b.ComplexIntegrands

namespace MagicFunction.b.RealIntegrands

open MagicFunction.b.ComplexIntegrands

def Ψ₁ : ℝ → ℂ := fun t ↦ I * Ψ₁' r (z₁' t)

def Ψ₂ : ℝ → ℂ := fun t ↦ Ψ₂' r (z₂' t)

def Ψ₃ : ℝ → ℂ := fun t ↦ I * Ψ₃' r (z₃' t)

def Ψ₄ : ℝ → ℂ := fun t ↦ -1 * Ψ₄' r (z₄' t)

def Ψ₅ : ℝ → ℂ := fun t ↦ I * Ψ₅' r (z₅' t)

def Ψ₆ : ℝ → ℂ := fun t ↦ I * Ψ₆' r (z₆' t)

section Def

end Def

end MagicFunction.b.RealIntegrands

end Integrands

namespace MagicFunction.b.RealIntegrals

noncomputable section Real_Input

open MagicFunction.b.RealIntegrands

def J₁' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₁ x t

def J₂' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₂ x t

def J₃' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₃ x t

def J₄' : ℝ → ℂ := fun x ↦ ∫ t in (0 : ℝ)..1, Ψ₄ x t

def J₅' : ℝ → ℂ := fun x ↦ -2 * ∫ t in (0 : ℝ)..1, Ψ₅ x t

def J₆' : ℝ → ℂ := fun x ↦ 2 * ∫ t in Ici (1 : ℝ), Ψ₆ x t

def b' : ℝ → ℂ := fun x ↦ J₁' x + J₂' x + J₃' x + J₄' x + J₅' x + J₆' x

end Real_Input

end MagicFunction.b.RealIntegrals

open MagicFunction.b.RealIntegrals

namespace MagicFunction.b.RadialFunctions

noncomputable section Vector_Input

def b : V → ℂ := fun x ↦ b' (‖x‖ ^ 2)

end Vector_Input

open intervalIntegral MagicFunction.b.ComplexIntegrands MagicFunction.b.RealIntegrands
  MagicFunction.b.RealIntegrals

section Eq₀

end Eq₀

end MagicFunction.b.RadialFunctions
