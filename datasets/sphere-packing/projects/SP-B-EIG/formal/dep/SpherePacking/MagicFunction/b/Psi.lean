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

open UpperHalfPlane hiding I

open Complex Real Matrix ModularGroup ModularForm SlashAction MatrixGroups

noncomputable section defs

/-- The auxiliary function `h = 128 (H₃ + H₄) / H₂ ^ 2`, from which the `ψ` functions are obtained
via slash actions. -/
def h : ℍ → ℂ := 128 • (H₃ + H₄) / (H₂ ^ 2)

/-- `ψI = h - h ∣[-2] (S * T)`. -/
def ψI : ℍ → ℂ := h - h ∣[-2] (S * T)

/-- `ψT = ψI ∣[-2] T`. -/
def ψT : ℍ → ℂ := ψI ∣[-2] T

/-- `ψS = ψI ∣[-2] S`. -/
def ψS : ℍ → ℂ := ψI ∣[-2] S

/-- `ψI`, extended by zero to a function on `ℂ`. -/
def ψI' (z : ℂ) : ℂ := if hz : 0 < z.im then ψI ⟨z, hz⟩ else 0

/-- `ψS`, extended by zero to a function on `ℂ`. -/
def ψS' (z : ℂ) : ℂ := if hz : 0 < z.im then ψS ⟨z, hz⟩ else 0

/-- `ψT`, extended by zero to a function on `ℂ`. -/
def ψT' (z : ℂ) : ℂ := if hz : 0 < z.im then ψT ⟨z, hz⟩ else 0

end defs

section eq

end eq

section rels

end rels

open MagicFunction.Parametrisations Set

section eq_of_mem

end eq_of_mem

section slash_explicit

end slash_explicit

section rels_explicit

end rels_explicit
