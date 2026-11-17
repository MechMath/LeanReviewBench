module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import dep.SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import dep.SpherePacking.MagicFunction.IntegralParametrisations
public import dep.SpherePacking.MagicFunction.b.Basic
public import dep.SpherePacking.MagicFunction.b.Psi
public import dep.SpherePacking.ModularForms.Derivative
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

open MagicFunction MagicFunction.b MagicFunction.b.RadialFunctions MagicFunction.b.RealIntegrals
  MagicFunction.Parametrisations

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.b.SchwartzProperties

section Smooth

theorem J₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₁' := sorry

theorem J₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₂' := sorry

theorem J₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₃' := sorry

theorem J₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₄' := sorry

theorem J₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₅' := sorry

theorem J₆'_smooth' : ContDiff ℝ ∞ RealIntegrals.J₆' := sorry

end Smooth

section Decay

theorem J₁'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₁' x‖ ≤ C := sorry

theorem J₂'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₂' x‖ ≤ C := sorry

theorem J₃'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n RealIntegrals.J₃' x‖ ≤ C := sorry

theorem J₄'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₄' x‖ ≤ C := sorry

theorem J₅'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₅' x‖ ≤ C := sorry

theorem J₆'_decay' : ∀ (k n : ℕ), ∃ C, ∀ (x : ℝ),
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n J₆' x‖ ≤ C := sorry

end Decay

end MagicFunction.b.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.b.SchwartzIntegrals

def J₁' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₁'
  smooth' := MagicFunction.b.SchwartzProperties.J₁'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₁'_decay'

def J₂' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₂'
  smooth' := MagicFunction.b.SchwartzProperties.J₂'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₂'_decay'

def J₃' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₃'
  smooth' := MagicFunction.b.SchwartzProperties.J₃'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₃'_decay'

def J₄' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₄'
  smooth' := MagicFunction.b.SchwartzProperties.J₄'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₄'_decay'

def J₅' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₅'
  smooth' := MagicFunction.b.SchwartzProperties.J₅'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₅'_decay'

def J₆' : 𝓢(ℝ, ℂ) where
  toFun := MagicFunction.b.RealIntegrals.J₆'
  smooth' := MagicFunction.b.SchwartzProperties.J₆'_smooth'
  decay' := MagicFunction.b.SchwartzProperties.J₆'_decay'

end MagicFunction.b.SchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b' : 𝓢(ℝ, ℂ) :=
    MagicFunction.b.SchwartzIntegrals.J₁'
  + MagicFunction.b.SchwartzIntegrals.J₂'
  + MagicFunction.b.SchwartzIntegrals.J₃'
  + MagicFunction.b.SchwartzIntegrals.J₄'
  + MagicFunction.b.SchwartzIntegrals.J₅'
  + MagicFunction.b.SchwartzIntegrals.J₆'

/-- The -1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def b : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ) := schwartzMap_multidimensional_of_schwartzMap_real
  (EuclideanSpace ℝ (Fin 8)) b'

end MagicFunction.FourierEigenfunctions

end SchwartzMap
