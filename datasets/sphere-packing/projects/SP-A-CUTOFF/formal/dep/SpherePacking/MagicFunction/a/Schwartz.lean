module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.Tactic.NormNum.Parity
public import dep.SpherePacking.ForMathlib.RadialSchwartz.Basic
public import dep.SpherePacking.ForMathlib.RadialSchwartz.Multidimensional
public import dep.SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap
public import dep.SpherePacking.MagicFunction.IntegralParametrisations
public import dep.SpherePacking.MagicFunction.a.Basic
public import dep.SpherePacking.ModularForms.Delta
public import dep.SpherePacking.ModularForms.E2
public import dep.SpherePacking.ModularForms.Eisenstein
public import dep.SpherePacking.ModularForms.ResToImagAxis

@[expose] public section

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

open MagicFunction MagicFunction.a MagicFunction.a.RadialFunctions MagicFunction.a.RealIntegrals
  MagicFunction.Parametrisations MagicFunction.a.ComplexIntegrands MagicFunction.a.RealIntegrands

open Set Complex Real SchwartzMap

open scoped ContDiff

namespace MagicFunction.a.SchwartzProperties

section Smooth

theorem I₁'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₁' := sorry

theorem I₂'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₂' := sorry

theorem I₃'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₃' := sorry

theorem I₄'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₄' := sorry

theorem I₅'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₅' := sorry

theorem I₆'_smooth' : ContDiff ℝ ∞ RealIntegrals.I₆' := sorry

end Smooth

section Decay

end Decay

end MagicFunction.a.SchwartzProperties

noncomputable section SchwartzMap

namespace MagicFunction.a.RadialSchwartzIntegrals

def I₁' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₁'_smooth' <| sorry

def I₂' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₂'_smooth' <| sorry

def I₃' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₃'_smooth' <| sorry

def I₄' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₄'_smooth' <| sorry

def I₅' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₅'_smooth' <| sorry

def I₆' : 𝓢(ℝ, ℂ) := ofDecayOn (a := 1) MagicFunction.a.SchwartzProperties.I₆'_smooth' <| sorry

end MagicFunction.a.RadialSchwartzIntegrals

namespace MagicFunction.FourierEigenfunctions

/-- The radial component of the +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a' : 𝓢(ℝ, ℂ) :=
    MagicFunction.a.RadialSchwartzIntegrals.I₁'
  + MagicFunction.a.RadialSchwartzIntegrals.I₂'
  + MagicFunction.a.RadialSchwartzIntegrals.I₃'
  + MagicFunction.a.RadialSchwartzIntegrals.I₄'
  + MagicFunction.a.RadialSchwartzIntegrals.I₅'
  + MagicFunction.a.RadialSchwartzIntegrals.I₆'

/-- The +1-Fourier Eigenfunction of Viazovska's Magic Function. -/
@[simps!]
def a : RadialSchwartzMap ℂ ℝ⁸ ℂ := a'.toRadialSchwartzMap ℝ⁸

end MagicFunction.FourierEigenfunctions

end SchwartzMap
