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
public import dep.SpherePacking.MagicFunction.a.Schwartz
public import dep.SpherePacking.ModularForms.Delta
public import dep.SpherePacking.ModularForms.E2
public import dep.SpherePacking.ModularForms.Eisenstein
public import dep.SpherePacking.ModularForms.ResToImagAxis

@[expose] public section

open SchwartzMap Real Complex MagicFunction.FourierEigenfunctions

namespace MagicFunction.a.SpecialValues

section Zero

theorem a_zero : a 0 = -8640 * I / π := sorry

end Zero

end MagicFunction.a.SpecialValues
