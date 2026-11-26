module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
public import dep.SpherePacking.ModularForms.Delta
public import dep.SpherePacking.ModularForms.E2
public import dep.SpherePacking.ModularForms.ResToImagAxis

@[expose] public section

open ModularForm hiding E₄ E₆

open UpperHalfPlane Complex

open scoped Real Nat ArithmeticFunction.sigma

noncomputable section

/-- The normalised Eisenstein series of weight `k` and level one, with constant term `1`.
The scaling by `1/2` matches the normalisation, since the sum is taken over coprime pairs. -/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma 1) k :=
  (1 / 2 : ℂ) • eisensteinSeriesMF hk 0

/-- The normalised Eisenstein series of weight `4` and level one, with constant term `1`. -/
def E₄ := E 4 (sorry)

/-- The normalised Eisenstein series of weight `6` and level one, with constant term `1`. -/
def E₆ := E 6 (sorry)

/-- The quotient `(E₂E₄ - E₆)² / Δ`, the blueprint's `φ₀`. -/
def φ₀ (z : ℍ) := (((E₂ z) * (E₄ z) - (E₆ z)) ^ 2) / (Δ z)

/-- The extension of `φ₀` to `ℂ`, vanishing outside the upper half plane. -/
def φ₀'' (z : ℂ) : ℂ := if hz : 0 < z.im then φ₀ ⟨z, hz⟩ else 0
