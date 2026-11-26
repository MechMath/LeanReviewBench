module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.CoarseDeGiorgi.Statements.ArrayFracSeminorm
public import dep.CoarseDeGiorgi.Statements.EuclidDist
public import dep.CoarseDeGiorgi.Statements.IsWeakDerivArray
public import dep.CoarseDeGiorgi.Statements.SobolevNorm
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Sobolev.L2Ambient
public import dep.Homogenization.Sobolev.WeakDerivatives

@[expose] public section

open Homogenization MeasureTheory

open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace CoarseDeGiorgi

/-- The negative Sobolev norm `e.negative.sobolev.norm`: for an open `U`, `β ≥ 0`, `1 < p < ∞`, `p' = p / (p - 1)`, and
a matrix field `b` with `|b| ∈ L¹(U)` (entrywise integrability on `U`, as in `besovCubeNorm`),
`‖b‖_{W^{-β,p}(U)} = sup {|∫_U g b| : g ∈ L^∞(U), ‖g‖_{W^{β,p'}(U)} ≤ 1}`,
the dual norm tested on bounded functions. `∫_U g b` is the entrywise integral and `|·|` is
the ℓ²→ℓ² operator norm. The order of the space is `-β`. The value lies in `[0, ∞]`; the
case `p = ∞` (`p' = 1`) is not formalized. -/
noncomputable def negSobolevNorm {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U) (b : Vec d → Mat d)
    (_hb : ∀ i j, Integrable (fun x => b x i j) (volume.restrict U))
    (β p : ℝ) (hβ : 0 ≤ β) (hp : 1 < p) : ℝ≥0∞ :=
  ⨆ (g : Vec d → ℝ) (_ : MemLp g ⊤ (volume.restrict U))
    (_ : sobolevNorm U hU β (p / (p - 1)) hβ
      ((le_div_iff₀ (sub_pos.mpr hp)).mpr (sorry)) g ≤ 1),
    ENNReal.ofReal ‖Matrix.of fun i j => ∫ x in U, g x * b x i j ∂volume‖

end CoarseDeGiorgi
