module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import dep.CoarseDeGiorgi.Statements.EuclidDist
public import dep.Homogenization.Ambient.Basic
public import dep.Homogenization.Ambient.CoefficientField
public import dep.Homogenization.Ambient.HilbertFinite
public import dep.Homogenization.Sobolev.L2Ambient

@[expose] public section

open Homogenization MeasureTheory

open scoped BigOperators ENNReal

namespace CoarseDeGiorgi

/-- The seminorm `e.fractional.seminorm` for an array-valued function `F = (F i)_{i : ι}`:
`[F]_{W^{α,r}(V)} = (∫_V ∫_V |F(x) - F(y)|^r / |x - y|^{d + α r} dx dy)^{1/r}`, where `|·|` on the
array `F(x) - F(y) ∈ ℝ^ι` is the Euclidean norm (as in the notation section: "On vectors, |·| is the Euclidean
norm") and `|x - y|` is `euclidDist`. It is `fracSeminorm` (via
`fracKernelWithDimension`) with `|w x - w y|` replaced by the Euclidean norm of the array
difference; for a one-entry array the two agree. Used with `F = ∇ᵐw` in `sobolevNorm`. -/
noncomputable def arrayFracSeminorm {d : ℕ} {ι : Type*} [Fintype ι] (V : Set (Vec d))
    (α r : ℝ) (F : ι → Vec d → ℝ) : ℝ≥0∞ :=
  (∫⁻ p : Vec d × Vec d,
      ENNReal.ofReal
        (Real.sqrt (∑ i, (F i p.1 - F i p.2) ^ 2) ^ r /
          euclidDist p.1 p.2 ^ ((d : ℝ) + α * r))
    ∂((volume.restrict V).prod (volume.restrict V))).rpow (1 / r)

end CoarseDeGiorgi
