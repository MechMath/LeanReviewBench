import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators

open MeasureTheory

namespace FormalSLT.Risk

variable {ι Z : Type*}

/-- The empirical risk on a fixed sequence `z : Fin n → Z` is the arithmetic
mean of the per-sample losses. This is purely a deterministic real number
once `z`, `ℓ`, and `i` are fixed. -/
noncomputable def empiricalRisk {n : ℕ} (z : Fin n → Z) (ℓ : ι → Z → ℝ)
    (i : ι) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k, ℓ i (z k)

end FormalSLT.Risk
