


import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.RingTheory.Finiteness.Defs

namespace LinearIsometry

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    [Module.Finite 𝕜 F]

theorem comp_contDiff_iff {L : E →ₗᵢ[𝕜] F} {f : G → E} {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (L ∘ f) ↔ ContDiff 𝕜 n f  := by sorry

end LinearIsometry

