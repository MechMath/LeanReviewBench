import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Support

open Set

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : E → F} {s t : Set E}

theorem ContDiffOn.contDiffOn_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) : ContDiffOn 𝕜 n f t  := by sorry

theorem ContDiffOn.contDiff_of_tsupport_subset (hf : ContDiffOn 𝕜 n f s)
    (hs : IsOpen s) (hfs : tsupport f ⊆ s) : ContDiff 𝕜 n f  := by sorry

theorem ContDiffOn.indicator_of_tsupport_subset (hf : ContDiffOn 𝕜 n f (s ∩ t))
    (hs : IsOpen s) (hfs : tsupport f ∩ t ⊆ s) :
    ContDiffOn 𝕜 n ((s ∩ t).indicator f) t  := by sorry

