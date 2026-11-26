module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

open ContDiff SchwartzMap

variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

open Filter Topology

/-- Construct a `SchwartzMap` from a smooth function `f` whose Schwartz decay bounds only need
to hold eventually at infinity (i.e. cocompactly), rather than for every `x`. This relaxes the
hypothesis of the anonymous-constructor form `⟨f, smooth, decay⟩`, since on a bounded region a
continuous function is automatically bounded. -/
@[expose, simps]
public def SchwartzMap.mkOfCocompact (f : E → F) (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ k n : ℕ, ∃ C : ℝ, ∀ᶠ x in cocompact E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(E, F) where
  toFun := f
  smooth' := smooth
  decay' k n := sorry
