module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import dep.SpherePacking.ForMathlib.RadialSchwartz.Basic
public import dep.SpherePacking.ForMathlib.RadialSchwartz.SchwartzMap

@[expose] public noncomputable section

open SchwartzMap Function RCLike ContDiff Set

namespace SchwartzMap

section ofDecay

/-- A Schwartz map constructed from a smooth function decaying on a subset by multiplying by a
smooth transition function. -/
@[simps!]
def ofDecayOn {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    𝓢(ℝ, ℂ) :=
  let F' : ℝ → ℂ := fun x ↦ Real.smoothTransition (x - a + 1) * f x
  SchwartzMap.mkOfCocompact F' (sorry) <| sorry

end ofDecay

section toRadial

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

@[simps!]
def compNormSq (f : 𝓢(ℝ, ℂ)) : 𝓢(F, ℂ) :=
    f.compCLM ℝ (Function.hasTemperateGrowth_norm_sq F) <| sorry

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 ℂ] [SMulCommClass ℝ 𝕜 ℂ]

/-- A radial Schwartz map on `F` obtained by composing a Schwartz map on `ℝ` with `‖·‖ ^ 2`. -/
@[simps!]
def toRadialSchwartzMap (f : 𝓢(ℝ, ℂ)) : RadialSchwartzMap 𝕜 F ℂ :=
  RadialSchwartzMap.mk (compNormSq F f) (Function.isRadial_norm_sq F).comp_right

/-- A radial Schwartz map on `F` built from a smooth function on `ℝ` decaying on `[a, ∞)`. -/
@[simps!]
def _root_.RadialSchwartzMap.ofDecay {f : ℝ → ℂ} {a : ℝ}
    (smooth : ContDiff ℝ ∞ f)
    (decay : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, a ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    RadialSchwartzMap 𝕜 F ℂ :=
  (ofDecayOn smooth decay).toRadialSchwartzMap F

end toRadial

end SchwartzMap
