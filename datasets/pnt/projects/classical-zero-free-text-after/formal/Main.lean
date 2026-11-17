import Mathlib

open Real

noncomputable def riemannZeta.classicalZeroFree (R : ℝ) :=
  ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) →
  riemannZeta (σ + t * Complex.I) ≠ 0
