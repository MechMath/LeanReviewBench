import Mathlib

open Real

namespace KLN

def a₁ : ℝ := 0.63

noncomputable def a₂ : ℝ := (6 / exp 1) * a₁ - (riemannZeta (1 / 2)).re

def b₁ : ℝ := 0.62

def b₂ : ℝ := 1.048

noncomputable def m₀ : ℝ := sqrt (1 + (2 / 3) * sqrt (6 / 5))

noncomputable def C₁ (H₀ k : ℝ) : ℝ := 6 / π ^ 2 + b₂ / log (k * H₀)

noncomputable def C₂ (H₀ k : ℝ) : ℝ :=
  (π * m₀ * b₁) / log (k * H₀) + 6 * m₀ / (π * k * H₀) +
    (π * m₀ * b₂) / (k * H₀ * log (k * H₀))

noncomputable def I (α β A : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi 0, x ^ A * exp (-2 * α * x ^ β) * (log x) ^ n

noncomputable def J (H₀ α β k T : ℝ) : ℝ :=
  I α β (β + 1 / 3) 0 + (C₂ H₀ k) / (C₁ H₀ k) * k * (I α β (β - 2 / 3) 0) +
    (2 * (I α β (β + 1 / 3) 0) + 2 * (C₂ H₀ k) / (C₁ H₀ k) * k *
      (I α β (β - 2 / 3) 0)) / log (k * T) +
    (I α β (β + 1 / 3) 2) + (C₂ H₀ k) / (C₁ H₀ k) * k *
      (I α β (β - 2 / 3) 2) / (log (k * T)) ^ 2 +
    2 * a₂ * ((I α β (β + 1 / 6) 0) + (C₂ H₀ k) * k / (C₁ H₀ k) *
      (I α β (β - 5 / 6) 0)) / (a₁ * T ^ ((1 : ℝ) / 6) * (log T)) +
    2 * a₂ * ((I α β (β + 1 / 6) 2) + (C₂ H₀ k) * k / (C₁ H₀ k) *
      (I α β (β - 5 / 6) 1)) / (a₁ * T ^ ((1 : ℝ) / 6) * (log T) ^ 2) +
    a₂ ^ 2 * ((I α β (β) 0) + (C₂ H₀ k) * k / (C₁ H₀ k) *
      (I α β (β - 1) 0)) / (a₁ ^ 2 * T ^ ((1 : ℝ) / 3) * (log T) ^ 2)

end KLN
