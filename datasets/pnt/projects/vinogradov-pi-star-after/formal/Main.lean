import Mathlib

open ArithmeticFunction hiding log

open Nat hiding log

open Finset Topology

open BigOperators Filter Real Classical Asymptotics

open MeasureTheory intervalIntegral

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Omega Chebyshev

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k : ℝ))) / (k : ℝ)

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)

def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))
