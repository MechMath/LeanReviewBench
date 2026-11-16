import Mathlib.NumberTheory.Chebyshev
open Finset Real
open scoped BigOperators ArithmeticFunction

noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, (Λ n : ℝ) / n
