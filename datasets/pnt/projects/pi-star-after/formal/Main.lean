import Mathlib.NumberTheory.Chebyshev

open Finset Real

open scoped BigOperators ArithmeticFunction

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k : ℝ))) / (k : ℝ)
