import Mathlib.NumberTheory.Chebyshev

open Finset Real

open scoped BigOperators ArithmeticFunction

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)
