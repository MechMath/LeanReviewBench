import Mathlib
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics Chebyshev
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

namespace MassiasRobin
theorem p_n_lower (n : ℕ) (hn2 : 2 ≤ n)
    (hn : (n : ℝ) ≤ exp 598 ∨ (n : ℝ) ≥ exp 1800) :
    nth_prime' n ≥ n * (log n + log (log n) - 1) := by sorry
end MassiasRobin

