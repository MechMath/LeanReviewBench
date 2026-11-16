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

namespace Robin
theorem p_n_lower_const1 (n : ℕ) (hn : (nth_prime' n : ℝ) ≤ (10 : ℝ) ^ 11) :
    nth_prime' n > n * (log n + log (log n) - 1) := by sorry
end Robin

