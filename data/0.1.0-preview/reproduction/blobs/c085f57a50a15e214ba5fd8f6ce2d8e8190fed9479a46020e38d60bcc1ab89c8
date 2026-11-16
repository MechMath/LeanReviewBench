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

namespace Dusart1999
theorem p_n_upper (n : ℕ) (hn : n > 39017) :
    nth_prime' n < n * (log n + log (log n) - 0.9484) := by sorry
end Dusart1999

