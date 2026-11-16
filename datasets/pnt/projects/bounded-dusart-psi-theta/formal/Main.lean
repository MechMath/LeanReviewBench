import Mathlib
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics Chebyshev
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

namespace Dusart
theorem proposition_4_3 {x : ℝ} (hx : x ≥ 121) :
  ψ x - θ x > 0.9999 * sqrt x ∧
  ψ x - θ x > sqrt x * (1 - 4 / (log x) ^ 3) := by
  sorry
end Dusart

