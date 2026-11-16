import Mathlib
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics Chebyshev
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

namespace Dusart
theorem corollary_5_5 {x : ℝ} (hx : x ≥ 468991632) :
    HasPrimeInInterval x (x / (5000 * (log x) ^ 2)) := by
  sorry
end Dusart

