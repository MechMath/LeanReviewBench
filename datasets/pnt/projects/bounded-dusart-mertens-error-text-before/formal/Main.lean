import Mathlib

open ArithmeticFunction hiding log

open Nat hiding log

open Finset Topology

open BigOperators Filter Real Classical Asymptotics Chebyshev

open MeasureTheory intervalIntegral

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.Omega Chebyshev

namespace RS_prime

noncomputable def L (f : ℝ → ℝ) : ℝ :=
    2 * f 2 / Real.log 2 - ∫ y in Set.Ioi 2, (θ y - y) * deriv (fun t ↦ f t / log t) y

end RS_prime

namespace RS_prime

noncomputable def _root_.mertensConstant : ℝ := - Real.log 2 + L (fun x => log x / x)

end RS_prime

namespace Dusart

theorem theorem_5_7 {x : ℝ} (hx : x ≥ 912560) : ∃ E,
  ( (∑ p ∈ Finset.filter Prime (Finset.range (⌊x⌋₊ + 1)), Real.log p / p) = log x
  + mertensConstant + E ∧ |E| ≤ 0.3 / (log x) ^ 2 ) := sorry

end Dusart
