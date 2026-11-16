import Mathlib
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics Chebyshev
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊

noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))

namespace Trudgian2016
theorem theorem_2 (x : ℝ) (hx : x ≥ 229) :
    |pi x - li x| ≤ 0.2795 * x / (log x) ^ ((3 : ℝ) / 4) *
      exp (-sqrt (log x / 6.455)) := by
  sorry
end Trudgian2016

