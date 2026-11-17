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

noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀

namespace Trudgian2016

theorem theorem_2 (x : ℝ) (hx : x ≥ 229) :
    Eπ.numericalBound x (fun x ↦ 0.2795 * (log x)^(1/4) * exp (-sqrt (log x / 6.455))) := sorry

end Trudgian2016
