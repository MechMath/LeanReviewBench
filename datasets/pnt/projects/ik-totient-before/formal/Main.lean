import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
open ArithmeticFunction hiding log
open Finset Nat Real
open scoped zeta sigma
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation
namespace ArithmeticFunction

lemma LSeries_totient_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗totient) s = riemannZeta (s - 1) / riemannZeta s := by
  sorry
end ArithmeticFunction
