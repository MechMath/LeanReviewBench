import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
open ArithmeticFunction hiding log
open Finset Nat Real
open scoped zeta sigma
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation
namespace ArithmeticFunction

def liouville : ArithmeticFunction ℤ :=
  toArithmeticFunction (fun n => (-1 : ℤ) ^ Ω n)

lemma LSeries_liouville_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (↗(liouville : ArithmeticFunction ℤ)) s = riemannZeta (2 * s) / riemannZeta s := by
  sorry
end ArithmeticFunction
