import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing

open ArithmeticFunction hiding log

open Finset Nat Real

open scoped zeta sigma

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

open scoped ArithmeticFunction.Moebius

open scoped LSeries.notation

namespace ArithmeticFunction

lemma pow_divisors_mul {m n k : ℕ} (hmn : Nat.Coprime m n) :
    (m * n).divisors.filter (fun x => x ^ k ∣ m * n) =
    (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)).image
      (fun p => p.1 * p.2) := sorry

end ArithmeticFunction
