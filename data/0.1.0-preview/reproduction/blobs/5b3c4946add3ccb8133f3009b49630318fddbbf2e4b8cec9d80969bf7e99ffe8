import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
open ArithmeticFunction hiding log
open Finset Nat Real
open scoped zeta sigma
open scoped ArithmeticFunction.omega ArithmeticFunction.Omega
open scoped ArithmeticFunction.Moebius
open scoped LSeries.notation
namespace ArithmeticFunction

lemma divisors_mul_injective {m n : ℕ} (hmn : m.Coprime n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (m.divisors ×ˢ n.divisors) := by
  /- comes from mathlib PR #36495 -/
  sorry

lemma pow_divisors_mul_injective {m n k : ℕ} (hmn : Nat.Coprime m n) :
    Set.InjOn (fun (p : ℕ × ℕ) => p.1 * p.2) (m.divisors.filter (fun x => x ^ k ∣ m) ×ˢ n.divisors.filter (fun x => x ^ k ∣ n)) := by
  apply Set.InjOn.mono _ (divisors_mul_injective hmn)
  intro ⟨_, _⟩ hab
  simp only [Finset.coe_filter, Set.mem_prod, Set.mem_setOf_eq, Finset.mem_coe] at hab ⊢
  exact ⟨hab.1.1, hab.2.1⟩
end ArithmeticFunction
