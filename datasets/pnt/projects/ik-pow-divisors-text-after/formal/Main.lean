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
      (fun p => p.1 * p.2) := by
  ext x
  simp only [mem_image, mem_product, mem_filter, mem_divisors, ne_eq, Prod.exists]
  constructor
  · intro hx
    obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ a * b = x := Nat.dvd_mul.mp hx.1.1
    simp only [mul_eq_zero, not_or, ← hab, mul_pow] at hx
    exact ⟨a, b, ⟨⟨⟨⟨ha, hx.1.2.1⟩, (hmn.coprime_dvd_left ha).pow_left k |>.dvd_of_dvd_mul_right (dvd_trans (dvd_mul_right _ _) hx.2)⟩,
      ⟨⟨hb, hx.1.2.2⟩, (hmn.symm.coprime_dvd_left hb).pow_left k |>.dvd_of_dvd_mul_left (dvd_trans (dvd_mul_left _ _) hx.2)⟩⟩, hab⟩⟩
  · intro ⟨a, b, hab⟩
    rw[← hab.2, mul_pow]
    exact ⟨⟨Nat.mul_dvd_mul hab.1.1.1.1 hab.1.2.1.1, Nat.mul_ne_zero_iff.mpr ⟨hab.1.1.1.2, hab.1.2.1.2⟩⟩, mul_dvd_mul hab.1.1.2 hab.1.2.2⟩
end ArithmeticFunction
