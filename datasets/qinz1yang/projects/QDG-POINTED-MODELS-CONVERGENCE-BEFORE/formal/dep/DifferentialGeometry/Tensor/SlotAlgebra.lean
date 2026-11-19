import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace DifferentialGeometry.Tensor.SlotAlgebra

lemma sum_fin3_fun_eq_triple
    {R ι : Type*} [AddCommMonoid R] [Mul R] [Fintype ι]
    (A B C : ι -> R) (K : ι -> ι -> ι -> R) :
    (∑ r : Fin 3 -> ι, A (r 0) * B (r 1) * C (r 2) * K (r 0) (r 1) (r 2)) =
      ∑ i : ι, ∑ k : ι, ∑ j : ι, A i * B k * C j * K i k j  := by sorry

lemma double_sum_sub_eq_diag_sub_diag_of_offdiag_swap
    {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (F G : ι → ι → A)
    (h : ∀ q p, q ≠ p → F q p = G p q) :
    (∑ q, ∑ p, F q p) - (∑ q, ∑ p, G q p) =
      (∑ q, F q q) - (∑ q, G q q)  := by sorry

lemma double_update_sum_cancel_diag
    {ι V A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    (eval : (ι → V) → A)
    (slots X Y XY YX : ι → V) :
    - (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (Y q))
            p
            (if p = q then XY q else X p)))
      + (∑ q, ∑ p,
        eval
          (Function.update
            (Function.update slots q (X q))
            p
            (if p = q then YX q else Y p)))
      =
    - (∑ q, eval (Function.update slots q (XY q)))
      + (∑ q, eval (Function.update slots q (YX q)))  := by sorry

lemma sum_update_finCons_of_cons
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head dHead : V) (tail dTail : Fin s → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        ((Fin.cons dHead dTail : Fin (s + 1) → V) a))) =
      F (Fin.cons dHead tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (dTail q)))  := by sorry

lemma sum_update_finCons
    {s : ℕ} {V A : Type*} [AddCommMonoid A]
    (F : (Fin (s + 1) → V) → A)
    (head : V) (tail : Fin s → V) (d : Fin (s + 1) → V) :
    (∑ a : Fin (s + 1),
      F (Function.update (Fin.cons head tail : Fin (s + 1) → V) a
        (d a))) =
      F (Fin.cons (d 0) tail) +
        ∑ q : Fin s, F (Fin.cons head (Function.update tail q (d q.succ)))  := by sorry

lemma sum_rotate3
    {ι κ ι' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [AddCommMonoid A] (F : ι → κ → ι' → A) :
    (∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j) =
      ∑ j : ι', ∑ i : ι, ∑ k : κ, F i k j  := by sorry

lemma sum_rotate4
    {ι κ ι' κ' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] [AddCommMonoid A] (F : ι → κ → ι' → κ' → A) :
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m) =
      ∑ m : κ', ∑ i : ι, ∑ k : κ, ∑ l : ι', F i k l m  := by sorry

lemma sum_rotate4_two
    {ι κ ι' κ' A : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [Fintype κ'] [AddCommMonoid A] (F : ι → κ → ι' → κ' → A) :
    (∑ i : ι, ∑ k : κ, ∑ l : ι', ∑ m : κ', F i k l m) =
      ∑ l : ι', ∑ m : κ', ∑ i : ι, ∑ k : κ, F i k l m  := by sorry

lemma sum_mul_right3
    {ι κ ι' R : Type*} [Fintype ι] [Fintype κ] [Fintype ι']
    [NonUnitalNonAssocSemiring R] (F : ι → κ → ι' → R) (c : ι' → R) :
    (∑ j : ι', (∑ i : ι, ∑ k : κ, F i k j) * c j) =
      ∑ i : ι, ∑ k : κ, ∑ j : ι', F i k j * c j  := by sorry

end DifferentialGeometry.Tensor.SlotAlgebra

