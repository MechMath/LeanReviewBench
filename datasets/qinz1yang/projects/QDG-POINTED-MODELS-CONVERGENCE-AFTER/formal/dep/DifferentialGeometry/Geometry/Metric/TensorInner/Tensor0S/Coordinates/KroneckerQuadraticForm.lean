import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Matrix

open scoped BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma isHermitian_entry
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (i j : n) :
    A i j = ∑ k : n,
        (hA.eigenvectorUnitary : Matrix n n ℝ) i k *
          hA.eigenvalues k *
          (hA.eigenvectorUnitary : Matrix n n ℝ) j k  := by sorry

omit [DecidableEq n] in
theorem sum_posSemidef_mul_posSemidef_nonneg
    {M G : Matrix n n ℝ} (hM : M.PosSemidef) (hG : G.PosSemidef) :
    0 ≤ ∑ i, ∑ j, M i j * G i j  := by sorry

section KroneckerPow

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

omit [DecidableEq Idx] in
private lemma sum_fin_succ_fun {R : Type*} [AddCommMonoid R] (s : ℕ)
    (f : (Fin (s + 1) → Idx) → R) :
    (∑ I : Fin (s + 1) → Idx, f I)
      = ∑ k : Idx, ∑ I : Fin s → Idx, f (Fin.cons k I)  := by sorry

omit [DecidableEq Idx] in
private lemma sum_fin_succ_fun₂ {R : Type*} [AddCommMonoid R] (s : ℕ)
    (f : (Fin (s + 1) → Idx) → (Fin (s + 1) → Idx) → R) :
    (∑ I : Fin (s + 1) → Idx, ∑ J : Fin (s + 1) → Idx, f I J)
      = ∑ k : Idx, ∑ I : Fin s → Idx, ∑ l : Idx, ∑ J : Fin s → Idx,
          f (Fin.cons k I) (Fin.cons l J)  := by sorry

omit [Fintype Idx] [DecidableEq Idx] in
private lemma prod_fin_succ_Q (s : ℕ) (Q : Idx → Idx → ℝ)
    (k l : Idx) (I J : Fin s → Idx) :
    (∏ a : Fin (s + 1),
        Q ((Fin.cons k I : Fin (s + 1) → Idx) a)
          ((Fin.cons l J : Fin (s + 1) → Idx) a))
      = Q k l * ∏ a : Fin s, Q (I a) (J a)  := by sorry

private lemma diag_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ℝ) (G : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, (α * (if i = j then (1 : ℝ) else 0)) * G i j)
      = α * ∑ i : ι, G i i  := by sorry

private lemma matrix_posSemidef_of_quad_nonneg {ι : Type*} [Fintype ι]
    (A : ι → ι → ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hquad : ∀ x : ι → ℝ, 0 ≤ ∑ i : ι, ∑ j : ι, A i j * (x i * x j)) :
    (Matrix.of A).PosSemidef  := by sorry

private lemma shifted_posSemidef
    (Q : Idx → Idx → ℝ) (α : ℝ)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (hQlb : ∀ w : Idx → ℝ, α * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, Q i j * (w i * w j)) :
    (Matrix.of fun i j : Idx =>
      Q i j - α * (if i = j then (1 : ℝ) else 0)).PosSemidef  := by sorry

omit [DecidableEq Idx] in
private lemma kron_kernel_posSemidef_of_ih (s : ℕ) (Q : Idx → Idx → ℝ) (α : ℝ)
    (hαnonneg : 0 ≤ α)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (ih : ∀ w : (Fin s → Idx) → ℝ,
      α ^ s * ∑ I : Fin s → Idx, w I ^ 2 ≤
        ∑ I : Fin s → Idx, ∑ J : Fin s → Idx,
          (∏ a : Fin s, Q (I a) (J a)) * (w I * w J)) :
    (Matrix.of fun I J : Fin s → Idx =>
      ∏ a : Fin s, Q (I a) (J a)).PosSemidef  := by sorry

private lemma sandwich_entry {ι κ : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (V : Matrix ι κ ℝ) (k l : κ) :
    (Vᴴ * P * V) k l = ∑ I : ι, ∑ J : ι, P I J * (V I k * V J l)  := by sorry

omit [DecidableEq Idx] in
theorem quadForm_id_le_pow
    (Q : Idx → Idx → ℝ) (C : ℝ) (hC : 0 < C)
    (hQsymm : ∀ i j, Q i j = Q j i)
    (hQlb : ∀ w : Idx → ℝ, (1 / C) * ∑ i, w i ^ 2 ≤
      ∑ i, ∑ j, Q i j * (w i * w j)) :
    ∀ (s : ℕ) (c : (Fin s → Idx) → ℝ),
      (1 / C) ^ s * ∑ I0 : Fin s → Idx, c I0 ^ 2 ≤
        ∑ I0 : Fin s → Idx, ∑ J0 : Fin s → Idx,
          (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0)  := by sorry

theorem quad_lb_of_near_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → ι → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hnear : ∀ i j, |Q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε)
    (hsmall : (Fintype.card ι : ℝ) * ε ≤ 1 / 2) :
    ∀ w : ι → ℝ, (1 / 2) * ∑ i, w i ^ 2 ≤ ∑ i, ∑ j, Q i j * (w i * w j)  := by sorry

theorem quad_ub_of_near_id {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → ι → ℝ) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hnear : ∀ i j, |Q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε)
    (s : ℕ) (c : (Fin s → ι) → ℝ) :
    (∑ I0 : Fin s → ι, ∑ J0 : Fin s → ι,
        (∏ a, Q (I0 a) (J0 a)) * (c I0 * c J0)) ≤
      ((1 + ε) * (Fintype.card ι : ℝ)) ^ s * ∑ I0 : Fin s → ι, c I0 ^ 2  := by sorry

end KroneckerPow

end Matrix

