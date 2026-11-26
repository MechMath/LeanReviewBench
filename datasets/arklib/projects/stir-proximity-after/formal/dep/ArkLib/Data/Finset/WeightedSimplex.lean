module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Sym.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace Finset

open scoped BigOperators

/-- The finite box of nonnegative vectors of weighted sum at most `W`. A zero-weight coordinate
still ranges from `0` to `W`; at an empty index type there is exactly one vector. -/
def natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (W : ℕ) : Finset (σ → ℕ) :=
  (Fintype.piFinset fun _ ↦ range (W + 1)).filter fun c ↦ ∑ i, w i * c i ≤ W

/-- Membership always implies the weighted budget, including with zero weights and `W = 0`. -/
theorem weightedSum_le_of_mem_natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    {w : σ → ℕ} {W : ℕ} {c : σ → ℕ} (hc : c ∈ natWeightedSimplex w W) :
    ∑ i, w i * c i ≤ W := sorry

/-- With every weight positive, the weighted budget itself enforces the finite coordinate box.
For a zero weight this equivalence fails when that coordinate exceeds `W`. -/
theorem mem_natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) {W : ℕ} {c : σ → ℕ} :
    c ∈ natWeightedSimplex w W ↔ ∑ i, w i * c i ≤ W := sorry

private def ordinarySimplex (σ : Type*) [Fintype σ] (W : ℕ) :=
  {c : σ → ℕ // ∑ i, c i ≤ W}

private def exactSimplex (σ : Type*) [Fintype σ] (W : ℕ) :=
  {c : Option σ → ℕ // ∑ i, c i = W}

/-- Slack-coordinate equivalence between the unit-weight executable simplex and functions on
`Option σ` whose coordinates sum exactly to `W`. The `none` coordinate stores the unused budget.
This is the public exact-simplex form of stars and bars. -/
def natWeightedSimplexOneEquivExact
    {σ : Type*} [Fintype σ] [DecidableEq σ] (W : ℕ) :
    ↑(natWeightedSimplex (fun _ : σ ↦ 1) W) ≃
      {c : Option σ → ℕ // ∑ i, c i = W} :=
  {
    toFun := fun c ↦ ⟨fun i ↦ i.elim (W - ∑ j, c.1 j) c.1, sorry⟩
    invFun := fun c ↦ ⟨fun i ↦ c.1 (some i), sorry⟩
    left_inv := fun c ↦ sorry
    right_inv := fun c ↦ sorry
  }

/-- The unit-weight executable simplex is the subtype of tuples of total at most `W`. -/
private def natWeightedSimplexOneEquivOrdinary {σ : Type*} [Fintype σ] [DecidableEq σ]
    (W : ℕ) : ↑(natWeightedSimplex (fun _ : σ ↦ 1) W) ≃ ordinarySimplex σ W where
  toFun c := ⟨c.1, by
    simpa only [one_mul] using weightedSum_le_of_mem_natWeightedSimplex c.2⟩
  invFun c := ⟨c.1, (mem_natWeightedSimplex (fun _ ↦ one_ne_zero)).mpr
    (sorry)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def ordinaryEquivExact {σ : Type*} [Fintype σ] (W : ℕ) :
    ordinarySimplex σ W ≃ exactSimplex σ W := by
  classical
  exact (natWeightedSimplexOneEquivOrdinary W).symm.trans (natWeightedSimplexOneEquivExact W)

private noncomputable def ordinaryEquivSym {σ : Type*} [Fintype σ] (W : ℕ) :
    ordinarySimplex σ W ≃ Sym (Option σ) W := by
  classical
  exact (ordinaryEquivExact W).trans (Sym.equivNatSumOfFintype _ _).symm

private noncomputable instance ordinarySimplexFintype {σ : Type*} [Fintype σ] (W : ℕ) :
    Fintype (ordinarySimplex σ W) := by
  classical
  exact Fintype.ofEquiv (Sym (Option σ) W) (ordinaryEquivSym W).symm

end Finset
