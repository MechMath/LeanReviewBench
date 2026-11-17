import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Order.SupClosed

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A B C S T : Finset α} {P : Finset (Finset α)} {x y : α}

/-- The hull of `S` in the family `P` on the ground set `A`: the points of `A` lying in every
member of `P` that contains `S`.  For a convex geometry and `S ⊆ A` it is the least closed
superset of `S` (`hull_mem`, `subset_hull`, `hull_subset`). -/
def hull (A : Finset α) (P : Finset (Finset α)) (S : Finset α) : Finset α :=
  {x ∈ A | ∀ B ∈ P, S ⊆ B → x ∈ B}

/-- The points of `B` whose removal from `B` leaves a member of `P`.  For a closed `B` in a
convex geometry these are the extreme points of `B`, the points outside the hull of the rest of
`B` (`IsConvexGeometry.mem_extremes_iff`); for a set that is not closed the two notions
differ. -/
def extremes (P : Finset (Finset α)) (B : Finset α) : Finset α :=
  {x ∈ B | B.erase x ∈ P}

/-- A hull lies in the ground set. -/
theorem hull_subset_ground : hull A P S ⊆ A := sorry

/-- The closed-set axioms of a finite **convex geometry** on the ground set `A`: closed sets
are subsets of `A`, the empty set and `A` are closed, closed sets are closed under intersection,
and the hull satisfies anti-exchange (if `x ∉ B` lies in the hull of `B ∪ {y}` for a closed `B`
and `y ≠ x`, then `y` does not lie in the hull of `B ∪ {x}`). -/
structure IsConvexGeometry (A : Finset α) (P : Finset (Finset α)) : Prop where
  /-- Closed sets are subsets of the ground set. -/
  subset_of_mem ⦃B : Finset α⦄ : B ∈ P → B ⊆ A
  /-- The empty set is closed. -/
  empty_mem : ∅ ∈ P
  /-- The ground set is closed. -/
  ground_mem : A ∈ P
  /-- Closed sets are closed under intersection. -/
  infClosed : InfClosed (P : Set (Finset α))
  /-- Anti-exchange at closed sets. -/
  antiExchange ⦃B : Finset α⦄ : B ∈ P → ∀ ⦃x y : α⦄, x ≠ y → x ∉ B →
    x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B)

namespace IsConvexGeometry

variable (hP : IsConvexGeometry A P)

include hP

end IsConvexGeometry

/-- Being a convex geometry is decidable: the axioms are bounded quantifications over the finite
data (the points in anti-exchange may be taken in the ground set). -/
instance : Decidable (IsConvexGeometry A P) :=
  decidable_of_iff ((∀ B ∈ P, B ⊆ A) ∧ ∅ ∈ P ∧ A ∈ P ∧ (∀ B ∈ P, ∀ C ∈ P, B ∩ C ∈ P) ∧
      ∀ B ∈ P, ∀ x ∈ A, ∀ y ∈ A, x ≠ y → x ∉ B →
        x ∈ hull A P (insert y B) → y ∉ hull A P (insert x B))
    ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨h1, h2, h3, fun B hB C hC ↦ h4 B hB C hC,
        fun B hB x y hxy hxB hx hy ↦
          h5 B hB x (hull_subset_ground hx) y (hull_subset_ground hy) hxy hxB hx hy⟩,
      fun h ↦ ⟨h.subset_of_mem, h.empty_mem, h.ground_mem, fun _ hB _ hC ↦ h.infClosed hB hC,
        fun B hB x _ y _ ↦ @h.antiExchange B hB x y⟩⟩

end VaughtConjecture.Geometry
