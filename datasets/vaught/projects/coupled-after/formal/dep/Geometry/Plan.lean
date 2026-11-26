import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Order.SupClosed
import dep.Geometry.ConvexGeometry

namespace VaughtConjecture.Geometry

open Finset

variable {α : Type*} [DecidableEq α] {A B C S : Finset α} {P Q R : Finset (Finset α)} {x : α}

/-- `IsPlan A P`: the family `P` is a recursive visible-face plan on the finite set `A`.  The
base plans are `{∅}` on `∅` and `{∅, {a}}` on `{a}`.  A plan on `A` glues plans `Q` on
`A \ {a}` and `R` on `A \ {b}` for distinct `a, b ∈ A`, provided the common face `A \ {a, b}` is
visible in `Q` and `Q`, `R` have the same members below it; the result is `Q ∪ R` together with
`A` itself (the amalgamation plan of [Kni26, Definition 2.1.1]). -/
inductive IsPlan : Finset α → Finset (Finset α) → Prop
  /-- The plan on the empty set. -/
  | empty : IsPlan ∅ {∅}
  /-- The plan on a singleton. -/
  | singleton (a : α) : IsPlan {a} {∅, {a}}
  /-- Gluing two plans on one-point deletions that agree on their common face. -/
  | step {A : Finset α} {a b : α} {Q R : Finset (Finset α)} (ha : a ∈ A) (hb : b ∈ A)
      (hab : a ≠ b) (hQ : IsPlan (A.erase a) Q) (hR : IsPlan (A.erase b) R)
      (hface : (A.erase a).erase b ∈ Q)
      (hagree : ∀ C ⊆ (A.erase a).erase b, C ∈ Q ↔ C ∈ R) :
      IsPlan A (insert A (Q ∪ R))

namespace IsPlan

/-- Every visible face is a subset of the ground set. -/
theorem subset_of_mem (hP : IsPlan A P) (hB : B ∈ P) : B ⊆ A := sorry

/-- The ground set is a visible face. -/
theorem ground_mem (hP : IsPlan A P) : A ∈ P := sorry

/-- The empty set is a visible face. -/
theorem empty_mem (hP : IsPlan A P) : ∅ ∈ P := sorry

/-- Visible faces are closed under intersection. -/
theorem infClosed (hP : IsPlan A P) : InfClosed (P : Set (Finset α)) := sorry

end IsPlan

include α in
/-- A convex geometry in which every closed set with at least two points has exactly two
extreme points is a plan.  By strong induction on the ground set: its two extreme points `a, b`
give closed coatoms `A \ {a}`, `A \ {b}`, the restrictions to these are plans, and every other
closed set lies below one of them. -/
theorem IsConvexGeometry.isPlan (hP : IsConvexGeometry A P)
    (htwo : ∀ B ∈ P, 1 < #B → #(extremes P B) = 2) : IsPlan A P := sorry

/-- **Plans are exactly the convex geometries with two extremes.**  A family is a recursive
visible-face plan on `A` iff it is a convex geometry on `A` in which every closed set with at
least two points has exactly two extreme points. -/
theorem isPlan_iff_isConvexGeometry_and_card_extremes :
    IsPlan A P ↔ IsConvexGeometry A P ∧ ∀ B ∈ P, 1 < #B → #(extremes P B) = 2 := sorry

/-- Being a plan is decidable, through its characterization as a two-extreme convex
geometry. -/
instance : Decidable (IsPlan A P) :=
  decidable_of_iff _ isPlan_iff_isConvexGeometry_and_card_extremes.symm

namespace IsPlan

end IsPlan

end VaughtConjecture.Geometry

namespace VaughtConjecture.Geometry.IsPlan

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : β ↪ α}

include β in
/-- A plan on a ground set inside the range of an embedding pulls back to a plan: the faces of
the pullback are the sets whose image is a face. -/
theorem preimage {A : Finset α} {P : Finset (Finset α)} (hP : IsPlan A P)
    (hA : (A : Set α) ⊆ Set.range f) :
    IsPlan (A.preimage f f.injective.injOn)
      (P.preimage (Finset.map f) (map_injective f).injOn) := sorry

end VaughtConjecture.Geometry.IsPlan

namespace VaughtConjecture.Geometry

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {A : Finset α} {P : Finset (Finset α)}

end VaughtConjecture.Geometry

namespace VaughtConjecture.Geometry.IsPlan

open Finset

variable {α : Type*} [DecidableEq α] {A B S : Finset α} {P : Finset (Finset α)} {σ : α ↪ α}

end VaughtConjecture.Geometry.IsPlan
