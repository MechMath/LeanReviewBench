module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Constructions
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Pi

@[expose] public section

theorem Continuous.piSemialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J}
    [(j : J) → TopologicalSpace (g j)] [(i : I) → TopologicalSpace (f i)]
    (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (h : ∀ i, Continuous (p i)) :
    Continuous (Pi.semialgHomPi f g p) := sorry
