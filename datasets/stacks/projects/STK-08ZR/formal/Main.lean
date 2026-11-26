module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.13.2 (`08ZR`), generalized to `R1Space`: weak local compactness
and local compactness agree in an `R₁` space. -/
@[stacks 08ZR "weak local compactness in R₁ spaces"]
theorem locallyCompactSpace_iff_weaklyLocallyCompactSpace [R1Space X] :
    LocallyCompactSpace X ↔ WeaklyLocallyCompactSpace X := sorry
