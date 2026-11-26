module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

@[expose] public section

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

instance : SecondCountableTopology (v.Completion) := sorry

instance : SecondCountableTopology (InfiniteAdeleRing K) := sorry
