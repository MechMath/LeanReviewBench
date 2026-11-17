module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

@[expose] public section

instance NumberField.InfinitePlace.Completion.secondCountableTopology
    {K : Type*} [Field K] (v : InfinitePlace K) :
    SecondCountableTopology (v.Completion) := sorry
