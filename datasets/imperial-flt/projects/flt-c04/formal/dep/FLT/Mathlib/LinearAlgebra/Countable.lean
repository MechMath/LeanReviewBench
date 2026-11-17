module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

instance (K : Type*) [Field K] [NumberField K] : Countable K := sorry
