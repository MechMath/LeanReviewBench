module

public import Mathlib.Order.Filter.Cofinite

@[expose] public section

instance (ι : Type*) [Countable ι] : Countable (.cofinite : Filter ι).sets := sorry
