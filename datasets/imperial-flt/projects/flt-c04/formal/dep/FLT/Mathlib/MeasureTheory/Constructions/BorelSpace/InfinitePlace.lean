module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import dep.FLT.Mathlib.Topology.MetricSpace.ProperSpace.InfinitePlace

@[expose] public section

open NumberField

open InfinitePlace.Completion

variable (K : Type*) [Field K] [NumberField K] (v : InfinitePlace K)

noncomputable instance : MeasurableSpace (v.Completion) := borel _

instance : BorelSpace (v.Completion) := sorry

noncomputable instance : MeasurableSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (MeasurableSpace (∀ _, _))

instance : BorelSpace (InfiniteAdeleRing K) := sorry
