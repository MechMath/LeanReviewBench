module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import dep.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.FiniteAdeleRing
public import dep.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.InfinitePlace
public import dep.FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import dep.FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion
public import dep.FLT.Mathlib.Topology.MetricSpace.ProperSpace.InfinitePlace

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open NumberField

instance : MeasurableSpace (AdeleRing (𝓞 K) K) := inferInstanceAs (MeasurableSpace (_ × _))

instance : BorelSpace (AdeleRing (𝓞 K) K) := sorry
