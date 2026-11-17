module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import dep.FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion

@[expose] public section

variable (K : Type*) [Field K]

open NumberField InfinitePlace

instance : T2Space (InfiniteAdeleRing K) := sorry

variable [NumberField K] in
instance : SecondCountableTopology (InfiniteAdeleRing K) := sorry

/-- The ℝ algebra structure on InfiniteAdeleRing K. -/
noncomputable instance : Algebra ℝ (InfiniteAdeleRing K) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K|>.symm.toRingHom.comp (algebraMap ℝ _)).toAlgebra

variable [NumberField K] in
instance : Module.Finite ℝ (InfiniteAdeleRing K) := sorry

instance : IsModuleTopology ℝ ℂ := sorry

variable [NumberField K] in
instance : IsModuleTopology ℝ (InfiniteAdeleRing K) := sorry
