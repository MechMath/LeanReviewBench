module

public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.BaseChange
public import dep.FLT.DedekindDomain.IntegralClosure

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

open IsDedekindDomain NumberField HeightOneSpectrum

instance : Countable (HeightOneSpectrum (𝓞 ℚ)) := sorry

instance : Countable (HeightOneSpectrum (𝓞 K)) := sorry
