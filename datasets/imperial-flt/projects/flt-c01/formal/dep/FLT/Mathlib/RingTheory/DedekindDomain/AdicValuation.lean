module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) := sorry

end IsDedekindDomain.HeightOneSpectrum
