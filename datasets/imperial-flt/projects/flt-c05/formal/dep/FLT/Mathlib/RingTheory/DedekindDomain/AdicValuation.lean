module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) := sorry

/-- `adicCompletion.equiv` as a `K`-algebra isomorphism onto the underlying completion. -/
noncomputable def adicCompletion.algEquiv
    {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (v : HeightOneSpectrum A) :
    v.adicCompletion K ≃ₐ[K] (v.valuation K).Completion :=
  AlgEquiv.ofRingEquiv (f := adicCompletion.equiv K v)
    fun x => algebraMap_adicCompletion_toCompletion A K v x

end IsDedekindDomain.HeightOneSpectrum
