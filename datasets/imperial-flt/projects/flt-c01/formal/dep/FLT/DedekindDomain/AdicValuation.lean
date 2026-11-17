module

public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Path
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

instance : Valuation.IsRankOneDiscrete vK := sorry

/-- The maximal ideal of the integers of the completion of `v`. -/
noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)

instance : (v.completionIdeal K).LiesOver v.asIdeal := sorry

noncomputable instance : CommSemiring ↥(adicCompletionIntegers K v) := inferInstance

noncomputable instance : Field (adicCompletion K v) := inferInstance

set_option synthInstance.maxHeartbeats 200000

attribute [local instance 9999] Algebra.toModule in
theorem inertiaDeg_asIdeal_completionIdeal :
    Ideal.inertiaDeg' v.asIdeal (v.completionIdeal K) = 1 := sorry

namespace adicCompletion

noncomputable instance : Ring (adicCompletion K v) := inferInstance

set_option synthInstance.maxHeartbeats 200000

instance : Ring.DimensionLEOne (v.adicCompletionIntegers K) := sorry

open scoped algebraMap in
instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := sorry

instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) := sorry

open scoped Valued in
instance : IsDiscreteValuationRing (𝒪[v.adicCompletion K]) := sorry

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum
