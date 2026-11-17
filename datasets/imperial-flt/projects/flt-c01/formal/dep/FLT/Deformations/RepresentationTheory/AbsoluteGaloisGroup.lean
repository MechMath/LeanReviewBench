module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Path
public import dep.FLT.DedekindDomain.AdicValuation
public import dep.FLT.Deformations.Lemmas
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
public import dep.FLT.Deformations.RepresentationTheory.Frobenius
public import dep.FLT.Deformations.RepresentationTheory.IntegralClosure
public import dep.FLT.Mathlib.LinearAlgebra.Countable
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.NumberField.Completion.Finite

@[expose] public section

variable {K L : Type*} [Field K] [Field L]

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [CommRing B] [TopologicalSpace B]

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

variable {n : Type*} [Fintype n] [DecidableEq n]

open NumberField

variable [NumberField K]

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

local notation3 "𝔪" => IsLocalRing.maximalIdeal

local notation3 "κ" => IsLocalRing.ResidueField

local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)

local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v

local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

set_option backward.isDefEq.respectTransparency false in
/-- Given a field extension, this is a map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.mapAux (f : K →+* L) : Γ L →* Γ K where
  toFun σ :=
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    ((σ.restrictScalars K).toAlgHom.comp
      (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ)).restrictNormal' (Kᵃˡᵍ)
  map_one' := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (IsAlgClosed.lift : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans (by simp)
  map_mul' σ₁ σ₂ := by
    letI := f.toAlgebra
    letI := (AlgebraicClosure.map f).toAlgebra
    apply AlgEquiv.ext fun i ↦ ?_
    apply (AlgebraicClosure.map f).injective
    refine (AlgHom.restrictNormal_commutes _ _ _).trans ?_
    refine ((AlgHom.restrictNormal_commutes _ _ _).trans ?_).symm
    simpa [absoluteGaloisGroup] using! AlgHom.restrictNormal_commutes _ _ _

/-- Given a field extension, this is a continuous map between its absolute galois group.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures -/
noncomputable
def Field.absoluteGaloisGroup.flt_map (f : K →+* L) : Γ L →ₜ* Γ K where
  __ := Field.absoluteGaloisGroup.mapAux f
  continuous_toFun := by
    classical
    letI := f.toAlgebra
    let F : Kᵃˡᵍ →ₐ[K] Lᵃˡᵍ := IsAlgClosed.lift
    letI := F.toRingHom.toAlgebra
    apply continuous_of_continuousAt_one (Field.absoluteGaloisGroup.mapAux f)
    rw [ContinuousAt, map_one]
    refine ((galGroupBasis L (Lᵃˡᵍ)).nhds_one_hasBasis.tendsto_iff
      (galGroupBasis K (Kᵃˡᵍ)).nhds_one_hasBasis).mpr ?_
    rintro _ ⟨_, ⟨K', hK', rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨.adjoin _ (K'.map F), ?_, rfl⟩, rfl⟩, fun σ hσ x ↦ ?_⟩
    · have : FiniteDimensional _ _ := hK'
      obtain ⟨s, hs⟩ := K'.fg_iff_finiteType.mpr (inferInstanceAs (Algebra.FiniteType K K'))
      obtain rfl := IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ hs.symm
      simp only [IntermediateField.adjoin_map, IntermediateField.adjoin_adjoin_right,
        ← Finset.coe_image]
      refine IntermediateField.finiteDimensional_adjoin fun _ _ ↦ Algebra.IsIntegral.isIntegral _
    · exact F.injective ((AlgHom.restrictNormal_commutes _ _ _).trans
        (hσ ⟨F x, IntermediateField.subset_adjoin _ _ ⟨_, x.2, rfl⟩⟩))

set_option allowUnsafeReducibility true in
attribute [reducible] Field.absoluteGaloisGroup

instance finiteIndex_fixingSubgroup {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] : E.fixingSubgroup.FiniteIndex := sorry

open IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    CompactSpace (L ≃ₐ[K] L) := sorry

open scoped IntermediateField in
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] :
    ContinuousSMulDiscrete (L ≃ₐ[K] L) L := sorry

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) := sorry

attribute [local instance 100000]
  instAlgebraSubtypeMemValuationSubring_dep IntermediateField.algebra'
  Algebra.toSMul Subalgebra.toCommRing Algebra.toModule
  Subalgebra.toRing Ring.toAddCommGroup AddCommGroup.toAddGroup
  ValuationSubring.smulCommClass IntermediateField.toAlgebra
  IntermediateField.smulCommClass_of_normal
  mulSemiringActionIntegralClosure
  Subalgebra.algebra
  CommRing.toCommSemiring
  Valued.toIsUniformAddGroup

attribute [local instance] Valued.toNormedField in
lemma isIntegral_of_spectralNorm_le_one
    {K L Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Field K] [Field L]
    [Valued K Γ₀] [(Valued.v : Valuation K Γ₀).RankOne] [Algebra K L] [Algebra.IsAlgebraic K L]
    {x : L} (hx : spectralNorm K L x ≤ 1) : IsIntegral (Valued.v : Valuation K Γ₀).integer x := sorry

noncomputable instance : NontriviallyNormedField Kᵥ := Valued.toNontriviallyNormedField _ _

instance valuationRing_integralClosure
    {L : Type*} [Field L] [Algebra Kᵥ L] [Algebra.IsAlgebraic Kᵥ L] :
    ValuationRing (IntegralClosure 𝒪ᵥ L) := sorry

/-- The local inertia subgroup of a number field at a prime, defined as a subgroup
of the local galois group. -/
noncomputable
def localInertiaGroup : Subgroup (Γ Kᵥ) :=
  (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))).toAddSubgroup.inertia (Γ Kᵥ)

instance : CharZero Kᵥ := sorry

instance {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    Algebra.IsInvariant K L (L ≃ₐ[K] L) := sorry

instance : Finite (IsLocalRing.ResidueField 𝒪ᵥ) := sorry

instance finite_adicCompletionIntegers_quotient
    {I : Ideal 𝒪ᵥ} [I.IsPrime] [NeZero I] : Finite (𝒪ᵥ ⧸ I) := sorry

instance neZero_maximalIdeal_integralClosure :
    NeZero (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ))) := sorry

/-- An arbitrary choice of an (arithmetic) frobenious element of a local galois group. -/
noncomputable
def Field.AbsoluteGaloisGroup.adicArithFrob : Γ Kᵥ :=
  arithFrobAt' 𝒪ᵥ (Γ Kᵥ) (𝔪 (IntegralClosure 𝒪ᵥ (Kᵥᵃˡᵍ)))

local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v
