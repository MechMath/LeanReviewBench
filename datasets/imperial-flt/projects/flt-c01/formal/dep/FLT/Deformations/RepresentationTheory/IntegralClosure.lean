module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.Lemmas
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete

@[expose] public section

section

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- `IntegralClosure R A` is the integral closure of `R` in `A` as a type.
We don't use the subring directly to avoid horrendous timeouts. -/
def IntegralClosure : Type _ := integralClosure R A

instance : CommRing (IntegralClosure R A) := (integralClosure R A).toCommRing

instance : Algebra R (IntegralClosure R A) := (integralClosure R A).algebra

instance : Algebra (IntegralClosure R A) A := (integralClosure R A).toAlgebra

instance [IsDomain A] : IsDomain (IntegralClosure R A) := sorry

instance : Algebra.IsIntegral R (IntegralClosure R A) := sorry

instance : IsScalarTower R (IntegralClosure R A) A := sorry

instance [FaithfulSMul R A] : FaithfulSMul R (IntegralClosure R A) := sorry

instance mulSemiringActionIntegralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    MulSemiringAction G (IntegralClosure R K) where
  smul σ x := ⟨σ • x.1, x.2.map (MulSemiringAction.toAlgHom R K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance smulCommClass_integralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    SMulCommClass G R (IntegralClosure R K) := sorry

instance isInvariant_integralClosure
    {G K L : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G K L] [Algebra.IsInvariant K L G] (R : ValuationSubring K) :
    Algebra.IsInvariant R (IntegralClosure R L) G := sorry

instance continuousSMulDiscrete_integralClosure
    {G R L : Type*} [CommRing R] [Field L] [Algebra R L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G R L] [TopologicalSpace G] [ContinuousSMulDiscrete G L] :
    ContinuousSMulDiscrete G (IntegralClosure R L) := sorry

instance {R S : Type*} [CommRing R] [CommRing S] {I : Ideal S} [Algebra R S]
    [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S] [NeZero I] : NeZero (I.under R) := sorry

end
