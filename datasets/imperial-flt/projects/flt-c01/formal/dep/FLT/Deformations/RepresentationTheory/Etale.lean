module

public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

variable (X : Type u) [MulAction (L ≃ₐ[K] L) X]

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [MulAction G Y]
    [SMul H Y] [SMulCommClass G H Y] :
    SMul H (X →[G] Y) where
  smul h f := ⟨h • f, sorry⟩

instance {G H X Y : Type*} [Monoid G] [MulAction G X] [Semiring Y] [MulSemiringAction G Y]
    [CommSemiring H] [Algebra H Y] [SMulCommClass G H Y] :
    Algebra H (X →[G] Y) where
  algebraMap :=
  { toFun h := ⟨fun _ ↦ algebraMap H Y h, sorry⟩
    map_one' := sorry
    map_mul' _ _ := sorry
    map_zero' := sorry
    map_add' _ _ := sorry }
  commutes' _ _ := MulActionHom.ext fun _ ↦ Algebra.commutes _ _
  smul_def' _ _ := MulActionHom.ext fun _ ↦ Algebra.smul_def _ _

open TensorProduct

instance {R S T G : Type*} [CommSemiring R] [Semiring S] [Semiring T] [Algebra R S] [Algebra R T]
    [Monoid G] [MulSemiringAction G T] [SMulCommClass G R T] : MulAction G (S →ₐ[R] T) where
  smul g := (MulSemiringAction.toAlgHom _ _ g).comp
  one_smul f := sorry
  mul_smul g g' f := sorry

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] : Algebra.FormallyEtale K (X →[L ≃ₐ[K] L] L) := sorry

open MulAction IntermediateField in
instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Module.Finite K (X →[L ≃ₐ[K] L] L) := sorry

instance [IsGalois K L] [Finite X] [ContinuousSMulDiscrete (L ≃ₐ[K] L) X] :
    Algebra.Etale K (X →[L ≃ₐ[K] L] L) := sorry

/-- Evaluating a `AlgHom` is an `MulActionHom`, bundled as a `AlgHom`. -/
def AlgHom.evalMulActionHom (G R A Y : Type*) [CommSemiring R] [Semiring Y] [Algebra R Y]
    [Monoid G] [Semiring A] [Algebra R A] [MulSemiringAction G Y] [SMulCommClass G R Y] :
    A →ₐ[R] ((A →ₐ[R] Y) →[G] Y) where
  toFun a := ⟨fun f ↦ f a, fun g f ↦ rfl⟩
  map_one' := sorry
  map_mul' a b := sorry
  map_zero' := sorry
  map_add' a b := sorry
  commutes' r := sorry

variable (A : Type u) [CommRing A] [Algebra K A]

instance [Module.Finite K A] : ContinuousSMulDiscrete (L ≃ₐ[K] L) (A →ₐ[K] L) := sorry

attribute [local instance] Ideal.Quotient.field RingHom.ker_isPrime in
lemma InfiniteGalois.evalMulActionHom_bijective [Algebra.Etale K A] [IsGalois K L]
    (H : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → Nonempty (A ⧸ 𝔪 →ₐ[K] L)) :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := sorry

attribute [local instance] Ideal.Quotient.field Algebra.FormallyUnramified.isSeparable in
lemma InfiniteGalois.evalMulActionHom_bijective_of_isSepClosed
    [Algebra.Etale K A] [IsGalois K L] [IsSepClosed L] :
    Function.Bijective (AlgHom.evalMulActionHom (L ≃ₐ[K] L) K A L) := sorry

attribute [local instance 1000000] SemilinearEquivClass.instSemilinearMapClass in
noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] : Monoid (A →ₐ[K] L) where
  mul f g := .comp (Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)) (Bialgebra.comulAlgHom K A)
  mul_assoc a b c := sorry
  one := (Algebra.ofId K L).comp (Bialgebra.counitAlgHom K A)
  one_mul f := sorry
  mul_one f := sorry

noncomputable
instance {A : Type*} [CommRing A] [Bialgebra K A] :
    MulDistribMulAction (L ≃ₐ[K] L) (A →ₐ[K] L) where
  smul_mul r f g := sorry
  smul_one r := sorry
