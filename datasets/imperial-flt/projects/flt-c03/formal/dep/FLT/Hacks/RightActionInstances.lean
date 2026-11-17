module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

set_option linter.dupNamespace false

namespace TensorProduct.RightActions

noncomputable section semiring

variable (R S A B M : Type*) [CommSemiring R] [CommSemiring S] [AddCommMonoid M]
    [Algebra R S] [Module R M]
    [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B]

/-- Right action of a commutative semiring `S` on `M ⊗ S`. An instance only when
the `TensorProduct.RightActions` scope is open. -/
scoped instance : SMul S (M ⊗[R] S) where
  smul s e := TensorProduct.comm _ _ _ (s • (TensorProduct.comm _ _ _ e))

/-- The `S`-module structure on `M ⊗ S`, when `S` is a commutative semiring.
An instance only when the `TensorProduct.RightActions` scope is open. -/
scoped instance : Module S (M ⊗[R] S) where
  one_smul x := sorry
  mul_smul a b x := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The `S`-algebra structure on `B ⊗ S`, when `S` is a commutative semiring
and `B` is a semiring. An instance only when the `TensorProduct.RightActions` scope is open. -/
scoped instance : Algebra S (B ⊗[R] S) where
  algebraMap := Algebra.TensorProduct.includeRight.toRingHom
  commutes' s bs := sorry
  smul_def' s bs := sorry

/-- The A-algebra isomorphism A ⊗ B = B ⊗ A, available in the `TensorProduct.RightActions` scope. -/
def Algebra.TensorProduct.comm : A ⊗[R] B ≃ₐ[A] B ⊗[R] A where
  __ := _root_.Algebra.TensorProduct.comm R A B
  commutes' _ := rfl

/-- The A-module isomorphism A ⊗ M = M ⊗ A, available in the `TensorProduct.RightActions` scope. -/
def Module.TensorProduct.comm : A ⊗[R] M ≃ₗ[A] M ⊗[R] A where
  __ := (_root_.TensorProduct.comm R A M).toAddEquiv
  map_smul' a am := sorry

scoped instance [Module.Finite R M] : Module.Finite A (M ⊗[R] A) :=
  Module.Finite.equiv (Module.TensorProduct.comm R A M)

scoped instance [Module.Free R M] : Module.Free A (M ⊗[R] A) :=
  Module.Free.of_equiv (Module.TensorProduct.comm R A M)

scoped instance : IsScalarTower R A (M ⊗[R] A) where
  smul_assoc r a ma := sorry

/-- We equip `M ⊗[R] A` with the `A`-module topology if `M` is finite over `R`. -/
@[nolint unusedArguments] -- we don't need that M is a finite R-module to make this
-- definition, but I don't think I want the instance to be there in general.
scoped instance [TopologicalSpace A] [Module.Finite R M] :
    TopologicalSpace (M ⊗[R] A) :=
  moduleTopology A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [Module.Finite R M] :
  IsModuleTopology A (M ⊗[R] A) := ⟨rfl⟩

/-- Base extension of an `R`-linear map `V → W` to an `A`-linear
map `V ⊗ A → W ⊗ A`. Available in the `TensorProduct.RightActions` scope. -/
noncomputable abbrev LinearMap.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V →ₗ[R] W) : V ⊗[R] A →ₗ[A] W ⊗[R] A :=
  (Module.TensorProduct.comm R A W) ∘ₗ
    (_root_.LinearMap.baseChange A φ) ∘ₗ
    (Module.TensorProduct.comm R A V).symm

/-- Base extension of an `R`-linear iso `V → W` to an `A`-linear
iso `V ⊗ A → W ⊗ A`. Available in the `TensorProduct.RightActions` scope. -/
noncomputable abbrev LinearEquiv.baseChange (R : Type*) [CommRing R]
    (V W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : V ≃ₗ[R] W) : V ⊗[R] A ≃ₗ[A] W ⊗[R] A where
  __ := LinearMap.baseChange _ _ _ _ φ.toLinearMap
  invFun := LinearMap.baseChange _ _ _ _ φ.symm.toLinearMap
  left_inv := sorry
  right_inv := sorry

/-- Base extension of an `R`-algebra map `B → C` to an `A`-linear
map `B ⊗ A → C ⊗ A`. Available in the `TensorProduct.RightActions` scope. -/
noncomputable def AlgebraMap.baseChange (R : Type*) [CommRing R]
    (B C : Type*) [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (A : Type*) [CommRing A] [Algebra R A]
    (φ : B →ₐ[R] C) : B ⊗[R] A →ₐ[A] C ⊗[R] A where
  __ := Algebra.TensorProduct.map φ (.id R A)
  commutes' a := sorry

end semiring

noncomputable section ring

variable (R A B M : Type*) [CommRing R]
    [CommRing A] [Algebra R A]
    [Ring B] [Algebra R B]
    [AddCommGroup M] [Module R M]

scoped instance [TopologicalSpace A] [Module.Finite R M] :
    IsTopologicalAddGroup (M ⊗[R] A) := IsModuleTopology.topologicalAddGroup A (M ⊗[R] A)

scoped instance [TopologicalSpace A] [IsTopologicalRing A] [Module.Finite R B] :
    IsTopologicalRing (B ⊗[R] A) :=
  IsModuleTopology.Module.topologicalRing A _

scoped instance [TopologicalSpace A] [IsTopologicalRing A] [Module.Finite R B] :
    IsTopologicalRing (B ⊗[R] A) :=
  IsModuleTopology.Module.topologicalRing A _

scoped instance [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [Module.Finite R M] :
    LocallyCompactSpace (M ⊗[R] A) := IsModuleTopology.locallyCompactSpaceOfFinite A

end ring

end TensorProduct.RightActions
