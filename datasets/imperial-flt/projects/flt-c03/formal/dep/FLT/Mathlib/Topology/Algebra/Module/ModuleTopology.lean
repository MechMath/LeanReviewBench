module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Mathlib.Algebra.Algebra.Tower

@[expose] public section

namespace IsModuleTopology

open ModuleTopology

section semiring_bilinear

variable {R : Type*} [τR : TopologicalSpace R] [CommSemiring R]

variable {A : Type*} [AddCommMonoid A] [Module R A] [aA : TopologicalSpace A] [IsModuleTopology R A]

variable {B : Type*} [AddCommMonoid B] [Module R B] [aB : TopologicalSpace B] [IsModuleTopology R B]

variable {C : Type*} [AddCommMonoid C] [Module R C] [aC : TopologicalSpace C] [IsModuleTopology R C]

end semiring_bilinear

section semiring_algebra

open scoped TensorProduct

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]

variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

end semiring_algebra

section ring_algebra

variable (R) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable (D : Type*) [Ring D] [Algebra R D] [Module.Finite R D]

variable [TopologicalSpace D] [IsModuleTopology R D]

open scoped TensorProduct

include R in
lemma Module.topologicalRing : IsTopologicalRing D := sorry

end ring_algebra

section algebra

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra R S]

end algebra

section trans

variable (R : Type*) [CommRing R] [TopologicalSpace R]

variable (S : Type*) [CommRing S] [TopologicalSpace S] [Algebra R S]

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- If S is an R-algebra, finite as an R-module, with the module topology,
  then the S-module topology on an S-module coincides with the R-module topology.
-/
lemma _root_.moduleTopology.trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S] :
    moduleTopology R M = moduleTopology S M := sorry

lemma trans [IsTopologicalRing R] [Module.Finite R S] [IsModuleTopology R S]
    [τ : TopologicalSpace M] :
    IsModuleTopology R M ↔ IsModuleTopology S M := sorry

end trans

section opensubring

variable (R S : Type*)
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S]

end opensubring

section quotientMap

variable {R M : Type*} [Ring R] [TopologicalSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M]
  (N : Type*) [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsModuleTopology R N]

variable [ContinuousAdd M] [ContinuousSMul R M]

end quotientMap

/--
An algebra isomorphism `e : A →ₐ[S] B` which also has scalars `S'`, with `A` and `B` both having the
`S'`-module topology, is automatically continuous.
-/
def continuousAlgEquivOfIsBiscalar {A B : Type*} (S' : Type*) {S : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S]
    [Algebra S A] [Algebra S B] [Algebra S' A] [Algebra S' B] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace S'] [IsModuleTopology S' A]
    [IsModuleTopology S' B] (e : A ≃ₐ[S] B) [IsBiscalar S S' e.toAlgHom] :
    A ≃A[S] B where
  toAlgEquiv := e
  continuous_toFun := sorry
  continuous_invFun := sorry

section Prod

variable {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M] [AddCommGroup N]
  [Module A M] [Module B N]

/-- `A` can be viewed as an `(A × B)`-algebra by having `B` act trivially. -/
local instance _root_.Prod.leftAlgebra : Algebra (A × B) A :=
  RingHom.toAlgebra <| RingHom.fst A B

/-- `B` can be viewed as an `(A × B)`-algebra by having `A` act trivially. -/
local instance _root_.Prod.rightAlgebra : Algebra (A × B) B :=
  RingHom.toAlgebra <| RingHom.snd A B

/-- An `A` module can be viewed as an `(A × B)`-module by having `B` act trivially. -/
local instance _root_.Prod.leftModule : Module (A × B) M :=
  Module.compHom M (RingHom.fst A B)

/-- A `B` module can be viewed as an `(A × B)`-module by having `A` act trivially. -/
local instance _root_.Prod.rightModule : Module (A × B) N :=
  Module.compHom N (RingHom.snd A B)

set_option backward.isDefEq.respectTransparency false in
/-- `A` is a finite `(A × B)`-module. -/
instance _root_.Prod.instFinite_leftAlgebra : Module.Finite (A × B) A := sorry

set_option backward.isDefEq.respectTransparency false in
/-- `B` is a finite `(A × B)`-module. -/
instance _root_.Prod.instFinite_rightAlgebra : Module.Finite (A × B) B := sorry

variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace M]
  [TopologicalSpace N] [IsModuleTopology A M] [IsModuleTopology B N] [IsTopologicalRing A]
  [IsTopologicalRing B]

/-- `A` has the `(A × B)`-module topology. -/
instance Prod.instLeftAlgebra : IsModuleTopology (A × B) A := sorry

/-- `B` has the `(A × B)`-module topology. -/
instance Prod.instRightAlgebra : IsModuleTopology (A × B) B := sorry

/-- If `M` has the `A`-module topology, then it also has the `(A × B)`-module topology. -/
instance Prod.instLeftModule : IsModuleTopology (A × B) M := sorry

/-- If `N` has the `B`-module topology, then it also has the `(A × B)`-module topology. -/
instance Prod.instRightModule : IsModuleTopology (A × B) N := sorry

/-- If `M` has the `A`-module topology and `N` has the `B`-module topology
  then `M × N` has the `(A × B)`-module topology. -/
instance instProd' : IsModuleTopology (A × B) (M × N) := sorry

end Prod

section locally_compact

variable (R : Type*) [τR : TopologicalSpace R] [Ring R] [IsTopologicalRing R]

variable {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsModuleTopology R M]

theorem locallyCompactSpaceOfFinite [LocallyCompactSpace R] [Module.Finite R M] :
    LocallyCompactSpace M := sorry

end locally_compact

section ModuleFinite

end ModuleFinite

section SecondCountableTopology

end SecondCountableTopology

end IsModuleTopology
