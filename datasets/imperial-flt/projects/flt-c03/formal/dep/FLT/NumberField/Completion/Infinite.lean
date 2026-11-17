module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.NumberTheory.NumberField.Completion.Ramification
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
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
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Hacks.RightActionInstances
public import dep.FLT.Mathlib.Algebra.Algebra.Bilinear
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Pi
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.UniformRing
public import dep.FLT.Mathlib.Topology.Constructions
public import dep.FLT.NumberField.InfinitePlace.Extension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 800000

open scoped TensorProduct

noncomputable section

namespace NumberField.InfinitePlace.Completion

open AbsoluteValue.Completion UniformSpace.Completion SemialgHom

open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}
  {wv : v.Extension L}

instance : wv.1.1.LiesOver v.1 := sorry

instance {v : InfinitePlace K} : NontriviallyNormedField v.Completion where
  non_trivial :=
    let ⟨x, hx⟩ := v.isNontrivial.exists_abv_gt_one
    ⟨x, sorry⟩

noncomputable instance : FiniteDimensional v.Completion wv.1.Completion := sorry

/-- The map from `v.Completion` to `w.Completion` whenever the infinite place `w` of `L` lies
above the infinite place `v` of `K`. -/
abbrev comapHom (h : w.comap (algebraMap K L) = v) :
    v.Completion →ₛₐ[algebraMap K L] w.Completion :=
  have : w.1.LiesOver v.1 := ⟨sorry⟩
  RingHom.toSemialgHom (NumberField.LiesOver.completionMap (v := v) (w := w)) fun r x ↦ sorry

theorem comapHom_cont (h : w.comap (algebraMap K L) = v) : Continuous (comapHom h) := sorry

variable (L v)

/-- The map from `v.Completion` to the product of all completions of `L` lying above `v`. -/
def piExtension :
    v.Completion →ₛₐ[algebraMap K L] (wv : v.Extension L) → wv.1.Completion :=
  Pi.semialgHom _ _ fun wv ↦ comapHom wv.2

open scoped TensorProduct.RightActions

instance : TopologicalSpace (L ⊗[K] v.Completion) := moduleTopology v.Completion _

instance : IsModuleTopology v.Completion (L ⊗[K] v.Completion) := sorry

/-- The `L`-algebra map `L ⊗[K] v.Completion` to the product of all completions of `L` lying
above `v`, induced by `piExtension`. -/
abbrev baseChange :
    L ⊗[K] v.Completion →ₐ[L] (wv : v.Extension L) → wv.1.Completion :=
  baseChangeOfAlgebraMap (piExtension L v)

variable [NumberField L]

variable {L v}

instance : Module.Free v.Completion wv.1.Completion := sorry

variable (L v)

include K in
set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
theorem baseChange_surjective : Function.Surjective (baseChange L v) := sorry

variable [NumberField K]

set_option backward.isDefEq.respectTransparency false in
theorem baseChange_injective :
    Function.Injective (baseChange L v) := sorry

instance : IsModuleTopology v.Completion wv.1.Completion := sorry

set_option backward.isDefEq.respectTransparency false in
/-- The `L`-algebra homeomorphism between `L ⊗[K] v.Completion` and the product of all completions
of `L` lying above `v`. -/
def baseChangeEquiv :
    L ⊗[K] v.Completion ≃A[L] (wv : v.Extension L) → wv.1.Completion :=
  let e := AlgEquiv.ofBijective _ ⟨baseChange_injective L v, baseChange_surjective L v⟩
  have : IsBiscalar L v.Completion e.toAlgHom :=
    inferInstanceAs (IsBiscalar L v.Completion (baseChange L v))
  IsModuleTopology.continuousAlgEquivOfIsBiscalar v.Completion e

set_option backward.isDefEq.respectTransparency false in
instance : IsBiscalar L v.Completion (baseChangeEquiv L v).toAlgHom := sorry

end NumberField.InfinitePlace.Completion
