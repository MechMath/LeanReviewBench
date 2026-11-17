module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
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
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Hacks.RightActionInstances
public import dep.FLT.Mathlib.Algebra.Algebra.Bilinear
public import dep.FLT.Mathlib.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Algebra.Algebra.Pi
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.LinearAlgebra.Pi
public import dep.FLT.Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import dep.FLT.Mathlib.NumberTheory.NumberField.InfinitePlace.Completion
public import dep.FLT.Mathlib.Topology.Algebra.Algebra.Hom
public import dep.FLT.Mathlib.Topology.Algebra.ContinuousAlgEquiv
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.UniformRing
public import dep.FLT.Mathlib.Topology.Constructions
public import dep.FLT.NumberField.Completion.Infinite
public import dep.FLT.NumberField.InfinitePlace.Extension

@[expose] public section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

open NumberField InfinitePlace SemialgHom

open scoped TensorProduct

namespace NumberField.InfiniteAdeleRing

/-- `K∞` is notation for `InfiniteAdeleRing K`. -/
scoped notation:10000 K "∞" => InfiniteAdeleRing K

/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def baseChange :
    K∞ →SA[algebraMap K L] L∞ where
  __ := Pi.semialgHomPi _ _ fun _ => Completion.comapHom rfl
  continuous_toFun := .piSemialgHomPi Completion Completion _ fun _ => Completion.comapHom_cont rfl

open scoped TensorProduct.RightActions

noncomputable instance [Algebra K∞ L∞] :
    Algebra ((v : InfinitePlace K) → v.Completion) ((w : InfinitePlace L) → w.Completion) :=
  inferInstanceAs (Algebra K∞ L∞)

open scoped NumberField.LiesOver

variable [NumberField K] [NumberField L]

attribute [local instance 9999] Algebra.toModule

instance instIsModuleTopology_fLT [Algebra K∞ L∞]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] :
    IsModuleTopology K∞ L∞ := sorry

open scoped Classical in
/-- The $L$-algebra isomorphism $L\otimes_K K_{\infty} \cong L_{\infty}$. -/
noncomputable def baseChangeAlgEquiv :
    L ⊗[K] K∞ ≃ₐ[L] L∞ :=
  -- L ⊗ K_∞ ≃[K_∞] ∏ v, L ⊗ K_v
  Algebra.TensorProduct.piRight K L L Completion |>.trans
    -- lift the established equivalence L ⊗ K_v ≃[v.Completion] ∏ w ∣ v, L_w on fibers of comap
    (AlgEquiv.piCongrFiberwise
      (fun v : InfinitePlace K => (Completion.baseChangeEquiv L v).toAlgEquiv.symm)).symm

open TensorProduct.AlgebraTensorModule in
instance : Module.Free K∞ (L ⊗[K] K∞) := sorry

set_option backward.isDefEq.respectTransparency false in
/-- Take two arbitrary `Algebra K L∞` and `Algebra K∞ L∞` instances. Assume that
`Algebra K L∞` factors through (existing) `Algebra K L` and `Algebra L L∞`.
Assume further that `Algebra K∞ L∞` is determined by the fibers of restriction of infinite places
of `L` to `K` via (x • y) v = x (v.comap (algebraMap K L)) • y v. Then the `L` algebra base change
map is also linear in `K∞`. -/
instance [Algebra K∞ L∞]
    [Pi.FiberwiseSMul (fun a => a.comap (algebraMap K L)) Completion Completion] :
    IsBiscalar L K∞ (baseChangeAlgEquiv K L).toAlgHom := sorry

end NumberField.InfiniteAdeleRing
