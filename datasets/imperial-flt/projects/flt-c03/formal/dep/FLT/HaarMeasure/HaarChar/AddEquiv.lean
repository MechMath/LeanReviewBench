module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Group.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import dep.FLT.Mathlib.Order.Filter.Cofinite
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

open MeasureTheory.Measure

open scoped NNReal

namespace MeasureTheory

section basic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

variable [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

end basic

section prodCongr

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/-- The product of two multiplication-preserving homeomorphisms is
a multiplication-preserving homeomorphism. -/
@[to_additive
/-- The product of two addition-preserving homeomorphisms is
an addition-preserving homeomorphism. -/]
def _root_.ContinuousMulEquiv.prodCongr (φ : A ≃ₜ* B) (ψ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  __ := φ.toMulEquiv.prodCongr ψ
  continuous_toFun := Continuous.prodMap φ.continuous_toFun ψ.continuous_toFun
  continuous_invFun := sorry

end prodCongr

section prod

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H]

end prod

section piCongrRight

variable {ι : Type*} {G H : ι → Type*}
    [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
    [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]

/-- An arbitrary product of multiplication-preserving homeomorphisms
is a multiplication-preserving homeomorphism.
-/
@[to_additive
/-- An arbitrary product of addition-preserving homeomorphisms
is an addition-preserving homeomorphism. -/]
def _root_.ContinuousMulEquiv.piCongrRight (ψ : Π i, (G i) ≃ₜ* (H i)) :
    (∀ i, G i) ≃ₜ* (∀ i, H i) where
  __ := MulEquiv.piCongrRight (fun i ↦ ψ i)
  continuous_toFun := Continuous.piMap (fun i ↦ (ψ i).continuous_toFun)
  continuous_invFun := Continuous.piMap (fun i ↦ (ψ i).continuous_invFun)

end piCongrRight

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] [∀ i, SecondCountableTopology (H i)]

end pi

section restrictedproduct

open ENNReal

open RestrictedProduct

variable {ι : Type*}
    {G : ι → Type*}
    [Π i, Group (G i)] [Π i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    {C : (i : ι) → Subgroup (G i)}
    [hCopen : Fact (∀ (i : ι), IsOpen (C i : Set (G i)))]
    [hCcompact : ∀ i, CompactSpace (C i)]
    [∀ i, MeasurableSpace (G i)]
    [∀ i, BorelSpace (G i)]
    [∀ i, LocallyCompactSpace (G i)] -- follows from the hypotheses, but needed for *statement*
    [∀ i, SecondCountableTopology (G i)]

variable [∀ i, WeaklyLocallyCompactSpace (G i)]

end restrictedproduct

end MeasureTheory
