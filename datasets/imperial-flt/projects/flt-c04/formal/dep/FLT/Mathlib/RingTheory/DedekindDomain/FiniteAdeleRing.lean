module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Algebra.Module.Submodule.Basic
public import dep.FLT.Mathlib.Order.Filter.Cofinite
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

namespace IsDedekindDomain.FiniteAdeleRing

@[inherit_doc]
scoped[Adele] notation:max "𝔸ᶠ[" A ", " K "]" => IsDedekindDomain.FiniteAdeleRing A K

open scoped Adele

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The structure map `Π 𝒪ᵥ → 𝔸ᶠ` as a ring hom. -/
noncomputable abbrev structureMap :
    (Π v : HeightOneSpectrum R, v.adicCompletionIntegers K) →+* (FiniteAdeleRing R K) :=
  RestrictedProduct.structureMapRingHom _ _ _

/-- The integral adele subring inside the finite adele ring. -/
noncomputable abbrev integralAdeles : Subring ((FiniteAdeleRing R K)) :=
  (structureMap R K).range

variable {R K}

/-- Constructor for `(FiniteAdeleRing R K)`. An `abbrev`. -/
abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : (FiniteAdeleRing R K) :=
  ⟨f, h⟩

variable (R K)

end IsDedekindDomain.FiniteAdeleRing
