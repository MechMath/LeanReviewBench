module

public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
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
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Path
public import dep.FLT.DedekindDomain.AdicValuation
public import dep.FLT.DedekindDomain.IntegralClosure
public import dep.FLT.Deformations.ContinuousRepresentation.IsTopologicalModule
public import dep.FLT.Mathlib.Algebra.Algebra.Tower
public import dep.FLT.Mathlib.Algebra.Module.Submodule.Basic
public import dep.FLT.Mathlib.LinearAlgebra.Countable
public import dep.FLT.Mathlib.Order.Filter.Cofinite
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import dep.FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import dep.FLT.Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Equiv
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.Module
public import dep.FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import dep.FLT.NumberField.Completion.Finite
public import dep.FLT.NumberField.HeightOneSpectrum

@[expose] public section

open scoped TensorProduct

universe u

open NumberField IsDedekindDomain RestrictedProduct Adele

section Instances

variable (K : Type*) [Field K] [NumberField K]

open HeightOneSpectrum

/-- `𝔸ᶠ[K]` is notation for `FiniteAdeleRing (𝓞 K) K`. -/
scoped[Adele] notation:max "𝔸ᶠ[" K "]" => 𝔸ᶠ[𝓞 K, K]

namespace IsDedekindDomain.FiniteAdeleRing

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
instance : LocallyCompactSpace 𝔸ᶠ[K] := sorry

instance : CompactSpace (integralAdeles (𝓞 K) K) := sorry

instance : T2Space (FiniteAdeleRing (𝓞 K) K) := sorry

instance : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := sorry

instance {R : Type*} [CommRing R] [Algebra.IsIntegral ℤ R] [FaithfulSMul ℤ R] :
    Nonempty (HeightOneSpectrum R) := sorry

instance : Nontrivial (FiniteAdeleRing (𝓞 K) K) := sorry

end IsDedekindDomain.FiniteAdeleRing

end Instances
