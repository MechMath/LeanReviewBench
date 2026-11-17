module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
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
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Path
public import dep.FLT.DedekindDomain.AdicValuation
public import dep.FLT.Deformations.Lemmas
public import dep.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
public import dep.FLT.Deformations.RepresentationTheory.Etale
public import dep.FLT.Deformations.RepresentationTheory.Frobenius
public import dep.FLT.Deformations.RepresentationTheory.GaloisRep
public import dep.FLT.Deformations.RepresentationTheory.IntegralClosure
public import dep.FLT.Mathlib.LinearAlgebra.Countable
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.NumberField.Completion.Finite

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u := Submodule.torsionBy ℤ (E⁄k).Point n

noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| sorry

noncomputable instance (n : ℕ) : Module.Finite (ZMod n) (E.nTorsion n) := sorry

/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul := sorry -- these should all be easy
      mul_smul := sorry
      smul_zero := sorry
      smul_add := sorry

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
def WeierstrassCurve.galoisRep {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
  GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := sorry
