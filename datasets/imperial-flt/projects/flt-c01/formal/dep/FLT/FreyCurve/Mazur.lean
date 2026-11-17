module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.Rat.Encodable
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Countable
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.ModCases
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
public import dep.FLT.EllipticCurve.Torsion
public import dep.FLT.FreyCurve.Basic
public import dep.FLT.FreyCurve.FreyPackage
public import dep.FLT.GaloisRepresentation.HardlyRamified.Defs
public import dep.FLT.Mathlib.LinearAlgebra.Countable
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.NumberField.Completion.Finite

@[expose] public section

open WeierstrassCurve

/--
The p-torsion in the Frey curve associated to a counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := sorry
