module

public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
public import Mathlib.Algebra.Group.Int.TypeTags
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
public import Mathlib.Topology.Path
public import dep.FLT.DedekindDomain.AdicValuation
public import dep.FLT.Deformations.Lemmas
public import dep.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete
public import dep.FLT.Deformations.RepresentationTheory.Etale
public import dep.FLT.Deformations.RepresentationTheory.Frobenius
public import dep.FLT.Deformations.RepresentationTheory.IntegralClosure
public import dep.FLT.Mathlib.LinearAlgebra.Countable
public import dep.FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import dep.FLT.NumberField.Completion.Finite

@[expose] public section

set_option backward.isDefEq.respectTransparency false

set_option backward.defeqAttrib.useBackward true

open NumberField

universe uK

variable {K : Type uK} {L : Type*} [Field K] [Field L]

variable {A : Type*} [CommRing A] [TopologicalSpace A]

variable {B : Type*} [CommRing B] [TopologicalSpace B]

variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

variable {n : Type*} [Fintype n] [DecidableEq n]

variable [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

local notation3 "𝔪" => IsLocalRing.maximalIdeal

local notation3 "κ" => IsLocalRing.ResidueField

local notation "Ω" K => IsDedekindDomain.HeightOneSpectrum (𝓞 K)

local notation "Kᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletion K v

local notation "𝒪ᵥ" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v

local notation "Frobᵥ" => Field.AbsoluteGaloisGroup.adicArithFrob v

variable (K A M) in
/-- `GaloisRep K A M` are the `A`-linear galois reps of a field `K` on the `A`-module `M`. -/
def GaloisRep :=
  letI := moduleTopology A (Module.End A M)
  Γ K →ₜ* Module.End A M

noncomputable instance : FunLike (GaloisRep K A M) (Γ K) (Module.End A M) :=
  letI := moduleTopology A (Module.End A M)
  ContinuousMonoidHom.instFunLike

instance : MonoidHomClass (GaloisRep K A M) (Γ K) (Module.End A M) := sorry

omit [NumberField K] in
@[ext]
lemma GaloisRep.ext {ρ ρ' : GaloisRep K A M} (H : ∀ σ, ρ σ = ρ' σ) : ρ = ρ' := sorry

/-- The kernel of a galois rep. -/
noncomputable nonrec
abbrev GaloisRep.ker (ρ : GaloisRep K A M) : Subgroup (Γ K) :=
  letI := moduleTopology A (Module.End A M)
  ρ.ker

/-- A field extension induces a map between galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
def GaloisRep.map (ρ : GaloisRep K A M) (f : K →+* L) : GaloisRep L A M :=
  letI := moduleTopology A (Module.End A M)
  ρ.comp (Field.absoluteGaloisGroup.flt_map f)

variable (K A n) in
/-- A framed galois rep is a galois rep with a distinguished basis.
We implement it by via a galois rep on `Aⁿ`. -/
abbrev FramedGaloisRep := GaloisRep K A (n → A)

/-- A field extension induces a map between framed galois reps.
Note that this relies on an arbitrarily chosen embedding of the algebraic closures. -/
noncomputable
abbrev FramedGaloisRep.map (ρ : FramedGaloisRep K A n) (f : K →+* L) : FramedGaloisRep L A n :=
  GaloisRep.map ρ f

/-- We can conjugate a galois rep by a linear isomorphism on the space. -/
noncomputable
def GaloisRep.conj (ρ : GaloisRep K A M) (e : M ≃ₗ[A] N) : GaloisRep K A N :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology A (Module.End A N)
  let e' : Module.End A M ≃A[A] Module.End A N :=
    .ofIsModuleTopology <| LinearEquiv.conjAlgEquiv A e
  e'.toContinuousAlgHom.toContinuousMonoidHom.comp ρ

variable [IsTopologicalRing A]

/-- `A`-linear framed galois reps are equivalent to continuous homomorphisms into `GLₙ(A)`. -/
noncomputable
def FramedGaloisRep.GL : FramedGaloisRep K A n ≃ (Γ K →ₜ* GL n A) :=
  letI := moduleTopology A (Module.End A (n → A))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite A (Module.End A (n → A))⟩
  letI e : Module.End A (n → A) ≃A[A] Matrix n n A :=
    .ofIsModuleTopology LinearMap.toMatrixAlgEquiv'
  { toFun ρ := (e.toContinuousAlgHom.toContinuousMonoidHom.comp ρ).toHomUnits
    invFun ρ := e.symm.toContinuousAlgHom.toContinuousMonoidHom.comp ((Units.coeHomₜ _).comp ρ)
    left_inv _ := sorry
    right_inv _ := sorry }

/-- Make an `A`-linear framed galois reps from a continuous hom into `GLₙ(A)`. -/
noncomputable
abbrev FramedGaloisRep.ofGL := FramedGaloisRep.GL (K := K) (A := A) (n := n).symm

open TensorProduct in
variable (B) in
/-- Make a `A`-linear galois rep on `M` into a `B`-linear rep on `B ⊗ M`. -/
noncomputable
def GaloisRep.baseChange [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M]
    (ρ : GaloisRep K A M) : GaloisRep K B (B ⊗[A] M) :=
  letI := moduleTopology A (Module.End A M)
  letI := moduleTopology B (Module.End B (B ⊗[A] M))
  letI : ContinuousMul _ := ⟨IsModuleTopology.continuous_mul_of_finite B (Module.End B (B ⊗[A] M))⟩
  letI := IsModuleTopology.toContinuousAdd B (Module.End B (B ⊗[A] M))
  let F : Module.End A M →+* Module.End B (B ⊗[A] M) := Module.End.baseChangeHom A B M
  have : Continuous F := sorry
  .comp ⟨F, this⟩ ρ

/-- Make a framed `n` dimensional `A`-linear galois rep into a `B`-linear rep by composing with
`GLₙ(A) → GLₙ(B)`. -/
noncomputable
def FramedGaloisRep.baseChange [IsTopologicalRing B]
    (ρ : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) : FramedGaloisRep K B n :=
  .ofGL (.comp (Units.mapₜ ⟨f.mapMatrix.toMonoidHom, continuous_id.matrix_map hf⟩) ρ.GL)

/-- Given a (global) galois rep, this is the local galois rep at a finite prime `v`.
Note: this fixes an arbitrary embedding `Kᵃˡᵍ → Kᵥᵃˡᵍ`, or equivalently,
an arbitrary choice of valuation on `Kᵃˡᵍ` extending `v`. -/
noncomputable
abbrev GaloisRep.toLocal (ρ : GaloisRep K A M) (v : Ω K) : GaloisRep (v.adicCompletion K) A M :=
  ρ.map (algebraMap _ _)

universe v u

variable {R : Type u} [CommRing R]

/-- The class of galois reps unramified at `v`. -/
class GaloisRep.IsUnramifiedAt (ρ : GaloisRep K A M) (v : Ω K) : Prop where
  localInertiaGroup_le :
    letI := moduleTopology A (Module.End A M)
    localInertiaGroup v ≤ (ρ.toLocal v).ker

instance (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] (e : M ≃ₗ[A] N) :
    (ρ.conj e).IsUnramifiedAt v := sorry

instance [IsTopologicalRing B] [Algebra A B] [ContinuousSMul A B]
    [Module.Finite A M] [Module.Free A M] (ρ : GaloisRep K A M) (v : Ω K) [ρ.IsUnramifiedAt v] :
    (ρ.baseChange B).IsUnramifiedAt v := sorry

variable [Module.Free A M] [Module.Finite A M] [Module.Free A N] [Module.Finite A N]

noncomputable instance : CommRing Kᵥ := inferInstance

section Flat

set_option linter.unusedVariables false in
/-- The underlying space of a galois rep. This is a type class synonym that allows `G` to act
on it via `ρ`. -/
@[nolint unusedArguments]
def GaloisRep.Space (ρ : GaloisRep K A M) : Type _ := M

instance (ρ : GaloisRep K A M) : AddCommGroup ρ.Space := inferInstanceAs (AddCommGroup M)

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (ρ : GaloisRep K A M) : DistribMulAction (Γ K) ρ.Space where
  smul g v := ρ g v
  one_smul b := by unfold HSMul.hSMul; simp [instHSMul]
  mul_smul := by unfold HSMul.hSMul; simp [instHSMul]
  smul_zero := by unfold HSMul.hSMul; simp [instHSMul]
  smul_add := by unfold HSMul.hSMul; simp [instHSMul]

end Flat

/-- A Galois representation is a representation (note that we
are forgetting topological information here). -/
def GaloisRep.toRepresentation (ρ : GaloisRep K A M) : Representation A (Γ K) M :=
  letI := moduleTopology A (Module.End A M) -- ?!
  ρ.toMonoidHom

/-- Irreducibility of a Galois representation over a field. -/
def GaloisRep.IsIrreducible {k : Type*} [Field k] [TopologicalSpace k] [Module k M]
    (ρ : GaloisRep K k M) : Prop := ρ.toRepresentation.IsIrreducible
