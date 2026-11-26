module

public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Invariant.Profinite
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.MulAction
public import dep.FLT.Deformations.RepresentationTheory.ContinuousSMulDiscrete

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace IsArithFrobAt

open scoped Pointwise

variable {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

variable {Q : Ideal S} {σ σ' : G}

variable [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]

variable [IsTopologicalGroup G] [Algebra.IsInvariant R S G]

variable [ContinuousSMulDiscrete G S]

include S in
variable (R G Q) in
attribute [local instance] Ideal.Quotient.field in
/-- Let `G` be a finite group acting on `S`, and `R` be the fixed subring.
If `Q` is a prime of `S` with finite residue field,
then there exists a Frobenius element `σ : G` at `Q`. -/
lemma exists_of_isInvariant_of_profinite
    [Q.IsMaximal] [Finite (R ⧸ Q.under R)] : ∃ σ : G, IsArithFrobAt R σ Q := sorry

variable (S G) in
lemma exists_primesOver_isConj_of_profinite (P : Ideal R) [Finite (R ⧸ P)] [P.IsPrime] :
    ∃ σ : Ideal.primesOver P S → G, (∀ Q, IsArithFrobAt R (σ Q) Q.1) ∧
      (∀ Q₁ Q₂, IsConj (σ Q₁) (σ Q₂)) := sorry

variable (R G Q)

/-- Let `G` be a finite group acting on `S`, `R` be the fixed subring, and `Q` be a prime of `S`
with finite residue field. This is an arbitrary choice of a Frobenius over `Q`. It is chosen so that
the Frobenius elements of `Q₁` and `Q₂` are conjugate if they lie over the same prime. -/
noncomputable
def _root_.arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] : G :=
  (exists_primesOver_isConj_of_profinite S G (Q.under R)).choose ⟨Q, ‹_›, ⟨rfl⟩⟩

include S in
protected lemma arithFrobAt' [Q.IsPrime] [Finite (R ⧸ Q.under R)] :
    IsArithFrobAt R (arithFrobAt' R G Q) Q := sorry

end IsArithFrobAt
