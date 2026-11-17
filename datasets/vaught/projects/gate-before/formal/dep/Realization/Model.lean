import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Countable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.InitialSeg
import Mathlib.Order.SupClosed
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import dep.Geometry.ConvexGeometry
import dep.Geometry.Plan
import dep.Label.Basic
import dep.Label.Cap
import dep.Label.OrdinalVisibility
import dep.Label.Transform
import dep.Label.Visibility
import dep.Realization.Basic
import dep.Realization.Families
import dep.Realization.Hull
import dep.Realization.Transport
import dep.Scheme.Bountiful
import dep.Scheme.Cell
import dep.Scheme.Row
import dep.Scheme.Transport
import dep.Stage.Basic
import dep.Stage.Countable
import dep.Stage.Legal
import dep.Stage.Scheme
import dep.Stage.TopFree

universe u v w x

namespace VaughtConjecture.Realization

open Finset Label StageType

variable {α β : Ordinal.{u}} {M : Type v} {N : Type w} {P : Type x} {n : ℕ}

section RealizesOver

variable (R : Realization.{u, v} α M)

/-- `R` **realizes a member of `U` over `t`**: some typed tuple on one more point, with `t` as its
initial segment, has its type in `U`. -/
def RealizesOver (t : Fin n ↪ M) (U : Set (StageType.{u} α (n + 1))) : Prop :=
  ∃ u : Fin (n + 1) ↪ M, Fin.castSuccEmb.trans u = t ∧ ∃ q ∈ U, R.eval u = some q

variable {R} {t : Fin n ↪ M} {U U' : Set (StageType.{u} α (n + 1))}

end RealizesOver

variable (R : Realization.{u, v} α M)

/-- A **model** at stage `α` [Kni26, Definition 3.2.1]: a realization on a nonempty carrier with
legal types that is exactly consistent and covering and that, over every occurrence, realizes a
member of each instance of the four families: of the uniformity and dominance families for every
`γ` in the range of the source, and of the generalized-saturation and bottom-pattern families
whenever the instance has a member among the cofaces of its type.

The source defines models only at limit stages `α`, where every instance is nonempty
[Kni26, Lemma 4.4.1]; here the definition is made at every stage, and at a stage that is zero or
a limit the guarded clauses are equivalent to those of the source: they imply them
(`IsModel.saturation_of_isLegal`, `IsModel.bottomPattern_of_isLawful`), and every nonempty
instance is one of the source (`StageType.nonempty_cofaces_inter_saturationFamily_iff`,
`StageType.nonempty_cofaces_inter_bottomPatternFamily_iff`). -/
structure IsModel : Prop where
  /-- The carrier is nonempty. -/
  nonempty : Nonempty M
  /-- Clause 1: every type is legal. -/
  isLegal ⦃n : ℕ⦄ (t : Fin n ↪ M) (p : StageType.{u} α n) : R.eval t = some p → p.IsLegal
  /-- Clause 2: exact consistency. -/
  isConsistent : R.IsConsistent
  /-- Clause 3: covering. -/
  isCovering : R.IsCovering
  /-- Clause 4(a)i, generalized saturation. -/
  saturation (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) :
    (x.type.cofaces ∩ saturationFamily S).Nonempty → R.RealizesOver x.tuple (saturationFamily S)
  /-- Clause 4(a)ii, the bottom pattern. -/
  bottomPattern (x : R.Occurrence) (S : Scheme.{u} (x.arity + 1)) (ρ : Fin S.card → Label.{u}) :
    (x.type.cofaces ∩ bottomPatternFamily S ρ).Nonempty →
      R.RealizesOver x.tuple (bottomPatternFamily S ρ)
  /-- Clause 4(b), uniformity, for `γ` that is zero or a limit and below the stage. -/
  uniformity (x : R.Occurrence) (γ : Ordinal.{u}) : Order.IsSuccPrelimit γ → γ < α →
    R.RealizesOver x.tuple (uniformityFamily γ)
  /-- Clause 4(c), high-arity dominance, for `γ` below the stage. -/
  dominance (x : R.Occurrence) (γ : Ordinal.{u}) : γ < α →
    R.RealizesOver x.tuple (dominanceFamily γ)

variable {R}

/-- **Transport of models** along a bijection of carriers. -/
theorem IsModel.map (hR : R.IsModel) (e : M ≃ N) : (R.map e).IsModel := sorry

section Reduce

variable (hR : R.IsModel)

include hR

variable {β : Ordinal.{u}} (hβ : Order.IsSuccPrelimit β) (hβα : β ≤ α)

include hβ hβα

end Reduce

section Iso

variable (R) in
/-- An **isomorphism** from `R` to a realization `S` on `N`: a bijection of carriers carrying `R`
to `S`. -/
def Iso (S : Realization.{u, w} α N) : Type (max v w) :=
  {e : M ≃ N // R.map e = S}

variable (R) in
/-- `R` and `S` are **isomorphic**. -/
def IsIso (S : Realization.{u, w} α N) : Prop :=
  Nonempty (R.Iso S)

variable {S : Realization.{u, w} α N} {T : Realization.{u, x} α P}

/-- The inverse of an isomorphism. -/
def Iso.symm (i : R.Iso S) : S.Iso R :=
  ⟨i.1.symm, sorry⟩

/-- The composite of two isomorphisms. -/
def Iso.trans (R : Realization.{u, v} α M) (i : R.Iso S) (j : S.Iso T) : R.Iso T :=
  ⟨i.1.trans j.1, sorry⟩

/-- Isomorphism is symmetric. -/
theorem IsIso.symm (h : R.IsIso S) : S.IsIso R := sorry

/-- Isomorphism is transitive. -/
theorem IsIso.trans (h : R.IsIso S) (h' : S.IsIso T) : R.IsIso T := sorry

end Iso

section Receiving

variable (R)

/-- The **finite-cut receiving property**: over every occurrence, for every coface `d` of its type
and every permitted cutoff `c`, some point extends the occurrence to one with a type on the scheme
of `d` with the observation of `d` at `c`. -/
def HasFiniteCutReceiving : Prop :=
  ∀ (x : R.Occurrence), ∀ d ∈ x.type.cofaces, ∀ c : Label.{u}, IsPermittedCutoff α c →
    R.RealizesOver x.tuple (receivingFamily d c)

variable {R}

end Receiving

end VaughtConjecture.Realization
