import Cslib.Foundations.Data.RelatesInSteps
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Chain
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Find
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.GroupTheory.Perm.List
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import dep.EconCSLib.SocialChoice.FairDivision.IndivisibleGoods

open scoped BigOperators

namespace EconCSLib

namespace Auction

/-- Bundles in combinatorial auctions reuse the fair-division bundle model. -/
abbrev Bundle (Item : Type*) := FairDivision.Bundle Item

/-- Bundle allocations reuse the fair-division allocation model. -/
abbrev BundleAllocation (Bidder Item : Type*) :=
  FairDivision.Allocation Bidder Item

/-- A direct combinatorial-auction report is a value for every bundle. -/
abbrev CombinatorialReport (Bidder Item : Type*) :=
  Bidder → Bundle Item → ℝ

/--
A direct-revelation combinatorial auction over indivisible goods.

The allocation is intentionally allowed to leave goods unallocated; feasibility
is a separate predicate because approximation algorithms often reason about
partial allocations.
-/
structure CombinatorialAuction (Bidder Item : Type*) where
  allocation : CombinatorialReport Bidder Item → BundleAllocation Bidder Item
  payment : CombinatorialReport Bidder Item → Bidder → ℝ

namespace CombinatorialAuction

variable {Bidder Item : Type*}

/-- Quasilinear utility for a combinatorial-auction bidder. -/
def utility (M : CombinatorialAuction Bidder Item)
    (values reports : CombinatorialReport Bidder Item) (i : Bidder) : ℝ :=
  values i (M.allocation reports i) - M.payment reports i

/-- Dominant-strategy truthfulness for direct bundle-value reports. -/
def TruthfulDominantStrategy [DecidableEq Bidder]
    (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item)
      (i : Bidder) (report : Bundle Item → ℝ),
    M.utility values (Function.update values i report) i ≤
      M.utility values values i

/-- Truthful utility is always nonnegative. -/
def IndividuallyRational (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (values : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.utility values values i

/-- The mechanism never pays money to bidders. -/
def NoPositiveTransfers (M : CombinatorialAuction Bidder Item) : Prop :=
  ∀ (reports : CombinatorialReport Bidder Item) (i : Bidder),
    0 ≤ M.payment reports i

/-- Total payments collected by the auction. -/
noncomputable def revenue [Fintype Bidder]
    (M : CombinatorialAuction Bidder Item)
    (reports : CombinatorialReport Bidder Item) : ℝ :=
  ∑ i : Bidder, M.payment reports i

end CombinatorialAuction

variable {Bidder Item : Type*}

/--
Single-minded bundle value: the bidder has value `value` exactly when the
allocated bundle contains the desired bundle.
-/
structure SingleMindedBid (Item : Type*) where
  desired : Bundle Item
  value : ℝ

namespace SingleMindedBid

variable [DecidableEq Item]

/-- Bundle valuation induced by a single-minded bid. -/
def valuation (b : SingleMindedBid Item) : Bundle Item → ℝ :=
  fun S => if b.desired ⊆ S then b.value else 0

end SingleMindedBid

/-- Accepted single-minded bidders receive their desired bundles; others receive nothing. -/
def singleMindedAllocation [DecidableEq Bidder]
    (bids : Bidder → SingleMindedBid Item) (accepted : Finset Bidder) :
    BundleAllocation Bidder Item :=
  fun i => if i ∈ accepted then (bids i).desired else ∅

/--
A direct mechanism for single-minded bid profiles, represented by the accepted
set and payments. Exactness is built in: accepted bidders receive exactly their
declared desired bundle, and denied bidders receive nothing.
-/
structure SingleMindedAcceptedMechanism (Bidder Item : Type*) where
  accepted : (Bidder → SingleMindedBid Item) → Finset Bidder
  payment : (Bidder → SingleMindedBid Item) → Bidder → ℝ

namespace SingleMindedAcceptedMechanism

variable {Bidder Item : Type*}

/-- The exact allocation induced by an accepted-set mechanism. -/
def allocation [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (reports : Bidder → SingleMindedBid Item) :
    BundleAllocation Bidder Item :=
  singleMindedAllocation reports (M.accepted reports)

/-- Quasilinear utility for a true single-minded type under reported bids. -/
noncomputable def utility [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (values reports : Bidder → SingleMindedBid Item) (i : Bidder) : ℝ :=
  (values i).valuation (M.allocation reports i) - M.payment reports i

/-- Nonempty, nonnegative single-minded bid profiles. -/
def NonnegativeNonemptyProfile [DecidableEq Item]
    (bids : Bidder → SingleMindedBid Item) : Prop :=
  ∀ i, (bids i).desired.Nonempty ∧ 0 ≤ (bids i).value

/--
Critical-value data. The threshold may depend on other reports and the
candidate desired bundle, but not on the bidder's declared value for that bundle.
-/
structure CriticalValueCertificate [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → ℝ
  threshold_nonneg : ∀ reports i s, 0 ≤ threshold reports i s
  threshold_own_value_independent :
    ∀ reports i s v,
      threshold (Function.update reports i { desired := s, value := v }) i s =
        threshold reports i s
  below_denied :
    ∀ reports i s v,
      v < threshold reports i s →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports i s v,
      threshold reports i s < v →
        i ∈ M.accepted
          (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports i,
      i ∈ M.accepted reports →
        M.payment reports i = threshold reports i (reports i).desired

namespace CriticalValueCertificate

variable [DecidableEq Bidder] {M : SingleMindedAcceptedMechanism Bidder Item}

end CriticalValueCertificate

/--
Critical-value data with an explicit infinite case. A finite threshold
`some p` behaves as the usual critical price; `none` means the bidder is never
accepted for that desired bundle at any declared value.
-/
structure CriticalValueWithInfinityCertificate [DecidableEq Bidder]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → Option ℝ
  threshold_nonneg : ∀ reports i s p, threshold reports i s = some p → 0 ≤ p
  threshold_own_value_independent :
    ∀ reports i s v,
      threshold (Function.update reports i { desired := s, value := v }) i s =
        threshold reports i s
  below_denied :
    ∀ reports i s v p,
      threshold reports i s = some p →
        v < p →
          i ∉ M.accepted
            (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports i s v p,
      threshold reports i s = some p →
        p < v →
          i ∈ M.accepted
            (Function.update reports i { desired := s, value := v })
  infinite_denied :
    ∀ reports i s v,
      threshold reports i s = none →
        i ∉ M.accepted
          (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports i,
      i ∈ M.accepted reports →
        ∃ p,
          threshold reports i (reports i).desired = some p ∧
            M.payment reports i = p

namespace CriticalValueWithInfinityCertificate

variable [DecidableEq Bidder] {M : SingleMindedAcceptedMechanism Bidder Item}

end CriticalValueWithInfinityCertificate

/--
Critical-value data for the nonnegative single-minded report domain. The
finite and infinite threshold clauses only need to govern admissible
nonnegative reports, matching the type-space restriction and avoiding
forcing negative-value behavior that is irrelevant for truthfulness on this
domain.
-/
structure NonnegativeCriticalValueWithInfinityCertificate
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) where
  threshold : (Bidder → SingleMindedBid Item) → Bidder → Bundle Item → Option ℝ
  threshold_nonneg :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s p, s.Nonempty → threshold reports i s = some p → 0 ≤ p
  threshold_own_value_independent :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v,
          s.Nonempty →
            0 ≤ v →
              threshold
                  (Function.update reports i { desired := s, value := v }) i s =
                threshold reports i s
  below_denied :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v p,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = some p →
                v < p →
                  i ∉ M.accepted
                    (Function.update reports i { desired := s, value := v })
  above_granted :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v p,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = some p →
                p < v →
                  i ∈ M.accepted
                    (Function.update reports i { desired := s, value := v })
  infinite_denied :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i s v,
          s.Nonempty →
            0 ≤ v →
              threshold reports i s = none →
                i ∉ M.accepted
                  (Function.update reports i { desired := s, value := v })
  payment_eq_of_accepted :
    ∀ reports,
      NonnegativeNonemptyProfile reports →
        ∀ i,
          i ∈ M.accepted reports →
            ∃ p,
              threshold reports i (reports i).desired = some p ∧
                M.payment reports i = p

namespace NonnegativeCriticalValueWithInfinityCertificate

variable [DecidableEq Bidder] [DecidableEq Item]
    {M : SingleMindedAcceptedMechanism Bidder Item}

end NonnegativeCriticalValueWithInfinityCertificate

end SingleMindedAcceptedMechanism

namespace SingleMindedBid

variable [DecidableEq Item]

/-- The size of a single-minded desired bundle, as a real number. -/
def bundleSize (b : SingleMindedBid Item) : ℝ :=
  (b.desired.card : ℝ)

/-- Average amount per good, `a / |s|`. -/
noncomputable def averageAmountPerGood (b : SingleMindedBid Item) : ℝ :=
  b.value / b.bundleSize

end SingleMindedBid

variable {Vertex : Type*}

/--
Deterministic key for the concrete source average-density order. The primary
coordinate is dualized so increasing lexicographic sort lists larger averages
first; the bidder order is only a tie-breaker.
-/
noncomputable def singleMindedAverageTieKey
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) (i : Bidder) :
    (ℝᵒᵈ ×ₗ Bidder) :=
  toLex (OrderDual.toDual (bids i).averageAmountPerGood, i)

/-- Concrete total relation used to sort single-minded bidders by average density. -/
noncomputable def singleMindedAverageTieRel
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) : Bidder → Bidder → Prop :=
  Order.Preimage (singleMindedAverageTieKey bids) (· ≤ ·)

noncomputable instance singleMindedAverageTieRelDecidable
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    DecidableRel (singleMindedAverageTieRel bids) := by
  dsimp [singleMindedAverageTieRel]
  infer_instance

instance singleMindedAverageTieRelTrans
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    IsTrans Bidder (singleMindedAverageTieRel bids) := sorry

instance singleMindedAverageTieRelTotal
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    Std.Total (singleMindedAverageTieRel bids) := sorry

instance singleMindedAverageTieRelAntisymm
    [DecidableEq Item] [LinearOrder Bidder]
    (bids : Bidder → SingleMindedBid Item) :
    Std.Antisymm (singleMindedAverageTieRel bids) := sorry

end Auction

end EconCSLib
