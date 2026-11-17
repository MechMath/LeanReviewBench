import Mathlib

open scoped BigOperators

namespace EconCSLib

namespace Auction

structure PositionEnvironment (Slot : Type*) where
  clickThroughRate : Slot → ℝ

structure PositionOutcome (Bidder Slot : Type*) where
  slotOf : Bidder → Option Slot
  paymentPerClick : Bidder → ℝ

namespace PositionOutcome

variable {Bidder Slot : Type*}

def utility (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) (i : Bidder) : ℝ :=
  match O.slotOf i with
  | none => 0
  | some s => E.clickThroughRate s * (values i - O.paymentPerClick i)

def FeasibleAssignment (O : PositionOutcome Bidder Slot) : Prop :=
  ∀ ⦃i j : Bidder⦄ ⦃s : Slot⦄,
    O.slotOf i = some s → O.slotOf j = some s → i = j

def IndividuallyRational (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ) : Prop :=
  ∀ i, 0 ≤ O.utility E values i

end PositionOutcome

abbrev PositionMechanism (Bidder Slot : Type*) :=
  (Bidder → ℝ) → PositionOutcome Bidder Slot

namespace PositionMechanism

variable {Bidder Slot : Type*}

def utility (E : PositionEnvironment Slot)
    (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (i : Bidder) : ℝ :=
  (M bids).utility E values i

end PositionMechanism

namespace PositionOutcome

variable {Bidder Slot : Type*}

def SlotEnvyFree (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ) : Prop :=
  ∀ (i j : Bidder) (s : Slot),
    O.slotOf j = some s →
      E.clickThroughRate s * (values i - O.paymentPerClick j) ≤
        O.utility E values i

def NoProfitableAssignedSlotDeviation (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ) : Prop :=
  ∀ (i j : Bidder) (s : Slot),
    O.slotOf j = some s →
      E.clickThroughRate s * (values i - O.paymentPerClick j) ≤
        O.utility E values i

def StableAssignment (E : PositionEnvironment Slot)
    (O : PositionOutcome Bidder Slot) (values : Bidder → ℝ) : Prop :=
  O.FeasibleAssignment ∧
    O.IndividuallyRational E values ∧
      O.NoProfitableAssignedSlotDeviation E values

end PositionOutcome

namespace PositionMechanism

variable {Bidder Slot : Type*}

end PositionMechanism

end Auction

end EconCSLib
