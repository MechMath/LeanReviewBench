module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

/-- Type class for a group with an (implicit) prime order `p`. -/
class PrimeOrder (G : Type*) [Group G] where
  p : ℕ
  [hPrime : Fact (Nat.Prime p)]
  hCard : Nat.card G = p

namespace PrimeOrder

variable {G : Type*} [Group G] [PrimeOrder G]

instance : Fact (Nat.Prime (PrimeOrder.p G)) := sorry

instance [PrimeOrder G] : IsCyclic G := sorry

instance : CommGroup G := IsCyclic.commGroup

end PrimeOrder

/-- Type class for a group with a prime order `p` as an explicit output parameter. -/
class PrimeOrderWith (G : Type*) [Group G] (p : outParam ℕ) [Fact (Nat.Prime p)] where
  hCard : Nat.card G = p

namespace PrimeOrderWith

variable {G : Type*} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)] [PrimeOrderWith G p]

instance : PrimeOrder G where
  p := p
  hCard := PrimeOrderWith.hCard

end PrimeOrderWith
