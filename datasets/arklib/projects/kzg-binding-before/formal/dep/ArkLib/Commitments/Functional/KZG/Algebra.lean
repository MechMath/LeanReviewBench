module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import dep.ArkLib.Data.GroupTheory.PrimeOrder

@[expose] public section

namespace Groups

section PrimeOrder

variable {G : Type} [Group G] {p : outParam ℕ} [Fact (Nat.Prime p)]
  [PrimeOrderWith G p]

namespace PowerSrs

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}

/-- The vector of length `n + 1` consisting of the monomial powers
`#v[g, g ^ τ, g ^ (τ ^ 2), ..., g ^ (τ ^ n)]`. -/
def tower (g : G) (τ : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (τ.val ^ i.val))

/-- The monomial powers-of-τ SRS used by KZG, t-SDH, and ARSDH:
`(g₁, g₁^τ, ..., g₁^(τ^n)), (g₂, g₂^τ)`. -/
def generate (n : ℕ) (τ : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (tower g₁ τ n, tower g₂ τ 1)

end PowerSrs

end PrimeOrder

end Groups
