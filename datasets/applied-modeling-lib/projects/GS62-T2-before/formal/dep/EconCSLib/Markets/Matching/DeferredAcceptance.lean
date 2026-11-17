import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import dep.EconCSLib.Markets.Matching.Basic

namespace EconCSLib

namespace Matching

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

set_option linter.unusedSimpArgs false

set_option linter.unusedSimpArgs true

set_option linter.unusedSimpArgs false

set_option linter.unusedSimpArgs true

/-- Men have strict preferences over women. -/
def MenStrictPreferenceProfile (val_m : M → W → ℝ) : Prop :=
  ∀ m w w', val_m m w = val_m m w' → w = w'

/-- Women have strict preferences over men. -/
def WomenStrictPreferenceProfile (val_w : W → M → ℝ) : Prop :=
  ∀ w m m', val_w w m = val_w w m' → m = m'

/--
All potential pairs are acceptable to both sides. This is the marriage-problem
specialization in Roth's proof, where every agent must be matched.
-/
def AllPairsAcceptable (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w, 0 < val_m m w) ∧ (∀ w m, 0 < val_w w m)

end Matching

end EconCSLib
