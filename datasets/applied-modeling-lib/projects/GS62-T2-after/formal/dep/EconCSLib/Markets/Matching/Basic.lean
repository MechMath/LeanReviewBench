import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic

namespace EconCSLib

namespace Matching

/-- A matching between Men and Women. -/
structure Assignment (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  consistent_m : ∀ m w, m_match m = some w ↔ w_match w = some m

namespace Assignment

end Assignment

/-- The value of a match for a man. 0 if unmatched. -/
def valM {M W : Type*} (val : M → W → ℝ) (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val m w'

/-- The value of a match for a woman. 0 if unmatched. -/
def valW {M W : Type*} (val : W → M → ℝ) (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val w m'

end Matching

end EconCSLib
