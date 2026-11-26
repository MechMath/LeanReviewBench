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

structure DAState (M W : Type*) where
  m_match : M → Option W
  w_match : W → Option M
  m_proposals : M → Finset W
  consistent : ∀ m w, m_match m = some w ↔ w_match w = some m

def initialDAState (M W : Type*) [Fintype W] : DAState M W where
  m_match _ := none
  w_match _ := none
  m_proposals _ := Finset.univ
  consistent m w := sorry

def IsActiveMan (val_m : M → W → ℝ) (s : DAState M W) (m : M) : Prop :=
  s.m_match m = none ∧ ∃ w ∈ s.m_proposals m, 0 ≤ val_m m w

def BestRemainingWoman (val_m : M → W → ℝ) (s : DAState M W) (m : M) (w : W) : Prop :=
  w ∈ s.m_proposals m ∧ 0 ≤ val_m m w ∧
  ∀ w' ∈ s.m_proposals m, 0 ≤ val_m m w' → val_m m w' ≤ val_m m w

/-- Remove the proposal opportunity `m -> w` from a DA state's proposal sets. -/
def removeProposal (s : DAState M W) (m : M) (w : W) : M → Finset W :=
  fun m' => if m' = m then s.m_proposals m \ {w} else s.m_proposals m'

lemma exists_best_woman (val_m : M → W → ℝ) (s : DAState M W) (m : M)
    (hact : IsActiveMan val_m s m) : ∃ w, BestRemainingWoman val_m s m w := sorry

noncomputable def daStep (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) : DAState M W :=
  have _ : Decidable (∃ m, IsActiveMan val_m s m) := Classical.propDecidable _
  if h : ∃ m, IsActiveMan val_m s m then
    let m := Classical.choose h
    let hact := Classical.choose_spec h
    let w_exists := exists_best_woman val_m s m hact
    let w := Classical.choose w_exists
    let hw_best := Classical.choose_spec w_exists
    let new_proposals := removeProposal s m w
    let m_current := s.w_match w
    let accepts :=
      match m_current with
      | none => 0 ≤ val_w w m
      | some m' => val_w w m' < val_w w m
    have _ : Decidable accepts := Classical.propDecidable _
    if hacc : accepts then
      let new_w_match := Function.update s.w_match w (some m)
      let new_m_match := fun m'' =>
        if m'' = m then some w
        else if m_current = some m'' then none
        else s.m_match m''
      { m_match := new_m_match
        w_match := new_w_match
        m_proposals := new_proposals
        consistent := sorry }
    else
      { s with m_proposals := new_proposals }
  else
    s

set_option linter.unusedSimpArgs false

set_option linter.unusedSimpArgs true

noncomputable def deferredAcceptanceState (val_m : M → W → ℝ) (val_w : W → M → ℝ) : DAState M W :=
  let max_steps := Fintype.card M * Fintype.card W
  (List.range max_steps).foldl (fun s _ => daStep val_m val_w s) (initialDAState M W)

noncomputable def deferredAcceptance (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W where
  m_match := (deferredAcceptanceState val_m val_w).m_match
  w_match := (deferredAcceptanceState val_m val_w).w_match
  consistent_m := (deferredAcceptanceState val_m val_w).consistent

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
