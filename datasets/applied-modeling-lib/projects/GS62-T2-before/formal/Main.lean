import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import dep.EconCSLib.Markets.Matching.Basic
import dep.EconCSLib.Markets.Matching.DeferredAcceptance
import dep.EconCSLib.Markets.Matching.ManyToOne

namespace GS62CollegeAdmissions

namespace PaperInterface

open EconCSLib.Matching

/--
Strict marriage domain: both sides have strict preferences and every possible
man-woman pair is acceptable.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  MenStrictPreferenceProfile val_m ∧
    WomenStrictPreferenceProfile val_w ∧
    AllPairsAcceptable val_m val_w

/-- Stable marriage: no blocking pair, using the reusable matching API. -/
def stableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  IsStable val_m val_w mu

/-- Complete marriage: every participant is matched. -/
def completeMarriage {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/--
Applicant/proposer optimal stable marriage: every proposer weakly prefers this
stable marriage to any other stable marriage.
-/
def applicantOptimalStableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stableMarriage val_m val_w mu ∧
    ∀ mu', stableMarriage val_m val_w mu' →
      ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m (mu.m_match m)

/--
Theorem 2: the applicant-proposing deferred-acceptance assignment is complete
and applicant-optimal among stable assignments.
-/
theorem theorem2_applicant_optimality
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcard : Fintype.card Applicants = Fintype.card Colleges)
    (hdomain : strictMarriageDomain val_applicant val_college) :
    ∃ mu : Assignment Applicants Colleges,
      completeMarriage mu ∧
        applicantOptimalStableMarriage val_applicant val_college mu := sorry

end PaperInterface

end GS62CollegeAdmissions
