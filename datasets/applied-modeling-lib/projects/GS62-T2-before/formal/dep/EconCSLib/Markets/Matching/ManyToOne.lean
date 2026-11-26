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

namespace EconCSLib

namespace Matching

/-- A many-to-one assignment between applicants and colleges. -/
structure ManyToOneAssignment (Applicants Colleges : Type*) where
  app_match : Applicants → Option Colleges
  college_roster : Colleges → Finset Applicants
  consistent : ∀ a c, app_match a = some c ↔ a ∈ college_roster c

namespace ManyToOneAssignment

/-- A many-to-one assignment respects college quotas. -/
def RespectsQuota {Applicants Colleges : Type*}
    (quota : Colleges → ℕ) (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ∀ c, (mu.college_roster c).card ≤ quota c

/-- Seat copies used to reduce a capacity-constrained college to one-to-one slots. -/
abbrev CollegeSeat {Colleges : Type*} (quota : Colleges → ℕ) :=
  Σ c, Fin (quota c)

noncomputable instance instFintypeCollegeSeat {Colleges : Type*}
    [Fintype Colleges] (quota : Colleges → ℕ) :
    Fintype (CollegeSeat quota) := by
  classical
  infer_instance

noncomputable instance instDecidableEqCollegeSeat {Colleges : Type*}
    [DecidableEq Colleges] (quota : Colleges → ℕ) :
    DecidableEq (CollegeSeat quota) := by
  classical
  infer_instance

end ManyToOneAssignment

namespace ManyToOne

/-- Applicant utility from an optional college assignment. -/
def valApplicant {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (a : Applicants) (c : Option Colleges) : ℝ :=
  match c with
  | none => 0
  | some c' => val_applicant a c'

/--
College `c` would accept applicant `a` relative to roster `s`: either `c` has a
free acceptable seat or `c` strictly prefers `a` to some currently assigned
applicant.
-/
def CollegeWouldAccept {Applicants Colleges : Type*}
    (val_college : Colleges → Applicants → ℝ)
    (quota : Colleges → ℕ) (s : Finset Applicants)
    (a : Applicants) (c : Colleges) : Prop :=
  (0 < val_college c a ∧ s.card < quota c) ∨
    ∃ a' ∈ s, val_college c a' < val_college c a

/-- Stability for many-to-one college-admissions/hospital-resident assignments. -/
def IsStable {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneAssignment.RespectsQuota quota mu ∧
    (∀ a, 0 ≤ valApplicant val_applicant a (mu.app_match a)) ∧
    (∀ c a, a ∈ mu.college_roster c → 0 ≤ val_college c a) ∧
    (∀ a c,
      valApplicant val_applicant a (mu.app_match a) < val_applicant a c →
        CollegeWouldAccept val_college quota (mu.college_roster c) a c →
          False)

end ManyToOne

end Matching

end EconCSLib
