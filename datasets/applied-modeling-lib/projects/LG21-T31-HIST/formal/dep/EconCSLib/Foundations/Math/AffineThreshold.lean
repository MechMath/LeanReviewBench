import Mathlib

namespace EconCSLib

noncomputable section

/- Cutoff in the input variable for a positive-slope affine score. -/
def affineCutoff (intercept slope threshold : ℝ) : ℝ :=
  (threshold - intercept) / slope

/-
A positive-slope affine score exceeds a threshold exactly above the induced
cutoff.
-/
theorem affine_le_threshold_iff_le_cutoff
    {intercept slope threshold x : ℝ} (hslope : 0 < slope) :
    intercept + slope * x ≤ threshold ↔
      x ≤ affineCutoff intercept slope threshold := by
  unfold affineCutoff
  constructor
  · intro h
    have hsub : slope * x ≤ threshold - intercept := by
      linarith
    rw [le_div_iff₀ hslope]
    simpa [mul_comm] using hsub
  · intro h
    have hmul : slope * x ≤ threshold - intercept := by
      have := (le_div_iff₀ hslope).mp h
      simpa [mul_comm] using this
    linarith

/- A positive-slope affine score is strictly increasing. -/
theorem exists_lt_affine_after (lower intercept threshold : ℝ) {slope : ℝ}
    (hslope : 0 < slope) :
    ∃ x : ℝ, lower < x ∧ threshold < intercept + slope * x := by
  let cutoff : ℝ := affineCutoff intercept slope threshold
  let x : ℝ := max lower cutoff + 1
  have hlower_x : lower < x := by
    dsimp [x]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hcutoff_x : cutoff < x := by
    dsimp [x]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hnot_affine :
      ¬ intercept + slope * x ≤ threshold := by
    intro h
    have hx_le_cutoff :
        x ≤ affineCutoff intercept slope threshold :=
      (affine_le_threshold_iff_le_cutoff (intercept := intercept)
        (slope := slope) (threshold := threshold) (x := x) hslope).1 h
    linarith
  exact ⟨x, hlower_x, lt_of_not_ge hnot_affine⟩

end

end EconCSLib
