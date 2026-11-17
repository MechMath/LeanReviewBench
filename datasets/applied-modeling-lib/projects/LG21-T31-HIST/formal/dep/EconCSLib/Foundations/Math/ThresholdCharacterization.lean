import Mathlib

namespace EconCSLib

noncomputable section

open Set

/- A one-dimensional decision rule is a lower-cutoff rule. -/
theorem exists_indifference_lower_cutoff_of_continuous_strictMono_crossing
    {choosePayoff outsideAtCutoff : ℝ → ℝ} {low high : ℝ}
    (hcontChoose : ContinuousOn choosePayoff (Icc low high))
    (hcontOutside : ContinuousOn outsideAtCutoff (Icc low high))
    (hmonoChoose : StrictMono choosePayoff)
    (hlow_high : low < high)
    (hleft : choosePayoff low < outsideAtCutoff low)
    (hright : outsideAtCutoff high < choosePayoff high) :
    ∃ cutoff : ℝ,
      cutoff ∈ Ioo low high ∧
        outsideAtCutoff cutoff = choosePayoff cutoff ∧
          (∀ value : ℝ,
            outsideAtCutoff cutoff ≤ choosePayoff value ↔ cutoff ≤ value) ∧
            (∀ value : ℝ,
              choosePayoff value < outsideAtCutoff cutoff ↔ value < cutoff) := by
  let gap : ℝ → ℝ :=
    fun cutoff => choosePayoff cutoff - outsideAtCutoff cutoff
  have hgap_cont : ContinuousOn gap (Icc low high) :=
    hcontChoose.sub hcontOutside
  have hzero_mem : (0 : ℝ) ∈ Icc (gap low) (gap high) := by
    constructor <;> dsimp [gap] <;> linarith
  rcases intermediate_value_Icc hlow_high.le hgap_cont hzero_mem with
    ⟨cutoff, hcutoff_mem, hgap_zero⟩
  have hlow_lt_cutoff : low < cutoff := by
    have hne : cutoff ≠ low := by
      intro h
      subst cutoff
      dsimp [gap] at hgap_zero
      linarith
    exact lt_of_le_of_ne hcutoff_mem.1 (Ne.symm hne)
  have hcutoff_lt_high : cutoff < high := by
    have hne : cutoff ≠ high := by
      intro h
      subst cutoff
      dsimp [gap] at hgap_zero
      linarith
    exact lt_of_le_of_ne hcutoff_mem.2 hne
  have hindiff :
      outsideAtCutoff cutoff = choosePayoff cutoff := by
    dsimp [gap] at hgap_zero
    linarith
  refine ⟨cutoff, ⟨hlow_lt_cutoff, hcutoff_lt_high⟩,
    hindiff, ?_, ?_⟩
  · intro value
    constructor
    · intro hbest
      by_contra hnot
      have hvalue_lt : value < cutoff := lt_of_not_ge hnot
      have hstrict : choosePayoff value < choosePayoff cutoff :=
        hmonoChoose hvalue_lt
      rw [← hindiff] at hstrict
      linarith
    · intro hcutoff_le_value
      rcases lt_or_eq_of_le hcutoff_le_value with hlt | rfl
      · have hstrict : choosePayoff cutoff < choosePayoff value :=
          hmonoChoose hlt
        rw [hindiff]
        exact le_of_lt hstrict
      · rw [hindiff]
  · intro value
    constructor
    · intro hstrict
      by_contra hnot
      have hcutoff_le_value : cutoff ≤ value := le_of_not_gt hnot
      have hbest :
          outsideAtCutoff cutoff ≤ choosePayoff value := by
        rcases lt_or_eq_of_le hcutoff_le_value with hlt | rfl
        · have hmono : choosePayoff cutoff < choosePayoff value :=
            hmonoChoose hlt
          rw [hindiff]
          exact le_of_lt hmono
        · rw [hindiff]
      linarith
    · intro hvalue_lt
      have hmono : choosePayoff value < choosePayoff cutoff :=
        hmonoChoose hvalue_lt
      rw [← hindiff] at hmono
      exact hmono

/-
Indexed version of
`exists_indifference_lower_cutoff_of_continuous_strictMono_crossing`: for each
profile, a continuous crossing against a strictly increasing chosen payoff
produces an interior cutoff and a lower-cutoff choice rule.  A nonempty index
set also gives a concrete value below one cutoff where choosing is not weakly
optimal.
-/
theorem exists_indexed_indifference_lower_cutoffs_of_continuous_strictMono_crossing
    {ι : Type*} [Nonempty ι]
    (choosePayoff outsideAtCutoff : ι → ℝ → ℝ)
    (low high : ι → ℝ)
    (hcontChoose :
      ∀ i, ContinuousOn (choosePayoff i) (Icc (low i) (high i)))
    (hcontOutside :
      ∀ i, ContinuousOn (outsideAtCutoff i) (Icc (low i) (high i)))
    (hmonoChoose : ∀ i, StrictMono (choosePayoff i))
    (hlow_high : ∀ i, low i < high i)
    (hleft : ∀ i, choosePayoff i (low i) < outsideAtCutoff i (low i))
    (hright : ∀ i, outsideAtCutoff i (high i) < choosePayoff i (high i)) :
    ∃ cutoff : ι → ℝ,
      (∀ i, cutoff i ∈ Ioo (low i) (high i)) ∧
        (∀ i, outsideAtCutoff i (cutoff i) = choosePayoff i (cutoff i)) ∧
          (∀ i value,
            outsideAtCutoff i (cutoff i) ≤ choosePayoff i value ↔
              cutoff i ≤ value) ∧
            (∃ i value,
              ¬ outsideAtCutoff i (cutoff i) ≤ choosePayoff i value) ∧
              (∀ i, ∃ c : ℝ, ∀ value : ℝ,
                outsideAtCutoff i (cutoff i) ≤ choosePayoff i value ↔
                  c ≤ value) := by
  have hcutoff_exists :
      ∀ i, ∃ cutoff : ℝ,
        cutoff ∈ Ioo (low i) (high i) ∧
          outsideAtCutoff i cutoff = choosePayoff i cutoff ∧
            (∀ value : ℝ,
              outsideAtCutoff i cutoff ≤ choosePayoff i value ↔
                cutoff ≤ value) ∧
              (∀ value : ℝ,
                choosePayoff i value < outsideAtCutoff i cutoff ↔
                  value < cutoff) := by
    intro i
    exact
      exists_indifference_lower_cutoff_of_continuous_strictMono_crossing
        (hcontChoose i) (hcontOutside i) (hmonoChoose i)
        (hlow_high i) (hleft i) (hright i)
  choose cutoff hmem hindiff hthreshold _hbelow using hcutoff_exists
  refine ⟨cutoff, hmem, hindiff, hthreshold, ?_, ?_⟩
  · let i : ι := Classical.choice inferInstance
    refine ⟨i, low i, ?_⟩
    rw [hthreshold i (low i)]
    exact not_le.mpr (hmem i).1
  · intro i
    exact ⟨cutoff i, hthreshold i⟩

/-
If a continuous strictly increasing scalar function crosses a level between a
low point and a cutoff, then there is an interior indifference point, all
points from that indifference point to the cutoff weakly clear the level, and
some interior point strictly clears it.
-/
end

end EconCSLib
