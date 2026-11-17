import Mathlib

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace EconCSLib
namespace Probability

noncomputable section

/-
Unnormalized Gaussian upper-tail integral appearing in the Mills ratio.
-/
def gaussianMillsTail (t : ℝ) : ℝ :=
  ∫ x : ℝ in Ioi t, Real.exp (-(x ^ 2) / 2)

/-
Unnormalized Gaussian Mills ratio,
`R(t) = exp(t^2 / 2) * ∫_t^∞ exp(-x^2 / 2) dx`.
-/
def gaussianMillsRatio (t : ℝ) : ℝ :=
  Real.exp (t ^ 2 / 2) * gaussianMillsTail t

/- Derivative of the unnormalized Gaussian tail integral. -/
theorem gaussianMillsTail_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianMillsTail (-(Real.exp (-(t ^ 2) / 2))) t := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hIic_eq (u : ℝ) :
      (∫ x : ℝ in Iic u, f x) =
        (∫ x : ℝ in Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x := by
    have hfi0 : IntegrableOn f (Iic (0 : ℝ)) := hfint.integrableOn
    have hfiu : IntegrableOn f (Iic u) := hfint.integrableOn
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (f := f) (a := (0 : ℝ)) (b := u) hfi0 hfiu
    linarith
  have hIic_deriv : HasDerivAt
      (fun u : ℝ => ∫ x : ℝ in Iic u, f x) (f t) t := by
    have hderiv : HasDerivAt
        (fun u : ℝ =>
          (∫ x : ℝ in Iic (0 : ℝ), f x) + ∫ x : ℝ in (0 : ℝ)..u, f x)
        (f t) t := by
      exact (hcont.integral_hasStrictDerivAt (0 : ℝ) t).hasDerivAt.const_add
        (∫ x : ℝ in Iic (0 : ℝ), f x)
    refine hderiv.congr_of_eventuallyEq ?_
    exact Eventually.of_forall fun u => hIic_eq u
  have htail_eq : (fun u : ℝ => gaussianMillsTail u) =ᶠ[nhds t]
      (fun u : ℝ => (∫ x : ℝ, f x) - ∫ x : ℝ in Iic u, f x) := by
    exact Eventually.of_forall fun u => by
      have hsum := intervalIntegral.integral_Iic_add_Ioi
        (f := f) (b := u) (μ := volume) hfint.integrableOn hfint.integrableOn
      dsimp [gaussianMillsTail]
      dsimp [f] at hsum ⊢
      linarith
  exact hIic_deriv.const_sub (∫ x : ℝ, f x) |>.congr_of_eventuallyEq htail_eq

/- The Gaussian tail integral in the Mills ratio tends to zero at `+∞`. -/
theorem gaussianMillsTail_tendsto_atTop_zero :
    Tendsto gaussianMillsTail atTop (nhds 0) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2)
  have hfint : Integrable f := by
    have hbase := integrable_exp_neg_mul_sq (show 0 < (1 / 2 : ℝ) by norm_num)
    convert hbase using 1
    ext x
    dsimp [f]
    ring_nf
  have hanti : Antitone (fun t : ℝ => Ioi t) := by
    intro a b hab x hx
    exact hab.trans_lt hx
  have hInter : (⋂ t : ℝ, Ioi t) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxlt : x < x := by
        simpa using (mem_iInter.mp hx x)
      exact (lt_irrefl x hxlt).elim
    · intro hx
      simp at hx
  have htail :=
    tendsto_setIntegral_of_antitone
      (μ := volume) (s := fun t : ℝ => Ioi t) (f := f)
      (fun _ => measurableSet_Ioi) hanti ⟨(0 : ℝ), hfint.integrableOn⟩
  change Tendsto (fun t => ∫ x : ℝ in Ioi t, Real.exp (-(x ^ 2) / 2)) atTop (nhds 0)
  simpa only [hInter, MeasureTheory.setIntegral_empty, f] using htail

/- Riccati derivative identity for the concrete Gaussian Mills ratio. -/
def gaussianSampfordLowerComparison (t : ℝ) : ℝ :=
  (Real.sqrt (t ^ 2 + 4) - t) / 2

/- Sampford's comparison function is positive. -/
theorem gaussianSampfordLowerComparison_pos (t : ℝ) :
    0 < gaussianSampfordLowerComparison t := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_gt_abs : |t| < Real.sqrt (t ^ 2 + 4) := by
    rw [Real.lt_sqrt (abs_nonneg t)]
    nlinarith [sq_abs t]
  have ht_lt : t < Real.sqrt (t ^ 2 + 4) :=
    (le_abs_self t).trans_lt hsqrt_gt_abs
  linarith

/-
For nonnegative arguments, Sampford's lower comparison is bounded by `1`.
-/
theorem gaussianSampfordLowerComparison_le_one_of_nonneg {t : ℝ}
    (ht : 0 ≤ t) :
    gaussianSampfordLowerComparison t ≤ 1 := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_le : Real.sqrt (t ^ 2 + 4) ≤ t + 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  linarith

/- Sampford's comparison function is the positive root of `x^2 + t*x - 1 = 0`. -/
theorem gaussianSampfordLowerComparison_quadratic_eq (t : ℝ) :
    (gaussianSampfordLowerComparison t) ^ 2 +
        t * gaussianSampfordLowerComparison t - 1 = 0 := by
  unfold gaussianSampfordLowerComparison
  have hsqrt_sq : (Real.sqrt (t ^ 2 + 4)) ^ 2 = t ^ 2 + 4 := by
    exact Real.sq_sqrt (by nlinarith [sq_nonneg t])
  nlinarith

/- Derivative of Sampford's lower comparison function. -/
theorem gaussianSampfordLowerComparison_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianSampfordLowerComparison
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
  have hinner : HasDerivAt (fun u : ℝ => u ^ 2 + 4) (2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).add_const (4 : ℝ) using 1
    all_goals simp [id]
  have hpos : t ^ 2 + 4 ≠ 0 := by
    positivity
  have hsqrt := hinner.sqrt hpos
  have hsub := hsqrt.sub (hasDerivAt_id t)
  have hdiv := hsub.div_const (2 : ℝ)
  unfold gaussianSampfordLowerComparison
  convert hdiv using 1
  · rfl
  have hsqrt_ne : Real.sqrt (t ^ 2 + 4) ≠ 0 := by
    exact (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])).ne'
  field_simp [hsqrt_ne]

/- The comparison function is larger than the reciprocal derivative denominator. -/
theorem gaussianSampfordLowerComparison_inv_sqrt_lt (t : ℝ) :
    (Real.sqrt (t ^ 2 + 4))⁻¹ < gaussianSampfordLowerComparison t := by
  let L := gaussianSampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := gaussianSampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hroot : L ^ 2 + t * L - 1 = 0 :=
    gaussianSampfordLowerComparison_quadratic_eq t
  have hs_eq : s = 2 * L + t := by
    dsimp [L, s, gaussianSampfordLowerComparison]
    ring
  have hLs : L * s = 1 + L ^ 2 := by
    rw [hs_eq]
    nlinarith
  have hone : 1 < L * s := by
    rw [hLs]
    nlinarith [sq_pos_of_ne_zero hLpos.ne']
  exact (inv_lt_iff_one_lt_mul₀ hspos).2 hone

/- The derivative correction term in Sampford's comparison proof is positive. -/
theorem gaussianSampfordLowerComparison_sq_add_deriv_pos (t : ℝ) :
    0 <
      (gaussianSampfordLowerComparison t) ^ 2 +
        ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) := by
  let L := gaussianSampfordLowerComparison t
  let s := Real.sqrt (t ^ 2 + 4)
  have hLpos : 0 < L := gaussianSampfordLowerComparison_pos t
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.mpr (by nlinarith [sq_nonneg t])
  have hderiv_eq : ((t / s - 1) / 2) = -L / s := by
    dsimp [L, s, gaussianSampfordLowerComparison]
    field_simp [hspos.ne']
    ring
  have hinv_lt : s⁻¹ < L := gaussianSampfordLowerComparison_inv_sqrt_lt t
  have hgap : 0 < L - s⁻¹ := sub_pos.mpr hinv_lt
  calc
    0 < L * (L - s⁻¹) := mul_pos hLpos hgap
    _ = L ^ 2 + ((t / s - 1) / 2) := by
      rw [hderiv_eq]
      field_simp [hspos.ne']
      ring

/-
Sampford gap.  Multiplying `gaussianSampfordGap t > 0` by `exp(t^2/2)`
gives `gaussianSampfordLowerComparison t < gaussianMillsRatio t`.
-/
def gaussianSampfordGap (t : ℝ) : ℝ :=
  gaussianMillsTail t -
    gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)

/- Derivative of the Sampford lower-bound gap. -/
theorem gaussianSampfordGap_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianSampfordGap
      (-(Real.exp (-(t ^ 2) / 2) *
          ((gaussianSampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))) t := by
  let L := gaussianSampfordLowerComparison
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have htail := gaussianMillsTail_hasDerivAt t
  have hL : HasDerivAt L
      ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2) t := by
    simpa [L] using gaussianSampfordLowerComparison_hasDerivAt t
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      all_goals simp [id]
      <;> ring
    convert hinner.exp using 1
    all_goals
      dsimp [E]
      ring
  have hprod := hL.mul hE
  have hsub := htail.sub hprod
  unfold gaussianSampfordGap
  dsimp [L, E] at hsub ⊢
  convert hsub using 1
  have hroot :
      -((gaussianSampfordLowerComparison t) ^ 2) =
        t * gaussianSampfordLowerComparison t - 1 := by
    have h := gaussianSampfordLowerComparison_quadratic_eq t
    nlinarith
  have hroot_mul :
      Real.exp (t ^ 2 * (-1 / 2)) *
          (-((gaussianSampfordLowerComparison t) ^ 2)) =
        Real.exp (t ^ 2 * (-1 / 2)) *
          (t * gaussianSampfordLowerComparison t - 1) := by
    rw [hroot]
  ring_nf
  ring_nf at hroot_mul
  nlinarith

/- The Sampford gap has strictly negative derivative. -/
theorem gaussianSampfordGap_deriv_neg (t : ℝ) :
    let d :=
      -(Real.exp (-(t ^ 2) / 2) *
          ((gaussianSampfordLowerComparison t) ^ 2 +
            ((t / Real.sqrt (t ^ 2 + 4) - 1) / 2)))
    d < 0 := by
  dsimp
  have hpos :=
    gaussianSampfordLowerComparison_sq_add_deriv_pos t
  exact neg_neg_of_pos (mul_pos (Real.exp_pos _) hpos)

/- The Gaussian exponential factor decays at `+∞`. -/
theorem gaussianExpFactor_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2)) atTop (nhds 0) := by
  have harg :
      Tendsto (fun t : ℝ => (-(1 / 2 : ℝ)) * t ^ 2)
        atTop atBot := by
    exact tendsto_neg_const_mul_pow_atTop (n := 2) (by norm_num) (by norm_num)
  refine (Real.tendsto_exp_atBot.comp harg).congr' ?_
  filter_upwards with t
  have hpow : (-(t ^ 2) / 2 : ℝ) = (-(1 / 2 : ℝ)) * t ^ 2 := by
    ring
  simpa [Function.comp_apply, hpow]

/- Sampford's gap tends to zero at `+∞`. -/
theorem gaussianSampfordGap_tendsto_atTop_zero :
    Tendsto gaussianSampfordGap atTop (nhds 0) := by
  have hprod :
      Tendsto
        (fun t : ℝ =>
          gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2))
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ gaussianExpFactor_tendsto_atTop_zero
    · exact Eventually.of_forall fun t =>
        mul_nonneg (le_of_lt (gaussianSampfordLowerComparison_pos t))
          (le_of_lt (Real.exp_pos _))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_le_of_le_one_left (le_of_lt (Real.exp_pos _))
        (gaussianSampfordLowerComparison_le_one_of_nonneg ht)
  change Tendsto (fun t => gaussianMillsTail t - gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) atTop (nhds 0)
  simpa only [sub_zero] using
    gaussianMillsTail_tendsto_atTop_zero.sub hprod

/-
If the Sampford gap tends to zero at `+∞`, then it is positive everywhere
because its derivative is strictly negative.
-/
theorem gaussianSampfordGap_pos_of_tendsto_atTop_zero
    (hlim : Tendsto gaussianSampfordGap atTop (nhds 0)) :
    ∀ t, 0 < gaussianSampfordGap t := by
  have hanti : StrictAnti gaussianSampfordGap := by
    refine strictAnti_of_hasDerivAt_neg
      (f' := fun x =>
        -(Real.exp (-(x ^ 2) / 2) *
          ((gaussianSampfordLowerComparison x) ^ 2 +
            ((x / Real.sqrt (x ^ 2 + 4) - 1) / 2)))) ?_ ?_
    · exact gaussianSampfordGap_hasDerivAt
    · intro x
      exact gaussianSampfordGap_deriv_neg x
  intro t
  have hnext_nonneg : 0 ≤ gaussianSampfordGap (t + 1) := by
    refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (t + 1)] with y hy
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti hlt)
  have hstrict : gaussianSampfordGap (t + 1) < gaussianSampfordGap t := by
    exact hanti (by linarith)
  linarith

/- Positivity of the Sampford gap gives the explicit lower Mills-ratio bound. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio_of_gap_pos
    (hgap : ∀ t, 0 < gaussianSampfordGap t) :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t := by
  intro t
  have hgap_t := hgap t
  have htail_lt :
      gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2) <
        gaussianMillsTail t := by
    simpa [gaussianSampfordGap, sub_pos] using hgap_t
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold gaussianMillsRatio
  calc
    gaussianSampfordLowerComparison t
        = Real.exp (t ^ 2 / 2) *
            (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
          have hexp :
              Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2) = 1 := by
            rw [← Real.exp_add]
            have : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
            rw [this, Real.exp_zero]
          calc
            gaussianSampfordLowerComparison t =
                gaussianSampfordLowerComparison t *
                  (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) := by
              rw [hexp]
              ring
            _ = Real.exp (t ^ 2 / 2) *
                (gaussianSampfordLowerComparison t * Real.exp (-(t ^ 2) / 2)) := by
              ring
    _ < Real.exp (t ^ 2 / 2) * gaussianMillsTail t := hmul

/- Once the explicit gap limit is known, Sampford's lower bound follows. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    (hlim : Tendsto gaussianSampfordGap atTop (nhds 0)) :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t :=
  gaussianSampfordLowerComparison_lt_millsRatio_of_gap_pos
    (gaussianSampfordGap_pos_of_tendsto_atTop_zero hlim)

/- Sampford's explicit lower comparison holds for the concrete Gaussian Mills ratio. -/
theorem gaussianSampfordLowerComparison_lt_millsRatio :
    ∀ t, gaussianSampfordLowerComparison t < gaussianMillsRatio t :=
  gaussianSampfordLowerComparison_lt_millsRatio_of_gap_tendsto_atTop_zero
    gaussianSampfordGap_tendsto_atTop_zero

/- The concrete Gaussian Mills ratio is positive. -/
theorem gaussianMillsRatio_pos (t : ℝ) :
    0 < gaussianMillsRatio t :=
  (gaussianSampfordLowerComparison_pos t).trans
    (gaussianSampfordLowerComparison_lt_millsRatio t)

/- The unnormalized Gaussian upper tail in the Mills ratio is positive. -/
theorem gaussianMillsTail_pos (t : ℝ) :
    0 < gaussianMillsTail t := by
  have hR : 0 < Real.exp (t ^ 2 / 2) * gaussianMillsTail t := by
    simpa [gaussianMillsRatio] using gaussianMillsRatio_pos t
  exact pos_of_mul_pos_left (by simpa [mul_comm] using hR) (Real.exp_pos _).le

/- Scalar quadratic Mills inequality. -/
def gaussianMillsHazard (t : ℝ) : ℝ :=
  (gaussianMillsRatio t)⁻¹

/- The reciprocal Mills ratio is positive. -/
def gaussianMillsUpperGap (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2) / 2) / t - gaussianMillsTail t

/- Derivative of the Mills upper-bound gap away from zero. -/
theorem gaussianMillsUpperGap_hasDerivAt {t : ℝ} (ht_ne : t ≠ 0) :
    HasDerivAt gaussianMillsUpperGap
      (-(Real.exp (-(t ^ 2) / 2) / t ^ 2)) t := by
  let E : ℝ → ℝ := fun u => Real.exp (-(u ^ 2) / 2)
  have hE : HasDerivAt E (-(t * E t)) t := by
    have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2) / 2) (-t) t := by
      convert (((hasDerivAt_id t).pow 2).neg.div_const (2 : ℝ)) using 1
      all_goals simp [id]
      <;> ring
    convert hinner.exp using 1
    all_goals
      dsimp [E]
      ring
  have hdiv := hE.div (hasDerivAt_id t) ht_ne
  have htail := gaussianMillsTail_hasDerivAt t
  have hsub := hdiv.sub htail
  unfold gaussianMillsUpperGap
  dsimp [E] at hsub ⊢
  convert hsub using 1
  · rfl
  field_simp [ht_ne]
  ring

/- The Mills upper-bound gap has strictly negative derivative on positive arguments. -/
theorem gaussianMillsUpperGap_deriv_neg {t : ℝ} (ht : 0 < t) :
    -(Real.exp (-(t ^ 2) / 2) / t ^ 2) < 0 := by
  have hden : 0 < t ^ 2 := sq_pos_of_ne_zero ht.ne'
  exact neg_neg_of_pos (div_pos (Real.exp_pos _) hden)

/- The first term in the Mills upper-bound gap tends to zero at `+∞`. -/
theorem gaussianMillsUpperGap_firstTerm_tendsto_atTop_zero :
    Tendsto (fun t : ℝ => Real.exp (-(t ^ 2) / 2) / t) atTop (nhds 0) := by
  have hmul :=
    gaussianExpFactor_tendsto_atTop_zero.mul tendsto_inv_atTop_zero
  simpa [div_eq_mul_inv] using hmul

/- The Mills upper-bound gap tends to zero at `+∞`. -/
theorem gaussianMillsUpperGap_tendsto_atTop_zero :
    Tendsto gaussianMillsUpperGap atTop (nhds 0) := by
  change Tendsto (fun t => Real.exp (-(t ^ 2) / 2) / t - gaussianMillsTail t) atTop (nhds 0)
  simpa only [sub_zero] using
    gaussianMillsUpperGap_firstTerm_tendsto_atTop_zero.sub
      gaussianMillsTail_tendsto_atTop_zero

/- The Mills upper-bound gap is positive on positive arguments. -/
theorem gaussianMillsUpperGap_pos_of_pos {t : ℝ} (ht : 0 < t) :
    0 < gaussianMillsUpperGap t := by
  have hanti : StrictAntiOn gaussianMillsUpperGap (Set.Ioi 0) := by
    have hcont : ContinuousOn gaussianMillsUpperGap (Set.Ioi 0) := by
      intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact (gaussianMillsUpperGap_hasDerivAt hxpos.ne').continuousAt.continuousWithinAt
    refine strictAntiOn_of_hasDerivWithinAt_neg
      (D := Set.Ioi (0 : ℝ)) (f := gaussianMillsUpperGap)
      (f' := fun x : ℝ => -(Real.exp (-(x ^ 2) / 2) / x ^ 2))
      (convex_Ioi (0 : ℝ)) hcont ?_ ?_
    · intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact (gaussianMillsUpperGap_hasDerivAt hxpos.ne').hasDerivWithinAt
    · intro x hx
      have hxpos : 0 < x := by simpa using hx
      exact gaussianMillsUpperGap_deriv_neg hxpos
  have ht1 : t + 1 ∈ Set.Ioi (0 : ℝ) := by
    exact add_pos ht zero_lt_one
  have hnext_nonneg : 0 ≤ gaussianMillsUpperGap (t + 1) := by
    refine le_of_tendsto_of_tendsto
      gaussianMillsUpperGap_tendsto_atTop_zero tendsto_const_nhds ?_
    filter_upwards [eventually_ge_atTop (t + 1)] with y hy
    have hypos : y ∈ Set.Ioi (0 : ℝ) := by
      have : 0 < y := lt_of_lt_of_le (by linarith : 0 < t + 1) hy
      exact this
    by_cases hy_eq : y = t + 1
    · simp [hy_eq]
    · have hlt : t + 1 < y := lt_of_le_of_ne hy (Ne.symm hy_eq)
      exact le_of_lt (hanti ht1 hypos hlt)
  have hstrict : gaussianMillsUpperGap (t + 1) < gaussianMillsUpperGap t := by
    exact hanti (show t ∈ Set.Ioi (0 : ℝ) from ht) ht1 (by linarith)
  linarith

/- Classical upper Mills-ratio bound: `R(t) < 1/t` for `t > 0`. -/
theorem gaussianMillsRatio_lt_inv_of_pos {t : ℝ} (ht : 0 < t) :
    gaussianMillsRatio t < 1 / t := by
  have hgap := gaussianMillsUpperGap_pos_of_pos ht
  have htail_lt :
      gaussianMillsTail t < Real.exp (-(t ^ 2) / 2) / t := by
    simpa [gaussianMillsUpperGap, sub_pos] using hgap
  have hmul := mul_lt_mul_of_pos_left htail_lt (Real.exp_pos (t ^ 2 / 2))
  unfold gaussianMillsRatio
  calc
    Real.exp (t ^ 2 / 2) * gaussianMillsTail t
        < Real.exp (t ^ 2 / 2) * (Real.exp (-(t ^ 2) / 2) / t) := hmul
    _ = 1 / t := by
          calc
            Real.exp (t ^ 2 / 2) * (Real.exp (-(t ^ 2) / 2) / t)
                = (Real.exp (t ^ 2 / 2) * Real.exp (-(t ^ 2) / 2)) / t := by
                  ring
            _ = 1 / t := by
              rw [← Real.exp_add]
              have hsum : t ^ 2 / 2 + -(t ^ 2) / 2 = 0 := by ring
              rw [hsum, Real.exp_zero]

/- The reciprocal Mills ratio has positive derivative everywhere. -/
theorem gaussianMillsHazard_gt_arg_of_pos {t : ℝ} (ht : 0 < t) :
    t < gaussianMillsHazard t := by
  have hRlt : gaussianMillsRatio t < 1 / t :=
    gaussianMillsRatio_lt_inv_of_pos ht
  unfold gaussianMillsHazard
  exact (lt_inv_comm₀ ht (gaussianMillsRatio_pos t)).mpr
    (by simpa [one_div] using hRlt)

end

end Probability
end EconCSLib
