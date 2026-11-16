import dep.Carleson.Legacy212Norm
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import dep.Carleson.ToMathlib.ENorm
import dep.Carleson.ToMathlib.Misc

noncomputable section
local instance {E : Type*} [Legacy212_ContinuousENorm E] : ContinuousENorm E where
  continuous_enorm := Legacy212_ContinuousENorm.Legacy212_continuous_enorm


open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

section move


variable {α 𝕜 E : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- todo: move/rename/and perhaps reformulate in terms of ‖.‖ₑ
lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ :=
  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)

lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ :=
  (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) :
    μ B ≤ μ A := by
  apply measure_mono_ae
  change μ {x | ¬ B x ≤ A x} = 0
  simp only [le_Prop_eq, Classical.not_imp]
  exact h

end move

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {t s x y : ℝ≥0∞}
  {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

@[gcongr only]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) :=
  fun _ _ h ↦ distribution_mono_right h

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  simp_rw [distribution]
  apply measure_mono
  simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
  intro x hx
  exact hx.trans_le Legacy212_enorm_toReal_le

lemma distribution_add_le_of_enorm {A : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  unfold distribution
  have h₁ : μ ({x | A * (t + s) < ‖f x‖ₑ} \
      ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
    apply measure_mono_null ?_ h
    intro x
    simp only [mem_diff, mem_setOf_eq, mem_union, not_or, not_lt, mem_compl_iff, not_le, and_imp]
    intro h₁ h₂ h₃
    refine lt_of_le_of_lt ?_ h₁
    gcongr
  calc
    μ {x | A * (t + s) < ‖f x‖ₑ}
      ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := measure_mono_ae' h₁
    _ ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := measure_union_le _ _

lemma approx_above_superset (t₀ : ℝ≥0∞) :
    ⋃ n, (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}) n = {x | t₀ < ‖f x‖ₑ} := by
  ext y
  constructor <;> intro h
  · obtain ⟨n, wn⟩ := exists_exists_eq_and.mp h
    calc
      t₀ ≤ t₀ + (↑n)⁻¹ := le_self_add
      _  < ‖f y‖ₑ      := wn
  · have h₁ : Iio (‖f y‖ₑ - t₀) ∈ 𝓝 0 := Iio_mem_nhds (tsub_pos_of_lt h)
    have h₂ := ENNReal.tendsto_inv_nat_nhds_zero h₁
    simp only [mem_map, mem_atTop_sets, mem_preimage, mem_Iio] at h₂
    rcases h₂ with ⟨n, wn⟩
    simp only [mem_iUnion, mem_setOf_eq]
    use n
    exact lt_tsub_iff_left.mp (wn n (Nat.le_refl n))

lemma tendsto_measure_iUnion_distribution (t₀ : ℝ≥0∞) :
    Filter.Tendsto (⇑μ ∘ (fun n : ℕ ↦ {x | t₀ + (↑n)⁻¹ < ‖f x‖ₑ}))
      Filter.atTop (nhds (μ ({x | t₀ < ‖f x‖ₑ}))) := by
  rw [← approx_above_superset]
  apply tendsto_measure_iUnion_atTop
  intro a b h x h₁
  calc
    _ ≤ t₀ + (↑a)⁻¹ := by gcongr
    _ < _ := h₁

lemma select_neighborhood_distribution (t₀ : ℝ≥0∞) (l : ℝ≥0∞)
    (hu : l < distribution f t₀ μ) :
    ∃ n : ℕ, l < distribution f (t₀ + (↑n)⁻¹) μ := by
  have h₁ : Ioi l ∈ (𝓝 (distribution f t₀ μ)) := Ioi_mem_nhds hu
  have h₂ := (tendsto_measure_iUnion_distribution t₀) h₁
  simp only [mem_map, mem_atTop_sets, mem_preimage, comp_apply, mem_Ioi] at h₂
  rcases h₂ with ⟨n, wn⟩
  use n; exact wn n (Nat.le_refl n)

lemma continuousWithinAt_distribution (t₀ : ℝ≥0∞) :
    ContinuousWithinAt (distribution f · μ) (Ioi t₀) t₀ := by
  rcases (eq_top_or_lt_top t₀) with t₀top | t₀nottop
  · rw [t₀top]
    apply continuousWithinAt_of_notMem_closure
    simp
  · unfold ContinuousWithinAt
    rcases (eq_top_or_lt_top (distribution f t₀ μ)) with db_top | db_not_top
    -- Case: distribution f t₀ μ = ⊤
    · simp only
      rw [db_top, ENNReal.tendsto_nhds_top_iff_nnreal]
      intro b
      have h₀ : ∃ n : ℕ, ↑b < distribution f (t₀ + (↑n)⁻¹) μ :=
        select_neighborhood_distribution _ _ (db_top ▸ coe_lt_top)
      rcases h₀ with ⟨n, wn⟩
      refine eventually_mem_set.mpr (mem_inf_iff_superset.mpr ⟨Iio (t₀ + (↑n)⁻¹), ?_, ?_⟩)
      · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
          (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
      · exact ⟨Ioi t₀, by simp, fun z h₁ ↦ wn.trans_le (distribution_mono_right (le_of_lt h₁.1))⟩
    -- Case: distribution f t₀ μ < ⊤
    · refine (ENNReal.tendsto_nhds db_not_top.ne_top).mpr fun ε ε_gt_0 ↦
        eventually_mem_set.mpr (mem_inf_iff_superset.mpr ?_)
      rcases eq_zero_or_pos (distribution f t₀ μ) with db_zero | db_not_zero
      -- Case: distribution f t₀ μ = 0
      · use Ico 0 (t₀ + 1)
        constructor
        · refine IsOpen.mem_nhds isOpen_Ico_zero ?_
          simp only [mem_Ico, zero_le, lt_add_right t₀nottop.ne_top one_ne_zero, and_self]
        · use Ioi t₀
          refine ⟨by simp, fun z hz ↦ ?_⟩
          rw [db_zero]
          simp only [ge_iff_le, zero_le, tsub_eq_zero_of_le, zero_add]
          have h₂ : distribution f z μ ≤ distribution f t₀ μ :=
            distribution_mono_right (le_of_lt hz.2)
          rw [db_zero] at h₂
          change Icc 0 ε (distribution f z μ)
          rw [nonpos_iff_eq_zero.mp h₂]
          exact ⟨(by positivity), (by positivity)⟩
      -- Case: 0 < distribution f t₀ μ
      · obtain ⟨n, wn⟩ :=
          select_neighborhood_distribution t₀ _ (ENNReal.sub_lt_self db_not_top.ne_top
              (ne_of_lt db_not_zero).symm (ne_of_lt ε_gt_0).symm)
        use Iio (t₀ + (↑n)⁻¹)
        constructor
        · exact Iio_mem_nhds (lt_add_right t₀nottop.ne_top
            (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)))
        · use Ioi t₀
          refine ⟨by simp, fun z h ↦ ⟨?_, ?_⟩⟩
          · calc
              distribution f t₀ μ - ε
                ≤ distribution f (t₀ + (↑n)⁻¹) μ := le_of_lt wn
              _ ≤ distribution f z μ             := distribution_mono_right (le_of_lt h.1)
          · calc
              distribution f z μ
                ≤ distribution f t₀ μ := distribution_mono_right (le_of_lt h.2)
              _ ≤ distribution f t₀ μ + ε := le_self_add

/- The lemmas below are almost already in Mathlib, see
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`. -/

-- /-- The layer-cake theorem, or Cavalieri's principle for functions into `ℝ≥0∞` -/
-- lemma lintegral_norm_pow_eq_measure_lt {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
--     {p : ℝ} (hp : 1 ≤ p) :
--     ∫⁻ x, (f x) ^ p ∂μ =
--     ∫⁻ t in Ioi (0 : ℝ), .ofReal (p * t ^ (p - 1)) * μ { x | ENNReal.ofReal t < f x } := by
--   sorry

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' (f : α → ε) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

lemma wnorm'_zero (f : α → ε) (μ : Measure α) : wnorm' f 0 μ = ∞ := by
  simp only [wnorm', GroupWithZero.inv_zero, ENNReal.rpow_zero, mul_one, iSup_eq_top]
  refine fun b hb ↦ ⟨b.toNNReal + 1, ?_⟩
  rw [coe_add, ENNReal.coe_one, coe_toNNReal hb.ne_top]
  exact lt_add_right hb.ne_top one_ne_zero

lemma wnorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    wnorm' (ENNReal.toReal ∘ f) p μ ≤ wnorm' f p μ := by
  refine iSup_mono fun x ↦ ?_
  gcongr
  exact distribution_toReal_le

/-- The weak L^p norm of a function. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

lemma wnorm_zero : wnorm f 0 μ = ∞ := by
  simp [wnorm, wnorm'_zero]

@[simp]
lemma wnorm_top : wnorm f ⊤ μ = eLpNormEssSup f μ := by simp [wnorm]

lemma wnorm_coe {p : ℝ≥0} : wnorm f p μ = wnorm' f p μ := by simp [wnorm]

lemma wnorm_ofReal {p : ℝ} (hp : 0 ≤ p) : wnorm f (.ofReal p) μ = wnorm' f p μ := by
  simp [wnorm, hp]

-- todo: move
lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  exact essSup_mono_ae (Eventually.of_forall fun x ↦ Legacy212_enorm_toReal_le)

lemma wnorm_toReal_le {f : α → ℝ≥0∞} {p : ℝ≥0∞} :
    wnorm (ENNReal.toReal ∘ f) p μ ≤ wnorm f p μ := by
  induction p
  · simp [eLpNormEssSup_toReal_le]
  refine iSup_mono fun x ↦ ?_
  gcongr
  exact distribution_toReal_le

end ENorm

section Legacy212_ContinuousENorm

variable [Legacy212_ContinuousENorm ε] [Legacy212_ContinuousENorm ε₁] [Legacy212_ContinuousENorm ε₂] {f : α → ε} {f₁ : α → ε₁}

lemma wnorm'_le_eLpNorm' (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 1 ≤ p) :
    wnorm' f p μ ≤ eLpNorm' f p μ := by
  refine iSup_le (fun t ↦ ?_)
  simp_rw [distribution, eLpNorm']
  have p0 : 0 < p := lt_of_lt_of_le one_pos hp
  have p0' : 0 ≤ 1 / p := (div_pos one_pos p0).le
  have set_eq : {x | ofNNReal t < ‖f x‖ₑ} = {x | ofNNReal t ^ p < ‖f x‖ₑ ^ p} := by
    simp [ENNReal.rpow_lt_rpow_iff p0]
  have : ofNNReal t = (ofNNReal t ^ p) ^ (1 / p) := by simp [p0.ne.symm]
  nth_rewrite 1 [inv_eq_one_div p, this, ← mul_rpow_of_nonneg _ _ p0', set_eq]
  refine rpow_le_rpow ?_ p0'
  refine le_trans ?_ <| mul_meas_ge_le_lintegral₀ (hf.enorm.pow_const p) (ofNNReal t ^ p)
  gcongr
  exact fun h ↦ h.le

lemma wnorm_le_eLpNorm (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    wnorm f p μ ≤ legacy212Norm f p μ := by
  by_cases h : p = ⊤
  · simp [h, wnorm, legacy212Norm]
  · have p0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp).ne.symm
    simpa [h, wnorm, legacy212Norm, p0] using wnorm'_le_eLpNorm' hf (toReal_mono h hp)

/-- A function is in weak-L^p if it is (strongly a.e.)-measurable and has finite weak L^p norm. -/
def MemWℒp (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  AEStronglyMeasurable f μ ∧ wnorm f p μ < ∞

lemma Legacy212MemLp.memWℒp (hp : 1 ≤ p) (hf : Legacy212MemLp f p μ) : MemWℒp f p μ :=
  ⟨hf.1, wnorm_le_eLpNorm hf.1 hp |>.trans_lt hf.2⟩

lemma MemWℒp_zero : ¬ MemWℒp f 0 μ := by
  simp [MemWℒp, wnorm_zero]

lemma MemWℒp.aeStronglyMeasurable (hf : MemWℒp f p μ) : AEStronglyMeasurable f μ :=
  hf.1

lemma MemWℒp.wnorm_lt_top (hf : MemWℒp f p μ) : wnorm f p μ < ⊤ :=
  hf.2

lemma MemWℒp.ennreal_toReal {f : α → ℝ≥0∞} (hf : MemWℒp f p μ) :
    MemWℒp (ENNReal.toReal ∘ f) p μ :=
  ⟨hf.aeStronglyMeasurable.ennreal_toReal, wnorm_toReal_le.trans_lt hf.2⟩

/-- If a function `f` is `MemWℒp`, then its norm is almost everywhere finite.-/
theorem MemWℒp.ae_ne_top {f : α → ε} {p : ℝ≥0∞} {μ : Measure α}
    (hf : MemWℒp f p μ) : ∀ᵐ x ∂μ, ‖f x‖ₑ ≠ ∞ := by
  by_cases hp_inf : p = ∞
  · rw [hp_inf] at hf
    simp_rw [← lt_top_iff_ne_top]
    exact ae_lt_of_essSup_lt hf.2
  by_cases hp_zero : p = 0
  · exact (MemWℒp_zero <| hp_zero ▸ hf).elim
  set A := {x | ‖f x‖ₑ = ∞} with hA
  unfold MemWℒp wnorm wnorm' at hf
  simp only [hp_inf] at hf
  rw [Filter.eventually_iff, mem_ae_iff]
  simp only [ne_eq, compl_def, mem_setOf_eq, Decidable.not_not, ← hA]
  have hp_toReal_zero := toReal_ne_zero.mpr ⟨hp_zero, hp_inf⟩
  have h1 (t : ℝ≥0) : μ A ≤ distribution f t μ := by
    refine μ.mono ?_
    simp_all only [setOf_subset_setOf, coe_lt_top, implies_true, A]
  set C := ⨆ t : ℝ≥0, t * distribution f t μ ^ p.toReal⁻¹
  by_cases hC_zero : C = 0
  · simp only [ENNReal.iSup_eq_zero, mul_eq_zero, ENNReal.rpow_eq_zero_iff, inv_neg'', C] at hC_zero
    specialize hC_zero 1
    simp only [one_ne_zero, ENNReal.coe_one, not_lt_of_ge toReal_nonneg, and_false, or_false,
      false_or] at hC_zero
    exact measure_mono_null (setOf_subset_setOf.mpr fun x hx => hx ▸ one_lt_top) hC_zero.1
  by_contra h
  have h2 : C < ∞ := by aesop
  have h3 (t : ℝ≥0) : distribution f t μ ≤ (C / t) ^ p.toReal := by
    rw [← rpow_inv_rpow hp_toReal_zero (distribution ..)]
    refine rpow_le_rpow ?_ toReal_nonneg
    rw [ENNReal.le_div_iff_mul_le (Or.inr hC_zero) (Or.inl coe_ne_top), mul_comm]
    exact le_iSup_iff.mpr fun _ a ↦ a t
  have h4 (t : ℝ≥0) : μ A ≤ (C / t) ^ p.toReal := (h1 t).trans (h3 t)
  have h5 : μ A ≤ μ A / 2 := by
    convert h4 (C * (2 / μ A) ^ p.toReal⁻¹).toNNReal
    rw [coe_toNNReal ?_]
    swap
    · refine mul_ne_top h2.ne_top (rpow_ne_top_of_nonneg (inv_nonneg.mpr toReal_nonneg) ?_)
      simp [div_eq_top, h]
    nth_rw 1 [← mul_one C]
    rw [ENNReal.mul_div_mul_left _ _ hC_zero h2.ne_top, div_rpow_of_nonneg _ _ toReal_nonneg,
      ENNReal.rpow_inv_rpow hp_toReal_zero, ENNReal.one_rpow, one_div,
        ENNReal.inv_div (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) (Or.inr (NeZero.ne' 2).symm)]
  have h6 : μ A = 0 := by
    convert (fun hh ↦ ENNReal.half_lt_self hh (ne_top_of_le_ne_top (rpow_ne_top_of_nonneg
      toReal_nonneg ((div_one C).symm ▸ h2.ne_top)) (h4 1))).mt (not_lt_of_ge h5)
    tauto
  exact h h6

/- Todo: define `MeasureTheory.WLp` as a subgroup, similar to `MeasureTheory.Lp` -/

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, Legacy212MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * legacy212Norm f p μ

/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, Legacy212MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ legacy212Norm (T f) p' ν ≤ c * legacy212Norm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0) : Prop :=
  ∀ f : α → ε₁, Legacy212MemLp f p μ → legacy212Norm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ legacy212Norm (T f) p' ν ≤ c * legacy212Norm f p μ

lemma HasWeakType.memWℒp (h : HasWeakType T p p' μ ν c) (hf₁ : Legacy212MemLp f₁ p μ) :
    MemWℒp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasWeakType.ennreal_toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasWeakType T p p' μ ν c) :
    HasWeakType (fun u x ↦ T u x |>.toReal) p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1.ennreal_toReal, wnorm_toReal_le.trans (h f hf).2 ⟩


lemma HasStrongType.memℒp (h : HasStrongType T p p' μ ν c) (hf₁ : Legacy212MemLp f₁ p μ) :
    Legacy212MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁).1, h f₁ hf₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasStrongType.hasWeakType (hp' : 1 ≤ p')
    (h : HasStrongType T p p' μ ν c) : HasWeakType T p p' μ ν c :=
  fun f hf ↦ ⟨(h f hf).1, wnorm_le_eLpNorm (h f hf).1 hp' |>.trans (h f hf).2⟩


lemma HasBoundedStrongType.memℒp [Zero ε₁] (h : HasBoundedStrongType T p p' μ ν c)
    (hf₁ : Legacy212MemLp f₁ p μ) (h2f₁ : legacy212Norm f₁ ∞ μ < ∞) (h3f₁ : μ (support f₁) < ∞) :
    Legacy212MemLp (T f₁) p' ν :=
  ⟨(h f₁ hf₁ h2f₁ h3f₁).1, h f₁ hf₁ h2f₁ h3f₁ |>.2.trans_lt <| mul_lt_top coe_lt_top hf₁.2⟩

lemma HasStrongType.hasBoundedStrongType [Zero ε₁] (h : HasStrongType T p p' μ ν c) :
    HasBoundedStrongType T p p' μ ν c :=
  fun f hf _ _ ↦ h f hf

end Legacy212_ContinuousENorm

section NormedGroup

-- todo: generalize various results to ENorm.

variable {f g : α → ε}
section
variable [Legacy212_ContinuousENorm ε]

lemma distribution_eq_nnnorm {f : α → E} : distribution f t μ =  μ { x | t < ‖f x‖₊ } := rfl

@[gcongr only]
lemma distribution_mono_left (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    distribution f t μ ≤ distribution g t μ := by
  have h₀ : {x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ} ⊆ {x | ¬‖f x‖ₑ ≤ ‖g x‖ₑ} := fun x ↦ by
    simp_rw [mem_diff, mem_setOf_eq, not_lt, not_le, and_imp]
    intro i₁ i₂; simpa using i₂.trans_lt i₁
  calc
    _ ≤ μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ})
      + μ ({x | t < ‖f x‖ₑ} \ {x | t < ‖g x‖ₑ}) := measure_le_inter_add_diff μ _ _
    _ = μ ({x | t < ‖f x‖ₑ} ∩ {x | t < ‖g x‖ₑ}) := by rw [measure_mono_null h₀ h, add_zero]
    _ ≤ _ := by apply measure_mono; simp

@[gcongr only]
lemma distribution_mono (h₁ : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) (h₂ : t ≤ s) :
    distribution f s μ ≤ distribution g t μ :=
  (distribution_mono_left h₁).trans (distribution_mono_right h₂)

lemma distribution_snormEssSup : distribution f (eLpNormEssSup f μ) μ = 0 :=
  meas_essSup_lt -- meas_eLpNormEssSup_lt

lemma distribution_smul_left {f : α → E} {c : 𝕜} (hc : c ≠ 0) :
    distribution (c • f) t μ = distribution f (t / ‖c‖₊) μ := by
  simp_rw [distribution_eq_nnnorm]
  have h₀ : ofNNReal ‖c‖₊ ≠ 0 := ENNReal.coe_ne_zero.mpr (nnnorm_ne_zero_iff.mpr hc)
  congr with x
  simp only [Pi.smul_apply, mem_setOf_eq]
  rw [ENNNorm_absolute_homogeneous _]
  rw [ENNReal.div_lt_iff (Or.inl h₀) (Or.inl coe_ne_top)]
  rw [mul_comm]

lemma distribution_add_le' {A : ℝ≥0∞} {g₁ g₂ : α → ε}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ := by
  apply distribution_add_le_of_enorm
  simp (discharger := positivity) [← ofReal_mul, ← ofReal_add, h]

lemma HasStrongType.const_smul {𝕜 E' α α' : Type*} [NormedAddCommGroup E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')}
    {p p' : ℝ≥0∞} {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c)
    [NormedRing 𝕜] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E'] (k : 𝕜) :
    HasStrongType (k • T) p p' μ ν (‖k‖₊ * c) := by
  refine fun f hf ↦ ⟨AEStronglyMeasurable.const_smul (h f hf).1 k, ?_⟩
  change legacy212Norm (k • T f) p' ν ≤ _
  rw [legacy212Norm_eq_current ((h f hf).1.const_smul k)]
  have hb := eLpNorm_const_smul_le (f := T f) (c := k) (p := p') (μ := ν)
  rw [← legacy212Norm_eq_current (h f hf).1] at hb
  apply hb.trans
  simp only [ENNReal.smul_def, smul_eq_mul, coe_mul, mul_assoc, enorm_eq_nnnorm]
  gcongr
  exact (h f hf).2

lemma HasStrongType.const_mul {E' α α' : Type*} [NormedRing E']
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} {T : (α → ε) → (α' → E')} {p p' : ℝ≥0∞}
    {μ : Measure α} {ν : Measure α'} {c : ℝ≥0} (h : HasStrongType T p p' μ ν c) (e : E') :
    HasStrongType (fun f x ↦ e * T f x) p p' μ ν (‖e‖₊ * c) :=
  h.const_smul e

end

lemma distribution_add_le [Legacy212_ENormedAddMonoid ε] :
    distribution (f + g) (t + s) μ ≤ distribution f t μ + distribution g s μ :=
  calc
    _ ≤ μ ({x | t < ↑‖f x‖ₑ} ∪ {x | s < ↑‖g x‖ₑ}) := by
      refine measure_mono fun x h ↦ ?_
      simp only [mem_union, mem_setOf_eq, Pi.add_apply] at h ⊢
      contrapose! h
      exact (Legacy212_enorm_add_le _ _).trans (add_le_add h.1 h.2)
    _ ≤ _ := measure_union_le _ _

lemma _root_.ContinuousLinearMap.distribution_le {f : α → E₁} {g : α → E₂} :
    distribution (fun x ↦ L (f x) (g x)) (‖L‖₊ * t * s) μ ≤
    distribution f t μ + distribution g s μ := by
  unfold distribution
  have h₀ : {x | ↑‖L‖₊ * t * s < ↑‖(fun x ↦ (L (f x)) (g x)) x‖₊} ⊆
      {x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊} := fun z hz ↦ by
    simp only [mem_union, mem_setOf_eq, Pi.add_apply] at hz ⊢
    contrapose! hz
    calc
      (‖(L (f z)) (g z)‖₊ : ℝ≥0∞) ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ := by
        refine (toNNReal_le_toNNReal coe_ne_top coe_ne_top).mp ?_
        simp only [toNNReal_coe, coe_mul, toNNReal_mul]
        calc
          _ ≤ ↑‖L (f z)‖₊ * ↑‖g z‖₊ := ContinuousLinearMap.le_opNNNorm (L (f z)) (g z)
          _ ≤ ‖L‖₊ * ‖f z‖₊ * ‖g z‖₊ :=
            mul_le_mul' (ContinuousLinearMap.le_opNNNorm L (f z)) (by rfl)
      _ ≤ _ := mul_le_mul' (mul_le_mul_right hz.1 _) hz.2
  calc
    _ ≤ μ ({x | t < ↑‖f x‖₊} ∪ {x | s < ↑‖g x‖₊}) := measure_mono h₀
    _ ≤ _ := measure_union_le _ _

section BorelSpace

variable [Legacy212_ContinuousENorm ε] [MeasurableSpace E] [BorelSpace E]

/-- The layer-cake theorem, or Cavalieri's principle for functions into a normed group. -/
lemma lintegral_norm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ =
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (p * t ^ (p - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 ≤ p := hp.le
  have := lintegral_rpow_eq_lintegral_meas_lt_mul μ (f := fun x ↦ ‖f x‖)
    (Eventually.of_forall fun x ↦ norm_nonneg _) hf.norm hp
  simp only [enorm_eq_nnnorm, norm_nonneg, ← ofReal_rpow_of_nonneg, mul_comm (μ _), ne_eq,
    ofReal_ne_top, not_false_eq_true, ← lintegral_const_mul', ← mul_assoc,
    ← ofReal_norm, ofReal_mul, distribution, h2p] at this ⊢
  convert this using 1
  · simp only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    congr 2
    ext x
    simp only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)

/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy212Norm`. -/
lemma eLpNorm_pow_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ≥0} (hp : 0 < p) :
    legacy212Norm f p μ ^ (p : ℝ) =
    ∫⁻ t in Ioi (0 : ℝ), p * ENNReal.ofReal (t ^ ((p : ℝ) - 1)) * distribution f (.ofReal t) μ := by
  have h2p : 0 < (p : ℝ) := hp
  simp_rw [legacy212Norm_nnreal_eq_eLpNorm' hp.ne', eLpNorm', one_div, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ h2p.ne', ENNReal.rpow_one, lintegral_norm_pow_eq_distribution hf h2p,
    ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal]

/-- The layer-cake theorem, or Cavalieri's principle, written using `legacy212Norm`, without
    taking powers. -/
lemma eLpNorm_eq_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    legacy212Norm f (.ofReal p) μ =
    (ENNReal.ofReal p  * ∫⁻ t in Ioi (0 : ℝ), distribution f (.ofReal t) μ *
        ENNReal.ofReal (t ^ (p - 1)) ) ^ p⁻¹ := by
  unfold legacy212Norm
  split_ifs with sgn_p sz_p
  · exact False.elim (not_le.mpr hp (ofReal_eq_zero.mp sgn_p))
  · exact False.elim (coe_ne_top sz_p)
  · unfold eLpNorm'
    rw [toReal_ofReal (le_of_lt hp), one_div]
    congr 1
    rw [← lintegral_const_mul']
    on_goal 2 => exact coe_ne_top
    rw [lintegral_norm_pow_eq_distribution hf hp]
    congr 1 with x; rw [ofReal_mul] <;> [ring; positivity]

lemma lintegral_pow_mul_distribution {f : α → E} (hf : AEMeasurable f μ) {p : ℝ} (hp : -1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ p) * distribution f (.ofReal t) μ =
    ENNReal.ofReal (p + 1)⁻¹ * ∫⁻ x, ‖f x‖ₑ ^ (p + 1) ∂μ := by
  have h2p : 0 < p + 1 := by linarith
  have h3p : 0 ≤ p + 1 := by linarith
  have h4p : p + 1 ≠ 0 := by linarith
  rw [ENNReal.ofReal_inv_of_pos h2p]
  rw [lintegral_norm_pow_eq_distribution hf h2p, ← lintegral_const_mul' _ _ (by simp [h2p])]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [add_sub_cancel_right, ENNReal.ofReal_mul h3p, ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel (a := ENNReal.ofReal (p+1)) (by positivity) ENNReal.ofReal_ne_top, one_mul]

end BorelSpace

end NormedGroup

end MeasureTheory
