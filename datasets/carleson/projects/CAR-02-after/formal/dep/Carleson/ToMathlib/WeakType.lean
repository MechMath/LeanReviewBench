import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Holder
import dep.Carleson.Legacy297Norm
import dep.Carleson.ToMathlib.ENorm

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

section move

variable {α 𝕜 E : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  {p : ℝ≥0∞}

end move

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0∞}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  {t s x y : ℝ≥0∞} {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/-- The distribution function of a function `f`.
Todo: rename to something more Mathlib-appropriate. -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

/-- The weak L^p norm of a function, for `p < ∞` -/
def wnorm' (f : α → ε) (p : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  ⨆ t : ℝ≥0, t * distribution f t μ ^ (p : ℝ)⁻¹

/-- The weak L^p norm of a function. -/
def wnorm (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = ∞ then eLpNormEssSup f μ else wnorm' f (ENNReal.toReal p) μ

end ENorm

section ContinuousENorm

variable [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε₁] [ContinuousENorm ε₁]
    [TopologicalSpace ε₂] [ContinuousENorm ε₂] [TopologicalSpace ε₃] [ContinuousENorm ε₃]
    {f : α → ε} {f₁ : α → ε₁}

/-- An operator has weak type `(p, q)` if it is bounded as a map from L^p to weak-L^q.
`HasWeakType T p p' μ ν c` means that `T` has weak type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasWeakType (T : (α → ε₁) → (α' → ε₂)) (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α')
    (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, Legacy297MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ wnorm (T f) p' ν ≤ c * legacy297Norm f p μ

/-- An operator has strong type (p, q) if it is bounded as an operator on `L^p → L^q`.
`HasStrongType T p p' μ ν c` means that `T` has strong type (p, p') w.r.t. measures `μ`, `ν`
and constant `c`.  -/
def HasStrongType {α α' : Type*}
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, Legacy297MemLp f p μ → AEStronglyMeasurable (T f) ν ∧ legacy297Norm (T f) p' ν ≤ c * legacy297Norm f p μ

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def HasBoundedStrongType {α α' : Type*} [Zero ε₁]
    {_x : MeasurableSpace α} {_x' : MeasurableSpace α'} (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, Legacy297MemLp f p μ → legacy297Norm f ∞ μ < ∞ → μ (support f) < ∞ →
  AEStronglyMeasurable (T f) ν ∧ legacy297Norm (T f) p' ν ≤ c * legacy297Norm f p μ

lemma HasWeakType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasWeakType T p p' μ ν c) :
    HasWeakType (T · · |>.toReal) p p' μ ν c := sorry

lemma HasStrongType.toReal {T : (α → ε₁) → (α' → ℝ≥0∞)} (h : HasStrongType T p p' μ ν c) :
    HasStrongType (T · · |>.toReal) p p' μ ν c := sorry

section distribution

variable {f g : α → ε}

end distribution

end ContinuousENorm

section NormedGroup

variable {f g : α → ε}

section

variable [TopologicalSpace ε] [ContinuousENorm ε]

variable [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [MulActionWithZero 𝕜 E'] [IsBoundedSMul 𝕜 E']

end

variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]

section BorelSpace

variable [TopologicalSpace ε] [ContinuousENorm ε]
  [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

end BorelSpace

end NormedGroup

end MeasureTheory
