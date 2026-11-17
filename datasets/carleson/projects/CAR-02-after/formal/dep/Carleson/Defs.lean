import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Data.Real.StarOrdered
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Holder
import dep.Carleson.Legacy297Norm
import dep.Carleson.ToMathlib.CoverByBalls
import dep.Carleson.ToMathlib.DoublingMeasure
import dep.Carleson.ToMathlib.ENorm
import dep.Carleson.ToMathlib.WeakType

open MeasureTheory Measure Metric Complex Set TopologicalSpace Bornology Function ENNReal

open scoped NNReal

noncomputable section

section DoublingMeasure

universe u

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X]

section localOscillation

/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ≥0∞ :=
  ⨆ z ∈ E ×ˢ E, ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖

variable {E : Set X} {f g : C(X, 𝕜)}

end localOscillation

lemma fact_isCompact_ball (x : X) (r : ℝ) : Fact (IsBounded (ball x r)) := sorry

attribute [local instance] fact_isCompact_ball

/-- A class stating that continuous functions have distances associated to every ball.
We use a separate type to conveniently index these functions. -/
class FunctionDistances (𝕜 : outParam Type*) (X : Type u)
    [NormedField 𝕜] [TopologicalSpace X] where
  Θ : Type u
  coeΘ : Θ → C(X, 𝕜)
  coeΘ_injective {f g : Θ} (h : ∀ x, coeΘ f x = coeΘ g x) : f = g
  metric : ∀ (_x : X) (_r : ℝ), PseudoMetricSpace Θ

export FunctionDistances (Θ coeΘ)

section FunctionDistances

variable [FunctionDistances 𝕜 X]

instance : Coe (Θ X) C(X, 𝕜) := ⟨FunctionDistances.coeΘ⟩

instance : FunLike (Θ X) X 𝕜 where
  coe := fun f ↦ (f : C(X, 𝕜))
  coe_injective _ _ hfg := FunctionDistances.coeΘ_injective fun x ↦ congrFun hfg x

instance : ContinuousMapClass (Θ X) X 𝕜 := sorry

set_option linter.unusedVariables false in
@[nolint unusedArguments]
abbrev WithFunctionDistance (x : X) (r : ℝ) := Θ X

variable {x : X} {r : ℝ}

instance [d : FunctionDistances 𝕜 X] : PseudoMetricSpace (WithFunctionDistance x r) :=
  d.metric x r

end FunctionDistances

notation3 "dist_{" x " ," r "}" => @dist (WithFunctionDistance x r) _

notation3 "nndist_{" x " ," r "}" => @nndist (WithFunctionDistance x r) _

notation3 "ball_{" x " ," r "}" => @ball (WithFunctionDistance x r) _ in

/-- A set `Θ` of (continuous) functions is compatible. `A` will usually be `2 ^ a`. -/
class CompatibleFunctions (𝕜 : outParam Type*) (X : Type u) (A : outParam ℕ)
  [RCLike 𝕜] [PseudoMetricSpace X] extends FunctionDistances 𝕜 X where
  eq_zero : ∃ o : X, ∀ f : Θ, coeΘ f o = 0
  /-- The distance is bounded below by the local oscillation. (1.0.7) -/
  localOscillation_le_cdist {x : X} {r : ℝ} {f g : Θ} :
    localOscillation (ball x r) (coeΘ f) (coeΘ g) ≤ ENNReal.ofReal (dist_{x, r} f g)
  /-- The distance is monotone in the ball. (1.0.9) -/
  cdist_mono {x₁ x₂ : X} {r₁ r₂ : ℝ} {f g : Θ}
    (h : ball x₁ r₁ ⊆ ball x₂ r₂) : dist_{x₁, r₁} f g ≤ dist_{x₂, r₂} f g
  /-- The distance of a ball with large radius is bounded above. (1.0.8) -/
  cdist_le {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h : dist x₁ x₂ < 2 * r) :
    dist_{x₂, 2 * r} f g ≤ A * dist_{x₁, r} f g
  /-- The distance of a ball with large radius is bounded below. (1.0.10) -/
  le_cdist {x₁ x₂ : X} {r : ℝ} {f g : Θ} (h1 : ball x₁ r ⊆ ball x₂ (A * r)) :
    /-(h2 : A * r ≤ Metric.diam (univ : Set X))-/
    2 * dist_{x₁, r} f g ≤ dist_{x₂, A * r} f g
  /-- The distance of a ball with large radius is bounded below. (1.0.11) -/
  ballsCoverBalls {x : X} {r R : ℝ} :
    BallsCoverBalls (X := WithFunctionDistance x r) (2 * R) R A

instance nonempty_Space [CompatibleFunctions 𝕜 X A] : Nonempty X := sorry

instance inhabited_Space [CompatibleFunctions 𝕜 X A] : Inhabited X :=
  ⟨nonempty_Space.some⟩

export CompatibleFunctions (localOscillation_le_cdist cdist_mono cdist_le le_cdist)

variable (X) in
/-- The point `o` in the blueprint -/
def cancelPt [CompatibleFunctions 𝕜 X A] : X :=
  CompatibleFunctions.eq_zero (𝕜 := 𝕜) |>.choose

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜} [NormedField 𝕜] (ϕ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖ϕ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖ϕ x - ϕ y‖ₑ / edist x y

variable [hXA : DoublingMeasure X A]

variable (X) in
/-- Θ is τ-cancellative. `τ` will usually be `1 / a` -/
class IsCancellative (τ : ℝ) [CompatibleFunctions ℝ X A] : Prop where
  /- We register a definition with strong assumptions, which makes them easier to prove.
  However, `enorm_integral_exp_le` removes them for easier application. -/
  enorm_integral_exp_le' {x : X} {r : ℝ} {ϕ : X → ℂ} (hr : 0 < r) (h1 : iLipENorm ϕ x r ≠ ∞)
    (h2 : tsupport ϕ ⊆ ball x r) {f g : Θ X} :
    ‖∫ x, exp (I * (f x - g x)) * ϕ x‖ₑ ≤
    (A : ℝ≥0∞) * volume (ball x r) * iLipENorm ϕ x r * (1 + nndist_{x, r} f g) ^ (- τ)

/-- The "volume function" `V`. Preferably use `vol` instead. -/
protected def Real.vol {X : Type*} [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

/-- `R_Q(θ, x)` defined in (1.0.20). -/
def upperRadius [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X) (x : X) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : dist_{x, r} θ (Q x) < 1), ENNReal.ofReal r

/-- The linearized maximally truncated nontangential Calderon Zygmund operator `T_Q^θ` -/
def linearizedNontangentialOperator [FunctionDistances ℝ X] (Q : X → Θ X) (θ : Θ X)
    (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (x' : X) (_ : dist x x' ≤ R₁),
  ‖∫ y in {y | ENNReal.ofReal (dist x' y) ∈ Ioo (ENNReal.ofReal R₁) (upperRadius Q θ x')},
    K x' y * f y‖₊

/-- The maximally truncated nontangential Calderon Zygmund operator `T_*` -/
def nontangentialOperator (K : X → X → ℂ) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : R₁ < R₂) (x' : X) (_ : dist x x' < R₁),
  ‖∫ y in {y | dist x' y ∈ Ioo R₁ R₂}, K x' y * f y‖₊

/-- The linearized generalized Carleson operator `T_Q`, taking values in `ℝ≥0∞`.
Use `ENNReal.toReal` to get the corresponding real number. -/
def linearizedCarlesonOperator [FunctionDistances ℝ X] (Q : X → Θ X) (K : X → X → ℂ)
    (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (R₁ : ℝ) (R₂ : ℝ) (_ : 0 < R₁) (_ : R₁ < R₂),
  ‖∫ y in {y | dist x y ∈ Ioo R₁ R₂}, K x y * f y * exp (I * Q x y)‖₊

end DoublingMeasure

/-- This is usually the value of the argument `A` in `DoublingMeasure`
and `CompatibleFunctions` -/
@[simp] abbrev defaultA (a : ℕ) : ℕ := 2 ^ a

@[simp] def defaultD (a : ℕ) : ℕ := 2 ^ (100 * a ^ 2)

@[simp] def defaultκ (a : ℕ) : ℝ := 2 ^ (-10 * (a : ℝ))

@[simp] def defaultZ (a : ℕ) : ℕ := 2 ^ (12 * a)

@[simp] def defaultτ (a : ℕ) : ℝ := a⁻¹

section Kernel

variable {X : Type*} {a : ℕ} {K : X → X → ℂ} [PseudoMetricSpace X] [MeasureSpace X]

open Function

/-- The constant used twice in the definition of the Calderon-Zygmund kernel. -/
@[simp] def C_K (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- `K` is a one-sided Calderon-Zygmund kernel
In the formalization `K x y` is defined everywhere, even for `x = y`. The assumptions on `K` show
that `K x x = 0`.

Todo: maybe make enorm_K_le_vol_inv + enorm_K_sub_le + K_eq_zero_of_dist_eq_zero the axioms. -/
class IsOneSidedKernel (a : outParam ℕ) (K : X → X → ℂ) : Prop where
  measurable_K : Measurable (uncurry K)
  norm_K_le_vol_inv (x y : X) : ‖K x y‖ ≤ C_K a / Real.vol x y
  norm_K_sub_le {x y y' : X} (h : 2 * dist y y' ≤ dist x y) :
    ‖K x y - K x y'‖ ≤ (dist y y' / dist x y) ^ (a : ℝ)⁻¹ * (C_K a / Real.vol x y)

export IsOneSidedKernel (measurable_K norm_K_le_vol_inv norm_K_sub_le)

end Kernel

def C_Ts (a : ℝ) : ℝ≥0 := 2 ^ a ^ 3

/-- Data common through most of chapters 2-9. -/
class PreProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
  (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X] where
  d : DoublingMeasure X (defaultA a)
  four_le_a : 4 ≤ a
  cf : CompatibleFunctions ℝ X (defaultA a)
  c : IsCancellative X (defaultτ a)
  hcz : IsOneSidedKernel a K
  hasBoundedStrongType_Tstar :
    HasBoundedStrongType (nontangentialOperator K · ·) 2 2 volume volume (C_Ts a)
  measurableSet_F : MeasurableSet F
  measurableSet_G : MeasurableSet G
  measurable_σ₁ : Measurable σ₁
  measurable_σ₂ : Measurable σ₂
  finite_range_σ₁ : Finite (range σ₁)
  finite_range_σ₂ : Finite (range σ₂)
  σ₁_le_σ₂ : σ₁ ≤ σ₂
  Q : SimpleFunc X (Θ X)
  q_mem_Ioc : q ∈ Ioc 1 2

export PreProofData (four_le_a hasBoundedStrongType_Tstar measurableSet_F measurableSet_G
  measurable_σ₁ measurable_σ₂ finite_range_σ₁ finite_range_σ₂ σ₁_le_σ₂ Q q_mem_Ioc)

attribute [instance] PreProofData.d PreProofData.cf PreProofData.c PreProofData.hcz

section ProofData

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [PseudoMetricSpace X] [PreProofData a q K σ₁ σ₂ F G]

section Iterate

end Iterate

include a q K σ₁ σ₂ F G

variable (X) in
lemma S_spec : ∃ n : ℕ, ∀ x, -n ≤ σ₁ x ∧ σ₂ x ≤ n := sorry

section DBounds

variable (X)

open Classical in
def defaultS : ℕ := Nat.find (S_spec X)

end DBounds

variable (X)

include X in
lemma τ_nonneg : 0 ≤ defaultτ a := sorry

/-- `τ` as an element of `ℝ≥0`. -/
def nnτ : ℝ≥0 := ⟨defaultτ a, τ_nonneg X⟩

include X in
lemma q_nonneg : 0 ≤ q := sorry

/-- `q` as an element of `ℝ≥0`. -/
def nnq : ℝ≥0 := ⟨q, q_nonneg X⟩

end ProofData

class ProofData {X : Type*} (a : outParam ℕ) (q : outParam ℝ) (K : outParam (X → X → ℂ))
    (σ₁ σ₂ : outParam (X → ℤ)) (F G : outParam (Set X)) [PseudoMetricSpace X]
    extends PreProofData a q K σ₁ σ₂ F G where
  F_subset : F ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4)
  G_subset : G ⊆ ball (cancelPt X) (defaultD a ^ defaultS X / 4)
  /- The next two conditions are not in the blueprint, but will be useful in various steps.
  It is easy to prove finitary_carleson (or metric_carleson) separately when either of these
  fails. -/
  volume_F_pos : 0 < volume F
  volume_G_pos : 0 < volume G

namespace ShortVariables

set_option hygiene false

scoped notation "D" => defaultD a

scoped notation "κ" => defaultκ a

scoped notation "Z" => defaultZ a

scoped notation "τ" => defaultτ a

scoped notation "o" => cancelPt X

scoped notation "S" => defaultS X

scoped notation "nnτ" => nnτ X

scoped notation "nnq" => nnq X

end ShortVariables

open scoped ShortVariables

variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}

variable (a) in
/-- `D` as an element of `ℝ≥0`. -/
def nnD : ℝ≥0 := ⟨D, sorry⟩

namespace ShortVariables

set_option hygiene false

scoped notation "nnD" => nnD a

end ShortVariables

section PseudoMetricSpace

variable [PseudoMetricSpace X] [h : ProofData a q K σ₁ σ₂ F G]

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace X] [ProofData a q K σ₁ σ₂ F G]

end MetricSpace
