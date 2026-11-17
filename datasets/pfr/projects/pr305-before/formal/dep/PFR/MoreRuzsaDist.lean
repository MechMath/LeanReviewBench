module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Finiteness
public import Mathlib.Util.Notation3
public import dep.PFR.ForMathlib.ConditionalIndependence
public import dep.PFR.ForMathlib.Entropy.Basic
public import dep.PFR.ForMathlib.Entropy.Kernel.Basic
public import dep.PFR.ForMathlib.Entropy.Kernel.MutualInfo
public import dep.PFR.ForMathlib.Entropy.Kernel.RuzsaDist
public import dep.PFR.ForMathlib.Entropy.Measure
public import dep.PFR.ForMathlib.Entropy.RuzsaDist
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.ForMathlib.Pair
public import dep.PFR.ForMathlib.Uniform
public import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
public import dep.PFR.Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import dep.PFR.Mathlib.MeasureTheory.Measure.Prod
public import dep.PFR.Mathlib.Probability.IdentDistrib
public import dep.PFR.Mathlib.Probability.Independence.Basic
public import dep.PFR.Mathlib.Probability.Kernel.Composition.Comp
public import dep.PFR.Mathlib.Probability.Kernel.Disintegration

public section

open Filter Function MeasureTheory Measure ProbabilityTheory

universe uG

variable {Ω Ω' Ω'' Ω''' S T : Type*} {G : Type uG}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G] [MeasurableSingletonClass G] [AddCommGroup G] [Countable G]
  [Countable S] [MeasurableSpace S]
  [Countable T] [MeasurableSpace T]

variable {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

section multiDistance

open Filter Function MeasureTheory Measure ProbabilityTheory

variable {G : Type uG} [hG : MeasurableSpace G] [AddCommGroup G]

/-- Let `X_[m] = (X₁, ..., Xₘ)` be a non-empty finite tuple of `G`-valued random variables `X_i`.
Then we define `D[X_[m]] = H[∑ i, X_i'] - 1/m*∑ i, H[X_i']`, where the `X_i'` are independent copies
of the `X_i`. -/
@[expose] noncomputable def multiDist {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i))
    (X : ∀ i, Ω i → G) : ℝ :=
  H[fun x ↦ ∑ i, x i; .pi (fun i ↦ (hΩ i).volume.map (X i))] - (m:ℝ)⁻¹ * ∑ i, H[X i]

@[inherit_doc multiDist] notation3:max "D[" X "; " hΩ "]" => multiDist hΩ X

variable [MeasurableSingletonClass G] [Countable G]

/-- If `X_[m] = (X_1, ..., X_m)` and `Y_[m] = (Y_1, ..., Y_m)` are tuples of random variables,
with the `X_i` being `G`-valued (but the `Y_i` need not be), then we define
`D[X_[m] | Y_[m]] = ∑_{(y_i)_{1 \leq i \leq m}} (∏ i, p_{Y_i}(y_i)) D[(X_i | Y_i = y_i)_{i=1}^m]`
where each `y_i` ranges over the support of `p_{Y_i}` for `1 ≤ i ≤ m`.
-/
@[expose]
noncomputable
def condMultiDist {m : ℕ} {Ω : Fin m → Type*} (hΩ : ∀ i, MeasureSpace (Ω i)) {S : Type*} [Fintype S]
    (X : ∀ i, Ω i → G) (Y : ∀ i, Ω i → S) : ℝ :=
  ∑ ω : Fin m → S,
    (∏ i, volume.real (Y i ⁻¹' {ω i})) * D[X; fun i ↦ ⟨cond (hΩ i).volume (Y i ⁻¹' {ω i})⟩]

@[inherit_doc multiDist] notation3:max "D[" X " | " Y " ; " hΩ "]" => condMultiDist hΩ X Y

end multiDistance

section multiDistance_chainRule

end multiDistance_chainRule
