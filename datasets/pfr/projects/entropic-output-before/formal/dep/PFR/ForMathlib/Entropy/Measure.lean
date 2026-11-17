module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Probability.UniformOn
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory Real Set

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure on a measurable space.

We normalize the measure by `(μ Set.univ)⁻¹` to extend the entropy definition to finite measures.
What we really want to do is deal with `μ=0` or `IsProbabilityMeasure μ`, but we don't have
a typeclass for that (we could create one though).
The added complexity ∈ the expression is not an issue because if `μ` is a probability measure,
a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S := by volume_tac) : ℝ :=
  ∑' s, negMulLog (((μ Set.univ)⁻¹ • μ).real {s})

@[inherit_doc measureEntropy] notation:100 "Hm[" μ "]" => measureEntropy μ

/-- A measure has finite support if there exists a finite set whose complement has zero measure. -/
class FiniteSupport (μ : Measure S := by volume_tac) : Prop where
  finite : ∃ A : Finset S, ∀ᵐ x ∂μ, x ∈ A

instance finiteSupport_zero : FiniteSupport (0 : Measure S) := sorry

instance finiteSupport_of_fintype {μ : Measure S} [Finite S] : FiniteSupport μ := sorry

instance finiteSupport_of_mul {μ : Measure S} [FiniteSupport μ] (c : ℝ≥0∞) :
    FiniteSupport (c • μ) := sorry

section

variable [MeasurableSingletonClass S]

instance finiteSupport_of_dirac (x : S) : FiniteSupport (Measure.dirac x) := sorry

instance finiteSupport_of_finiteRange {μ : Measure Ω} {X : Ω → S} [hX' : FiniteRange X] :
    FiniteSupport (μ.map X) := sorry

instance finiteSupport_of_prod {μ : Measure S} [FiniteSupport μ] {ν : Measure T} [SigmaFinite ν]
    [FiniteSupport ν] :
    FiniteSupport (μ.prod ν) := sorry

end

variable [MeasurableSingletonClass S]

end measureEntropy

section measureMutualInfo

/-- The mutual information between the marginals of a measure on a product space. -/
noncomputable
def measureMutualInfo (μ : Measure (S × T) := by volume_tac) : ℝ :=
  Hm[μ.map Prod.fst] + Hm[μ.map Prod.snd] - Hm[μ]

/-- The mutual information between the marginals of a measure on a product space. -/
notation:100 "Im[" μ "]" => measureMutualInfo μ

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]

end measureMutualInfo

end ProbabilityTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function ProbabilityTheory

end Mathlib.Meta.Positivity
