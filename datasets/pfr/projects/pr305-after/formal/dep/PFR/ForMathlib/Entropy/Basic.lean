module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Insert
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
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
public import dep.PFR.ForMathlib.Entropy.Kernel.Basic
public import dep.PFR.ForMathlib.Entropy.Kernel.MutualInfo
public import dep.PFR.ForMathlib.Entropy.Measure
public import dep.PFR.ForMathlib.FiniteRange.Defs
public import dep.PFR.ForMathlib.Pair
public import dep.PFR.ForMathlib.Uniform
public import dep.PFR.Mathlib.MeasureTheory.Constructions.Pi
public import dep.PFR.Mathlib.MeasureTheory.Measure.Prod
public import dep.PFR.Mathlib.Probability.IdentDistrib
public import dep.PFR.Mathlib.Probability.Independence.Basic
public import dep.PFR.Mathlib.Probability.Kernel.Composition.Comp
public import dep.PFR.Mathlib.Probability.Kernel.Disintegration

@[expose] public section

open Function MeasureTheory Measure Real

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

section entropy

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) (μ : Measure Ω := by volume_tac) := Hm[μ.map X]

@[inherit_doc entropy] notation3:max "H[" X "; " μ "]" => entropy X μ

@[inherit_doc entropy] notation3:max "H[" X "]" => entropy X volume

@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "; " μ "]" => entropy X (μ[|Y ← y])

@[inherit_doc entropy] notation3:max "H[" X " | " Y " ← " y "]" => entropy X (ℙ[|Y ← y])

open Set

open Function

variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]

variable [Countable T]

end entropy

section condEntropy

variable [MeasurableSpace T]

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  (μ.map Y)[fun y ↦ H[X | Y ← y ; μ]]

@[inherit_doc condEntropy] notation3:max "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

@[inherit_doc condEntropy] notation3:max "H[" X " | " Y "]" => condEntropy X Y volume

section

variable [MeasurableSingletonClass T]

variable [Countable T] [Nonempty T] [Nonempty S] [MeasurableSingletonClass S] [Countable S]
  [Countable U] [MeasurableSingletonClass U]

end

variable [MeasurableSingletonClass T]

variable [MeasurableSingletonClass S]

variable [Countable S]

end condEntropy

section pair

variable [MeasurableSpace T]

variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

end pair

section mutualInfo

variable [MeasurableSpace T]

/-- The mutual information `I[X : Y]` of two random variables
is defined to be `H[X] + H[Y] - H[X ; Y]`. -/
noncomputable
def mutualInfo (X : Ω → S) (Y : Ω → T) (μ : Measure Ω := by volume_tac) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]

@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

@[inherit_doc mutualInfo] notation3:max "I[" X " : " Y "]" => mutualInfo X Y volume

/-- The conditional mutual information `I[X : Y| Z]` is the mutual information of `X| Z=z` and
`Y| Z=z`, integrated over `z`. -/
noncomputable
def condMutualInfo (X : Ω → S) (Y : Ω → T) (Z : Ω → U) (μ : Measure Ω := by volume_tac) :
    ℝ := (μ.map Z)[fun z ↦ H[X | Z ← z ; μ] + H[Y | Z ← z ; μ] - H[⟨X, Y⟩ | Z ← z ; μ]]

@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z ";" μ "]" => condMutualInfo X Y Z μ

@[inherit_doc condMutualInfo]
notation3:max "I[" X " : " Y "|" Z "]" => condMutualInfo X Y Z volume

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable S] [Countable T]

variable [Countable U] [MeasurableSingletonClass U] [Nonempty S] [Nonempty T]

end

section

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable S] [Countable T]

variable [MeasurableSingletonClass U]

end

section IsProbabilityMeasure

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable U] [MeasurableSingletonClass U]

variable (μ)

variable [Countable S] [Countable T]

variable [IsZeroOrProbabilityMeasure μ]

end IsProbabilityMeasure

end mutualInfo

end ProbabilityTheory

section dataProcessing

open Function MeasureTheory Measure Real

open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ProbabilityTheory

universe uΩ uS uT uU uV uW

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}

end ProbabilityTheory

end dataProcessing

section MeasureSpace_example

open ProbabilityTheory

variable {Ω S T : Type*} [MeasureSpace Ω] [IsZeroOrProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  [Fintype T] [Nonempty T] [MeasurableSpace T] [MeasurableSingletonClass T]
  {X : Ω → S} {Y : Ω → T}

end MeasureSpace_example
