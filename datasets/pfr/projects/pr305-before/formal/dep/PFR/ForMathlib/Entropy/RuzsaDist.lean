module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
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

@[expose] public section

open Filter Function MeasureTheory Measure ProbabilityTheory

open scoped Topology

variable {Ω Ω' Ω'' Ω''' G S T : Type*}
  [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [mΩ' : MeasurableSpace Ω'] {μ' : Measure Ω'}
  [mΩ'' : MeasurableSpace Ω''] {μ'' : Measure Ω''}
  [mΩ''' : MeasurableSpace Ω'''] {μ''' : Measure Ω'''}
  [hG : MeasurableSpace G]

variable [AddCommGroup G]
  {X : Ω → G} {Y : Ω' → G} {Z : Ω'' → G}

/-- The Ruzsa distance `rdist X Y` or `d[X ; Y]` between two random variables is defined as
`H[X'- Y'] - H[X']/2 - H[Y']/2`, where `X', Y'` are independent copies of `X, Y`. -/
noncomputable
def rdist (X : Ω → G) (Y : Ω' → G) (μ : Measure Ω := by volume_tac)
    (μ' : Measure Ω' := by volume_tac) : ℝ :=
  H[fun x ↦ x.1 - x.2 ; (μ.map X).prod (μ'.map Y)] - H[X ; μ]/2 - H[Y ; μ']/2

@[inherit_doc rdist] notation3:max "d[" X "; " μ " # " Y "; " μ' "]" => rdist X Y μ μ'

@[inherit_doc rdist] notation3:max "d[" X " # " Y "]" => rdist X Y volume volume

section rdist

variable [Countable G] [MeasurableSingletonClass G]

variable [FiniteRange X] [FiniteRange Y]

end rdist

variable [MeasurableSpace S] [MeasurableSpace T] [Countable G] [MeasurableSingletonClass G]

/-- The conditional Ruzsa distance `d[X|Z ; Y|W]`. -/
noncomputable
def condRuzsaDist (X : Ω → G) (Z : Ω → S) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ]
    (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  dk[condDistrib X Z μ ; μ.map Z # condDistrib Y W μ' ; μ'.map W]

@[inherit_doc condRuzsaDist]
notation3:max "d[" X " | " Z " ; " μ " # " Y " | " W " ; " μ'"]" => condRuzsaDist X Z Y W μ μ'

@[inherit_doc condRuzsaDist]
notation3:max "d[" X " | " Z " # " Y " | " W "]" => condRuzsaDist X Z Y W volume volume

variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]

variable [Countable S]

/-- The conditional Ruzsa distance `d[X ; Y|W]`. -/
noncomputable
def condRuzsaDist' (X : Ω → G) (Y : Ω' → G) (W : Ω' → T)
    (μ : Measure Ω := by volume_tac) (μ' : Measure Ω' := by volume_tac) [IsFiniteMeasure μ'] : ℝ :=
  dk[Kernel.const Unit (μ.map X) ; Measure.dirac () # condDistrib Y W μ' ; μ'.map W]

@[inherit_doc condRuzsaDist']
notation3:max "d[" X " ; " μ " # " Y " | " W " ; " μ' "]" => condRuzsaDist' X Y W μ μ'

@[inherit_doc condRuzsaDist']
notation3:max "d[" X " # " Y " | " W "]" => condRuzsaDist' X Y W volume volume

open scoped ENNReal

section

variable [Countable T]

end

section BalogSzemerediGowers

end BalogSzemerediGowers
