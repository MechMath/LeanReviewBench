import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.Cases
import dep.LearningTheory.Rademacher.Defs
import dep.LearningTheory.Rademacher.Symmetrization

open Real Function MeasureTheory

open scoped ENNReal

universe u v w

variable (n : ℕ) (k l : Fin n)

local instance : Inhabited { z : ℤ // z ∈ ({-1, 1} : Finset ℤ) } :=
  ⟨⟨1, sorry⟩⟩

local instance : Inhabited (Signs n) :=
  ⟨fun _ => ⟨1, sorry⟩⟩

noncomputable def signVecPMF (n : ℕ) : PMF (Signs n) :=
  PMF.uniformOfFintype (Signs n)

variable {ι : Type v} {𝒳 : Type w}

@[reducible] noncomputable instance : MeasurableSpace (Signs n) := MeasurableSpace.pi

local notation3 "𝙋" => (signVecPMF n).toMeasure
