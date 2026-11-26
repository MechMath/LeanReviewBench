import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Tilted
import Mathlib.Probability.Notation
import Mathlib.Tactic.Cases

open MeasureTheory ProbabilityTheory

variable {𝓧 : Type*}

variable {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {X' : Fin m → Ω → 𝓧} {f' : (Fin m → 𝓧) → ℝ}

variable {c' : Fin m → ℝ}

variable {m𝓧 : MeasurableSpace 𝓧}

variable [hnonempty𝓧 : Nonempty 𝓧]

variable {ι : Type*} [DecidableEq ι]

variable  [Fintype ι]

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)
