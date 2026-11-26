module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Kernel.IndepFun
public import Mathlib.Tactic.Basic
public import Mathlib.Util.Notation3
public import dep.PFR.ForMathlib.Pair
public import dep.PFR.Mathlib.Probability.Independence.Basic

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} [MeasureSpace Ω]
  {G : Type*} [hG : MeasurableSpace G]

variable {Z₁ Z₂ Z₃ : Ω → G} (h_indep : iIndepFun ![Z₁, Z₂, Z₃])

include h_indep

private abbrev κ : Fin 2 → Type
  | 0 => Fin 1
  | 1 => Fin 2

private instance fintype_kappa : ∀ (i : Fin 2), Fintype (κ i)
  | 0 | 1 => inferInstanceAs (Fintype (Fin _))

end ProbabilityTheory.iIndepFun
