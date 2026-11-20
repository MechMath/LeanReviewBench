import Mathlib

noncomputable section
open Set MeasureTheory Filter intervalIntegral
open scoped ENNReal NNReal Topology InnerProductSpace
namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

def timeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) T)

abbrev timeL2 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : Type _ :=
  MeasureTheory.Lp X 2 (timeMeasure T)

def timeH1 (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (T : ℝ) : Type _ :=
  WithLp 2 (X × timeL2 X T)

namespace timeH1

instance : NormedAddCommGroup (timeH1 X T) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (X × timeL2 X T)))

instance : NormedSpace ℝ (timeH1 X T) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (X × timeL2 X T)))

instance : InnerProductSpace ℝ (timeH1 X T) :=
  inferInstanceAs (InnerProductSpace ℝ (WithLp 2 (X × timeL2 X T)))

instance : CompleteSpace (timeH1 X T) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (X × timeL2 X T)))

def init (u : timeH1 X T) : X :=
  (WithLp.ofLp u).1

def deriv (u : timeH1 X T) : timeL2 X T :=
  (WithLp.ofLp u).2

def toFun (u : timeH1 X T) : ℝ → X :=
  fun t => u.init + ∫ s in (0 : ℝ)..t, u.deriv s

end timeH1
end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

theorem maxreg_l2deriv_to_pointwise_hasderivwithinat
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {T : ℝ} (u : timeH1 X T) {g : ℝ → X}
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) T))
    (hrep : u.deriv =ᵐ[timeMeasure T] g) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt u.toFun (g t) (Set.Ici (0 : ℝ)) t := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
