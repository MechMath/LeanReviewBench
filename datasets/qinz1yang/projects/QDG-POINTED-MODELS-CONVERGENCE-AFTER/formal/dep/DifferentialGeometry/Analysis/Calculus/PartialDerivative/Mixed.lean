import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped Topology ContDiff

namespace DifferentialGeometry

section ModelMixed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem model_spatial_fderiv_eq
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (s : ℝ) (x V : E) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V)  := by sorry

private theorem model_spatial_fderiv_eq_of_contDiffAt
    (F : ℝ -> E -> ℝ)
    {s : ℝ} {x V : E}
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (s, x)) :
    (fderiv ℝ (F s) x) V =
      (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (s, x)) (0, V)  := by sorry

private theorem model_hasDerivAt_fixed_snd
    (A : ℝ × E -> ℝ) (t : ℝ) (x : E)
    (hA : DifferentiableAt ℝ A (t, x)) :
    HasDerivAt (fun s : ℝ => A (s, x))
      ((fderiv ℝ A (t, x)) (1, 0)) t  := by sorry

theorem modelLine_fst_hasDerivAt
    {A : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hA : DifferentiableAt ℝ A (s, t)) :
    HasDerivAt (fun σ : ℝ => A (σ, t))
      ((fderiv ℝ A (s, t)) ((1 : ℝ), 0)) s  := by sorry

theorem modelLine_snd_hasDerivAt
    {A : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hA : DifferentiableAt ℝ A (s, t)) :
    HasDerivAt (fun τ : ℝ => A (s, τ))
      ((fderiv ℝ A (s, t)) (0, (1 : ℝ))) t  := by sorry

theorem fixedBaseFDerivTimeDerivativeAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    (t : ℝ) (x V : E) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t  := by sorry

theorem fixedBaseFDerivTimeDerivativeAt_of_contDiffAt
    (F : ℝ -> E -> ℝ)
    {t : ℝ} {x V : E}
    (hF : ContDiffAt ℝ 2 (fun p : ℝ × E => F p.1 p.2) (t, x)) :
    HasDerivAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      t  := by sorry

theorem fixedBaseFDerivTimeDerivativeWithinAt_of_contDiff
    (F : ℝ -> E -> ℝ)
    (hF : ContDiff ℝ 2 (fun p : ℝ × E => F p.1 p.2))
    {timeSet : Set ℝ} {t : ℝ}
    (x V : E) :
    HasDerivWithinAt
      (fun s : ℝ => (fderiv ℝ (F s) x) V)
      ((fderiv ℝ
        (fun y : E =>
          (fderiv ℝ (fun p : ℝ × E => F p.1 p.2) (t, y)) (1, 0))
        x) V)
      timeSet
      t  := by sorry

theorem fderiv_fst_fderiv_snd_eq_fderiv_snd_fderiv_fst
    {φ : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hφ : ContDiffAt ℝ 2 φ (s, t)) :
    (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ φ p) (0, (1 : ℝ))) (s, t))
        ((1 : ℝ), 0) =
      (fderiv ℝ (fun p : ℝ × ℝ => (fderiv ℝ φ p) ((1 : ℝ), 0)) (s, t))
        (0, (1 : ℝ))  := by sorry

theorem fderiv_fst_fderiv_snd_fderiv_snd_eq_fderiv_snd_fderiv_fst_fderiv_snd
    {φ : ℝ × ℝ -> ℝ} {s t : ℝ}
    (hφ : ContDiffAt ℝ 3 φ (s, t)) :
    (fderiv ℝ
        (fun p : ℝ × ℝ =>
          (fderiv ℝ (fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ))) p)
            (0, (1 : ℝ))) (s, t))
        ((1 : ℝ), 0) =
      (fderiv ℝ
        (fun p : ℝ × ℝ =>
          (fderiv ℝ (fun q : ℝ × ℝ => (fderiv ℝ φ q) (0, (1 : ℝ))) p)
            ((1 : ℝ), 0)) (s, t))
        (0, (1 : ℝ))  := by sorry

end ModelMixed

end DifferentialGeometry

