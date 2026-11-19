import dep.DifferentialGeometry.Tensor.RSTensor.Evaluation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem eval02_slots_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (m : Fin 2 -> TangentSpace I x) (v w : TangentSpace I x)
    (h0 : m 0 = v) (h1 : m 1 = w) :
    A m = eval02 (I := I) (M := M) A v w  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem quad02_add_smul_eq
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v w : TangentSpace I x} {a : Real}
    (hsym : eval02 (I := I) (M := M) A w v =
      eval02 (I := I) (M := M) A v w) :
    quad02 (I := I) (M := M) A (v + a • w) =
      quad02 (I := I) (M := M) A v +
        2 * a * eval02 (I := I) (M := M) A v w +
        a * a * quad02 (I := I) (M := M) A w  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_left
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A v w = 0  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem psd_null_right
    {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    {v : TangentSpace I x}
    (hsym : ∀ u w : TangentSpace I x,
      eval02 (I := I) (M := M) A u w = eval02 (I := I) (M := M) A w u)
    (hpsd : ∀ u : TangentSpace I x, 0 ≤ quad02 (I := I) (M := M) A u)
    (hnull : quad02 (I := I) (M := M) A v = 0) :
    ∀ w : TangentSpace I x, eval02 (I := I) (M := M) A w v = 0  := by sorry

end DifferentialGeometry

