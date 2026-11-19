import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Realization
import dep.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Tensor.RicciIdentity

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor0S_commutator_expansion_from_realizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (Xsec Ysec : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (Vsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _))
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    let X : TangentSpace I x := Xsec x
    let Y : TangentSpace I x := Ysec x
    let slots : Fin s → TangentSpace I x := fun q => Vsec q x
    nabla2Alpha (metricTraceInput (I := I) X Y slots) -
        nabla2Alpha (metricTraceInput (I := I) Y X slots) =
      curvatureAction0SAt (I := I) Rm13 alpha X Y slots -
        torsionCorrection0SAt (I := I) nablaAlpha (cov.torsion x X Y) slots  := by sorry

theorem tensor0S_ricciIdentity_with_torsion
    [IsManifold I 1 M] [IsManifold I 2 M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha) :
    Tensor0SRicciIdentityWithTorsionAt (I := I) Rm13 alpha nablaAlpha
      nabla2Alpha (fun X Y => cov.torsion x X Y)  := by sorry

theorem tensor0S_ricciIdentity_of_torsionFree
    [IsManifold I 1 M] [IsManifold I 2 M]
    [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (1 : WithTop ℕ∞))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {s : ℕ}
    (alphaSec : Tensor0SSection (I := I) (M := M) s)
    (nablaAlphaSec : Tensor0SSection (I := I) (M := M) (s + 1))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x)
    (nablaAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 1) x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (hRm13 : rm13RealizesConnection (I := I) cov Rm13)
    (halpha : alphaSec x = alpha)
    (hnablaAlpha : nablaAlphaSec x = nablaAlpha)
    (hnabla2 : Nabla20SRealizesAt (I := I) s cov alphaSec nablaAlphaSec x
      nabla2Alpha)
    (htor : cov.torsion x = 0) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

def RicciIdentity0SAt {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x) :
    Prop :=
  comm = curvatureAction

omit [FiniteDimensional ℝ E] in
theorem ricci_identity_0s {x : M} {s : ℕ}
    (comm curvatureAction :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) (s + 2) x)
    (h : RicciIdentity0SAt (I := I) comm curvatureAction) :
    comm = curvatureAction  := by sorry

end DifferentialGeometry.Tensor.RicciIdentity

