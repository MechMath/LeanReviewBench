import dep.DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import dep.DifferentialGeometry.Geometry.Curvature.Sections.Connection
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.MixedComponents
import dep.DifferentialGeometry.Tensor.SlotAlgebra
import dep.DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.CurvatureAction
import dep.DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Basic
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Tensor.RicciIdentity

attribute [local instance] Fintype.ofFinite Classical.propDecidable

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.SlotAlgebra
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev Tensor0SSection (s : ℕ) :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) s

abbrev OneFormSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 1

abbrev TwoTensorSection :=
  Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    (∞ : WithTop ℕ∞) 2

def NablaOneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : (x : M) ->
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 2 x)
    (x : M) : Prop :=
  ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
      (Y : TangentSpace I x),
    nablaAlpha x (vec2 (X x) Y) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        1 cov X alpha x (fun _ : Fin 1 => Y)

def NablaOneFormRealizes
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M)) : Prop :=
  ∀ x : M, NablaOneFormRealizesAt (I := I) cov alpha (fun y => nablaAlpha y) x

def Nabla2OneFormRealizesAt
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  NablaOneFormRealizes (I := I) cov alpha nablaAlpha ∧
    ∀ (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
        (Y Z : TangentSpace I x),
      nabla2Alpha (vec3 (X x) Y Z) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 cov X nablaAlpha x (vec2 Y Z)

theorem nabla2OneFormRealizesAt_first
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha) :
    NablaOneFormRealizes (I := I) cov alpha nablaAlpha  := by sorry

theorem nabla2OneFormRealizesAt_apply
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (x : M)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x nabla2Alpha)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _))
    (Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 (X x) Y Z) =
      nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 cov X nablaAlpha x (vec2 Y Z)  := by sorry

theorem nabla2OneFormRealizesAt_of_totalNabla
    [IsManifold I 1 M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (alpha : OneFormSection (I := I) (M := M))
    (nablaAlpha : TwoTensorSection (I := I) (M := M))
    (nabla2AlphaSec :
      Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 3)
    (h1 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 1 cov alpha nablaAlpha)
    (h2 : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 2 cov nablaAlpha nabla2AlphaSec)
    (x : M) :
    Nabla2OneFormRealizesAt (I := I) cov alpha nablaAlpha x
      (nabla2AlphaSec x)  := by sorry

def Nabla2DuTrailingSymmCoord {Idx : Type*}
    (U : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i j k : Idx, U i j k = U i k j

def OneFormRicciIdentityCoord {Idx : Type*}
    (U curvatureAction : Idx -> Idx -> Idx -> Real) : Prop :=
  ∀ i k j : Idx, U i k j - U k i j = curvatureAction i k j

def CurvatureActionTraceEqualsRicGradCoord {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real) : Prop :=
  ∀ k : Idx,
    (∑ i : Idx, ∑ j : Idx, gInv i j * curvatureAction i k j) = ricGrad k

theorem oneFormRicciTraceCommCoord_of_identities {Idx : Type*} [Fintype Idx]
    (gInv : Idx -> Idx -> Real)
    (U curvatureAction : Idx -> Idx -> Idx -> Real)
    (ricGrad : Idx -> Real)
    (h_symm : Nabla2DuTrailingSymmCoord U)
    (h_comm : OneFormRicciIdentityCoord U curvatureAction)
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv curvatureAction ricGrad) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx, gInv i j * U i j k) =
        (∑ i : Idx, ∑ j : Idx, gInv i j * U k i j) + ricGrad k  := by sorry

def OneFormThirdCovDerivCommAt
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z)

theorem one_form_third_covDeriv_comm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) - nabla2Alpha (vec3 Y X Z) =
      -Rm13 x alpha (vec3 X Y Z)  := by sorry

def swapFirstTwo0S {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x :=
  A.domDomCongr (Equiv.swap (0 : Fin 3) 1)

omit [FiniteDimensional ℝ E] in
@[simp] theorem swapFirstTwo0S_apply_vec3 {x : M}
    (A : Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (X Y Z : TangentSpace I x) :
    swapFirstTwo0S (I := I) A (vec3 X Y Z) = A (vec3 Y X Z)  := by sorry

theorem one_form_third_comm_of_coord
    {Idx : Type*} [Finite Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ slots : Fin 3 -> Idx,
      nabla2Alpha (fun a => basis (slots a)) -
        nabla2Alpha (fun a => basis (slots ((Equiv.swap (0 : Fin 3) 1) a))) =
          -Rm13 x alpha (fun a => basis (slots a))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

theorem one_form_third_comm_of_coord_ijk
    {Idx : Type*} [Finite Idx]
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcoord : ∀ i k j : Idx,
      nabla2Alpha (vec3 (basis i) (basis k) (basis j)) -
        nabla2Alpha (vec3 (basis k) (basis i) (basis j)) =
          -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

def OneFormLastTwoSymmAt {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ X Y Z : TangentSpace I x,
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y)

omit [FiniteDimensional ℝ E] in
theorem one_form_last_two_symm {x : M}
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (X Y Z : TangentSpace I x) :
    nabla2Alpha (vec3 X Y Z) = nabla2Alpha (vec3 X Z Y)  := by sorry

def traceNablaOneFormAt
    {Idx : Type*} [Fintype Idx]
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (Y : TangentSpace I x) : Real :=
  ∑ i : Idx, ∑ j : Idx,
    gInv i j * nabla2Alpha (vec3 Y (basis i) (basis j))

def OneFormRicciTraceCommWithVectorAt
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Prop :=
  ∀ Y : TangentSpace I x,
    roughLap1FormAt (I := I) basis gInv nabla2Alpha Y =
      traceNablaOneFormAt (I := I) basis gInv nabla2Alpha Y +
        Ric x (vec2 Y curvatureVector)

def nabla2OneFormCoord
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (i j k : Idx) : Real :=
  nabla2Alpha (vec3 (basis i) (basis j) (basis k))

def curvatureActionOnOneFormCoord
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (i k j : Idx) : Real :=
  -Rm13 x alpha (vec3 (basis i) (basis k) (basis j))

def ricciVectorCoord
    {Idx : Type*}
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (curvatureVector : TangentSpace I x)
    (k : Idx) : Real :=
  Ric x (vec2 (basis k) curvatureVector)

omit [FiniteDimensional ℝ E] in
theorem nabla2OneFormTrailingSymmCoord_of_tensor
    {Idx : Type*}
    {x : M} (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha) :
    Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)  := by sorry

theorem oneFormRicciIdentityCoord_of_tensor
    {Idx : Type*}
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)  := by sorry

theorem oneFormRicciTraceComm_basisCoord_of_identities
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h_symm : Nabla2DuTrailingSymmCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha))
    (h_comm : OneFormRicciIdentityCoord
      (nabla2OneFormCoord (I := I) basis nabla2Alpha)
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis))
    (h_trace : CurvatureActionTraceEqualsRicGradCoord gInv
      (curvatureActionOnOneFormCoord (I := I) Rm13 alpha basis)
      (ricciVectorCoord (I := I) Ric basis curvatureVector)) :
    ∀ k : Idx,
      (∑ i : Idx, ∑ j : Idx,
        gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha i j k) =
        (∑ i : Idx, ∑ j : Idx,
          gInv i j * nabla2OneFormCoord (I := I) basis nabla2Alpha k i j) +
          ricciVectorCoord (I := I) Ric basis curvatureVector k  := by sorry

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem metricTraceInput_one_eq_vec3 {x : M}
    (X Y Z : TangentSpace I x) :
    metricTraceInput (I := I) X Y (fun _ : Fin 1 => Z) = vec3 X Y Z  := by sorry

theorem oneForm_ricci_trace_comm_of_third_comm
    {Idx : Type*} [Fintype Idx]
    (Ric : Tensor02Section (I := I) (M := M))
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (curvatureVector : TangentSpace I x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (hsymm : OneFormLastTwoSymmAt (I := I) nabla2Alpha)
    (hcomm : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha)
    (hcurv : ∀ Y : TangentSpace I x,
      -∑ i : Idx, ∑ j : Idx,
        gInv i j * Rm13 x alpha (vec3 (basis i) Y (basis j)) =
          Ric x (vec2 Y curvatureVector)) :
    OneFormRicciTraceCommWithVectorAt (I := I) Ric basis gInv curvatureVector
      nabla2Alpha  := by sorry

def RicciIdentityOneFormAt
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x) : Prop :=
  ∀ Y : TangentSpace I x,
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector)

theorem ricci_identity_one_form
    (Ric : Tensor02Section (I := I) (M := M))
    {x : M}
    (roughAlpha dLapAlpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (curvatureVector : TangentSpace I x)
    (h : RicciIdentityOneFormAt (I := I) Ric roughAlpha dLapAlpha curvatureVector)
    (Y : TangentSpace I x) :
    roughAlpha (fun _ : Fin 1 => Y) =
      dLapAlpha (fun _ : Fin 1 => Y) + Ric x (vec2 Y curvatureVector)  := by sorry

theorem tensor0S_ricciIdentity_one_of_oneForm
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

theorem oneFormThirdCovDerivCommAt_of_tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x)
    (h : Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha) :
    OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

theorem tensor0S_ricciIdentity_one
    (Rm13 : Tensor13Section (I := I) (M := M))
    {x : M}
    (alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 1 x)
    (nabla2Alpha :
      Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) 3 x) :
    Tensor0SRicciIdentityAt (I := I) Rm13 alpha nabla2Alpha ↔
      OneFormThirdCovDerivCommAt (I := I) Rm13 alpha nabla2Alpha  := by sorry

end DifferentialGeometry.Tensor.RicciIdentity

