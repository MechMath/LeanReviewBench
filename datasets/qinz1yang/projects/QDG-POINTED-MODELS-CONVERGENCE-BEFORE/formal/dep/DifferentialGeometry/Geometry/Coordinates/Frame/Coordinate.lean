import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import dep.DifferentialGeometry.Tensor.RSTensor.Coordinates.FieldComponents
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry.Tensor.Coordinates

open Set Bundle DifferentialGeometry.Tensor0SBundle Filter
open scoped Topology Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev CoordinateIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [hfinite : FiniteDimensional 𝕜 E] :=
  let _ := hfinite
  Fin (Module.finrank 𝕜 E)

structure LocalChartAt (x₀ : M) where
  chart : OpenPartialHomeomorph M H
  mem_source : x₀ ∈ chart.source
  mem_max : chart ∈ IsManifold.maximalAtlas I (∞ : WithTop ℕ∞) M
  triv : Trivialization E (π E (TangentSpace I : M -> Type _))
  triv_mem : MemTrivializationAtlas triv
  triv_baseSet_eq : triv.baseSet = chart.source

namespace LocalChartAt


def source {x₀ : M} (C : LocalChartAt (I := I) x₀) : Set M :=
  C.chart.source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem source_open {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    IsOpen C.source  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem triv_baseSet {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.triv.baseSet = C.source  := by sorry

def default (x₀ : M) : LocalChartAt (I := I) x₀ where
  chart := chartAt H x₀
  mem_source := mem_chart_source H x₀
  mem_max := IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : WithTop ℕ∞)) x₀
  triv := trivializationAt E (TangentSpace I : M -> Type _) x₀
  triv_mem := inferInstance
  triv_baseSet_eq := by
    simp only [TangentBundle.trivializationAt_baseSet]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_mem (x₀ : M) :
    x₀ ∈ (LocalChartAt.default (I := I) x₀).source  := by sorry

def ext {x₀ : M} (C : LocalChartAt (I := I) x₀) : PartialEquiv M E :=
  C.chart.extend I

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    C.ext.source = C.source  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_ext_source {x₀ : M} (C : LocalChartAt (I := I) x₀) :
    x₀ ∈ C.ext.source  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem default_ext (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).ext = extChartAt I x₀  := by sorry

def overlap {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : Set M :=
  C.source ∩ D.source

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem overlap_open {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    IsOpen (C.overlap D)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem mem_overlap {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    x ∈ C.overlap D ↔ x ∈ C.source ∧ x ∈ D.source  := by sorry

def change {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) : PartialEquiv E E :=
  ModelWithCorners.extendCoordChange (I := I) C.chart D.chart

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_symm {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    (C.change D).symm = D.change C  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem change_smooth {x₀ x₁ : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) :
    ContDiffOn 𝕜 (∞ : WithTop ℕ∞) (C.change D) (C.change D).source  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem ext_mem_change {x₀ x₁ x : M} (C : LocalChartAt (I := I) x₀)
    (D : LocalChartAt (I := I) x₁) (hx : x ∈ C.overlap D) :
    C.ext x ∈ (C.change D).source  := by sorry

def vec {x₀ : M} (C : LocalChartAt (I := I) x₀) {x : M}
    (hx : x ∈ C.source) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    TangentSpace I x := by
  have hx_ext : x ∈ C.ext.source := by
    simpa [source] using hx
  have hleft : C.ext.symm (C.ext x) = x := C.ext.left_inv hx_ext
  exact hleft ▸
    ((mfderiv[Set.range I] C.ext.symm (C.ext x)) ((Module.finBasis 𝕜 E) i))

end LocalChartAt


abbrev coordinateTrivializationAt
    (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  trivializationAt E (TangentSpace I : M -> Type _) x₀

namespace LocalChartAt


abbrev defaultTriv (x₀ : M) :
    Trivialization E (π E (TangentSpace I : M -> Type _)) :=
  (LocalChartAt.default (I := I) x₀).triv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
@[simp]
theorem default_triv (x₀ : M) :
    LocalChartAt.defaultTriv (I := I) x₀ =
      coordinateTrivializationAt (I := I) x₀  := by sorry

end LocalChartAt

def coordinateFrameAt (x₀ : M) :
    CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x :=
  (coordinateTrivializationAt (I := I) x₀).localFrame (Module.finBasis 𝕜 E)


def coordinateFrameSet (x₀ : M) : Set M :=
  (coordinateTrivializationAt (I := I) x₀).baseSet

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameSet_open (x₀ : M) :
    IsOpen (coordinateFrameSet (I := I) x₀)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem coordinateFrameAt_mem (x₀ : M) :
    x₀ ∈ coordinateFrameSet (I := I) x₀  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_isLocalFrame (x₀ : M) :
    IsLocalFrameOn I E (∞ : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀)  := by sorry

namespace LocalChartAt

structure Frame {x₀ : M} (C : LocalChartAt (I := I) x₀) where
  domain : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  isLocalFrame : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame domain
  isOpen_domain : IsOpen domain
  mem_base : x₀ ∈ domain
  domain_subset_source : domain ⊆ C.source

namespace Frame


omit [CompleteSpace 𝕜] in
theorem mem_source {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) :
    x ∈ C.source  := by sorry

def basisAt {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame) {x : M}
    (hx : x ∈ F.domain) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  F.isLocalFrame.toBasisAt hx

omit [CompleteSpace 𝕜] in
theorem basisAt_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {x : M} (hx : x ∈ F.domain) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    F.basisAt hx i = F.frame i x  := by sorry

end Frame

def toFrame {x₀ : M} (C : LocalChartAt (I := I) x₀) : C.Frame where
  domain := C.triv.baseSet
  frame := by
    haveI : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.localFrame (Module.finBasis 𝕜 E)
  isLocalFrame := by
    have : MemTrivializationAtlas C.triv := C.triv_mem
    exact C.triv.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (Module.finBasis 𝕜 E)
  isOpen_domain := C.triv.open_baseSet
  mem_base := by
    rw [C.triv_baseSet]
    exact C.mem_source
  domain_subset_source := by
    intro x hx
    rw [C.triv_baseSet] at hx
    exact hx


def defaultFrame (x₀ : M) : (LocalChartAt.default (I := I) x₀).Frame where
  domain := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  isLocalFrame := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_domain := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  domain_subset_source := by
    intro x hx
    have hx_triv : x ∈ (trivializationAt E (TangentSpace I : M -> Type _) x₀).baseSet := by
      change x ∈ coordinateFrameSet (I := I) x₀
      exact hx
    rw [TangentBundle.trivializationAt_baseSet] at hx_triv
    exact hx_triv

omit [CompleteSpace 𝕜] in
theorem defaultFrame_domain (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).domain =
      coordinateFrameSet (I := I) x₀  := by sorry

omit [CompleteSpace 𝕜] in
theorem defaultFrame_frame (x₀ : M) :
    (LocalChartAt.defaultFrame (I := I) x₀).frame =
      coordinateFrameAt (I := I) x₀  := by sorry

end LocalChartAt


omit [CompleteSpace 𝕜] in
lemma coordinateFrameAt_isLocalFrame_one (x₀ : M) :
    IsLocalFrameOn I E (1 : WithTop ℕ∞)
      (coordinateFrameAt (I := I) x₀) (coordinateFrameSet (I := I) x₀)  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_mdifferentiableAt (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    MDiffAt (T% (coordinateFrameAt (I := I) x₀ i)) x₀  := by sorry

def coordinateFrameAtBasis (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x) :=
  (coordinateFrameAt_isLocalFrame (I := I) x₀).toBasisAt hx

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_basis_apply (x₀ : M) {x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAtBasis (I := I) x₀ hx i =
      coordinateFrameAt (I := I) x₀ i x  := by sorry

def coordinateFrameAtToBasis (x₀ : M) :
    Module.Basis (CoordinateIdx (𝕜 := 𝕜) E) 𝕜 (TangentSpace I x₀) :=
  coordinateFrameAtBasis (I := I) x₀ (coordinateFrameAt_mem (I := I) x₀)

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordinateFrameAt_toBasis_apply (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAtToBasis (I := I) x₀ i =
      coordinateFrameAt (I := I) x₀ i x₀  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_coeff_eq_toBasis_coord
    (x₀ : M) (Z : TangentSpace I x₀) (j : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff j x₀ Z =
      (coordinateFrameAtToBasis (I := I) x₀).coord j Z  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_apply_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    coordinateFrameAt (I := I) x₀ i x =
      (mfderiv[Set.range I] (extChartAt I x₀).symm (extChartAt I x₀ x))
        ((Module.finBasis 𝕜 E) i)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
theorem LocalChartAt.default_source (x₀ : M) :
    (LocalChartAt.default (I := I) x₀).source =
      coordinateFrameSet (I := I) x₀  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_basis_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt
        𝕜 x ((coordinateFrameAtBasis (I := I) x₀ hx) i) =
      (Module.finBasis 𝕜 E) i  := by sorry

omit [CompleteSpace 𝕜] in
theorem basisRepr_eq_triv
    (x₀ : M) {x : M} (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) :
    (coordinateFrameAtBasis (I := I) x₀ hx).repr v =
      (Module.finBasis 𝕜 E).repr
        ((coordinateTrivializationAt (I := I) x₀).continuousLinearMapAt 𝕜 x v)  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_toBasis_eq_finBasis (x₀ : M) :
    coordinateFrameAtToBasis (I := I) x₀ = Module.finBasis 𝕜 E  := by sorry

def normalCoordLinearEquiv (x : M) : TangentSpace I x ≃L[𝕜] E :=
  ContinuousLinearEquiv.refl 𝕜 E


def normalCoord (x : M) (v : TangentSpace I x) : E :=
  normalCoordLinearEquiv (I := I) x v

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalCoord_zero (x : M) :
    normalCoord (I := I) x (0 : TangentSpace I x) = 0  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
theorem normalCoord_injective (x : M) :
    Function.Injective (normalCoord (I := I) x)  := by sorry

def normalHCoord (x : M) (v : TangentSpace I x) : H :=
  I.symm (normalCoord (I := I) x v)

def normalHCoordHomeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₜ H :=
  (normalCoordLinearEquiv (I := I) x).toHomeomorph.trans I.toHomeomorph.symm

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordHomeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordHomeomorph (I := I) x v = normalHCoord (I := I) x v  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem model_normalHCoord [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    I (normalHCoord (I := I) x v) = normalCoord (I := I) x v  := by sorry

def modelSymmDiffeomorph [I.Boundaryless] :
    E ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, E), I⟯ H where
  toEquiv := I.toHomeomorph.symm.toEquiv
  contMDiff_toFun := by
    rw [← contMDiffOn_univ]
    have h := I.contMDiffOn_symm (n := (∞ : WithTop ℕ∞))
    rw [ModelWithCorners.range_eq_univ (I := I)] at h
    exact h.congr fun _ _ => rfl
  contMDiff_invFun := I.contMDiff

def normalHCoordDiffeomorph [I.Boundaryless] (x : M) :
    TangentSpace I x ≃ₘ^(∞ : WithTop ℕ∞)⟮𝓘(𝕜, TangentSpace I x), I⟯ H :=
  (normalCoordLinearEquiv (I := I) x).toDiffeomorph.trans
    (modelSymmDiffeomorph (I := I))

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_apply [I.Boundaryless]
    (x : M) (v : TangentSpace I x) :
    normalHCoordDiffeomorph (I := I) x v = normalHCoord (I := I) x v  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [IsManifold I ∞ M] in
@[simp]
theorem normalHCoordDiffeomorph_toHomeomorph [I.Boundaryless] (x : M) :
    (normalHCoordDiffeomorph (I := I) x).toHomeomorph =
      normalHCoordHomeomorph (I := I) x  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordCoeff_eq_chart {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (v : TangentSpace I x) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    (coordinateFrameAt_isLocalFrame_one (I := I) x₀).coeff i x v =
      (Module.finBasis 𝕜 E).repr
        ((mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x) v) i  := by sorry

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const (x₀ : M) (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x₀)]
        fun _ : E => (Module.finBasis 𝕜 E i : E)  := by sorry

omit [CompleteSpace 𝕜] in
private theorem coordinateFrame_pullback_eq_const_of_mem {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (coordinateFrameAt (I := I) x₀ i) (Set.range I)
      =ᶠ[𝓝[Set.range I] (extChartAt I x₀ x)]
        fun _ : E => (Module.finBasis 𝕜 E i : E)  := by sorry

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
private theorem lieBracketWithin_const_const {s : Set E} {x v w : E} :
    VectorField.lieBracketWithin 𝕜 (fun _ : E => v) (fun _ : E => w) s x = 0  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordinateFrameAt_bracket_zero (x₀ : M) (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x₀ = 0  := by sorry

theorem coordinateFrameAt_bracket_zero_of_mem [IsRCLikeNormedField 𝕜] {x₀ x : M}
    (hx : x ∈ coordinateFrameSet (I := I) x₀)
    (i j : CoordinateIdx (𝕜 := 𝕜) E) :
    VectorField.mlieBracket I
      (coordinateFrameAt (I := I) x₀ i)
      (coordinateFrameAt (I := I) x₀ j) x = 0  := by sorry

structure CoordinateFrameAt (x₀ : M) where
  domain : Set M
  frame : CoordinateIdx (𝕜 := 𝕜) E -> (x : M) -> TangentSpace I x
  isLocalFrame : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame domain
  isOpen_domain : IsOpen domain
  mem_base : x₀ ∈ domain
  bracket_zero : ∀ i j : CoordinateIdx (𝕜 := 𝕜) E,
    VectorField.mlieBracket I (frame i) (frame j) x₀ = 0


def canonicalCoordinateFrameAt (x₀ : M) : CoordinateFrameAt (I := I) x₀ where
  domain := coordinateFrameSet (I := I) x₀
  frame := coordinateFrameAt (I := I) x₀
  isLocalFrame := coordinateFrameAt_isLocalFrame (I := I) x₀
  isOpen_domain := coordinateFrameSet_open (I := I) x₀
  mem_base := coordinateFrameAt_mem (I := I) x₀
  bracket_zero := coordinateFrameAt_bracket_zero (I := I) x₀

namespace LocalChartAt
namespace Frame


def comp0S {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (F.basisAt hx) A slots

omit [CompleteSpace 𝕜] in
theorem comp0S_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {s : ℕ} {x : M} (hx : x ∈ F.domain)
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.comp0S hx A slots =
      A (fun a => F.basisAt hx (slots a))  := by sorry

def compRS {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRSField (I := I) (F.basisAt hx) T upper lower

theorem compRS_apply {x₀ : M} {C : LocalChartAt (I := I) x₀} (F : C.Frame)
    {r s : ℕ} {x : M} (hx : x ∈ F.domain)
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    F.compRS hx T upper lower =
      componentRSField (I := I) (F.basisAt hx) T upper lower  := by sorry

end Frame
end LocalChartAt


def coordComponent0SAt {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  component0S (I := I) (coordinateFrameAtToBasis (I := I) x₀) A slots

omit [CompleteSpace 𝕜] in
@[simp]
theorem coordComponent0SAt_apply {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponent0SAt (I := I) A slots =
      A (fun a => coordinateFrameAtToBasis (I := I) x₀ (slots a))  := by sorry

def coordComponentRSAt {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) : 𝕜 :=
  componentRSField (I := I) (coordinateFrameAtToBasis (I := I) x₀) T upper lower

@[simp]
theorem coordComponentRSAt_apply {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E) (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    coordComponentRSAt (I := I) T upper lower =
      componentRSField (I := I) (coordinateFrameAtToBasis (I := I) x₀) T upper lower  := by sorry

omit [CompleteSpace 𝕜] in
theorem coordComponent0SAt_congr_slots {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    {slots slots' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (h : slots = slots') :
    coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) A slots'  := by sorry

theorem coordComponentRSAt_congr_slots {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    {upper upper' : Fin r -> CoordinateIdx (𝕜 := 𝕜) E}
    {lower lower' : Fin s -> CoordinateIdx (𝕜 := 𝕜) E}
    (hu : upper = upper') (hl : lower = lower') :
    coordComponentRSAt (I := I) T upper lower =
      coordComponentRSAt (I := I) T upper' lower'  := by sorry

theorem coordExt0SAt {s : ℕ} {x₀ : M}
    {A B : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀}
    (h : ∀ slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponent0SAt (I := I) A slots = coordComponent0SAt (I := I) B slots) :
    A = B  := by sorry

theorem coordExtRSAt {r s : ℕ} {x₀ : M}
    {A B : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀}
    (h : ∀ upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E,
         ∀ lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E,
      coordComponentRSAt (I := I) A upper lower =
        coordComponentRSAt (I := I) B upper lower) :
    A = B  := by sorry

namespace LocalChartAt
namespace Frame

omit [CompleteSpace 𝕜] in
theorem default_comp0S {s : ℕ} {x₀ : M}
    (A : Tensor0SSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) s x₀)
    (slots : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).comp0S
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base A slots =
      coordComponent0SAt (I := I) A slots  := by sorry

theorem default_compRS {r s : ℕ} {x₀ : M}
    (T : TensorRSSpace (𝕜 := 𝕜) (E := E) (H := H) (I := I) (M := M) r s x₀)
    (upper : Fin r -> CoordinateIdx (𝕜 := 𝕜) E)
    (lower : Fin s -> CoordinateIdx (𝕜 := 𝕜) E) :
    (LocalChartAt.defaultFrame (I := I) x₀).compRS
        (LocalChartAt.defaultFrame (I := I) x₀).mem_base T upper lower =
      coordComponentRSAt (I := I) T upper lower  := by sorry

end Frame
end LocalChartAt

end DifferentialGeometry.Tensor.Coordinates

