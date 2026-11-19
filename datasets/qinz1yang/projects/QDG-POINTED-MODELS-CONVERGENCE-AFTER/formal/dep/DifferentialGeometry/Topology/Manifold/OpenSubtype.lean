import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem hasMFDerivAt_subtype_val (U : TopologicalSpace.Opens M) (x : U) :
    HasMFDerivAt I I (Subtype.val : U → M) x (ContinuousLinearMap.id Real E)  := by sorry

theorem mfderiv_subtype_val
    (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I I (Subtype.val : U → M) x = ContinuousLinearMap.id Real E  := by sorry

theorem mfderiv_subtype_val_apply
    (U : TopologicalSpace.Opens M) (x : U) (v : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x v = v  := by sorry

@[simp] theorem mfderiv_opens_incl {U V : TopologicalSpace.Opens M} (hVU : V ≤ U) (x : V) :
    mfderiv I I (TopologicalSpace.Opens.inclusion hVU : V → U) x =
      ContinuousLinearMap.id Real E  := by sorry

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem mdifferentiableAt_subtype_iff {U : TopologicalSpace.Opens M} {f : M → N} {x : U} :
    MDifferentiableAt I J (fun y : U => f y) x ↔ MDifferentiableAt I J f (x : M)  := by sorry

theorem mfderiv_restrict_open (f : M → N) (U : TopologicalSpace.Opens M) (x : U) :
    mfderiv I J (fun y : U => f y) x = mfderiv I J f (x : M)  := by sorry

end DifferentialGeometry

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem MDifferentiableAt.subtypeVal_comp_iff {U : TopologicalSpace.Opens N}
    (f : M → U) (x : M) :
    MDifferentiableAt I J (fun y => (f y : N)) x ↔ MDifferentiableAt I J f x  := by sorry

theorem DifferentialGeometry.mfderiv_subtypeVal_comp {U : TopologicalSpace.Opens N}
    (f : M → U) (x : M) :
    mfderiv I J (fun y => (f y : N)) x = mfderiv I J f x  := by sorry

end

