
import Mathlib.Topology.VectorBundle.Basic



open Bundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]


theorem continuous_zeroSection (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] [VectorBundle 𝕜 F E] :
    Continuous (zeroSection F E)  := by sorry

