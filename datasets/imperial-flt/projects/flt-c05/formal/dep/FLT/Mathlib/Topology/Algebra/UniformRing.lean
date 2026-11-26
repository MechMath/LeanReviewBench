module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Topology.Algebra.UniformRing
public import dep.FLT.Mathlib.Algebra.Algebra.Hom

@[expose] public section

namespace UniformSpace.Completion

variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)

variable {f}

/-- The semialgebra homomorphism `Completion α →ₛₐ[f] Completion β` induced from
a continuous ring homomorphism `f : α →+* β`.
-/
noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    Completion α →ₛₐ[f] Completion β where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m x := sorry

end UniformSpace.Completion
