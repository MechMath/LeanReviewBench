Original upstream closure is preserved byte-for-byte in original/. formal/Main.lean imports the natural root module, checks the original root name and prints its proof axioms. No new sorry or axiom is introduced. Existing sorry and knownin1980s admissions remain. All labels are undetermined and this is a control candidate.

Compatibility changes preserve mathematical statements: explicit tensor induction, renamed or moved upstream API imports, typeclass elaboration options, completion-wrapper coercion transport, and collision avoidance for local names already present in the unified Mathlib. The local Field.absoluteGaloisGroup.map is renamed flt_map with its local references updated to retain the historical implementation. Full before/after source diff is in compatibility.patch.

Additional migration follows upstream #1100 (adicCompletion wrapper), #1121 (InfinitePlace.Completion wrapper), and #1192 (tensor induction API), with commit API evidence preserved in ../upstream-migration-evidence/. The historical target statements are retained; existing admissions are preserved. Completion maps are presented through the upstream wrapper equivalences/maps, while finite/infinite adele notation collisions are expanded to their existing definitions. Extensionality stops at the relevant wrapper boundary. Proof-only adjustments replace formerly automatic subtype, scalar and addition reasoning.

Changed upstream files:

- FLT/AutomorphicForm/GroupTheoryStuff.lean
- FLT/DedekindDomain/AdicValuation.lean
- FLT/DedekindDomain/Completion/BaseChange.lean
- FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean
- FLT/DedekindDomain/FiniteAdeleRing/TensorProduct.lean
- FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean
- FLT/DedekindDomain/IntegralClosure.lean
- FLT/Deformations/ContinuousRepresentation/IsTopologicalModule.lean
- FLT/DivisionAlgebra/Finiteness.lean
- FLT/HaarMeasure/HaarChar/AdeleRing.lean
- FLT/HaarMeasure/HaarChar/FiniteAdeleRing.lean
- FLT/HaarMeasure/HaarChar/Padic.lean
- FLT/Hacks/RightActionInstances.lean
- FLT/Mathlib/Algebra/Algebra/Bilinear.lean
- FLT/Mathlib/Algebra/Algebra/Hom.lean
- FLT/Mathlib/Algebra/Central/TensorProduct.lean
- FLT/Mathlib/GroupTheory/DoubleCoset.lean
- FLT/Mathlib/LinearAlgebra/TensorProduct/Algebra.lean
- FLT/Mathlib/NumberTheory/NumberField/InfinitePlace/Completion.lean
- FLT/Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean
- FLT/Mathlib/NumberTheory/Padics/PadicIntegers.lean
- FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean
- FLT/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean
- FLT/Mathlib/RingTheory/Localization/BaseChange.lean
- FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean
- FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean
- FLT/Mathlib/Topology/Algebra/RestrictedProduct/Module.lean
- FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean
- FLT/Mathlib/Topology/HomToDiscrete.lean
- FLT/NumberField/AdeleRing.lean
- FLT/NumberField/Completion/Finite.lean
- FLT/NumberField/Completion/Infinite.lean
- FLT/NumberField/InfiniteAdeleRing.lean
- FLT/NumberField/Padics/RestrictedProduct.lean

See technical/receipt.json for actual closure/target/graph outcomes; failure logs identify unresolved migration work.

2026-11-13: relocated repository modules under formal/dep and prefixed local imports with dep. Declaration names and proof bodies unchanged. Historical receipts apply to pre-relocation sources; new receipt tracked separately.

Anonymous instance names generated from the top-level module prefix were adjusted from suffix _fLT to _dep after relocation; instance definitions and mathematical assumptions are unchanged.
