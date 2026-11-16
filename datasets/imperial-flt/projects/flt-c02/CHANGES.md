Original upstream closure is preserved byte-for-byte in original/. formal/Main.lean imports the natural root module, checks the original root name and prints its proof axioms. No new sorry or axiom is introduced. Existing sorry and knownin1980s admissions remain. All labels are undetermined and this is a control candidate.

Compatibility changes preserve mathematical statements: explicit tensor induction, renamed or moved upstream API imports, typeclass elaboration options, completion-wrapper coercion transport, and collision avoidance for local names already present in the unified Mathlib. The local Field.absoluteGaloisGroup.map is renamed flt_map with its local references updated to retain the historical implementation. Full before/after source diff is in compatibility.patch.

Changed upstream files:


See technical/receipt.json for actual closure/target/graph outcomes; failure logs identify unresolved migration work.

2026-11-13: relocated repository modules under formal/dep and prefixed local imports with dep. Declaration names and proof bodies unchanged. Historical receipts apply to pre-relocation sources; new receipt tracked separately.
