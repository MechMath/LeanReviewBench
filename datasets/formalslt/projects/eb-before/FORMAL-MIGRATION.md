# Historical semantics

Source revision: 3d96374ae0ab353a154a1db74708645a28973807. Historical Lean 4.30.0-rc2 / Mathlib 25b7ac7d0cf8eef34ced5525f4a62b7613ad649b. Unified Lean 4.34.1 / Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

See CHANGES.md for every compatibility edit. No theorem hypothesis/conclusion or project definition is repaired by the port; the original before/after difference is retained. No new sorry or axiom. Successful extraction and standard-axiom audit: `reports/formalslt-history/technical/eb-before/20261103T130336866752Z/receipt.json`. Raw graph and failed earlier attempts are retained beside it.

Mathlib signature audit covers StronglyAdapted and condExp_of_stronglyMeasurable only; it is not a whole-library equivalence proof. See reports/formalslt-history/specification/mathlib-boundary-audit.json. Packaged Main/dep imports were separately recompiled; see technical/eb-before/packaged/receipt.json.
