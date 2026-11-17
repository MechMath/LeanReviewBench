# Lean migration

Source: [https://github.com/Robby955/FormalSLT at `94a4bfc3f8b50c8e905a44672babaff6d74619e6`](https://github.com/Robby955/FormalSLT/blob/94a4bfc3f8b50c8e905a44672babaff6d74619e6/FormalSLT/AnytimeValid/EmpiricalBernsteinCS.lean).

Roots: `FormalSLT.AnytimeValid.empiricalBernstein_confidence_sequence_uniformPrior`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt proof elaboration to the pinned APIs, including scalar actions, order reasoning and integrals. Retain root types and non-proof definition values.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
