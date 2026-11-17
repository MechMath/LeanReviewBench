# Lean migration

Source: [https://github.com/Robby955/FormalSLT at `4ddd339369a093cc4a6eea761d1322ad6484f0ec`](https://github.com/Robby955/FormalSLT/blob/4ddd339369a093cc4a6eea761d1322ad6484f0ec/FormalSLT/AnytimeValid/MixtureCS.lean).

Roots: `FormalSLT.AnytimeValid.mixture_confidence_sequence_uniformPrior`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt proof elaboration to the pinned APIs, including scalar actions, order reasoning and integrals. Retain root types and non-proof definition values.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
