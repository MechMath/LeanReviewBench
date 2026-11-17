# Lean migration

Source: [https://github.com/Robby955/FormalSLT at `3d96374ae0ab353a154a1db74708645a28973807`](https://github.com/Robby955/FormalSLT/blob/3d96374ae0ab353a154a1db74708645a28973807/FormalSLT/AnytimeValid/MixtureCS.lean).

Roots: `FormalSLT.AnytimeValid.mixture_confidence_sequence_uniformPrior`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt proof elaboration to the pinned APIs, including scalar actions, order reasoning and integrals. Retain root types and non-proof definition values.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
