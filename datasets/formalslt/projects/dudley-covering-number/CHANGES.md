# Lean migration

Source: [https://github.com/Robby955/FormalSLT at `815d10dabf7c295417f82a1d7435a39214600e5f`](https://github.com/Robby955/FormalSLT/blob/815d10dabf7c295417f82a1d7435a39214600e5f/FormalSLT/Covering/ContinuousDudleyUnitIntervalCovering.lean).

Roots: `FormalSLT.Covering.ContinuousDudleyUnitIntervalCovering.continuous_dudley_entropy_integral_iSup_unitInterval_coveringNumber`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt proof elaboration to the pinned APIs, including scalar actions, order reasoning and integrals. Retain root types and non-proof definition values.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
