# Lean migration

Source: [https://github.com/teorth/pfr at `06b0b0e2dfdc5062ab992c4c3f4b8d5957c9097e`](https://github.com/teorth/pfr/blob/06b0b0e2dfdc5062ab992c4c3f4b8d5957c9097e/PFR/Mathlib/Probability/Independence/Basic.lean).

Roots: `ProbabilityTheory.iIndepFun.finsets`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
