# Lean migration

Source: [https://github.com/teorth/pfr at `c30479cd5cfcea7c9e7af6b0da5f50d6d8c2bd32`](https://github.com/teorth/pfr/blob/c30479cd5cfcea7c9e7af6b0da5f50d6d8c2bd32/PFR/ForMathlib/ConditionalIndependence.lean).

Roots: `ProbabilityTheory.condIndep_copies`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
