# Lean migration

Source: [https://github.com/teorth/pfr at `47299fac2eb0a561f093204237dc6a5a82babf81`](https://github.com/teorth/pfr/blob/47299fac2eb0a561f093204237dc6a5a82babf81/PFR/ImprovedPFR.lean).

Roots: `entropic_PFR_conjecture_improv`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
