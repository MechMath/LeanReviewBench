# Lean migration

Source: [https://github.com/teorth/pfr at `7347e1422d12ecd324f7bc9a56a9284fc140ea83`](https://github.com/teorth/pfr/blob/7347e1422d12ecd324f7bc9a56a9284fc140ea83/PFR/Mathlib/Probability/Independence/Conditional.lean).

Roots: `ProbabilityTheory.condIndep_copies`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
