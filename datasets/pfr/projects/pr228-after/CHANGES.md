# Lean migration

Source: [https://github.com/teorth/pfr at `238db8a8e77897bd2f996837ae9c8711c6aebce5`](https://github.com/teorth/pfr/blob/238db8a8e77897bd2f996837ae9c8711c6aebce5/PFR/RhoFunctional.lean).

Roots: `rhoMinus`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and retain the selected historical root and definition context.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
