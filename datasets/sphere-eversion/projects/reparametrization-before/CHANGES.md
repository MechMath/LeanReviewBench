# Lean migration

Source: [https://github.com/leanprover-community/sphere-eversion at `a8898f0d4208052375450d4bdc7271197e7021c1`](https://github.com/leanprover-community/sphere-eversion/blob/a8898f0d4208052375450d4bdc7271197e7021c1/src/loops/reparametrization.lean).

Roots: `reparametrization`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Select the historical declaration closure, relocate imports and adapt syntax/library APIs. Spell historical smooth-order `SmoothManifoldWithCorners` as `IsManifold`; retain the historical regularity index and avoid adding an analytic-order case.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
