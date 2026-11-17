# Lean migration

Source: [https://github.com/leanprover-community/sphere-eversion at `27a2c7fdff78bb5509831699899796eaffe62a4b`](https://github.com/leanprover-community/sphere-eversion/blob/27a2c7fdff78bb5509831699899796eaffe62a4b/SphereEversion/ToMathlib/Geometry/Manifold/Immersion.lean).

Roots: `Immersion`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Select the historical declaration closure, relocate imports and adapt syntax/library APIs. Spell historical smooth-order `SmoothManifoldWithCorners` as `IsManifold`; retain the historical regularity index and avoid adding an analytic-order case.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Historical SmoothManifoldWithCorners is spelled IsManifold at smooth order. The after regularity index is still ENat; no extra analytic-order case is added.
