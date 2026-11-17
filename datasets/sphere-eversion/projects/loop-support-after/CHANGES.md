# Lean migration

Source: [https://github.com/leanprover-community/sphere-eversion at `094437437b24ee7a8b6a8f1f28da241a1ba9f280`](https://github.com/leanprover-community/sphere-eversion/blob/094437437b24ee7a8b6a8f1f28da241a1ba9f280/src/loops/basic.lean).

Roots: `loop.support`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Select the historical declaration closure, relocate imports and adapt syntax/library APIs. Spell historical smooth-order `SmoothManifoldWithCorners` as `IsManifold`; retain the historical regularity index and avoid adding an analytic-order case.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Lean3 loop, period-one condition, function coercion, is_const and support are syntax-ported; definition bodies are unchanged. Both target revisions use identical Formal bytes.
