# Lean migration

Source: [https://github.com/leanprover-community/sphere-eversion at `357f2951c949baa5a3bcf6166a26b8205ff1deaf`](https://github.com/leanprover-community/sphere-eversion/blob/357f2951c949baa5a3bcf6166a26b8205ff1deaf/src/loops/reparametrization.lean).

Roots: `smooth_surrounding_family.reparametrize_average`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Select the historical declaration closure, relocate imports and adapt syntax/library APIs. Spell historical smooth-order `SmoothManifoldWithCorners` as `IsManifold`; retain the historical regularity index and avoid adding an analytic-order case.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
