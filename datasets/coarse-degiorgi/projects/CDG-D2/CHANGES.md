# Lean migration

Source: [https://github.com/scottnarmstrong/CoarseDeGiorgi at `200c40c9c55a5e19188739d27466ddffcb2660c4`](https://github.com/scottnarmstrong/CoarseDeGiorgi/blob/200c40c9c55a5e19188739d27466ddffcb2660c4/CoarseDeGiorgi/Statements/MomentBoundsBesov.lean).

Roots: `CoarseDeGiorgi.moment_bounds_besov`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate local imports. Where recorded below, adjust proof-local elaboration in selection adapters; retain the target statements and data definitions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
