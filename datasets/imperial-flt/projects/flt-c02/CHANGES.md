# Lean migration

Source: [https://github.com/ImperialCollegeLondon/FLT at `8c4bb0b2046a1d564623057bb359212f92e0d1f2`](https://github.com/ImperialCollegeLondon/FLT/blob/8c4bb0b2046a1d564623057bb359212f92e0d1f2/FLT/FreyCurve/FreyPackage.lean).

Roots: `FreyPackage.of_not_FermatLastTheoremFor_p_ge_5`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Adapt imports, tensor-induction APIs, typeclass elaboration and completion-wrapper coercions. Rename the historical local `Field.absoluteGaloisGroup.map` to `flt_map` where needed to avoid a library-name collision, updating its local references.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
