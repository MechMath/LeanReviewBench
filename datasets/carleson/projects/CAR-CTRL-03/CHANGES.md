# Lean migration

Source: [https://github.com/fpvandoorn/carleson at `f10c441921273ee2a04cea802f2c32b7c6ebc5ea`](https://github.com/fpvandoorn/carleson/blob/f10c441921273ee2a04cea802f2c32b7c6ebc5ea/Carleson/Defs.lean).

Roots: `LinearizedMetricCarleson`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate the selected historical modules under `dep`. Preserve the selected control statement; no additional migration edits are described in the input metadata.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
