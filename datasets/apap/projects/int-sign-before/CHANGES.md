# Lean migration

Source: [https://github.com/YaelDillies/apap at `8261296e61a6895823bee87664a335c56ae10258`](https://github.com/YaelDillies/apap/blob/8261296e61a6895823bee87664a335c56ae10258/APAP/Integer.lean).

Roots: `int`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports under `dep`. The recorded packaging retains the selected historical declarations, including their existing proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
