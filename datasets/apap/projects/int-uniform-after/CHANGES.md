# Lean migration

Source: [https://github.com/YaelDillies/apap at `251c21abcbac96793baeb67050732380d94550aa`](https://github.com/YaelDillies/apap/blob/251c21abcbac96793baeb67050732380d94550aa/APAP/Integer.lean).

Roots: `int`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports under `dep`. The recorded packaging retains the selected historical declarations, including their existing proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
