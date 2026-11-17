# Lean migration

Source: [https://github.com/YaelDillies/apap at `2e86fa43e17d2721d00f1016916cf616e55f34f8`](https://github.com/YaelDillies/apap/blob/2e86fa43e17d2721d00f1016916cf616e55f34f8/APAP/Integer.lean).

Roots: `int`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports under `dep`. The recorded packaging retains the selected historical declarations, including their existing proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
