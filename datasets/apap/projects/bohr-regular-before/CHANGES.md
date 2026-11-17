# Lean migration

Source: [https://github.com/YaelDillies/apap at `d5f5f6054ec7967d05e87d7e0579a0b08a6c5cb2`](https://github.com/YaelDillies/apap/blob/d5f5f6054ec7967d05e87d7e0579a0b08a6c5cb2/APAP/Prereqs/Bohr/Regular.lean).

Roots: `BohrSet.IsRegular`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate project-local imports under `dep`. The recorded packaging retains the selected historical declarations, including their existing proof admissions.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
