# Lean migration

Source: [https://github.com/cameronfreer/vaught-conjecture-counterexample at `e7b6efbc3cc3210864666f48567c6aafd55dfb34`](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/e7b6efbc3cc3210864666f48567c6aafd55dfb34/VaughtConjecture/Extension/TwoFaceLift.lean).

Roots: `VaughtConjecture.StageType.hasApexCoatomExtensions_of_twoFaceLift`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate the selected project modules under `dep`. The source mapping and preparation receipts are recorded in `project.json`; no further compatibility edits are described in the input metadata.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
