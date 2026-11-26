# Lean migration

Source: [https://github.com/cameronfreer/vaught-conjecture-counterexample at `d3201f45109dc93df14102127ffcee91ec6b974f`](https://github.com/cameronfreer/vaught-conjecture-counterexample/blob/d3201f45109dc93df14102127ffcee91ec6b974f/VaughtConjecture/Realization/CoupledFiniteCutReceiving.lean).

Roots: `VaughtConjecture.Realization.IsModel.hasFiniteCutReceiving_of_hasCoupledGatedPinnedExtensions`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate the selected project modules under `dep`. The source mapping and preparation receipts are recorded in `project.json`; no further compatibility edits are described in the input metadata.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
