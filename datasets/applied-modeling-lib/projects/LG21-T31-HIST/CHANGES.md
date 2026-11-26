# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `dbfa918c02cd35c8279f8f8a9183f6bcbe72c817`](https://github.com/nikhgarg/AppliedModelingLib/blob/dbfa918c02cd35c8279f8f8a9183f6bcbe72c817/papers/LG21TestOptionalPolicies/PaperInterface.lean).

Roots: `LG21TestOptionalPolicies.PaperInterface.theorem3_1_optional_reporting`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Vendor the required historical EconCSLib modules and select the relevant policy and Gaussian declarations. Adapt affine-threshold and Gaussian-tail proof elaboration, including explicit integral and limit expressions. Preserve the historical policy definitions and target type.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
