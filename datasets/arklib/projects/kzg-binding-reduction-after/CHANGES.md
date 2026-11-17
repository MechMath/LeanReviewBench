# Lean migration

Source: [https://github.com/Verified-zkEVM/ArkLib at `7f5bd412460755d1d0ffccd0fc1f72df833aa23d`](https://github.com/Verified-zkEVM/ArkLib/blob/7f5bd412460755d1d0ffccd0fc1f72df833aa23d/ArkLib/Commitments/Functional/KZG/Binding.lean#L757).

Roots: `KZG.CommitmentScheme.binding_reduces_to_tSdh`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Update module names and elaboration interfaces; vendor compatibility modules for the historical Cslib/Mathlib interfaces. Adapt polynomial coefficient/support representations and elaborator registry/meta staging. Retain the selected root and its mathematical constraints.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
