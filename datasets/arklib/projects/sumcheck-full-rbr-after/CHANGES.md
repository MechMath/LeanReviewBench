# Lean migration

Source: [https://github.com/Verified-zkEVM/ArkLib at `b660c6d4a5e2ea93fd6d8255606975bc6b263ec7`](https://github.com/Verified-zkEVM/ArkLib/blob/b660c6d4a5e2ea93fd6d8255606975bc6b263ec7/ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L223).

Roots: `Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Update module names and elaboration interfaces; vendor compatibility modules for the historical Cslib/Mathlib interfaces. Adapt polynomial coefficient/support representations and elaborator registry/meta staging. Retain the selected root and its mathematical constraints.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
