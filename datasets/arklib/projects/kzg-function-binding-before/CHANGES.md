# Lean migration

Source: [https://github.com/Verified-zkEVM/ArkLib at `7056c8b857b194f4a3fa45eb841d01476ec9b1bc`](https://github.com/Verified-zkEVM/ArkLib/blob/7056c8b857b194f4a3fa45eb841d01476ec9b1bc/ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L635).

Roots: `KZG.CommitmentScheme.function_binding`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Cslib `7c8f6c0f67015df29b152fdcffaf7850db2e9185`.

Update module names and elaboration interfaces; vendor compatibility modules for the historical Cslib/Mathlib interfaces. Adapt polynomial coefficient/support representations and elaborator registry/meta staging. Retain the selected root and its mathematical constraints.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
