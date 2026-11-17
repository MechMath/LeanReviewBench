# Lean migration

Source: [https://github.com/Robby955/FormalSLT at `37ed81115a3c898dc432735cb52dd55545547452`](https://github.com/Robby955/FormalSLT/blob/37ed81115a3c898dc432735cb52dd55545547452/FormalSLT/TestTimeMeta/FlagshipComposition.lean).

Roots: `FormalSLT.TestTimeMeta.FlagshipComponentWorkedExample.flagshipComponentWorkedExample_scalarAssembly`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt proof elaboration to the pinned APIs, including scalar actions, order reasoning and integrals. Retain root types and non-proof definition values.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.
