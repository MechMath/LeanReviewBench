# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `175d656d056721bbf56ce57b2421908ec345921a`](https://github.com/nikhgarg/AppliedModelingLib/blob/175d656d056721bbf56ce57b2421908ec345921a/papers/GS62CollegeAdmissions/PaperInterface.lean).

Roots: `GS62CollegeAdmissions.PaperInterface.theorem2_applicant_optimality`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical many-to-one matching interfaces and proof elaboration. Preserve each snapshot's matching definitions and theorem statement.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Recorded compatibility edits affect `EconCSLib/Markets/Matching/ManyToOne.lean`.
