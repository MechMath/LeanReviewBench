# Lean migration

Source: [https://github.com/nikhgarg/AppliedModelingLib at `7dfef1f11f46a5709da0f1a6de422863d2301b10`](https://github.com/nikhgarg/AppliedModelingLib/blob/7dfef1f11f46a5709da0f1a6de422863d2301b10/papers/GS62CollegeAdmissions/PaperInterface.lean).

Roots: `GS62CollegeAdmissions.PaperInterface.theorem2_applicant_optimality`.

Target environment: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Relocate imports and adapt the historical many-to-one matching interfaces and proof elaboration. Preserve each snapshot's matching definitions and theorem statement.

Packaging maps the target module to `formal/Main.lean` (or imports it there) and local dependency modules to `formal/dep/`. Historical before/after fixes remain separate inputs.

Before context pruning, compatibility edits affected `EconCSLib/Markets/Matching/ManyToOne.lean`.

## Released statement context

- Retain the target declaration closure and source support needed to elaborate it; remove other declarations and modules.
- Replace theorem and lemma bodies, proof-valued declaration bodies, and proof-valued tactic blocks with `sorry`. Preserve declaration types, section parameters, and computational definitions.
