# Vaught historical roadmap cases

Three snapshots from
[`cameronfreer/vaught-conjecture-counterexample`](https://github.com/cameronfreer/vaught-conjecture-counterexample)
are assessed against two independently recorded roadmap completion criteria:
the apex coatom-extension goal (R6/checkpoint 2.7) and all-model finite-cut
receiving (R1). The informal targets come from immutable historical blueprint
text, not from the conditional root docstrings or from reverse-translating Lean.

Historical upstream commits report the universal two-face and gated-extension
hypotheses as refuted and the replacement coupled hypothesis as open. Those
historical statements remain preserved in [upstream evidence](../../metadata/evidence/upstream/vaught.jsonl).
A later pinned upstream revision (`e9f465e1`) also refutes the coupled hypothesis
at every stage above 1. The 2026-11-09 follow-up review checks that the relevant
definitions match this dataset's frozen snapshot and marks coupled-after
misaligned with the unconditional R1 target. This does not refute R1 itself.
All three current provisional labels are in `metadata/labels/vaught.jsonl`;
the new evidence and independent check are in `reports/undetermined-review-2026-11-09/`.

`gate-before` and `coupled-after` share the same frozen informal text and a history group. Reciprocal links record a proposed successor sequence, without certifying a repair. Conditional theorem docstrings and independent roadmap goals have different scopes; a report about a refuted premise does not by itself classify an informal/Formal pair.

All projects preserve the exact historical statements, namespaces and local
context; only imports are relocated to `Main` and `dep`. No compatibility patch
was needed for Lean 4.34.1. Historical modules and the packaged Main/dep projects
were separately compiled and actually extracted in default and explicit modes.
The latter have the same root types as the original exports. Root axioms are
`propext`, `Classical.choice` and `Quot.sound`, with no `sorryAx`.

Historical model reviews remain in the archive; source, input, export and preparation bindings remain available through project provenance.

The [index](index.csv) and text projects follow the
[project-case workflow](../../docs/DATA-FORMAT.md). See
[specification and semantic review](https://github.com/MechMath/PaperLeanBench/blob/8012191c69c75a008356ba7b7bd422f0d57d2884/reports/vaught-preparation/README.md),
[compilation evidence](https://github.com/MechMath/PaperLeanBench/blob/8012191c69c75a008356ba7b7bd422f0d57d2884/reports/vaught-build/README.md), and
[upstream Apache-2.0 license](../../licenses/vaught/LICENSE).

The PR 119 printed/native separation witnesses are retained as research evidence
only: the currently retrievable published PDF differs from the old draft on the
decisive conditions. The exact old draft has not been acquired, so those
witnesses are not paired to that PDF or added here as negative tasks.
