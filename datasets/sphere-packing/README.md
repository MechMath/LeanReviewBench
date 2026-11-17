# thefundamentaltheor3m/Sphere-Packing-Lean

9 root snapshots are listed in [index.csv](index.csv), including
9 historically compiled and LeanTrace-extracted snapshots.
Before/after versions are separate projects; a later version does not imply
a semantic verdict. No benchmark labels are published.

Each `projects/<id>/` contains `project.json`, `informal.jsonl` and
`formal/Main.lean`, with retained local modules under `formal/dep/`.
`CHANGES.md` is present when the selected source closure has compatibility edits.
The target module is retained with its surrounding declarations, namespace
context, definitions and proof source. Only local import paths are relocated;
proof correctness is outside the benchmark task. This conservative packaging
retains source context instead of synthesizing Lean declarations from pretty
printed extraction graphs.

See [maintenance and environment setup](../../docs/PROJECT-CASE-WORKFLOW.md) and
[fixed dependency versions](../project-cases.json). Dependency locations are read
from `PAPERLEAN_MATHLIB` and `PAPERLEAN_CSLIB`; no checkout location is assumed.
Explicit upstream statements, when retained, are indexed in
[upstream evidence](../../metadata/evidence/upstream/README.md), outside model inputs.
There is no `tasks.jsonl` in this batch.

The preparation archive is pinned at
[`964f2d92`](https://github.com/MechMath/PaperLeanBench/tree/964f2d92e71b1b911e568790a7196a6fb7e1250b).
Project metadata links directly to the original catalog and review at that
commit; runtime logs, full upstream checkouts and repeated extraction formats
are omitted here. Source authorship and notices in the Lean files are retained.
