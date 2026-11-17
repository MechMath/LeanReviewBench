# FormalSLT historical cases

The first four of six snapshots form two before/after pairs from [Robby955/FormalSLT](https://github.com/Robby955/FormalSLT), a 2026 repository: mixture and empirical-Bernstein confidence-sequence roots. Both pairs concern the same reported assumption issue and one repository split group. Counts must not be interpreted as four independent mathematical problems.

| Pair | Before | Upstream successor |
| --- | --- | --- |
| Mixture CS | `4ddd339369a093cc4a6eea761d1322ad6484f0ec` | [`3d96374`](https://github.com/Robby955/FormalSLT/commit/3d96374ae0ab353a154a1db74708645a28973807) |
| Empirical Bernstein CS | `3d96374ae0ab353a154a1db74708645a28973807` | [`94a4bfc`](https://github.com/Robby955/FormalSLT/commit/94a4bfc3f8b50c8e905a44672babaff6d74619e6) |

The author's two repair commits explicitly describe vacuity from combining same-time increment measurability and zero conditional mean, and change the increment measurability to the next filtration time. These upstream claims are retained in [upstream evidence](../../metadata/evidence/upstream/formalslt.jsonl) without certifying their correctness or assigning either snapshot a label.

Informal statements are explicit bounded-increment, compact-uniform-prior specializations of [Howard et al., v6](https://arxiv.org/html/1810.08240v6). The EB case uses a predictable conditional-second-moment proxy; it does not claim the paper's realized empirical-variance Theorem 4. The same frozen informal text is used on both sides of each pair. The archived specification JSON is a review transcription with locators, not a downloaded original paper.

All six historical root modules and relocated packaged projects compile under Lean 4.34.1. Actual LeanTrace graphs include roots and reachable project definitions; companion explicit-argument graphs expose filtration indices hidden by default pretty printing. Compatibility changes are proof-only, recorded in each `CHANGES.md`, with no new axioms or holes. Mathlib is the pinned environment in [project-cases.json](../project-cases.json).

No benchmark labels are published. Historical model labels and independent subagent reviews remain in the archive rather than the publication candidate.

The dataset contains text inputs and an [index](index.csv). [Preparation evidence](https://github.com/MechMath/PaperLeanBench/blob/8012191c69c75a008356ba7b7bd422f0d57d2884/reports/formalslt-history/README.md) retains history indexes, pinned original sources, unsuccessful attempts, successful receipts, actual graphs, migration diffs and independent review. [MIT license](../../licenses/formalslt/LICENSE).

Two standalone historical roots are also retained: `dudley-covering-number` and `flagship-scalar-reflexive`. Both have compiled/extracted roots. The Dudley informal is a concrete specialization with separately sourced covering-number semantics, not a verbatim paper theorem. This pass retained no sufficiently explicit upstream discrepancy report for these two standalone inputs.
