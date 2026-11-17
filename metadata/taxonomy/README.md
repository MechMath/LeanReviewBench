# Misalignment taxonomy and annotations

The [current five-category standard](standard.md) and diagnostic annotations are
kept together here. All **90 currently misaligned inputs** have one to three
category labels. These remain provisional classifications of retained semantic
judgments, not human-adjudicated category labels or a new binary evaluation task.
The underlying binary judgments are human reviewed; the category-assignment
review state is separate.

| File | Purpose |
| --- | --- |
| [standard.md](standard.md) | Category definitions, decision tree, boundary rules, and annotation instructions |
| [cases.jsonl](cases.jsonl) | Input-bound classifications, English explanations, source evidence, and boundary notes |
| [cases.csv](cases.csv) | Flat classification table for inspection |
| [summary.json](summary.json) | Coverage, counts, and standard/classification hashes |

## Distribution

| Category | Inputs containing label | Primary inputs |
| --- | ---: | ---: |
| O | 15 | 13 |
| A | 38 | 31 |
| Q | 8 | 5 |
| F | 30 | 28 |
| P | 20 | 13 |

There are 70 single-label, 19 two-label, and 1 three-label inputs.
Counts use versioned inputs, not independent mathematical errors. Multi-label
counts overlap. They describe this selected benchmark, not natural error rates.
The first label retains the primary discrepancy identified by the review; do not
infer severity from label order.

## Scope and provenance

The collection combines 70 existing classifications and 20 classifications added
on November 17, 2026 from retained review evidence. All classification input hashes
match the current release. The closed-certificate specialization case
`formalslt:flagship-scalar-reflexive` is updated from Q to A to follow the current
explicit applicability boundary rule. No input or binary alignment label changes.
Prior versions are managed by Git rather than duplicated historical directories.

Each record binds the current standard by hash and identifies its source label
file, input hash, and supporting review. Historical evidence locators and issue
links are provenance; an issue link does not assert its current open/closed
status. Archive-only reviews are marked explicitly. `source_reason` follows the
current binary record; category explanations are the diagnostic classification.
Classification records cite current input-bound analysis evidence; those records
explicitly distinguish detailed local reviews from reason-only summaries and
retain archive-only source locators where relevant.
All categories still require human review, especially the documented boundaries.

These files are evaluation-side metadata and must not be included in model inputs.
