# Misalignment taxonomy and annotations

The [current five-category standard](standard.md) and diagnostic annotations are
kept together here. The **110 misaligned inputs across all 18 source batches** have one to three
category labels, including all 20 Poincare negatives. These remain provisional
classifications of retained semantic judgments, not human-adjudicated category
labels or a new binary evaluation task. The underlying binary judgments are
human reviewed; category-assignment review is separate.

| File | Purpose |
| --- | --- |
| [standard.md](standard.md) | Category definitions, decision tree, boundary rules, and annotation instructions |
| [cases.jsonl](cases.jsonl) | Input-bound classifications, English explanations, source evidence, and boundary notes |
| [cases.csv](cases.csv) | Flat classification table for inspection |
| [summary.json](summary.json) | Coverage, counts, and standard/classification hashes |

## Distribution

| Category | Inputs containing label | Primary inputs |
| --- | ---: | ---: |
| O | 22 | 20 |
| A | 48 | 41 |
| Q | 8 | 5 |
| F | 30 | 28 |
| P | 26 | 16 |

There are 87 single-label, 22 two-label, and 1 three-label inputs.
Counts use versioned inputs, not independent mathematical errors. Multi-label
counts overlap. They describe this selected benchmark, not natural error rates.
The first label retains the primary discrepancy identified by the review; do not
infer severity from label order.

## Scope and provenance

The collection retains 90 original classifications and 20 current Poincare
classifications from input-bound review evidence. FM-COVERING-before was removed
from the negative classification table after its aligned adjudication under the
positive-dimensional source interpretation on November 20, 2026; its review retains
the zero-dimensional alternative. All classification input hashes match the current
release. The closed-certificate specialization case
`formalslt:flagship-scalar-reflexive` is updated from Q to A to follow the current
explicit applicability boundary rule. Mathematical input bytes are unchanged.
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
