# Explicit upstream evidence

The release retains 34 explicit upstream statements linked to 89 of 171
versioned inputs. The other 82 inputs have no retained upstream evidence in this
collection. Coverage for all 16 batches is recorded in [index.json](index.json).
These are not counts of independent errors or confirmed misalignments. Our
judgments and available reasoning are separate [analysis evidence](../analysis/README.md).

Retain a statement only when upstream text explicitly describes a discrepancy,
refuted hypothesis, definition correction, open assumption or semantic scope
change relevant to a registered root. Generic proof completion, unexplained
repair titles and local model reviews are skipped. Brownian PR99's
"Fix some assumptions in various lemmas" does not clearly identify the admitted
root's missing finiteness premise. Skipped inputs get no placeholder evidence.

Each JSONL record contains:

- `source`: original URL, source kind and author when available.
- `excerpts`: exact text and its original field, with material qualifications.
- `archive`: immutable archive commit, payload path, SHA-256 and JSON pointer;
  repository-document excerpts point to frozen upstream bytes.
- `projects`: project ID, declaration, source commit and input hash. The
  relationship distinguishes a reported subject from dependency context.
- `association_note`: a curator's explanation, separate from upstream quotes.
- `truth_status: unverified_upstream_claim` and `usable_as_scoring_label: false`.

Input links identify a report's subject or context. Their
`statement_applicability: not_adjudicated` leaves open whether a claim applies
to each precise snapshot. Both historical versions may be linked for navigation;
after does not mean aligned or fixed. Blueprint corrections need not change
Formal. AI-generated upstream text remains upstream evidence with its disclosure
preserved; upstream origin does not mean human validation.

This pass examined locally frozen history payloads, registered discovery links
and source revisions, and selected upstream scope documentation. It is not an
exhaustive search of live repositories. Some retained batches, including AppliedModelingLib and Brownian, have no
retained upstream records. The excluded statistical-learning-theory batch has
no active inputs. Absence of a record does not establish absence of an upstream
statement or correctness of an input.

```sh
python3 scripts/data/upstream_evidence.py
python3 scripts/data/upstream_evidence.py --archives
```

Normal validation checks scope, counts, source URLs and exact input bindings.
The optional archive check additionally verifies original payload hashes, URLs
and every excerpt against its original source field. It uses local historical
Git objects and never fetches them automatically. Document authenticity relies
on the frozen source copy and recorded revision; this is not a fresh upstream
fetch or an independent verification of the mathematical claim.
