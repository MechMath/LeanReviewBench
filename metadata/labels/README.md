# Binary alignment labels

The current release has 171 input-bound provisional verdicts across 16 batches:
81 aligned and 90 misaligned. Each `<batch>.jsonl` record identifies an input,
its complete root scope, verdict, reason, review status, and input SHA-256.

`review_report` and `review_report_sha256` point to the current per-input
[analysis evidence](../evidence/analysis/README.md). Its explicit coverage state
distinguishes detailed reviews (38 inputs), retained label reasons only (130),
and missing reasons (3). Source references and earlier decision fields are
provenance, not additional active verdicts. An input is classified independently
of its before/after partner; a later revision need not be aligned.

[Upstream evidence](../evidence/upstream/README.md) preserves original upstream
claims and exact source associations. These claims are not benchmark labels.
[The taxonomy](../taxonomy/README.md) separately classifies all 90 negative inputs.

All verdicts remain provisional: `human_adjudicated` and `reference_ready` are
false, and `gold_label` is null. User confirmation following model review does
not silently become independent human adjudication. No reason is invented for
the three existing aligned records whose reason is empty. The joint Stacks
`STK-0B34` record binds both roots and their shared informal target.

Run `python3 scripts/data/check_release_candidate.py` for exact input, evidence,
label and graph checks. The SLT batch is excluded. Evidence relocation changes
references and metadata hashes, not input bytes, labels, reasons, or review
states. Keep this entire directory outside model-visible task exports.
