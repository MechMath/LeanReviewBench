# Binary alignment labels

The release contains 171 human-reviewed labels across 16 batches: 81 aligned and
90 misaligned. Each `<batch>.jsonl` contains only the current annotation result.

| Fields | Meaning |
| --- | --- |
| `task_id`, `dataset`, `project_id` | Input identity |
| `input_sha256` | Binding to the frozen mathematical input |
| `root`, or `roots` and `target_mode` | Selected declaration scope |
| `label` | Binary alignment verdict |
| `reason` | Concise English mathematical explanation |
| `review_scope` | Concise English statement of the target and relevant restrictions |
| `review_status`, `human_adjudicated` | `human_reviewed` and `true` for all current labels |
| `reference_ready`, `gold_label` | Formal evaluation-export readiness, still `false` and `null` |

Completed human review is recorded independently from readiness of a separately
frozen model-task export. Before/after order does not determine the label.
Three existing aligned labels lack a retained mathematical reason; their `reason`
remains empty rather than receiving an invented justification.

[The analysis index](../evidence/analysis/index.json) associates input identities
and hashes with evidence files and their digests. Evidence paths and hashes are
not duplicated in label records. Full reasoning and original wording remain in
[analysis evidence](../evidence/analysis/README.md); earlier label states and
restoration logs do not belong in JSONL annotation results. Superseded versions
are managed by Git. Restoration and status-change logs are omitted from the current release; Git
history retains those process records.

[Upstream evidence](../evidence/upstream/README.md) contains original source claims;
[the taxonomy](../taxonomy/README.md) separately classifies the negative inputs.
Keep labels, scope notes, reasons, and all evidence outside model-visible inputs.
Run `python3 scripts/data/check_release_candidate.py` to verify current bindings.
