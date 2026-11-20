# Binary alignment labels

The release contains 171 human-reviewed labels across 16 batches: 81 aligned and
90 misaligned. Each `<batch>.jsonl` contains only the current annotation result.

The two additional Poincare batches contain 26 human-confirmed judgments
(six aligned and twenty misaligned), including sixteen accepted by explicit
user batch confirmation. Across all inputs, 197 labels are human reviewed
(87 aligned and 110 misaligned). Individual verdicts and confirmation records
are retained in the label and analysis files. FM-COVERING-before is aligned under
the explicitly adjudicated positive-dimensional source convention. The broader
zero-dimensional interpretation and its different applicability judgment remain
documented in the review; the former connectedness rationale is withdrawn.
The November 20, 2026 Poincare review records:

| Batch | aligned | misaligned | undetermined |
| --- | ---: | ---: | ---: |
| qinz1yang | 2 | 13 | 0 |
| frenzymath | 4 | 7 | 0 |
| Total | 6 | 20 | 0 |

Every added record has an English reason and scope. Unresolved records also have
specific English adjudication questions in their analysis evidence. A confident
agent binary judgment remains `agent_preliminary` with `human_adjudicated=false`;
it does not promote the project's workflow status or constitute human approval.

| Fields | Meaning |
| --- | --- |
| `task_id`, `dataset`, `project_id` | Input identity |
| `input_sha256` | Binding to the frozen mathematical input |
| `root`, or `roots` and `target_mode` | Selected declaration scope |
| `label` | `aligned` or `misaligned`; unresolved pending records use `undetermined` |
| `reason` | Concise English mathematical explanation |
| `review_scope` | Concise English statement of the target and relevant restrictions |
| `review_status`, `human_adjudicated` | `human_reviewed` / `true` for all 197 adjudicated records; no current records remain pending |
| `reference_ready`, `gold_label` | Formal evaluation-export readiness, still `false` and `null` |

Completed human review is recorded independently from readiness of a separately
frozen model-task export. Before/after order does not determine the label.
Three existing aligned labels lack a retained mathematical reason; their `reason`
remains empty rather than receiving an invented justification.

[The analysis index](../evidence/analysis/index.json) associates input identities
and hashes with evidence files and their digests. Evidence paths and hashes are
not duplicated in label records. Full reasoning is retained in English in
[analysis evidence](../evidence/analysis/README.md), with the original wording in
Git history; earlier label states and
restoration logs do not belong in JSONL annotation results. Superseded versions
are managed by Git. Restoration and status-change logs are omitted from the current release; Git
history retains those process records.

[Upstream evidence](../evidence/upstream/README.md) contains original source claims;
[the taxonomy](../taxonomy/README.md) separately classifies the negative inputs.
Keep labels, scope notes, reasons, and all evidence outside model-visible inputs.
Run `python3 scripts/data/check_release_candidate.py` to verify current bindings.
