# Native publication format

The authoritative contract is [DATA-FORMAT.md](DATA-FORMAT.md), using `paperlean-project-case-1`. The paper's [construction appendix](source-contracts/paper/app_imple_detail.tex) and the research [maintenance documentation](source-contracts/research/PROJECT-CASE-WORKFLOW.md) describe the same project-oriented layout.

The earlier `leanreviewbench-input-1`, `leanreviewbench-context-1`, content-addressed source blob layout and release-only `reason/declarations` prediction interface have been removed. They are not alternative authoritative formats.

The active inventory is `datasets/project-cases.json`. A multi-root project is one input and one label record. Preserve the exact informal records, original input digest scheme, semantic labels, technical states, version links and family split identities. Source metadata and review/history information are curator data; native package directories must not be sent wholesale to models.

The only publication convenience addition is `metadata/derived-graphs/retained-index.json` (`paperlean-retained-graphs-1`). It binds each `(dataset, project_id)` to its original `input_sha256`, ordered `roots`, local `graph_path` and `graph_sha256`. `graph_source` preserves the source commit/path/hash and recovery method. Optional `retained_receipts` bind available current extraction receipts. `fresh_compilation=false` means this migration did not perform a new build; it does not change the original compilation flags or evidence.

Original derived records remain in `metadata/derived-graphs/index.json` and pass their original receipt checks. Other exact exported graphs are stored once in `metadata/derived-graphs/retained/` and indexed locally. These raw construction graphs can include documentation/source metadata; they require model export filtering.

`metadata/manifest.json` retains the original `paperlean-candidate-manifest-1` byte inventory contract. `metadata/provenance.json` retains `paperlean-provenance-2`. `metadata/release.json` records the publication's source and documentation commits and current counts; it does not redefine project inputs or labels.

The older `protocol/v1` transport and its runner are preserved for separately supplied compatible evaluation packages. As documented upstream, this native project-case collection does not yet have a frozen task export. Binary reference labels and optional model abstention are separate concepts.
