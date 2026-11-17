# Documentation

The release contains 171 inputs across 16 batches, with 81 aligned and 90 misaligned human-reviewed labels.

- [Data format](DATA-FORMAT.md): layout, input/root identities, labels, evidence and technical states.
- [Statistics](STATISTICS.md): generated counts and counting conventions.
- [Construction](CONSTRUCTION.md): source selection and formal/informal reconstruction methods.
- [Environment](ENVIRONMENT.md): compiler, library pins and optional tool configuration.
- [Validation](VALIDATION.md): integrity checks, tests and their limits.
- [Maintenance](MAINTENANCE.md): updating inputs, metadata and inventories.

Annotation details live with the [labels](../metadata/labels/README.md), [evidence](../metadata/evidence/README.md) and [taxonomy](../metadata/taxonomy/README.md).
The [evaluation tools](../scripts/evaluation/README.md) accept separately supplied evaluation packages; native task conversion and model input scope remain under [discussion](https://github.com/MechMath/LeanReviewBench/issues/1).
