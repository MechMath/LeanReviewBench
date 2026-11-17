# Formal context graphs and technical evidence

| Path | Purpose |
| --- | --- |
| `retained-index.json` | Input/hash-bound access to all 171 context graphs |
| `index.json` | Twelve recovered or composed context bindings and extraction receipts |
| `graphs/`, `retained/` | Retained historical and freshly extracted graph bytes |
| `receipts/<batch>/<id>.json` | Extraction and composition checks for named inputs |
| `components/stacks/` | Default/explicit graphs needed to verify the joint Stacks context |
| `composition-inputs/stacks/` | Two component source packages used solely for joint-context verification |

The two component packages are not active benchmark inputs. They remain because
the joint context checker verifies input digests, source equality, and graph
union against them. Receipt and graph bytes for these composition inputs are unchanged by relocation.
Embedded historical locators resolve through exact mappings in `../layout.json`;
active indexes use canonical paths. Six AppliedModelingLib inputs have fresh
Lean 4.34.1 compilation and extraction receipts for their native dependency
slices. Each records source hashes, root-type checks, axiom dependencies and a
replay command. Other entries retain their historical evidence. Technical
extraction success does not certify semantic alignment.
