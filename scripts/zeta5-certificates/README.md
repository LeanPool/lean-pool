# Reproducing the Zeta5 numerical certificates

This archive reproduces all 118 generated modules in Lean Pool PR #540, including
114 U/V endpoint tables, the 684-interval assembly, and the inner/outer growth
tables and inner sum. The manifest pins source commit
`154983b2d21f27207c078cccf2646715c58e0d3c`, upstream
[`mo271/Zeta5`](https://github.com/mo271/Zeta5/tree/f19a1960609f7d38e7b63fd2acb05e6f60a7b741),
and each output's SHA-256. The later removal of the unused paper normalizer does
not change any archived file.

Use Python 3.13 or later. No third-party packages, network, Lean installation,
floating-point arithmetic, or execution of archived code is needed for rendering:

```sh
python3 scripts/zeta5-certificates/regenerate.py --verify-archive
python3 scripts/zeta5-certificates/regenerate.py --output "$CODEX_SCRATCH_ROOT/zeta5-regenerated"
python3 scripts/zeta5-certificates/regenerate.py --check /path/to/import-checkout
```

`--output` writes only the recorded project modules underneath its argument;
the destination must not already exist, even as an empty directory or symlink.
Generation stages all files in a new sibling directory and publishes the complete
tree by rename only after every record renders successfully. A failed generation
removes its staging tree and publishes nothing. `--check` compares
bytes without writing. The archive hash verification is separate so a deliberate
template edit can be rendered before its baseline hashes are updated.

## Data and shared proof templates

The archive contains 14,147 blocks represented by 461 text templates. A record
is `[template_identifier, decimal_integer_strings]`. Replace the consecutive
`{{integer}}` markers in the named template with those strings, preserving all
other bytes, and concatenate a file's records in order. Signs, rational division,
Lean syntax, tactic calls, and layout live in the templates. Parameters include
numeric suffixes in declaration names as well as mathematical integers. Integer
strings avoid any JSON floating-point precision loss.

The templates were extracted from the canonical, compiled Lean port, splitting
before top-level `lemma`, `theorem`, and `def` declarations (including private
ones), and replacing each ASCII decimal digit run with a marker. Templates with
identical resulting bytes are shared. Layout variants remain separate to preserve
byte-for-byte output. The complete round trip and all output hashes were checked.

This is a generator for the **preserved certificate set**, not a search algorithm
for stronger bounds or a claim to reconstruct the original numerical search.
The upstream scripts document that search, but do not reproduce this port. Here
the exact certified rational parameters are explicit inputs. Changes to a common
proof idiom can be made once in its template rather than across its users; the
most-used template occurs 4,500 times. Grepping `records/` for its identifier finds
all affected modules. A change to the number of markers requires corresponding
parameter changes and is rejected if their counts disagree.

After editing, render to scratch, inspect the diff, copy the intended outputs to
a content branch, and run the project build, style checks, linters, and trust
audit. Every emitted theorem must still pass the Lean kernel. New interval
partitions or new rational bounds additionally need mathematical validation;
this tool does not certify them on its own. Keep tooling edits in a separate PR
from Lean content, as required by the repository's separation policy.

The certificate text and numeric data derive from Moritz Firsching's Apache-2.0
formalization, with AI-assisted proof refactoring by the Lean Pool acquisition
agent. Original copyright/author headers are reproduced in the outputs. This
tool and archive are distributed under the repository's Apache-2.0 license.
