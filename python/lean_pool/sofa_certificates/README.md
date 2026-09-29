# Reproducing the moving-sofa Part E certificates

This recipe regenerates all **32** files in
`LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates/`, byte for byte,
at content commit `9ac84ed0910d4615a0238a6d465b471d7cee53a0` in PR #548
(see `data/outputs.json`).
That corpus contains 323,037 lines and 25,086 named declarations. The recipe
also verifies the intermediate 47-file layout at content commit
`0f0182131407cb4e2f7b1234f07f34271982d46a` against its original digests.
The recipe contains transformations, subdivision witnesses, module assignments,
and checksums; it does not embed the final Lean files or a compressed copy of them.

The source input is the public
[MovingSofa commit 4d556913](https://github.com/deancureton/MovingSofa/tree/4d5569131940815f47a9ccf3e90a4c5043c56127).
Its vendored GerverSofa source is derived from Dawid Trela's MIT-licensed
[GerverSofaLean v1.1.0 release](https://github.com/dawidmtrela-dotcom/GerverSofaLean/releases/tag/v1.1.0).
The release ZIP has SHA-256
`7c496150f709ac709ae01f4836e9a702a18f752450efa69f15cf44264c0c2f77`.
MovingSofa has subsequently pruned imports and unused semantic declarations and
normalized whitespace. This recipe therefore uses the exact MovingSofa snapshot,
not an assumption that the two trees are identical. Every input source file has
its own SHA-256 in `data/inputs.json`. The original copyright attribution survives
the transformations; the complete MIT notice is in `LeanPool/MovingSofa.lean`.

## Run from a clean directory

Requires the repository's Python 3.13+ environment. Generation itself does not
require a Lean build or network access once the archive is downloaded. From the
repository root, with `$TMPDIR` pointing to a suitable scratch disk:

```bash
curl --fail --location \
  https://codeload.github.com/deancureton/MovingSofa/tar.gz/4d5569131940815f47a9ccf3e90a4c5043c56127 \
  --output "$TMPDIR/MovingSofa-4d556913.tar.gz"
cd python
uv run python -m lean_pool.sofa_certificates generate \
  --archive "$TMPDIR/MovingSofa-4d556913.tar.gz" \
  --workspace "$TMPDIR/sofa-certificates-replay"
```

The workspace must not already exist. The command checks archive SHA-256
`88538a166208cdb7ba2c4079a296c8d7becf18758c9b4540750d81b271e79f70`,
reads only named archive members without extracting arbitrary paths, validates
all witness trees, and runs the ordered source transformations. It requires all
32 expected output digests to match before reporting success. The generated
files are under the workspace's `pool/LeanPool/MovingSofa/.../Certificates/`.
`verification.json` records the archive digest, every final output digest, and elapsed
wall time. Intermediate source and audit reports remain available for inspection.
The command never writes to the content checkout.

To compare a content checkout directly against the expected corpus:

```bash
uv run python -m lean_pool.sofa_certificates verify \
  /path/to/content-checkout/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates
```

## Recompute the subdivision witnesses

The checked-in witnesses are search results, not trusted mathematical premises.
Every generated terminal proof uses `decide +kernel`; every internal node uses
the proved four-child cover lemma. An incorrect numerical witness fails Lean's
kernel check. Structural validation also rejects missing quadrants, overlapping
leaves, wrong remaining depths and invalid path digits before source generation.

The separate search command recomputes all **10,801 leaves across 550 roots**.
It requires the content checkout at the pinned commit, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, with the semantic prerequisites built:

```bash
# In the content checkout:
lake build LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005

# In this tooling checkout's python/ directory:
uv run python -m lean_pool.sofa_certificates.discover \
  --pool /path/to/content-checkout \
  --workspace "$TMPDIR/sofa-cover-search"
```

This creates an inspectable `Discover.lean`, runs the rational interval evaluator,
and requires byte-identical results for both witness sets. Four subdivision digits
mean LL, LH, HL, HH, in that order. Search checks physical irrelevance, membership
of the already-certified local cell, and interval rejection before descending.
All leaves in these particular inputs end in interval rejection. The standalone
search uses evaluation to find witnesses; it does not add evaluation commands or
trust assumptions to the imported library.

## Transformation stages and maintenance

1. Import the 814 pinned Part E source files with namespaced imports and headers.
2. Factor large closed proof subtrees into named lemmas; share repeated subdivision
   paths every four levels. Re-expansion checks the original source text exactly.
3. Normalize visibility, module documentation, resource options, API names and
   line wrapping. Rename source modules and split the long theta reconstruction.
4. Expand 549 selected adaptive checks using the recorded quadtree witnesses,
   plus the separately profiled depth-nine phi-above check. Leaves are checked
   in the kernel and internal nodes compose existing soundness lemmas.
5. Assemble the 804 resulting generated fragments into the recorded 46 batches.
   Hoist private cell aliases, document public aliases, and expand roots whose
   earlier aliases would otherwise become forward references. Expansion audits
   check identical unary subdivision paths.
6. Move 119 pure combination fragments to `Reconstruction.lean`, preserving all
   25,086 public declaration names. This lets expensive leaf modules build in
   parallel. Normalize trailing whitespace and check all 47 intermediate digests.
7. Repack those modules into 32 certificate bundles, moving closed cell definitions
   before proof bodies, removing vacuous namespaces and preserving all names.
   This keeps the combined pool index below its size limit after main gained a
   further project. Check every final output digest.

`data/batch-assignment.json` records ordered source fragments;
`data/module-consolidation-map.json` records import relocation, including semantic
modules outside the emitted corpus. `data/cover-expansion-candidates.json` records
each selected theorem, root region, subdivision path and recursion budget.
`data/final-batch-assignment.json` and `data/final-module-map.json` record the
subsequent packing and semantic import relocation. These are explicit inputs
to the deterministic recipe. No current build timings,
GitHub credentials, machine-specific source paths or private generator are needed.

This is a reproduction of the **imported and optimized certificate corpus from
public upstream source**, not a claim to recover the upstream author's private
search history or regenerate the whole MovingSofa project from the paper alone.
The 22 other imported modules contain semantic and geometric proofs and are
outside this recipe. Mathematical changes to a cover domain or evaluator require
new witness search, reviewed source changes and the usual full Lean validation;
updating a checksum alone does not certify such a change. The expected digests
are tied to this content version and intentionally fail after an unrecorded port.

The initial clean replay verified all 47 intermediate modules in 25.42 seconds;
the complete replay including all 32 final bundles took 70.14 seconds on the
shared Azure VM. These measure source generation only. The import PR separately records
controlled Lean compile benchmarks and complete CI validation.
