# Daily documentation

API documentation and exposition publish through
[Daily documentation](../.github/workflows/docs-publish.yml) at **06:23 UTC daily**.
Maintainers can also dispatch that workflow manually. Publication never runs on a
PR, merge group or ordinary push. The independent `Documentation preflight`
check still validates workspace compatibility and generated indexes.

Each run uses one fixed Git revision. The previously published site stays online
until API documentation and exposition both pass validation. `/SOURCE_SHA` and
`/deployments/<commit>.txt` identify the published revision. A manual dispatch
on another branch produces build artifacts but cannot publish Pages.

## Incremental analysis

The pinned doc-gen fork implements interproject linking from upstream
[PR396](https://github.com/leanprover/doc-gen4/pull/396). Only `LeanPool` modules
receive full analysis and HTML pages. Mathlib and Lean references link to hosted
Mathlib documentation; Tau Ceti references link to its own documentation. These
sites may describe a different dependency revision, so declaration links use
their name resolver. Toolchain upgrades must select a compatible doc-gen revision
as well as updating the nested manifest.

The runtime discovers every local module directly. It never modifies the empty
production `LeanPool.lean` or loads an import-all Lean environment. After local
analysis, it records external names from dependency environments and renders all
local module records directly from the database.

Four sequential analysis stages each allow 90 minutes of analysis. They restore
the newest checkpoint compatible with the pinned dependencies, then process
modules in dependency order in batches of 128. Each successful batch advances a
cursor tied to all source files, configuration and linking policy. Changes reset
that cursor while retaining Lake's ordinary per-module trace checking.

Before each batch, the runner snapshots the database and its markers. If the
batch times out, its process group is stopped and that pair is restored before
the completed work is saved. A build error fails the stage and does not publish
a checkpoint from the failed batch. Every saved database passes SQLite integrity
and WAL checks. Checkpoint keys include the run, attempt and stage; cache
maintenance retains the latest saved main checkpoint.

If all four allowances are used, the run reports failure and leaves the site
unchanged. The next daily or manually dispatched run resumes saved progress.
Repeated no-progress failures require diagnosis rather than repeated retries.

HTML rendering has its own job budget and requires complete analysis for the
same snapshot. Validation requires a page for every local module, rejects
accidentally rendered dependency trees and verifies the source marker when the
two sites are assembled. Announcement jobs continue to defer projects whose
published documentation is unavailable.

## Local commands

From the repository root, after fetching the compiled Lean artifacts:

```bash
export DOCGEN_LOCAL_MODULE_ROOTS=LeanPool
export DOCGEN_DEPS_DOCS_URL=https://leanprover-community.github.io/mathlib4_docs
export DOCGEN_DEPS_DOCS_URLS=TauCeti=https://taucetiproject.github.io/TauCeti/docs
PYTHONPATH=python python3 -m lean_pool.documentation prepare
PYTHONPATH=python python3 -m lean_pool.documentation batch --seconds 5400
PYTHONPATH=python python3 -m lean_pool.documentation render
```

Repeat `batch` until complete before running `render`. Preserve the whole
`docbuild/.lake/build` tree together: a marker alone does not contain its SQLite
documentation data. Workflow artifacts retain analysis cursors for diagnosis;
GitHub Actions reports publishing failures separately from PR validation.
