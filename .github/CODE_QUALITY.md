# Code Quality Automation

Lean Pool uses deterministic CI for mechanical quality checks and LLM review for judgment calls. This page separates checks that are enforced today from planned automation.

## Enforced CI Gates

### 1. Lean Baseline

[`lean_action_ci.yml`](workflows/lean_action_ci.yml) currently runs:

- `lake exe mk_all --module --check` (the pool and project indexes must use `module` and `public import`)
- `lake build LeanPool`, with a 60-minute hard limit on every Lean process
- a warning scan over the build log
- a per-file build-time limit: every added or modified `LeanPool` file must build in under 600 s
- a per-file memory limit: the compiler of an added `LeanPool` file is stopped above 3 GiB, and the largest compiler is stopped if the runner runs out of memory
- the `LeanPoolLinters` compiler plugin, loaded by Lake for every LeanPool module
- `lake exe runLinter` on `LeanPool`
- `lake exe lint-style` on `LeanPool`
- `python -m lean_pool.quality --repo ..`

With `warningAsError = true` in `lakefile.toml`, every Lean warning is a
compile error (locally too). The warning scan over the build log remains for
warnings Lake itself prints.

Build-time limits follow Tau Ceti's CI performance gate.
[`build_time_limits.py`](../python/lean_pool/build_time_limits.py) runs every CI
`lake build` in its own process group and stops any Lean process still running after
60 minutes, which fails the build. Before returning, it cleans up its process group
and the descendants it observed, including after reparenting. If the process table
cannot be read, the build is stopped rather than left unwatched.

After the build, it reads Lake's per-module times from the log and fails when a file
the PR adds or modifies took more than 600 s. Times are Lake's wall-clock times on
GitHub's 4-vCPU runners. Existing files are checked only once a PR changes them.

The same watchdog looks at the memory of every Lean process once a second. It
counts anonymous memory, resident or swapped (`RssAnon` and `VmSwap`); the
compiled imports a process maps are shared and are not counted. This is a
sampled protection: it bounds what a compiler can gain between two looks, and
cannot guarantee that every workload fits between them.

- The compiler of a file the PR adds is stopped once it holds more than 3 GiB.
  Four compilers at that size, their shared imports and the system fit the
  runner's 16 GB. A compiled output restored from an earlier run is not seen
  by the watchdog, so for an added file it is kept only if its timing receipt
  records that it was compiled under this limit; otherwise it is rebuilt.
- When free memory and swap together fall below 1.5 GiB, the Lean process
  holding the most is stopped, and the error names every file that was compiling
  and what it held. Without this the runner dies and the log names nothing.

Lake reports a stopped file as failed and builds the rest, so one run names every
file over its limit. A file seen over its own limit fails the build. A stop asked
for under a shortage fails it only if the build then fails: a compiler that had
just finished is not counted as stopped. Existing files have no fixed limit:
when the budget was set (`main`, 2026-11-19, Lean v4.35.0) two files exceeded
it, `MovingSofa/Development/Geometry/Applications/Development001.lean` (8.6 GiB)
and `MovingSofa/Development/Geometry/Foundations/Development004.lean` (7.8 GiB),
and every other file held at most 2.7 GiB. The build log starts with the limits
and the runner's memory, and ends with every file whose compiler held 2 GiB or
more.

`check` records each changed module's time in a receipt next to its compiled
output (`<Module>.timing.json`), bound to a hash of that output's `.olean` files.
After all cache and artifact restores, `prepare` removes the compiled outputs of
every added or modified module the job is responsible for whose output has no
matching receipt. So output that was compiled without being timed is always
rebuilt, even from a cache produced under the same policy: an untouched file in
that cache need not have passed the changed-file limit. Each changed module must
then have either a fresh successful build timing from its responsible job or the
recorded time of the exact output being reused; that time is checked against the
limit either way, and a module with neither fails the check.

A receipt counts only for output that is present: a module whose `.olean` is
missing has no recorded time, whatever its receipt says, and is compiled and
timed again.

Shards check their assigned modules. Assembly, like single and rebased root
builds, checks every changed module, including those in the shards' projects. It
reuses a shard's output when that output arrived with its receipt; anything
assembly compiles itself is judged by assembly's own build time, which replaces
any time recorded earlier. No job can exempt a project from the check. The
canonical gate requires every shard and assembly to succeed. Untouched modules
can still reuse compiled output.

"Changed" is measured from the main commit the run is tested against: the tested
merge commit's first parent for a PR, not the event's `base.sha`, which can trail
main and would count projects merged since as the PR's own.

A later push to a PR restores the outputs of modules whose own source is unchanged
from that PR's newest successful run; Lake's traces decide which are still valid.
Reused PR, rebase and queue artifacts must still match `build_time_limits.py`.

The Lean workflow runs on Lean, Lake, project metadata, quality-checker, and workflow changes. It restores and saves Lake caches and pulls Mathlib oleans with `lake exe cache get` when the cache is cold.

The compiler plugin enforces the 200-line proof cap during the normal build, using original
source syntax and elaborated types rather than a Python text heuristic. Both tactic and term
proofs are checked, including proofs embedded in definitions, instances, and examples; tactic
blocks constructing data are not proofs. Declaration headers and comment-only lines are
excluded. Blank lines count, except inside block comments. Only the outermost overlong proof
is reported when proof ranges overlap. The existing build-warning gate rejects these warnings.
The plugin is build tooling under `scripts/ci/`, not a mathematical import of project modules.
Its pinned-Lean regression test runs in all three compiled-artifact CI test steps.

Lean Pool uses one `public import LeanPool.<Project>.Imports` per project in
`LeanPool.lean`. Each generated `LeanPool/<Project>/Imports.lean` publicly imports
the original project entry module and every source under that project, exactly
once and in sorted order. It contains only imports; keep mathematical declarations
and project cards in the existing source files. Run `lake exe mk_all --module`
after adding, removing or moving a source, and commit the project aggregate as
well as the pool index. The quality linter and `mk_all --check` verify complete
public coverage at both levels. The 10,000-line limit still applies to every file.

The generated module-system indexes import every library file, so building them rejects any file missing a `module` header. Regenerate the indexes with `lake exe mk_all --module`. Package-level `requiresModuleSystem = true` also makes Lake warn when a legacy file imports Lean Pool.

### 2. Repository Quality Checker

[`python/lean_pool/quality.py`](../python/lean_pool/quality.py) enforces the repository-specific content rules.

Current checks:

- Lake discovers every `.lean` file under `LeanPool/`; every project source is also reachable from its public `Imports.lean`
- every content `.lean` file except `LeanPool.lean` has the exact four-line file header
- content files do not contain `set_option`, `nolint` waivers, broad `import Mathlib`, `sorry`, `admit`, unchecked declarations (`axiom`, `constant`, `unsafe`, `partial`, `opaque`, `@[extern]`), or diagnostic commands (`#check`, `#print`, `#eval`, `#reduce`, `#guard_msgs`, `#lint`)
- content files do not manipulate elaborator options programmatically: option-API tokens (`withOptions`, `modifyOptions`, `withRecDepth`, `withCurrHeartbeats`, `KVMap`/`Options`/`Option` setters, ...) and gated option names (`maxRecDepth`, `maxHeartbeats`, `maxSynthPendingDepth`, `linter.*`) are forbidden in code (comments are fine) — ``withOptions (fun o => o.set `maxRecDepth 100000)`` inside an elaborator is still `set_option maxRecDepth 100000`
- Lake configuration does not pass forbidden option overrides, trace options, linter disables, or heartbeat / recursion-depth overrides
- the style-linter allowlist `scripts/nolints-style.txt` has no active entries
- no Lean content file exceeds 10000 non-blank, non-comment code lines
- `LeanPool/projects/` contains one valid YAML mapping per project, with its filename matching the unique slug; duplicate fields, nested cards, and mixed old/new registries fail validation
- project entries have required fields: `slug`, `title`, `entry_module`, `authors`, `source`, `status`, `provenance`, `main_declarations`, and `tags`
- project entries also carry documentation metadata: `summary`, `branch`, `main_results`, and `msc`
- project `status` is `verified`
- project `provenance` records who wrote the Lean proofs and is one of `human`, `AI`, or `mix` (see [`candidates/provenance.md`](../candidates/provenance.md) for the rubric): `human` when the proofs were written by people, `AI` when they mostly came from an AI system, and `mix` when both contributed substantially
- project `source` includes at least one recognized primary source key among `arxiv`, `doi`, and `url` (more than one is fine)
- project authors, main declarations, and tags are nonempty string lists
- project summaries and branches are nonempty strings, MSC codes are a nonempty string list, and `main_results` is a nonempty list of `declaration` / `informal` entries
- project `main_results[*].declaration` values include every `main_declarations` entry, so compact project cards and richer documentation metadata cannot drift
- project `slug` and `entry_module` values are unique
- every registered project `entry_module` is imported by its project’s public `Imports.lean`
- every project has a top-level entry file `LeanPool/<Project>.lean`, including projects with nested registered entry modules
- every nested registered entry module is reachable through its top-level entry file's imports
- every top-level module `LeanPool/Foo.lean` belongs to the namespace of a registered `entry_module`; no module is exempt
- project entry modules and listed main declarations resolve in Lean
- generated entry-point project cards match `LeanPool/projects/*.yaml`
- public declarations depend only on the allowed axiom set: `Classical.choice`, `propext`, and `Quot.sound`
- no pool module prints a message when it is compiled. Lake keeps each module's compiler output beside its compiled files, and the checker rejects every entry there: a `Try this` suggestion nobody followed (from `simp?`, `exact?`, a `ring` that fell back to `ring_nf`, a linter hint), `@[simps?]` or `to_additive?` output, or anything a custom elaborator logs. Write the suggested tactic and remove the output. A module without a readable log fails
- a Lean environment audit (run via `lake env lean --run` with extensions disabled, so project notation cannot interfere) walks **every** declaration compiled into a pool module — including elaborator auxiliaries and generated declarations the textual scans cannot see — and rejects any that references option-manipulating constants, embeds a gated option-name literal (however the `Name` was assembled), directly references an axiom-injecting constant (`sorryAx`, `ofReduceBool`, ...), or is itself an axiom declared inside a pool module (which is how `native_decide` and `addDecl`-of-an-axiom backdoors surface)

The checker also has `--write-project-cards` to regenerate entry-point module docstrings from `LeanPool/projects/*.yaml`.

### 3. PR Separation

[`content-pr-guard.yml`](workflows/content-pr-guard.yml) enforces PR scope separation.

Content files are:

- `LeanPool/**/*.lean`
- `LeanPool/projects/*.yaml`

A PR may touch only content files or only non-content files. Mixing these categories fails CI, except that a Lean/Mathlib version bump may pair content with the toolchain, manifest, lakefile, their `docbuild/` equivalents, and this workflow.

Branch protection requires the build, separation and documentation gates; the merge queue validates their combined result on current main.

### 4. Python CI

[`python_ci.yml`](workflows/python_ci.yml) runs:

- `uv sync --locked --group dev`
- `uv run ruff check .`
- `uv run ruff format --check .`
- `uv sync --locked --group test`
- `uv run pytest --cov`

### 5. Workflow Hygiene

[`workflow_lint.yml`](workflows/workflow_lint.yml) runs `actionlint` and checks that GitHub Actions are SHA-pinned.

### 6. LLM Review

A private worker polls open PRs and `/review` comments every ten minutes. Automatic content reviews wait for successful Lean Action CI on the current head. Anyone can request a review on any open PR with `/review`. The worker posts the existing sticky comment with the reviewed head SHA, rubric verdicts, findings, and token accounting. Reviews run at `xhigh` on Codex subscription quota with no paid API fallback; the heading of each review names the model that produced it. See [review operations](../python/review-operations.md).

The rules applied depend on what the PR does:

| PR kind | Detected by | Rules |
|---|---|---|
| project | adds a project directory that appears only through added `.lean` files | [`REVIEW_RULES.md`](REVIEW_RULES.md) — fit and significance |
| refactor | only touches projects already in the pool | [`REFACTOR_REVIEW_RULES.md`](REFACTOR_REVIEW_RULES.md) — tech debt and maintainability |

The review workflow checks out the base branch only. It does not execute PR-head code.

### 7. Proof Profiling

[`proof-profile.yml`](workflows/proof-profile.yml) is advisory. It runs on PR open, `/profile` comments from trusted users, and `workflow_dispatch`.

Current behavior:

- checks out the PR head
- restores Lake caches and fetches Mathlib cache if needed
- profiles new and modified Lean files under `LeanPool/`
- posts or updates a sticky PR comment
- uploads the raw profile log as an artifact

Proof profiling does not block merge.

### 8. Dependency Updates

[`update.yml`](workflows/update.yml) is manually dispatched. It uses `leanprover-community/mathlib-update-action` to check for Mathlib updates and create a PR on success or an issue on failure.

Scheduled update checks are future work.

### 9. Stale Bot

[`stale.yml`](workflows/stale.yml) runs daily:

- PRs idle over 30 days are labeled `stale`
- stale PRs idle another 14 days are closed
- issues idle over 90 days are labeled `stale`
- stale issues idle another 30 days are closed
- `pinned`, `roadmap`, and `good-first-issue` labels are exempt

### 10. Documentation

[`docs.yml`](workflows/docs.yml) retains cheap workspace and generated-index
preflight checks for PRs and merge groups. It does not generate documentation.

[`docs-publish.yml`](workflows/docs-publish.yml) publishes documentation daily
at 06:23 UTC or on manual dispatch, independently of merges. It documents only
LeanPool modules and links dependencies to their hosted documentation. Bounded
analysis jobs save consistent incremental checkpoints; a separate rendering job
and exposition build must both finish and validate before Pages is replaced.
The published `SOURCE_SHA` records the documented snapshot. See the
[documentation operations guide](../docbuild/README.md).

## Future Work

The following items are documented goals but are not fully implemented or enforced yet:

- branch protection requiring the CI gates before merge
- scheduled Lean/Mathlib update checks
- LeanExplore semantic dedup comments in PRs; the prototype CLI is [`python/lean_pool/semantic_dedup.py`](../python/lean_pool/semantic_dedup.py)
- controlled tag vocabulary for `LeanPool/projects/*.yaml`; tags are currently only checked as nonempty strings
- generated domain/status indexes
- directory index-file policy: every directory under `LeanPool/` containing Lean files should have an import-only index file with a module docstring
- repository-wide slowest-proof reports and persisted performance trend artifacts
