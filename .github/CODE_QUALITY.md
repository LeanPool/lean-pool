# Code Quality Automation

Lean Pool uses deterministic CI for mechanical quality checks and LLM review for judgment calls. This page separates checks that are enforced today from planned automation.

## Enforced CI Gates

### 1. Lean Baseline

[`lean_action_ci.yml`](workflows/lean_action_ci.yml) currently runs:

- `lake exe mk_all --module --check` (the pool and project indexes must use `module` and `public import`)
- `lake build LeanPool`
- a warning scan over the build log
- `lake exe runLinter` on `LeanPool`
- `lake exe lint-style` on `LeanPool`
- `python -m lean_pool.quality --repo ..`

The Lean workflow runs on Lean, Lake, project metadata, quality-checker, and workflow changes. It restores and saves Lake caches and pulls Mathlib oleans with `lake exe cache get` when the cache is cold.

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
- no theorem/lemma proof body exceeds 200 non-blank, non-comment code lines, using the current text heuristic
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
- every top-level project module `LeanPool/Foo.lean`, except `LeanPool/Basic.lean`, belongs to the namespace of a registered `entry_module`
- project entry modules and listed main declarations resolve in Lean
- generated entry-point project cards match `LeanPool/projects/*.yaml`
- public declarations depend only on the allowed axiom set: `Classical.choice`, `propext`, and `Quot.sound`
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

A private worker polls open PRs and `/review` comments every ten minutes. Automatic content reviews wait for successful Lean Action CI on the current head. Anyone can request a review on any open PR with `/review`. The worker posts the existing sticky comment with the reviewed head SHA, rubric verdicts, findings, and token accounting. Reviews use GPT-6-Astra at `xhigh` with Codex subscription quota and no paid API fallback. See [review operations](../python/review-operations.md).

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

[`docs.yml`](workflows/docs.yml) builds doc-gen4 documentation with the nested
[`docbuild/`](../docbuild/) Lake project. Pull requests build the docs site as a
check. Pushes to `main` build `LeanPool:docs` and deploy
`docbuild/.lake/build/doc` to GitHub Pages.

## Future Work

The following items are documented goals but are not fully implemented or enforced yet:

- branch protection requiring the CI gates before merge
- scheduled Lean/Mathlib update checks
- LeanExplore semantic dedup comments in PRs; the prototype CLI is [`python/lean_pool/semantic_dedup.py`](../python/lean_pool/semantic_dedup.py)
- controlled tag vocabulary for `LeanPool/projects/*.yaml`; tags are currently only checked as nonempty strings
- generated domain/status indexes
- directory index-file policy: every directory under `LeanPool/` containing Lean files should have an import-only index file with a module docstring
- AST-aware proof-size measurement; the current 200-line proof cap uses a text heuristic
- repository-wide slowest-proof reports and persisted performance trend artifacts
