<p align="center">
  <img src="logo.png" alt="Lean Pool logo" width="240">
</p>

# lean-pool

[![Lean Action CI](https://github.com/LeanPool/lean-pool/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LeanPool/lean-pool/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://leanpool.github.io/lean-pool/)
[![Exposition](https://img.shields.io/badge/exposition-online-8a4fff)](https://leanpool.github.io/lean-pool/exposition/)
[![Zulip](https://img.shields.io/badge/Zulip-Lean_Pool-6492FE?logo=zulip&logoColor=white)](https://leanprover.zulipchat.com/#narrow/channel/619231-Lean-Pool)
[![Semantic Search](https://img.shields.io/badge/semantic_search-Octo-2f80ed)](https://octo.axiomatic-ai.com/search?scopes=repo%3ALeanPool%2Flean-pool)
[![License](https://img.shields.io/github/license/LeanPool/lean-pool)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20513444.svg)](https://doi.org/10.5281/zenodo.20513444)
[![arXiv](https://img.shields.io/badge/arXiv-2609.25199-b31b1b)](https://arxiv.org/abs/2609.25199)

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, it relies on deterministic linters and LLM judgment, so it can grow faster while staying `sorry`-free and pinned to the latest Mathlib. Tau Ceti is also a pinned Lake dependency; import its modules directly instead of vendoring projects already in Tau Ceti or Mathlib. See [`MOTIVATION.md`](MOTIVATION.md) for the why, browse the API docs at <https://leanpool.github.io/lean-pool/>, and explore each project's dependency graph and declarations in the [exposition site](https://leanpool.github.io/lean-pool/exposition/).

Semantic search is also available via the [API](https://search.octo.axiomatic-ai.com/api/search).

<!-- BEGIN STATS -->
**289** formalization projects · **9,933,135** lines of Lean
<!-- END STATS -->

<sub>(stats above are refreshed automatically by the [generated-metadata workflow](.github/workflows/notice.yml) — edit [`python/lean_pool/stats.py`](python/lean_pool/stats.py), not the numbers)</sub>

So far, projects have been added by hand: each is a suitable, permissively licensed (Apache-2.0 or MIT) Lean repository, bumped to the latest Lean and Mathlib, made to pass [CI](.github/workflows/lean_action_ci.yml) — it builds warning-free and clears Mathlib's linters, the style checker, and the repository quality gates (no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, file headers, size limits) — and an [LLM review](.github/REVIEW_RULES.md) of fit and significance, then merged.

LLM reviews use GPT-6-Astra at `xhigh` reasoning effort through a privately operated Codex worker, without paid OpenAI API requests or an API fallback. Reviews also show an estimated dollar cost at official Standard API token rates, labeled separately from Codex quota billing. See [review operations](python/review-operations.md) for deployment and diagnostics.

Project PRs also receive an advisory Greptile review, configured in [`.greptile/`](.greptile/), for cross-file integration, reusable abstractions, completeness, maintainability, and measured cost. It supplements rather than replaces the independent LLM verdict.

### Getting started

Requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup    # pull Mathlib oleans, build the whole pool (~1.5h), install Python tooling
```

To work on a single project you don't need the whole pool built — see the
[fast per-project build](CONTRIBUTING.md#dev-setup) in `CONTRIBUTING.md`.

To regenerate the preserved Zeta5 numerical certificates, see the
[certificate reproduction guide](scripts/zeta5-certificates/README.md).

The [moving-sofa certificate recipe](python/lean_pool/sofa_certificates/README.md)
regenerates its optimized certificate modules from pinned public inputs.

### Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

The PR author or a maintainer can comment `/profile` to request an advisory
compile-cost report. Failed or zero-phase timed runs show unavailable timing
and are excluded from totals; errors and any successfully measured heartbeat
counts remain visible.

Accepted PRs enter GitHub’s merge queue. CI checks the combined changes against
current main without repeatedly updating authors’ branches. Each project owns
its YAML card and public `Imports.lean`; there is no shared import list to edit.
Conflicts in the same proof files still require a manual repair.

### Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).

### Difference from similar projects

[Tau Ceti](https://github.com/TauCetiProject/TauCeti) is another approach to solve the same problem. The differences are:
- Lean Pool accepts human-written projects, not just AI projects.
- Lean Pool is not a unified library like mathlib. Most projects are independent of each other.
- Lean Pool only accepts completed formalization projects.

[Palomar Registry](https://palomar-registry.org/) is also similar to Lean Pool. The differences are:
- Lean Pool maintains accepted projects.
- Lean Pool provides tools like search and documentation.
- Palomar is a registry, not a unified repository.

Projects accepted to the Palomar Registry may be submitted to Lean Pool, and priority will be given to them.

### Citation

To cite Lean Pool, use the [paper](https://arxiv.org/abs/2609.25199):

```bibtex
@misc{ilin2026leanpool,
  title = {{Lean Pool}: An {AI}-Maintained Archive of Formalized Mathematics},
  author = {Vasily Ilin},
  year = {2026},
  eprint = {2609.25199},
  archivePrefix = {arXiv},
  primaryClass = {cs.AI},
  doi = {10.48550/arXiv.2609.25199},
  url = {https://arxiv.org/abs/2609.25199}
}
```
