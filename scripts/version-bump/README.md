# Version bumps on the Lean VM

The `lean-pool-version-bump.timer` user timer checks for new Mathlib releases,
including release candidates, at **05:23 UTC daily**. It also activates five
minutes after boot to resume interrupted work. The service runs entirely on
`lean`, independently of GitHub runners. It survives logout through user lingering.

The controller resumes the oldest pending target, keeps a full-history private
checkout, merges current main without force-pushing, updates both sets of pins
and manifests, and fetches Mathlib's build cache. It builds each project's public
`Imports` module. Failing projects and warnings are repaired sequentially through
`cx`; each attempt probes quotas and picks the eligible account with the lowest
maximum used percentage across the reported windows. Thus the account with the
most remaining usable quota starts first, rather than the account resetting soonest.
Every eligible account is tried at most once per project per activation. Failed
attempts retain partial edits and refresh diagnostics for the next account.

Repairs use `gpt-6.1-sol` / `xhigh`, with a workspace sandbox and CLI Lake/Lean.
Account configuration and MCP servers are not loaded into the agent. Subscription
credentials are supplied by `cx`; the runner clears inherited API credentials.
There is no Claude or API fallback, purchase, or reset-credit action.

The service limits its process tree to 24 GiB and four CPU cores, with two Lean
threads, low scheduling weight and a 30 GiB free-space startup check. It neither
switches the shared `/data/lean-pool` checkout nor changes global account policy.
The account pool remains available to other services.

## Deploy

Use an authenticated VM operator account with GitHub push and PR access, elan,
Lake, uv, and the VM's existing `cx` installation. Enable user lingering if needed.
Install a trusted revision's Python package separately from the migration checkout:

```sh
# From the trusted LeanPool checkout on the VM:
install -d -m 700 /data/lean-pool-bump/engine /data/lean-pool-bump/tmp
# Record the deployed commit outside the archive.
git rev-parse HEAD > /data/lean-pool-bump/engine-revision
# Do not replace the controller while its service is running.
git archive HEAD python scripts/version-bump | tar -x -C /data/lean-pool-bump/engine
cd /data/lean-pool-bump/engine/python
uv sync --locked
uv run python -m lean_pool.bump_vm --help
install -m 644 ../scripts/version-bump/*.service ../scripts/version-bump/*.timer \
  ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now lean-pool-version-bump.timer
systemctl --user start --no-block lean-pool-version-bump.service
```

During migration from the old GitHub workflow, disable `mathlib-bump.yml` before
starting the VM service, so two controllers cannot write the same branch. This
change removes that workflow from the repository; its historical logs remain.

## Operate

```sh
systemctl --user status lean-pool-version-bump.service
systemctl --user list-timers lean-pool-version-bump.timer
journalctl --user -u lean-pool-version-bump.service -n 30
cat /data/lean-pool-bump/pending.json
# Manual check/resume, through the same process lock:
systemctl --user start --no-block lean-pool-version-bump.service
# Stop and disable future scheduling:
systemctl --user disable --now lean-pool-version-bump.timer
systemctl --user stop lean-pool-version-bump.service
```

With the service stopped, the installed module also accepts `--version v4.35.0`,
`--stable-only`, and `--probe-only`. Explicit targets must be published Mathlib
releases newer than main; a pending target cannot be silently replaced. Probe-only
runs still validate and publish a draft, but never invoke a repair account.
`LEAN_POOL_BUMP_MODEL` can override the repair model through the private optional
`/data/lean-pool-bump/environment` file.

`pending.json`, the private checkout, logs and PR-body staging stay under
`/data/lean-pool-bump` with a private umask. A process lock prevents timer/manual
activation overlap. Systemd retries failures after an hour, while boot activation
resumes after restarts. Partial project edits and pin updates are checkpointed
before upstream merges. Unexpected edits, merge conflicts and racing pushes stop
without discarding changes; inspect and repair those explicitly. Do not delete a
pending checkpoint to force a fresh run.

The controller commits and pushes repairs incrementally. A failed account
waterfall publishes saved progress as a draft and leaves the checkpoint pending.
Whole-pool build, warning, index, linter, style and quality results are measured
outside the agent. Only passing every gate clears the checkpoint; even then the
PR remains a draft for statement review and normal current-head CI.

## Tests

```sh
cd python
uv run ruff check
uv run ruff format --check
uv run --group test pytest tests/test_bump.py tests/test_bump_vm.py
```

Tests reproduce resuming a shallow clone with a real diverged Git history, check
live quota ordering and reordering, preserve failed-attempt checkpoints, reject
out-of-scope edits, and enforce independent warning and quality validation.
