# Automated Mathlib bumps

Version bumps run on the **Lean VM**, using its `cx` Codex accounts. GitHub-hosted
runners no longer perform migrations. The nightly check remains at 05:23 UTC.

See [VM deployment and operations](../scripts/version-bump/README.md) for installation,
manual activation, recovery and validation. The implementation is
[`lean_pool.bump_vm`](../python/lean_pool/bump_vm.py).

The controller uses a full-history checkout, preserving existing `bump/<version>`
repairs while merging current main. This fixes the shallow checkout that made
resumed GitHub runs fail with `refusing to merge unrelated histories`.

Each repair starts with the authenticated `cx` account with the most remaining
quota. Availability is measured using the highest used percentage across the
reported quota windows. After a failure or an unsuccessful repair, quotas are
probed again and the next eligible, untried account continues from the saved
edits. Unknown quota, identity failures, and accounts with 98% or more usage are
ineligible. Account occupancy does not affect eligibility. There is no Claude or
API fallback. Exhausted attempts keep a checkpoint and retry after an hour.

The controller builds each project's public `Imports` module, checks warnings,
then runs the whole-pool build, index check, Mathlib linters, style checker and
quality checker independently of the agent. It opens or updates a **draft** PR;
reviewers assess statement changes and normal required CI before merging.
Execution transcripts, account identities and credentials remain private on the VM.
