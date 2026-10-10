# Weekly whole-pool profiling

The Azure VM captures LeanPool every **Monday at 02:00 UTC**, using
[lean-source-profiler](https://github.com/Vilin97/lean-source-profiler)'s compact
source capture. The audited result replaces the
[public explorer](https://vilin97.github.io/lean-source-profiler/pool/) and its
date badge. A manual run uses the same service and publication path.

The service has no runtime timeout: a recording can take more than 24 hours.
It continues after logout, retries failures after an hour, and resumes an
unfinished run after reboot. A job lock prevents overlapping recordings.
Each run pins the current LeanPool and profiler commits; retries keep those
commits and reuse successfully captured files. Native Lake builds include every
source module, including files outside project entry imports. Sources, native
module setups, raw recordings and exported summaries are audited before
publication. Failed coverage leaves the previous public snapshot intact.

All checkouts, recordings, temporary files and npm downloads live under
`/data/lean-pool-profile`. Existing elan and user cache directories also resolve
onto `/data`. The runner refuses to start with less than 30 GiB free and retains
the two most recent successful recordings plus unfinished runs. Builds/captures
use the repository's native options. Source timings include instrumentation and
VM scheduling overhead; isolated file totals are not a parallel build duration.

## Install on this VM

The VM needs elan/Lake, Node.js 20+, npm, Python 3, Git and authenticated GitHub
push access to `Vilin97/lean-source-profiler`. The user service manager must have
lingering enabled (`loginctl show-user vasil -p Linger`). Publishing uses GitHub
Pages from that repository's `main:docs` directory and ordinary pushes; a racing
push is retried from current main while preserving unrelated viewer changes.

From the LeanPool checkout:

```bash
cx doctor
install -d /data/lean-pool-profile/bin /data/lean-pool-profile/tmp
install -m 755 scripts/weekly-profile/run.py /data/lean-pool-profile/bin/run.py
install -m 644 scripts/weekly-profile/*.service scripts/weekly-profile/*.timer \
  ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable lean-pool-source-profile-resume.service
systemctl --user enable --now lean-pool-source-profile.timer
systemctl --user start --no-block lean-pool-source-profile.service
```

The runner owns private checkouts under its data directory and never switches
the shared development checkout. Optional environment overrides belong in
`/data/lean-pool-profile/environment`; changing capture scope or configuration
requires finishing the current run first.

## Monitor or run manually

```bash
systemctl --user status lean-pool-source-profile.service
systemctl --user list-timers lean-pool-source-profile.timer
journalctl --user -u lean-pool-source-profile.service -f
cat /data/lean-pool-profile/active.json
# Once capture starts, the current recording also has progress.json and errors.json.
systemctl --user start --no-block lean-pool-source-profile.service
```

`active.json` names the run under `runs/` and its current stage. Each recording
contains its pinned `inventory.json`, raw captures, source summaries, build
receipts, progress and final coverage. Successful publication adds
`complete.json` and records the publication commit. The dataset manifest and
coverage audit are public at `/pool/manifest.json` and `/pool/coverage.json`.
