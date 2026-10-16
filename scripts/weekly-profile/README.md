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

Capture failures trigger one dependency repair per service attempt. The runner
checks the failed files' native Lake setup, force-restores the pinned Mathlib
cache when imported artifacts are missing (ordinary cache restoration can trust
stale trace files), and incrementally builds remaining imports and failed files
with Lake. It verifies the artifacts before retrying capture. Successful
recordings and source/profiler pins are preserved, including if repair itself is
interrupted. A repeated proof or profiler error fails the attempt rather than
looping inside it; systemd retains the hourly retry policy.

An independent hourly health check fails if the public recording is over ten
days old or an unfinished local run has made no useful progress for 72 hours.
It tracks the highest captured-file count per run/stage, so restarting a failed
capture or rewriting its progress timestamp cannot hide a stall. The health
service's failure and journal are available to host monitoring; the timer itself
does not send notifications.

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
install -m 755 scripts/weekly-profile/check-health.py /data/lean-pool-profile/bin/check-health.py
install -m 644 scripts/weekly-profile/*.service scripts/weekly-profile/*.timer \
  ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable lean-pool-source-profile-resume.service
systemctl --user enable --now lean-pool-source-profile.timer
systemctl --user enable --now lean-pool-source-profile-health.timer
systemctl --user start --no-block lean-pool-source-profile-health.service
systemctl --user start --no-block lean-pool-source-profile.service
```

The runner owns private checkouts under its data directory and never switches
the shared development checkout. Optional environment overrides belong in
`/data/lean-pool-profile/environment`; changing capture scope or configuration
requires finishing the current run first.

`LEAN_POOL_PROFILE_POOL_REF` and `LEAN_POOL_PROFILE_PROFILER_REF` optionally
select the Git revisions used for **new** recordings (both default to `main`).
An unfinished recording always keeps its original pins. To deploy a changed
profiler immediately, stop the service, preserve the old `active.json` alongside
its recording, set the new profiler ref, and start a new recording. Recordings
from different profiler revisions must not be combined. Clear a temporary ref
override after its fix lands on main to resume automatic weekly updates.

## Monitor or run manually

```bash
systemctl --user status lean-pool-source-profile.service
systemctl --user list-timers lean-pool-source-profile.timer
journalctl --user -u lean-pool-source-profile.service -f
cat /data/lean-pool-profile/active.json
# Independent freshness/progress check, also suitable for external monitoring:
python3 /data/lean-pool-profile/bin/check-health.py
systemctl --user status lean-pool-source-profile-health.service
journalctl --user -u lean-pool-source-profile-health.service -n 20
# Once capture starts, the current recording also has progress.json and errors.json.
systemctl --user start --no-block lean-pool-source-profile.service
```

`active.json` names the run under `runs/` and its current stage. Each recording
contains its pinned `inventory.json`, raw captures, source summaries, build
receipts, progress and final coverage. Successful publication adds
`complete.json` and records the publication commit. The dataset manifest and
coverage audit are public at `/pool/manifest.json` and `/pool/coverage.json`.
