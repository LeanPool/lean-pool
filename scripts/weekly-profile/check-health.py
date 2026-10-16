#!/usr/bin/env python3
"""Check publication age and useful capture progress independently of retries."""

import json
import logging
import os
from datetime import UTC, datetime, timedelta
from pathlib import Path
from urllib.request import urlopen

LOGGER = logging.getLogger(__name__)
MANIFEST_URL = "https://vilin97.github.io/lean-source-profiler/pool/manifest.json"


def check_progress(root: Path, now: datetime) -> None:
    """Repeated failed attempts must not count as useful recording progress."""
    active = root / "active.json"
    if not active.exists():
        return
    state = json.loads(active.read_text())
    progress = root / "runs" / state["runId"] / "recording/progress.json"
    successful = (
        json.loads(progress.read_text())["successful"] if progress.exists() else 0
    )
    fingerprint = [state["runId"], state["phase"]]
    checkpoint = root / "health.json"
    saved = json.loads(checkpoint.read_text()) if checkpoint.exists() else {}
    if saved.get("progress") != fingerprint or successful > saved.get("successful", 0):
        saved = {
            "progress": fingerprint,
            "successful": successful,
            "lastProgressAt": now.isoformat(),
        }
        temporary = checkpoint.with_suffix(".tmp")
        temporary.write_text(json.dumps(saved, indent=2) + "\n")
        temporary.replace(checkpoint)
    if state["phase"] != "complete" and now - datetime.fromisoformat(
        saved["lastProgressAt"]
    ) > timedelta(hours=72):
        raise RuntimeError(f"No useful profiling progress for 72 hours: {fingerprint}")


def check_health(root: Path, now: datetime) -> None:
    """Require a reachable recent public dataset and an advancing local run."""
    check_progress(root, now)
    with urlopen(MANIFEST_URL, timeout=20) as response:
        manifest = json.load(response)
    completed = datetime.fromisoformat(manifest["completedAt"])
    if now - completed > timedelta(days=10):
        raise RuntimeError(
            f"Public source profile is stale: completed {completed.isoformat()}"
        )
    LOGGER.info("Public source profile completed %s; progress is healthy.", completed)


def main() -> int:
    """Expose a nonzero health signal for systemd and external monitoring."""
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    root = Path(os.environ.get("LEAN_POOL_PROFILE_ROOT", "/data/lean-pool-profile"))
    try:
        check_health(root, datetime.now(UTC))
    except Exception:
        LOGGER.exception("Weekly source profiling is unhealthy.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
