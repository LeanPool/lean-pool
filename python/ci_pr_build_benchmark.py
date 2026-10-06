"""Measure compilation reuse on identical real PR sources and cache inputs."""
import json
import logging
import os
import re
import subprocess
import sys
import time
from pathlib import Path

from lean_pool import ci_pr_build

logging.basicConfig(level=logging.INFO, format="%(message)s")
root = Path.cwd()
results = root / "benchmark-results"
results.mkdir(exist_ok=True)
variant = os.environ["VARIANT"]
report = {
    "variant": variant,
    "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "cache": os.environ["BUILD_CACHE_KEY"],
    "dependency_cache": os.environ["DEPENDENCY_CACHE_KEY"],
    "phases": {},
}
assert report["head"] == os.environ["PR_HEAD"]
assert report["cache"] == os.environ["EXPECTED_CACHE"]

def save():
    (results / "timings.json").write_text(json.dumps(report, indent=2) + "\n")

def phase(name, command):
    started = time.monotonic()
    with (results / (name + ".log")).open("w") as log:
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        for line in process.stdout:
            print(line, end="", flush=True)
            log.write(line)
        status = process.wait()
    report["phases"][name] = {"seconds": time.monotonic() - started, "returncode": status}
    save()
    if status:
        raise subprocess.CalledProcessError(status, command)

started = time.monotonic()
if variant == "optimized":
    begin = time.monotonic()
    report["restored"] = ci_pr_build.restore_prior_build(
        root, os.environ["GITHUB_REPOSITORY"], int(os.environ["PR_NUMBER"]),
        os.environ["PR_BRANCH"], os.environ["PR_HEAD"], os.environ["PR_BASE"],
        int(os.environ["GITHUB_RUN_ID"]),
    )
    report["phases"]["reuse"] = {"seconds": time.monotonic() - begin, "returncode": 0}
    save()
    assert report["restored"], "Optimized measurement must actually recover matching compiled files"
phase("index", [os.path.expanduser("~/.elan/bin/lake"), "exe", "mk_all", "--module", "--check"])
phase("build", [os.path.expanduser("~/.elan/bin/lake"), "build", "LeanPool"])
assert not re.search(r"(^|: )warning:", (results / "build.log").read_text(), re.MULTILINE)
phase("lint", [sys.executable, "-m", "lean_pool.validation_cache", "lint", "--repo", "."])
phase("style", [os.path.expanduser("~/.elan/bin/lake"), "exe", "lint-style", "LeanPool"])
phase("quality", [sys.executable, "-m", "lean_pool.validation_cache", "quality", "--repo", "."])
report["total_seconds"] = time.monotonic() - started
save()
print(json.dumps(report, indent=2), flush=True)
