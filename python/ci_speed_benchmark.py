"""Compare complete validation paths without publishing any validation caches."""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

BASELINE_FILES = ("quality.py", "validation_cache.py", "ci_artifacts.py")


def prepare_tools(root: Path, directory: Path, variant: str, baseline: str) -> dict:
    """Load the selected implementation while keeping checked source inputs fixed."""
    package = directory / "lean_pool"
    shutil.copytree(
        root / "python/lean_pool",
        package,
        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
    )
    if variant == "baseline":
        for name in BASELINE_FILES:
            (package / name).write_bytes(
                subprocess.check_output(
                    ["git", "show", f"{baseline}:python/lean_pool/{name}"],
                    cwd=root,
                )
            )
    return os.environ | {"PYTHONPATH": str(directory)}


def run_phase(root: Path, env: dict, report: dict, name: str, command: list[str]):
    """Record wall time, peak process memory, outcome, and actual check reuse."""
    directory = root / "benchmark-results"
    log = directory / f"{name}.log"
    measurements = directory / f"{name}.time"
    print(f"Starting {name}", flush=True)
    started = time.perf_counter()
    with log.open("w") as output:
        process = subprocess.run(
            ["/usr/bin/time", "-v", "-o", str(measurements), *command],
            cwd=root,
            env=env,
            stdout=output,
            stderr=subprocess.STDOUT,
        )
    phase = {
        "name": name,
        "seconds": time.perf_counter() - started,
        "exit_code": process.returncode,
    }
    text = log.read_text()
    summary = re.search(r"Validation: (\d+) cached checks, (\d+) fresh checks", text)
    if summary:
        phase.update(cached_checks=int(summary[1]), fresh_checks=int(summary[2]))
    peak = re.search(
        r"Maximum resident set size \(kbytes\): (\d+)", measurements.read_text()
    )
    if peak:
        phase["peak_memory_mib"] = int(peak[1]) / 1024
    report["phases"].append(phase)
    (directory / "timings.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(phase), flush=True)
    if process.returncode:
        print(text[-20000:], flush=True)
        raise subprocess.CalledProcessError(process.returncode, command)
    if name.endswith("build") and re.search(r"(^|: )warning:", text, re.MULTILINE):
        raise ValueError("Lean build emitted warnings")
    if name.startswith("warm-") and name.endswith(("lint", "quality")):
        if summary is None or phase["fresh_checks"] != 0:
            raise ValueError("Warm measurement did not reuse every successful check")


def measure(root: Path, env: dict, report: dict, receipts: Path) -> None:
    """Exercise successful fresh checks, then reuse those passes on unchanged files."""
    python = ["uv", "run", "--project", "python", "python"]
    lake = str(Path.home() / ".elan/bin/lake")
    validation = [*python, "-m", "lean_pool.validation_cache"]
    common = ["--repo", str(root), "--cache", str(receipts)]
    archive = "lean-pool-build.tar." + (
        "gz" if report["variant"] == "baseline" else "zst"
    )
    run_phase(
        root, env, report, "indexes", [lake, "exe", "mk_all", "--module", "--check"]
    )
    run_phase(root, env, report, "initial-build", [lake, "build", "LeanPool"])
    run_phase(
        root, env, report, "package", [*python, "-m", "lean_pool.ci_artifacts", "pack"]
    )
    report["archive_bytes"] = (root / archive).stat().st_size
    run_phase(
        root,
        env,
        report,
        "unpack",
        [
            *python,
            "-c",
            "from pathlib import Path; "
            "from lean_pool.ci_artifacts import restore_build; "
            f"assert restore_build(Path.cwd(), Path({archive!r}))",
        ],
    )
    for state in ("fresh", "warm"):
        if state == "warm":
            run_phase(root, env, report, "warm-build", [lake, "build", "LeanPool"])
        run_phase(root, env, report, f"{state}-lint", [*validation, "lint", *common])
        run_phase(
            root, env, report, f"{state}-style", [lake, "exe", "lint-style", "LeanPool"]
        )
        run_phase(
            root, env, report, f"{state}-quality", [*validation, "quality", *common]
        )


def main() -> None:
    """Compare only the implementation, with the checkout and saved build held fixed."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--variant", choices=("baseline", "optimized"), required=True)
    parser.add_argument("--baseline", required=True)
    arguments = parser.parse_args()
    root = Path.cwd()
    (root / "benchmark-results").mkdir()
    report = {
        "variant": arguments.variant,
        "baseline": arguments.baseline,
        "checkout": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
        "initial_build_cache": os.environ.get("BUILD_CACHE_KEY"),
        "initial_dependency_cache": os.environ.get("DEPENDENCY_CACHE_KEY"),
        "phases": [],
    }
    print(json.dumps(report), flush=True)
    with tempfile.TemporaryDirectory(prefix="ci-speed-tools-") as name:
        directory = Path(name)
        env = prepare_tools(root, directory, arguments.variant, arguments.baseline)
        measure(root, env, report, directory / "receipts")


if __name__ == "__main__":
    main()
