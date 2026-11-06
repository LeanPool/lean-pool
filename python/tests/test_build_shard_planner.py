"""Cost-balanced CI build sharding (`scripts/ci/plan-build-shards.py`)."""

from __future__ import annotations

import json
import runpy
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PLANNER = runpy.run_path(str(ROOT / "scripts/ci/plan-build-shards.py"))
MEASURER = runpy.run_path(str(ROOT / "scripts/ci/measure-build-costs.py"))


def test_measured_seconds_sum_by_project() -> None:
    """Lake `Built` lines sum per project in both of Lake's duration units."""
    log = [
        "2026-11-06T14:54:55Z ✔ [8855/8879] Built "
        "LeanPool.MovingSofa.PartE.Bundle004 (865s)",
        "✔ [8858/8879] Built LeanPool.MovingSofa.Core.Bundle007 (87.4s)",
        "✔ [8859/8879] Built LeanPool.MovingSofa (250ms)",
        "✔ [10/20] Built LeanPool.CramerWold (2.6s)",
        "✔ [11/20] Built LeanPool.CramerWold:c.o (9s)",
        "✔ [3451/3818] Built LeanPoolLinters (933ms)",
        "⣿ [12/20] Running LeanPool.Other (5s)",
    ]
    assert MEASURER["project_seconds"](log) == {"CramerWold": 3, "MovingSofa": 953}


def test_unmeasured_projects_are_scaled_by_measured_rate() -> None:
    """A new project's size is converted to seconds on the measured scale."""
    costs = PLANNER["project_costs"](
        {"Measured": 1_000, "Heavy": 100, "New": 500},
        {"Measured": 20.0, "Heavy": 3_600.0, "Deleted": 99.0},
    )
    rate = (20.0 + 3_600.0) / 1_100
    assert costs == {"Measured": 20.0, "Heavy": 3_600.0, "New": 500 * rate}


def test_without_measurements_costs_are_source_bytes() -> None:
    """With no cost file at all, source size alone still ranks the projects."""
    assert PLANNER["project_costs"]({"A": 10, "B": 30}, {}) == {"A": 10, "B": 30}


@pytest.mark.parametrize(
    "content", [None, "not json", "[]", '{"seconds": [1, 2]}', '{"other": {}}']
)
def test_unusable_cost_file_degrades_to_estimates(
    tmp_path: Path, content: str | None, capsys: pytest.CaptureFixture[str]
) -> None:
    """A bad cost file must never break the plan job; it only warns."""
    path = tmp_path / "build-costs.json"
    if content is not None:
        path.write_text(content)
    assert PLANNER["load_measured_costs"](path) == {}
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "ignoring build costs" in captured.err


def test_assign_shards_isolates_expensive_few_file_project() -> None:
    """The run-42209045242 failure: cost, not file count, drives packing."""
    costs = {"MovingSofa": 21_000.0, "ConwaySoifer": 14_400.0}
    costs |= {f"Light{index:02d}": 1_000.0 for index in range(30)}
    shards = PLANNER["assign_shards"](costs, 3)
    loads = [load for load, _ in shards]
    assert sum(loads) == sum(costs.values())
    assert max(loads) <= 22_000.0
    homes = [
        names for _, names in shards if {"MovingSofa", "ConwaySoifer"} & set(names)
    ]
    assert len(homes) == 2
    assert sorted(name for _, names in shards for name in names) == sorted(costs)


def test_assign_shards_is_deterministic_and_drops_empty_shards() -> None:
    """Equal costs break ties on name; spare shards are not emitted."""
    costs = {"B": 1.0, "A": 1.0}
    assert PLANNER["assign_shards"](costs, 4) == [(1.0, ["A"]), (1.0, ["B"])]


def _plan(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    changed: list[str] | None = None,
    **environment: str,
) -> dict:
    """Run the planner's entry point against the repository tree."""
    monkeypatch.chdir(ROOT)
    for name in ("COLD", "FORCE_FULL", "DIFF_AVAILABLE", "CHANGED_FILES_PATH"):
        monkeypatch.delenv(name, raising=False)
    for name, value in environment.items():
        monkeypatch.setenv(name, value)
    if changed is not None:
        listing = Path(environment["CHANGED_FILES_PATH"])
        listing.write_text("\n".join(changed) + "\n")
    PLANNER["main"]()
    return json.loads(capsys.readouterr().out)


def test_cold_plan_covers_pool_in_balanced_shards(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    """A cold rebuild uses every shard, builds each project once, and balances."""
    plan = _plan(monkeypatch, capsys, COLD="true")
    shards = plan["matrix"]["include"]
    assert plan["mode"] == "sharded"
    assert len(shards) == plan["shard_count"] == PLANNER["MAX_SHARDS"]
    projects = [name for shard in shards for name in shard["projects"].split()]
    assert sorted(projects) == sorted(PLANNER["unit_sources"]())
    loads = plan["shard_seconds"]
    assert len(loads) == len(shards)
    assert max(loads) <= 1.25 * sum(loads) / len(loads)


def test_dirty_projects_are_sharded_by_cost_only_when_large(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    tmp_path: Path,
) -> None:
    """A many-project refactor shards just those projects; a small edit does not."""
    monkeypatch.chdir(ROOT)
    counts = {name: len(paths) for name, paths in PLANNER["unit_sources"]().items()}
    largest = sorted(counts, key=lambda name: (-counts[name], name))[:6]
    assert sum(counts[name] for name in largest) >= PLANNER["SHARD_MIN_FILES"]
    listing = str(tmp_path / "changed.txt")
    changed = [f"LeanPool/{name}/Changed.lean" for name in largest]
    plan = _plan(monkeypatch, capsys, changed, CHANGED_FILES_PATH=listing)
    assert plan["mode"] == "sharded"
    projects = [
        name
        for shard in plan["matrix"]["include"]
        for name in shard["projects"].split()
    ]
    assert sorted(projects) == sorted(largest)
    single = _plan(monkeypatch, capsys, changed[:1], CHANGED_FILES_PATH=listing)
    assert single["mode"] == "single"


def test_checked_in_costs_are_well_formed() -> None:
    """The committed measurement parses and holds non-negative seconds."""
    document = json.loads((ROOT / "scripts/ci/build-costs.json").read_text())
    seconds = document["seconds"]
    assert seconds and list(seconds) == sorted(seconds)
    assert all(isinstance(value, int) and value >= 0 for value in seconds.values())
    assert PLANNER["load_measured_costs"]() == {
        name: float(value) for name, value in seconds.items()
    }
