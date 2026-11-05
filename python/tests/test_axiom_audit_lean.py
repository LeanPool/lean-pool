"""Exercise the axiom audit against real compiled legacy and module-system files."""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from lean_pool.quality import _AXIOM_AUDIT_PREFIX, _audit_axioms


def test_compiled_axiom_audit(tmp_path: Path) -> None:
    """Audit public roots, including generated names, through private dependencies."""
    pin = (Path(__file__).resolve().parents[2] / "lean-toolchain").read_text().strip()
    lake = (
        Path.home()
        / ".elan/toolchains"
        / pin.replace("/", "--").replace(":", "---")
        / "bin/lake"
    )
    if not lake.is_file():
        if os.environ.get("LEAN_POOL_REQUIRE_TEST_TOOLCHAIN") == "1":
            pytest.fail("required pinned Lean toolchain unavailable")
        pytest.skip("pinned Lean toolchain unavailable")
    (tmp_path / "lean-toolchain").write_text(pin + "\n")
    (tmp_path / "lakefile.toml").write_text(
        'name = "audit_fixture"\n'
        '[[lean_lib]]\nname = "AuditModern"\n'
        '[[lean_lib]]\nname = "AuditLegacy"\n'
        '[[lean_lib]]\nname = "AuditLeaks"\n'
        '[[lean_lib]]\nname = "AuditDependency"\n'
        '[[lean_lib]]\nname = "AuditSmuggled"\n'
    )
    (tmp_path / "AuditDependency.lean").write_text(
        "axiom unusedImportedAxiom : False\n"
    )
    (tmp_path / "AuditModern.lean").write_text(
        "module\nimport Lean\nnamespace AuditModern\n"
        "theorem hiddenUnused : False := by sorry\n"
        "private theorem explicitlyPrivate : False := by sorry\n"
        "axiom hiddenAxiom : False\n"
        "public section\nnoncomputable section Local.Inner\n"
        "theorem good : True := True.intro\n"
        "unsafe def unsafeProof : False := lcProof\n"
        "theorem allowed (p q : Prop) (h : p ↔ q) : p = q := propext h\n"
        "end Local.Inner\nend\nend AuditModern\n"
    )
    (tmp_path / "AuditLegacy.lean").write_text(
        "import Lean\nimport AuditDependency\nnamespace AuditLegacy\n"
        'initialize IO.eprintln "PROJECT_INITIALIZER_EXECUTED"\n'
        "private theorem explicitlyPrivate : False := by sorry\n"
        "theorem good : True := True.intro\n"
        "unsafe def runtime._aux_1 : False := lcProof\n"
        'elab "makeAuditFact" : command => do\n'
        "  Lean.Elab.Command.elabCommand\n"
        "    (← `(theorem generatedFact : True := True.intro))\n"
        "makeAuditFact\nend AuditLegacy\n"
    )
    (tmp_path / "AuditLeaks.lean").write_text(
        "module\nimport all AuditModern\nnamespace AuditLeaks\n"
        "private theorem helper : False := AuditModern.hiddenUnused\n"
        "public theorem leakedSorry : False := helper\n"
        "public theorem leakedAxiom : False := AuditModern.hiddenAxiom\n"
        "public axiom newAxiom : False\n"
        "public theorem named._aux_1 : False := helper\nend AuditLeaks\n"
    )
    build = subprocess.run(
        [str(lake), "build", "AuditModern", "AuditLegacy", "AuditLeaks"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert build.returncode == 0, build.stdout + build.stderr
    processes: list[subprocess.CompletedProcess] = []
    original_run = subprocess.run

    def capture(command: list[str], **kwargs) -> subprocess.CompletedProcess:
        command[0] = str(lake)
        result = original_run(command, **kwargs, timeout=180)
        processes.append(result)
        return result

    with patch("lean_pool.quality.subprocess.run", side_effect=capture):
        errors = _audit_axioms(tmp_path, ["AuditModern", "AuditLegacy", "AuditLeaks"])
    assert processes[0].returncode == 0, processes[0].stdout + processes[0].stderr
    assert "PROJECT_INITIALIZER_EXECUTED" not in processes[0].stdout
    assert "PROJECT_INITIALIZER_EXECUTED" not in processes[0].stderr
    records = [
        json.loads(line.removeprefix(_AXIOM_AUDIT_PREFIX))
        for line in processes[0].stdout.splitlines()
        if line.startswith(_AXIOM_AUDIT_PREFIX)
    ]
    names = {record["name"] for record in records[:-1]}
    assert "AuditModern.good" in names
    assert "AuditLegacy.good" in names
    assert any("generatedFact" in name for name in names)
    assert not any(
        "hiddenUnused" in name or "explicitlyPrivate" in name for name in names
    )
    assert "unusedImportedAxiom" not in names
    assert "AuditModern.unsafeProof" not in names
    assert "AuditLegacy.runtime._aux_1" not in names
    assert len(errors) == 4, errors
    by_name = {error.message.split(" depends on")[0]: error for error in errors}
    assert set(by_name) == {
        "AuditLeaks.leakedSorry",
        "AuditLeaks.leakedAxiom",
        "AuditLeaks.newAxiom",
        "AuditLeaks.named._aux_1",
    }
    assert "sorryAx" in by_name["AuditLeaks.leakedSorry"].message
    assert "hiddenAxiom" in by_name["AuditLeaks.leakedAxiom"].message
    assert "sorryAx" in by_name["AuditLeaks.named._aux_1"].message
    assert by_name["AuditLeaks.leakedSorry"].path == tmp_path / "AuditLeaks.lean"
    assert by_name["AuditLeaks.leakedSorry"].line == 5

    # Skipping unsafe audit roots must not let one prove a safe theorem with them.
    (tmp_path / "AuditSmuggled.lean").write_text(
        "module\nimport AuditModern\n"
        "public theorem smuggled : False := AuditModern.unsafeProof\n"
    )
    rejected = subprocess.run(
        [str(lake), "build", "AuditSmuggled"],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        timeout=180,
    )
    assert rejected.returncode != 0
    diagnostics = rejected.stdout + rejected.stderr
    assert "unsafe" in diagnostics.lower()
    assert "AuditModern.unsafeProof" in diagnostics
    assert "AuditSmuggled.lean:3:" in diagnostics
