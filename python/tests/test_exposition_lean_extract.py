"""Check the real pinned-Lean extractor on shared expressions and small oracles."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]


def test_embedded_names_preserve_semantics_without_expanding_shared_nodes(
    tmp_path, monkeypatch
):
    """Compile the actual extractor, then compare name sets and detect DAG replay."""
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    lean = (
        Path.home()
        / ".elan/toolchains"
        / toolchain.replace(":", "---").replace("/", "--")
        / "bin/lean"
    )
    if not lean.exists():
        if os.environ.get("LEAN_POOL_REQUIRE_TEST_TOOLCHAIN") == "1":
            pytest.fail(f"required pinned Lean toolchain unavailable: {toolchain}")
        pytest.skip("pinned Lean toolchain unavailable")
    script = ROOT / "scripts/exposition/Extract.lean"
    subprocess.run(
        [str(lean), "-o", str(tmp_path / "Extract.olean"), script.name],
        cwd=script.parent,
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    monkeypatch.setenv("LEAN_PATH", str(tmp_path))
    result = subprocess.run(
        [str(lean), str(script.parent / "tests/EmbeddedNames.lean")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "shared-expression regression passed" in result.stdout
