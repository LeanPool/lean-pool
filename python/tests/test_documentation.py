"""Prevent API publication from omitting independent project modules."""

import sqlite3
import subprocess
import sys
from pathlib import Path

import pytest

from lean_pool import documentation, indexes


@pytest.fixture
def repository(tmp_path: Path) -> Path:
    """Create single-file and nested projects under the fixed discovery root."""
    (tmp_path / "LeanPool/Beta/Nested").mkdir(parents=True)
    (tmp_path / "docbuild").mkdir()
    for module in ("Alpha", "Beta", "Beta/Nested/Proof"):
        (tmp_path / f"LeanPool/{module}.lean").write_text("module\n")
    (tmp_path / "lakefile.toml").write_text(
        "requiresModuleSystem = true\n[[lean_lib]]\n"
        'name = "LeanPool"\nglobs = ["LeanPool.*"]\n'
    )
    assert indexes.main(["--repo", str(tmp_path), "--project-roots"]) == 0
    return tmp_path


def _page(site: Path, name: str) -> None:
    """Write a nonempty artifact entry."""
    path = site / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("documentation")


def test_fixed_root_does_not_hide_independent_projects(repository: Path) -> None:
    """A root with no imports still selects every complete public project API."""
    before = (repository / "LeanPool.lean").read_bytes()
    assert before.decode() == indexes.DISCOVERY_ROOT
    roots = documentation.documentation_roots(repository)
    assert "LeanPool.Alpha.Imports" in roots
    assert "LeanPool.Beta.Imports" in roots
    assert roots[-4:] == ["Init", "Std", "Lake", "Lean"]
    assert (repository / "LeanPool.lean").read_bytes() == before


def test_new_source_must_enter_public_closure(repository: Path) -> None:
    """Adding a proof cannot silently leave it outside the rendered closure."""
    (repository / "LeanPool/Beta/New.lean").write_text("module\n")
    with pytest.raises(ValueError, match="every source"):
        documentation.documentation_roots(repository)
    assert indexes.main(["--repo", str(repository), "--project-roots"]) == 0
    assert "LeanPool.Beta.Imports" in documentation.documentation_roots(repository)


def test_root_only_site_is_rejected(repository: Path) -> None:
    """The three files accepted by the former check cannot mask missing APIs."""
    site = repository / "docbuild/.lake/build/doc"
    for name in ("index.html", "LeanPool.html", "declarations/declaration-data.bmp"):
        _page(site, name)
    with pytest.raises(ValueError, match="LeanPool/Alpha.html"):
        documentation.validate_site(repository, site)


def test_every_source_page_is_required(repository: Path) -> None:
    """Nested proofs and public wrappers both need nonempty HTML pages."""
    site = repository / "docbuild/.lake/build/doc"
    for path in repository.glob("**/*.lean"):
        _page(site, str(path.relative_to(repository).with_suffix(".html")))
    _page(site, "index.html")
    _page(site, "declarations/declaration-data.bmp")
    documentation.validate_site(repository, site)
    (site / "LeanPool/Beta/Nested/Proof.html").write_text("")
    with pytest.raises(ValueError, match="Nested/Proof.html"):
        documentation.validate_site(repository, site)


def test_renderer_failure_propagates(
    repository: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Failed HTML generation never succeeds because old artifact files exist."""

    def fail(*args: object, **kwargs: object) -> None:
        raise subprocess.CalledProcessError(1, "doc-gen4")

    monkeypatch.setattr(documentation.subprocess, "run", fail)
    with pytest.raises(subprocess.CalledProcessError):
        documentation.build_site(repository, Path("/lake"))


def _checkpoint(repository: Path) -> Path:
    """Create a real database and one completed docInfo module."""
    build = repository / "docbuild/.lake/build"
    (build / "doc-data").mkdir(parents=True)
    (build / "doc-data/LeanPool.Alpha.doc").write_text("completed module")
    database = build / "api-docs.db"
    with sqlite3.connect(database) as connection:
        connection.execute("CREATE TABLE completed (value INTEGER)")
    return database


def _lake(repository: Path, source: str) -> Path:
    """Make a subprocess fixture with the same Lake invocation contract."""
    path = repository / "lake"
    path.write_text(f"#!{sys.executable}\n" + source)
    path.chmod(0o755)
    return path


def test_preparation_timeout_stops_sqlite_writers(repository: Path) -> None:
    """A surviving child writer cannot corrupt or lock the handed-off checkpoint."""
    database = _checkpoint(repository)
    child = """
import signal, sqlite3, time
from pathlib import Path
signal.signal(signal.SIGTERM, signal.SIG_IGN)
connection = sqlite3.connect('.lake/build/api-docs.db')
connection.execute('PRAGMA journal_mode=WAL')
connection.execute('INSERT INTO completed VALUES (1)')
Path('writer-started').touch()
time.sleep(60)
connection.commit()
"""
    lake = _lake(
        repository,
        "import subprocess, sys, time\n"
        f"subprocess.Popen([sys.executable, '-c', {child!r}])\n"
        "time.sleep(60)\n",
    )
    assert not documentation.prepare_data(repository, lake, 1)
    assert (repository / "docbuild/writer-started").exists()
    with sqlite3.connect(database) as connection:
        assert connection.execute("SELECT COUNT(*) FROM completed").fetchone() == (0,)
        connection.execute("INSERT INTO completed VALUES (2)")
    documentation.validate_checkpoint(repository)


def test_preparation_does_not_mask_compiler_failure(repository: Path) -> None:
    """An existing valid checkpoint cannot turn a failed Lake build into success."""
    _checkpoint(repository)
    with pytest.raises(subprocess.CalledProcessError) as error:
        documentation.prepare_data(
            repository, _lake(repository, "raise SystemExit(7)\n"), 1
        )
    assert error.value.returncode == 7


def test_completed_preparation_preserves_database(repository: Path) -> None:
    """Completed preparation hands off inputs while still requiring the renderer."""
    database = _checkpoint(repository)
    assert documentation.prepare_data(repository, _lake(repository, "pass\n"), 1)
    assert database.is_file()
    assert not (repository / "docbuild/.lake/build/doc").exists()


def test_invalid_checkpoint_is_not_publishable(repository: Path) -> None:
    """Interrupted or corrupt inputs are rejected before any cache publication."""
    database = _checkpoint(repository)
    database.write_bytes(b"corrupt SQLite database")
    with pytest.raises(sqlite3.DatabaseError):
        documentation.validate_checkpoint(repository)


def test_empty_pool_data_is_not_a_checkpoint(repository: Path) -> None:
    """A database without a completed pool module cannot seed continuation."""
    _checkpoint(repository)
    (repository / "docbuild/.lake/build/doc-data/LeanPool.Alpha.doc").write_bytes(b"")
    with pytest.raises(ValueError, match="no pool documentation data"):
        documentation.validate_checkpoint(repository)
